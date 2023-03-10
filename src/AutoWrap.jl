module AutoWrap
__precompile__(true)

export AutoWrapContext
export @make_macro, @wrap_with_context

import ExprTools as ET

include("utils.jl")

abstract type AbstractFallbackArg end

struct NewDefUntyped <: AbstractFallbackArg end
struct NewDef <: AbstractFallbackArg end
struct Wrapped <: AbstractFallbackArg end

abstract type AbstractBodyWrapper end

eval_wrapped(::AbstractBodyWrapper, body_fn, args...) = body_fn(NewDef(), args...)

struct PrePostProcessingWrapper{TypedBodyFlag, A, Z} <: AbstractBodyWrapper
    preprocessing_function :: A
    postprocessing_function :: Z
    function PrePostProcessingWrapper(;
        preprocessing_function::A=DEFAULT_PREPROCESSING_FUNCTION,
        postprocessing_function::Z=DEFAULT_POSTPROCESSING_FUNCTION, 
        typed_body::Bool=false
    ) where {A, Z}
        return new{typed_body, A, Z}(preprocessing_function, postprocessing_function)
    end
end
_extra_arg(::PrePostProcessingWrapper{true}) = NewDef()
_extra_arg(::PrePostProcessingWrapper{false}) = NewDefUntyped()
function eval_wrapped(w::PrePostProcessingWrapper, body_fn, args...)
    (_args, meta) = w.preprocessing_function(args...)
    ret = body_fn(_args...)
    return w.postprocessing_function(ret, meta)
end

abstract type AbstractNewMethodCondition end
struct NewMethodCondition <: AbstractNewMethodCondition
end
check_condition(::NewMethodCondition, sigtt, mdict) = true

abstract type AbstractArgTypesMapping end

"Map a method signature to at least one new signature (or an iterable of signatures)."
apply_type_mapping(::AbstractArgTypesMapping, sigtt, query_sigtt) = sigtt

function handle_new_sigs(::AbstractArgTypesMapping, vec_new_sigtt, vec_prev_sigtt)
    return tt_union(vec_new_sigtt, vec_prev_sigtt)
end
function handle_existing_sigs(::AbstractArgTypesMapping, vec_new_sigtt, vec_existing_sigtt)
    return setdiff(vec_new_sigtt, vec_existing_sigtt)
end

const DEFAULT_PREPROCESSING_FUNCTION(args...) = ((NewDef(), args...), nothing)
const (DEFAULT_POSTPROCESSING_FUNCTION(ret::R, meta)::R) where R = ret

const DEFAULT_NEW_METHOD_CONDITION(@nospecialize(arg_tuple_type)) = true

DEFAULT_ARG_TYPE_MAPPING(T) = T
DEFAULT_ARG_TYPE_MAPPING(tv::TypeVar) = tv.ub

Base.@kwdef struct ArgTypeExpander{F} <: AbstractArgTypesMapping
    arg_type_mapping :: F = DEFAULT_ARG_TYPE_MAPPING
    drop_n :: Int = 0
end

function apply_type_mapping(m::ArgTypeExpander, _sigtt, query_sigtt)
    sigtt = typeintersect(
        _sigtt, query_sigtt
    )
    sig_params = ET.parameters(sigtt)
    func_t = sig_params[1]
    arg_ts = sig_params[2:end]

    type_mapping = m.arg_type_mapping
    drop_n = m.drop_n

    atype_options = Any[]
    for atype in arg_ts
        # NOTE if `atype` is not a type variable, then it could have free type variables here. 
        # is this a problem? We **do** rewrap below...
        _aopts = try
            type_mapping(atype)
        catch e
            if e isa MethodError && atype isa TypeVar
                type_mapping(atype.ub)
            else
                throw(e)
            end
        end
        aopts = ensure_iterable(_aopts)
        push!(atype_options, aopts)
    end

    vec_new_sigtt = collect(
        Any, 
        map(Iterators.drop(Iterators.product( atype_options... ), drop_n)) do ttuple
            Base.rewrap_unionall( Tuple{func_t, ttuple... }, sigtt )
        end
    )
    return tt_unique(vec_new_sigtt)
end

function gather_existing_sigtts(
    func, query_sigtt, method_mods=nothing
)
    ret_vec = Any[]
    isnothing(method_mods) && return ret_vec
    ms = if isempty(method_mods)
        methods(func, query_sigtt)
    else
        methods(func, query_sigtt, method_mods)
    end
    for met in ms
        _sigtt = met.sig
        push!(ret_vec, _sigtt)
    end 
    return ret_vec
end

function sigtt_from_sigdict_expr(sigdict)
    quote
        Tuple{ typeof($(sigdict[:name])), $(sigdict[:arg_type_exs]...) } where{
            $(sigdict[:whereparams]...)
        }
    end
end

@nospecialize
function create_typed_body_method(
    eval_mod, body_fn, sigtt
)
    mdict = ET.signature(sigtt)
    inner_args = isempty(mdict[:args]) ? Symbol[] : _arg_name_expr.(mdict[:args])
    pushfirst!(mdict[:args], :(::$(NewDef)))
    mdict[:body] = quote
        $(body_fn)( $(NewDefUntyped()), $(inner_args...) )
    end

    method_expr = ET.combinedef(mdict)
    Core.eval(eval_mod, method_expr)
end
@specialize

function create_wrapped_body_method(
    eval_mod, body_wrapper, body_fn, sigtt
)
    global eval_wrapped
    mdict = ET.signature(sigtt)
    inner_args = isempty(mdict[:args]) ? Symbol[] : _arg_name_expr.(mdict[:args])
    pushfirst!(mdict[:args], :(::$(Wrapped)))
    mdict[:body] = quote
        $(eval_wrapped)( $(body_wrapper), $(body_fn), $(inner_args...) )
    end

    method_expr = ET.combinedef(mdict)
    Core.eval(eval_mod, method_expr)
end

function define_methods_for_new_sigtts(
    eval_mod, body_fn, new_sigtts, new_method_condition
)
    # build method definitons from the type option tuples
    func_name = :((::$(typeof(body_fn))))
    for stt in new_sigtts
        mdict = ET.signature(stt)
        mdict[:name] = func_name
        inner_args = isempty(mdict[:args]) ? Symbol[] : _arg_name_expr.(mdict[:args])
        mdict[:body] = quote
            return $(body_fn)($(Wrapped()), $(inner_args...))
        end
        if check_condition(new_method_condition, stt, mdict)
            method_expr = ET.combinedef(mdict)
            Core.eval(eval_mod, method_expr)
        end
    end
    @debug "AutoWrap.jl: Time for new method definitions: $(stats.time) secs."
    return nothing
end

Base.@kwdef struct WrappingContextDev1
    arg_types_mapping :: AbstractArgTypesMapping = ArgTypeExpander()
    body_wrapper :: AbstractBodyWrapper = PrePostProcessingWrapper()
    method_lookup_modules :: Union{Nothing, Vector{<:Module}} = nothing
end
Base.@kwdef struct WrappingContextDev2
    arg_types_mapping :: AbstractArgTypesMapping = ArgTypeExpander()
    body_wrapper :: AbstractBodyWrapper = PrePostProcessingWrapper()
    new_method_condition :: AbstractNewMethodCondition = NewMethodCondition()
    method_lookup_modules :: Union{Nothing, Vector{<:Module}} = nothing
end
WrappingContext = WrappingContextDev2
export WrappingContext

macro contextual_wrap(ctx, func_ex)
    func_def = safe_splitdef(func_ex)
    efunc_name = :($(esc(func_def[:name])))
    ectx = :($(esc(ctx)))
    quote
        $(esc(generic_fallback_expr(func_def)))
        sigtt = $(esc(sigtt_from_sigdict_expr(func_def)))
        wrapper = $(ectx).body_wrapper
        $(create_typed_body_method)($(__module__), $(efunc_name), sigtt)
        $(create_wrapped_body_method)($(__module__), wrapper, $(efunc_name), sigtt)

        atm = $(ectx).arg_types_mapping

        new_sigtts = $(apply_type_mapping)(atm, sigtt, sigtt)
        existing_sigtts = $(gather_existing_sigtts)(
            $(efunc_name), sigtt, $(ectx).method_lookup_modules,
        )
        for esigtt in existing_sigtts
            more_sigtts = $(apply_type_mapping)(atm, esigtt, sigtt)
            new_sigtts = $(handle_new_sigs)(atm, more_sigtts, new_sigtts)
        end
        new_sigtts = $(handle_existing_sigs)(atm, new_sigtts, existing_sigtts)

        $(define_methods_for_new_sigtts)(
            $(__module__), $(efunc_name), new_sigtts, $(ectx).new_method_condition,
        )
    end
end
export @contextual_wrap

"""
    AutoWrapContext(;
        arg_type_mapping = DEFAULT_ARG_TYPE_MAPPING,
        preprocessing_function = DEFAULT_PREPROCESSING_FUNCTION,
        postprocessing_function = DEFAULT_POSTPROCESSING_FUNCTION,
        method_lookup_modules = nothing,
        check_hasmethod = false,
        typed_body = false
    )

Return a context for automatically wrapping a function definition with 
[`@wrap_with_context`](@Ref).

# Keyword arguments:
* `arg_type_mapping::Any`: A function mapping types or type variables to types or type  
  variables or tuples thereof.
* `preprocessing_function::Any`: A function mapping the arguments `args...` to a tuple  
  `(_args, meta)` before they are plugged into the body of the originial function definition.
* `postprocessing_function::Any`: A function mapping `(ret, meta)` to the return value of 
  the overspecialized method, where `ret` is the return value resulting from evaluating the 
  originial function body on `_args`, and `(_args, meta)` results from calling 
  `preprocessing_function`.
* `method_lookup_modules::Union{Nothing, Vector{<:Modules}}`: List of modules to look up  
  method definitions in (or `nothing` to skip method lookup).
* `check_hasmethod::Bool`: Bool indicating whether to check for existing methods before  
  defining them.
* `typed_body::Bool`: Bool indicating whether or not to artificially throw a 
  MethodError for signatures not meant to exist for the function body...
"""# TODO update docstring
Base.@kwdef struct AutoWrapContext

    "A function mapping types or type variables to types or type variables or tuples thereof."
    arg_type_mapping :: Any = DEFAULT_ARG_TYPE_MAPPING

    "A function mapping the tuple of arguments `args` to a tuple `(_args, meta)` before they
    are plugged into the body of the originial function definition."
    preprocessing_function :: Any = DEFAULT_PREPROCESSING_FUNCTION

    "A function mapping `(ret, meta)` to the return value of the overspecialized method, 
    where `ret` is the return value resulting from evaluating the originial function body 
    on `_args`, and `(_args, meta)` results from calling `preprocessing_function`."
    postprocessing_function :: Any = DEFAULT_POSTPROCESSING_FUNCTION

    "List of modules to look up method definitions in (or `nothing` for calling scope)."
    method_lookup_modules :: Union{Nothing, Vector{<:Module}} = nothing

    "Bool indicating whether to check for existing methods before overwriting them."
    check_hasmethod :: Bool = false

    typed_body :: Bool = false
end

# helper inspired by ExprTools
_is_func_expr(ex) = false
_is_func_expr(ex::Expr) = (ex.head === :function || ex.head === :(=) || ex.head === :(->))

function _assert_ctx_ex(ctx_expr, macro_name="@macro_name")
    @assert(
        ctx_expr isa Symbol || Meta.isexpr(ctx_expr, :(=)),
        "`$(macro_name)`: Argument must be the name of a previously defined `AutoWrapContext`
        or an assignment like `ctx = AutoWrapContext(; ...)`."
    )
end

macro wrap_with_context(ctx_ex, func_ex, macro_name="@wrap_with_context")
    _assert_ctx_ex(ctx_ex, macro_name)
    return quote
        $(make_closure_expr(__module__, ctx_ex, func_ex))
    end
end

macro make_macro(ctx_expr)
    _assert_ctx_ex(ctx_expr, "@make_macro")

    ctx_name = if ctx_expr isa Symbol
        ctx_expr
    else
        first(ctx_expr.args)
    end
    ctx_copy_var = gensym(ctx_name)
    macro_name = Symbol(ctx_name, "_wrap")

    quote
        $(
            if !isa(ctx_expr, Symbol)
                # make sure, an AutoWrapContext object exists and is assigned to `$(ctx_name)`
                esc(ctx_expr)
            end
        )

        $(esc(ctx_copy_var)) = $(esc(ctx_name));

        macro $(esc(macro_name))(func_def_expr)
            quote
                # $($(wrap_with_context)) $($(Meta.quot(ctx_copy_var))) $(func_def_expr) $($("@" * string(macro_name)))
                $(make_closure_expr($(__module__), $(esc(ctx_copy_var)), func_def_expr))
            end
        end
    end
end


# https://github.com/JuliaLang/julia/issues/48777
"""
    contains_type(arr, tuple_type)

Return `true` if the type `tuple_type` is already stored in `arr`.
"""
function contains_type(arr, tuple_type)
    for tt in arr
        if tt == tuple_type
            return true
        end
    end
    return false
end

# helper to ensure tuple format (important for when `arg_type_mapping` does not return tuples)


"""
    _type_options_for_sig_arg_tuple!(unique_tuple_types_arr, sig_tuple_type, type_mapping, drop_n=1)

Fill the array `unique_tuple_types_arr` with tuple types, the parameters of which describe method
argument types. `type_mapping` is an function mapping types and type variables to types and 
type variables or tuples of either and `drop_n` is an internal varible to filter
redundant tuples.
"""#TODO update docstring
function _type_options_for_sig_arg_tuple!(
    unique_tuple_types_arr, existing_tuple_types, @nospecialize(sig_tuple_type), type_mapping, check_hasmethod, drop_n=0
)
    
    sig_params = ET.parameters(sig_tuple_type)

    atype_options = Any[]
    for atype in sig_params
        # NOTE if `atype` is not a type variable, then it could have free type variables here. 
        # is this a problem? If so, we can easily rewrap (see below)
        _aopts = try
            type_mapping(atype)
        catch e
            if e isa MethodError && atype isa TypeVar
                type_mapping(atype.ub)
            else
                throw(e)
            end
        end
        aopts = ensure_iterable(_aopts)
        push!(atype_options, aopts)
    end

    for ttuple in Iterators.drop(Iterators.product( atype_options... ), drop_n)
        tuple_type = Base.rewrap_unionall( Tuple{ ttuple... }, sig_tuple_type )
        if check_hasmethod && contains_type(@show(existing_tuple_types), @show(tuple_type))
            continue
        end
        if contains_type(unique_tuple_types_arr, tuple_type)
            continue
        end
        push!(unique_tuple_types_arr, tuple_type)
    end
    nothing
end

"""
    safe_splitdef(func_expr)

Like `ExprTools.splitdef`, but keys `:args` and `:whereparams` exist unconditionallly.
We also create entries for `:arg_name_exs` and `arg_type_exs`.

See also: [`ET.splitdef`](@ref)
"""
function safe_splitdef(func_ex)
    func_def = ET.splitdef(func_ex)
    if !haskey(func_def, :args)
        func_def[:args] = Expr[]
    end
    if !haskey(func_def, :whereparams)
        func_def[:whereparams] = Symbol[]
    end
    func_def[:arg_type_exs] = _arg_type_expr.(func_def[:args])
    func_def[:arg_name_exs] = _arg_name_expr.(func_def[:args])

    return func_def
end

"""
    define_methods(
        eval_module, body_fn, new_method_signature_tuple_types, arg_name_exprs, check_hasmethod
    )

Iteratively define new methods for `(::typeof(body_fn))` in Module `eval_mod` for the 
argument types defined in `new_method_signature_tuple_types` by calling `eval`.
If `check_hasmethod` is `true`, then the method is only defined if it does not exist already.
"""
function define_methods(
    eval_mod, body_fn, new_ms_tuple_types, arg_name_exs, check_hasmethod,
)
    # build method definitons from the type option tuples
    func_name = :((::$(typeof(body_fn))))
    for stt in new_ms_tuple_types
        mdict = signature_without_name(stt)
        mdict[:name] = func_name
        _match_argnames!(mdict, arg_name_exs)       # or re-parse argument names from `mdict`
        mdict[:body] = quote
            return $(body_fn)($(Wrapped()), $(arg_name_exs...))
        end
        method_expr = ET.combinedef(mdict)
        if check_hasmethod
            method_expr = quote
                display( $(stt) )
                if !hasmethod($(body_fn), $(stt))
                    println("DEFINE")
                    @eval $(method_expr)
                end
            end
        end
        Core.eval(eval_mod, method_expr)
    end
    @debug "AutoWrap.jl: Time for new method definitions: $(stats.time) secs."
    return nothing
end

function make_newdef_fallback(
    eval_mod, fallback_fn, arg_name_exs, @nospecialize(arg_tuple_type)
)
    func_name = :((::$(typeof(fallback_fn))))
    mdict = signature_without_name(arg_tuple_type)
    mdict[:name] = func_name
    _match_argnames!(mdict, arg_name_exs)
    pushfirst!(mdict[:args], :(::$(NewDef)))
    mdict[:body] = quote
        $(fallback_fn)($(NewDefUntyped()), $(arg_name_exs...))
    end
    method_expr = ET.combinedef(mdict)
    Core.eval(eval_mod, method_expr)
end

function make_wrapped_fallback(
    eval_mod, fallback_fn, arg_name_exs, preprocessing_function, postprocessing_function,
)
    mdict = Dict(
        :name => :((::$(typeof(fallback_fn)))),
        :args => Vector{Any}(arg_name_exs),
    )
    pushfirst!(mdict[:args], :(::$(Wrapped)))
    mdict[:body] = quote
        _args, meta = $(preprocessing_function)($(arg_name_exs...))
        ret = $(fallback_fn)(_args...)
        return $(postprocessing_function)(ret, meta) 
    end
    method_expr = ET.combinedef(mdict)
    Core.eval(eval_mod, method_expr)
end

function generic_fallback_expr(func_def)
    fallback_def = copy(func_def)
    empty!(fallback_def[:args])
    push!(fallback_def[:args], :(::$(NewDefUntyped)))
    append!(fallback_def[:args], fallback_def[:arg_name_exs])
    return ET.combinedef(fallback_def)
end

function make_closure_expr(
    __module__, ctx_ex, func_ex
)
    ctx_dict = ctx_gensyms()
    
    func_def = safe_splitdef(func_ex)
    func_name = haskey(func_def, :name) ? func_def[:name] : error("Cannot specialize an unnamed anonymous function.")
    func_nargs = length(func_def[:args])

    fallback_untyped_expr = generic_fallback_expr(func_def) |> esc

    defined_methods_sym = gensym("defined_methods")
    existing_tuple_types_sym = gensym("existing_tuple_types")
    arg_tuple_type_sym = gensym("arg_tuple_type")
    new_ms_tuple_types_sym = gensym("new_ms_tuple_types")

    def_globals_expr = quote
        # Declaration as global constants is crucial for performance
        # `deepcopy` is mostly a no-op though (except maybe for anonymous functions)
        Core.eval( 
            $(__module__), 
            quote 
                let ctx = $($(ctx_ex));
                $(
                    [ 
                        :(global const $(gs) = getfield(ctx, $(Meta.quot(fn))))
                            for (fn, gs) in $(ctx_dict) 
                    ]...
                )
                end#let
            end
        )
    end |> esc

    gather_sig_types_expr = quote
        $(existing_tuple_types_sym) = Any[]
        if !isnothing($(ctx_dict[:method_lookup_modules]))
            $(defined_methods_sym) = methods($(func_name), $(arg_tuple_type_sym), $(ctx_dict[:method_lookup_modules]))
            for m in $(defined_methods_sym)
                sig_tuple_type = Base.rewrap_unionall(
                    Tuple{Base.unwrap_unionall(m.sig).parameters[2:end]...}, 
                    m.sig
                )
                m_tuple_type = typeintersect(sig_tuple_type, $(arg_tuple_type_sym))
                push!($(existing_tuple_types_sym), sig_tuple_type)
                $(_type_options_for_sig_arg_tuple!)(
                    $(new_ms_tuple_types_sym), $(existing_tuple_types_sym), m_tuple_type, $(ctx_dict[:arg_type_mapping]), $(ctx_dict[:check_hasmethod])
                )
            end 
        end
    end |> esc

    return quote
        $(def_globals_expr)
        
        $(fallback_untyped_expr)

        $(esc(new_ms_tuple_types_sym)) = $(esc(:(Any[])))
        $(esc(arg_tuple_type_sym)) = $(esc(:(
            Tuple{
                $(func_def[:arg_type_exs]...)} where {$(func_def[:whereparams]...)
            }
        )))

        fback_arg_tuple_type = if $(esc(ctx_dict[:typed_body]))
            $(esc(arg_tuple_type_sym))
        else
            $(esc(:(NTuple{$(func_nargs), Any})))
        end
        
        $(make_newdef_fallback)(
            $(__module__), $(esc(func_name)), $(func_def[:arg_name_exs]), fback_arg_tuple_type
        )
        $(make_wrapped_fallback)(
            $(__module__), $(esc(func_name)), $(func_def[:arg_name_exs]),
            $(esc(ctx_dict[:preprocessing_function])), $(esc(ctx_dict[:postprocessing_function]))
        )
                
        $(_type_options_for_sig_arg_tuple!)(
            $(esc(new_ms_tuple_types_sym)), [], $(esc(arg_tuple_type_sym)), 
            $(esc(ctx_dict[:arg_type_mapping])), $(esc(ctx_dict[:check_hasmethod]))
        )

        initial_tuple_type_indices = $(esc(:(eachindex($(new_ms_tuple_types_sym)))))

        $(gather_sig_types_expr)

        # the list of existing function signature types did not yet exist when making 
        # the first few new signatures; check them now:
        if $(esc(ctx_dict[:check_hasmethod])) && !isempty($(esc(existing_tuple_types_sym)))
            del_indices = empty(initial_tuple_type_indices)
            for i in initial_tuple_type_indices
                if $(contains_type)($(esc(existing_tuple_types_sym)), $(esc(new_ms_tuple_types_sym))[i])
                    push!(del_indices, i)
                end
            end
            deleteat!($(esc(new_ms_tuple_types_sym)), del_indices)
        end
        
        $(define_methods)(
            $(__module__), $(esc(func_name)), $(esc(new_ms_tuple_types_sym)), $(func_def[:arg_name_exs]), 
            $(esc(ctx_dict[:check_hasmethod]))
            #$(esc(ctx_dict[:new_method_condition]))
        )
    end
end


function ctx_gensyms()
    Dict(
        fn => gensym("ctx_" * string(fn)) for fn = fieldnames(AutoWrapContext)
    )
end

function empty_args!(mdict)
    if haskey(mdict, :args)
        empty!(mdict[:args])
    else
        mdict[:args] = Expr[]
    end
    return nothing
end

# modified version of `ET.signature` to work on Tuple types missing function type as 
# first parameter
function signature_without_name(@nospecialize(orig_sig::Type{<:Tuple}); extra_hygiene=false)
    sig = extra_hygiene ? ET._truly_rename_unionall(orig_sig) : orig_sig
    def = Dict{Symbol, Any}()

    #=
    opT = parameters(sig)[1]
    def[:name] = :(op::$opT)
    =#

    arg_types = ET.name_of_type.(ET.parameters(sig))#(ET.argument_types(sig))
    arg_names = [Symbol(:x, ii) for ii in eachindex(arg_types)]
    def[:args] = [ Expr(:(::), aname, atype) for (aname, atype) = zip(arg_names, arg_types) ]
    def[:whereparams] = ET.where_parameters(sig)

    filter!(kv->last(kv)!==nothing, def)  # filter out nonfields.
    return def
end

"Modify `sig_dict[:args]` to match the names in `arg_name_exs`."
function _match_argnames!(sig_dict, arg_name_exs)
    old_args = deepcopy(sig_dict[:args])
    empty_args!(sig_dict)
    for (i, arg_ex) in enumerate(old_args)
        push!(sig_dict[:args], :($(arg_name_exs[i])::$(_arg_type_expr(arg_ex))))
    end
    nothing
end

function strip_lineno(expr::Expr)
    return strip_lineno!(copy(expr))
end

# taken from `strip_lineno` in ExprTools/test/function.jl
function strip_lineno!(expr::Expr)
    filter!(expr.args) do ex
        isa(ex, LineNumberNode) && return false
        if isa(ex, Expr)
            ex.head === :line && return false
            strip_lineno!(ex::Expr)
        end
        return true
    end
    return expr
end

end#module