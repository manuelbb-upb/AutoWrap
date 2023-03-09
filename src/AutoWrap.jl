module AutoWrap
__precompile__(true)

export AutoWrapContext
export @make_macro, @wrap_with_context

import ExprTools as ET

abstract type AbstractFallbackArg end

struct FallbackUntyped <: AbstractFallbackArg end
struct FallbackTyped <: AbstractFallbackArg end
struct Fallback <: AbstractFallbackArg end

const DEFAULT_PREPROCESSING_FUNCTION(args...) = (args, nothing)
const (DEFAULT_POSTPROCESSING_FUNCTION(ret::R, meta)::R) where R = ret

DEFAULT_ARG_TYPE_MAPPING(T) = T
DEFAULT_ARG_TYPE_MAPPING(tv::TypeVar) = tv.ub

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
"""
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

    "Bool indicating whether to check for existing methods before defining them."
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

"""
    _arg_type_expr(arg_expr)

Return the type expression parsed from `arg_expr`. `arg_ex` comes from a method definition 
and can be as simple as `arg_name` or `arg_name::arg_type`, but all valid expressions are 
possible.
"""
function _arg_type_expr(arge)
    if Meta.isexpr(arge, :(::), 2)  
        # :(arg_name :: arg_type) ↦ :(arg_type)
        # :(arg_name :: arg_type{type_var_symbol}) ↦ :(arg_type{type_var_symbol})
        # :(arg_name :: arg_type{type_var_symbol} where {type_var_symbol}) ↦
        #   :(arg_type{type_var_symbol} where {type_var_symbol})
        # :(arg_name :: Vararg{...}) ↦ :(Vararg{...})
        return arge.args[2]
    elseif Meta.isexpr(arge, :(::), 1) 
        # :(:: arg_type) ↦ :(arg_type)
        return arge.args[1]
    elseif Meta.isexpr(arge, :(...), 1)
        # :(args...) ↦ :(Vararg{Any})
        # :(args::Int...) ↦ :(Vararg{Int})
        return :(Vararg{$(_arg_type_expr(arge.args[1]))})
    else
        return :Any
    end
end

"""
    _arg_name_expr(arg_expr)

Return the argument name parsed from `arg_expr`. `arg_ex` comes from a method definition 
and can be as simple as `arg_name` or `arg_name::arg_type`, but all valid expressions are 
possible.
"""
_arg_name_expr(arge::Symbol) = arge
function _arg_name_expr(arge)
    Meta.isexpr(arge, :(::), 2) && return arge.args[1]
    return gensym("unused")
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
ensure_iterable(t::Tuple)=t
ensure_iterable(t::Vector)=t
ensure_iterable(x) = (x,)

"""
    _type_options_for_sig_arg_tuple!(unique_tuple_types_arr, sig_tuple_type, type_mapping, drop_n=1)

Fill the array `unique_tuple_types_arr` with tuple types, the parameters of which describe method
argument types. `type_mapping` is an function mapping types and type variables to types and 
type variables or tuples of either and `drop_n` is an internal varible to filter
redundant tuples.
"""
function _type_options_for_sig_arg_tuple!(unique_tuple_types_arr, sig_tuple_type, type_mapping, drop_n=0)
    
    sig_params = ET.parameters(sig_tuple_type)

    atype_options = Any[]
    for atype in sig_params
        # NOTE if `atype` is not a type variable, then it could have free type variables here. 
        # is this a problem? If so, we can easily rewrap (see below)
        push!(atype_options, ensure_iterable(type_mapping(atype)))
    end

    for ttuple in Iterators.drop(Iterators.product( atype_options... ), drop_n)
        tuple_type = Base.rewrap_unionall( Tuple{ ttuple... }, sig_tuple_type )
        #if !(tuple_type in unique_tuple_types_arr)
        if !(contains_type(unique_tuple_types_arr, tuple_type))
            push!(unique_tuple_types_arr, tuple_type)
        end
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
            return $(body_fn)($(Fallback()), $(arg_name_exs...))
        end
        method_expr = ET.combinedef(mdict)
        if check_hasmethod
            method_expr = quote
                if !hasmethod($(body_fn), $(stt))
                    @eval $(method_expr)
                end
            end
        end
        Core.eval(eval_mod, method_expr)
    end
    return nothing
end

function make_wrapped_fallback(
    eval_mod, fallback_fn, arg_name_exs, arg_tuple_type
)
    func_name = :((::$(typeof(fallback_fn))))
    mdict = signature_without_name(arg_tuple_type)
    mdict[:name] = func_name
    _match_argnames!(mdict, arg_name_exs)
    pushfirst!(mdict[:args], :(::$(FallbackTyped)))
    mdict[:body] = quote
        $(fallback_fn)($(FallbackUntyped()), $(arg_name_exs...))
    end
    method_expr = ET.combinedef(mdict)
    Core.eval(eval_mod, method_expr)
end

function make_final_fallback(
    eval_mod, fallback_fn, arg_name_exs, preprocessing_function, postprocessing_function,
)
    mdict = Dict(
        :name => :((::$(typeof(fallback_fn)))),
        :args => Vector{Any}(arg_name_exs),
    )
    pushfirst!(mdict[:args], :(::$(Fallback)))
    mdict[:body] = quote
        _args, meta = $(preprocessing_function)($(arg_name_exs...))
        ret = $(fallback_fn)($(FallbackTyped()), _args...)
        return $(postprocessing_function)(ret, meta) 
    end
    method_expr = ET.combinedef(mdict)
    Core.eval(eval_mod, method_expr)
end

function generic_fallback_expr(func_def)
    fallback_def = copy(func_def)
    empty!(fallback_def[:args])
    push!(fallback_def[:args], :(::$(FallbackUntyped)))
    append!(fallback_def[:args], fallback_def[:arg_name_exs])
    return ET.combinedef(fallback_def) |> esc
end

function make_closure_expr(
    __module__, ctx_ex, func_ex
)
    ctx_dict = ctx_gensyms()
    
    func_def = safe_splitdef(func_ex)
    func_name = haskey(func_def, :name) ? func_def[:name] : error("Cannot specialize an unnamed anonymous function.")
    func_nargs = length(func_def[:args])

    fallback_untyped_expr = generic_fallback_expr(func_def)

    def_globals_expr = quote
        # Declaration as global constants is crucial for performance
        # `deepcopy` is mostly a no-op though (except maybe for anonymous functions)
        Core.eval( 
            $(__module__), 
            quote 
                let ctx = $($(ctx_ex));
                $(
                    [ 
                        :(global const $(gs) = deepcopy(getfield(ctx, $(Meta.quot(fn)))))
                            for (fn, gs) in $(ctx_dict) 
                    ]...
                )
                end#let
            end
        )
    end |> esc

    gather_sig_types_expr = quote
        if !isnothing($(ctx_dict[:method_lookup_modules]))
            defined_methods = methods($(func_name), $(ctx_dict[:method_lookup_modules]))

            for m in defined_methods
                m_tuple_type = typeintersect(
                    Base.rewrap_unionall(Base.unwrap_unionall(m.sig).parameters[2:end], m.sig),
                    arg_tuple_type
                )
                $(_type_options_for_sig_arg_tuple!)(
                    new_ms_tuple_types, m_tuple_type, $(ctx_dict[:arg_type_mapping])
                )
            end 
        end
    end |> esc

    return quote
        $(def_globals_expr)
        
        $(fallback_untyped_expr)

        new_ms_tuple_types = $(esc(:(Any[])))
        arg_tuple_type = $(esc(:(
            Tuple{
                $(func_def[:arg_type_exs]...)} where {$(func_def[:whereparams]...)
            }
        )))

        fback_arg_tuple_type = if $(esc(ctx_dict[:typed_body]))
            arg_tuple_type
        else
            $(esc(:(NTuple{$(func_nargs), Any})))
        end
        
        $(make_wrapped_fallback)(
            $(__module__), $(esc(func_name)), $(func_def[:arg_name_exs]), fback_arg_tuple_type
        )
        $(make_final_fallback)(
            $(__module__), $(esc(func_name)), $(func_def[:arg_name_exs]),
            $(esc(ctx_dict[:preprocessing_function])), $(esc(ctx_dict[:postprocessing_function]))
        )
                
        $(_type_options_for_sig_arg_tuple!)(
            new_ms_tuple_types, arg_tuple_type, 
            $(esc(ctx_dict[:arg_type_mapping]))
        )

        $(gather_sig_types_expr)
        
        $(define_methods)(
            $(__module__), $(esc(func_name)), new_ms_tuple_types, $(func_def[:arg_name_exs]), 
            $(esc(ctx_dict[:check_hasmethod]))
        )
    end
end

#=
function make_closure_expr(
    __module__, ctx_ex, func_ex
)
    ctx_global_syms_dict = ctx_gensyms()
    
    func_def = safe_splitdef(func_ex)
    func_name = haskey(func_def, :name) ? func_def[:name] : error("Cannot specialize an unnamed anonymous function.")

    func_body_symb = gensym("func_body")
    func_body_symb_typed = gensym("func_body_typed")
    func_body_symb_untyped = gensym("func_body_untyped")

    # make the expressions for the fallback funtion body(s)
    cl_body_np_ex_typed = make_fallback_noprocessing_expr(func_def, func_body_symb, true)
    cl_body_np_ex_untyped = make_fallback_noprocessing_expr(func_def, func_body_symb, false)
    #cl_body_np_ex_typed = make_fallback_noprocessing_expr_anon(func_def, true)
    #cl_body_np_ex_untyped = make_fallback_noprocessing_expr_anon(func_def, false)
    cl_body_np_ex_user = make_fallback_noprocessing_expr_for_user(func_def, func_body_symb)
    cl_body_ex = make_fallback_expr(
        func_def, func_body_symb, ctx_global_syms_dict[:preprocessing_function], 
        ctx_global_syms_dict[:postprocessing_function]
    )

    return quote
        # Declaration as global constants is crucial for performance
        # `deepcopy` is mostly a no-op though (except maybe for anonymous functions)
        Core.eval( 
            $(__module__), 
            quote 
                let ctx = $($(esc(ctx_ex)));
                $(
                    [ 
                        :(global const $(gs) = deepcopy(getfield(ctx, $(Meta.quot(fn)))))
                            for (fn, gs) in $(ctx_global_syms_dict) 
                    ]...
                )
                end#let
            end#quote
        )
        
        #=$(esc(func_body_symb)) = if $(esc(ctx_global_syms_dict[:typed_body]))
            $(esc(cl_body_np_ex_typed))
        else
            $(esc(cl_body_np_ex_untyped))
        end=#
        $(esc(cl_body_np_ex_typed))
        $(esc(cl_body_np_ex_untyped))
        #=$(esc(func_body_symb)) = if $(esc(ctx_global_syms_dict[:typed_body])) isa Val{true}
            $(esc(func_body_symb_typed))
        else
            $(esc(func_body_symb_untyped))
        end=#
        @show isconst($(__module__), $(Meta.quot(ctx_global_syms_dict[:typed_body])))
        $(esc(cl_body_np_ex_user))
        $(esc(cl_body_ex))
        
        new_ms_tuple_types = Any[]
        arg_tuple_type = Tuple{
            $(esc.(func_def[:arg_type_exs])...)} where {$(esc.(func_def[:whereparams])...)
        }

        $(_type_options_for_sig_arg_tuple!)(
            new_ms_tuple_types, arg_tuple_type, 
            $(esc(ctx_global_syms_dict[:arg_type_mapping]))
        )
        
        if !isnothing($(esc(ctx_global_syms_dict[:method_lookup_modules])))
            defined_methods = methods($(esc(func_name)), $(esc(ctx_global_syms_dict[:method_lookup_modules])))

            for m in defined_methods
                m_tuple_type = typeintersect(
                    Base.rewrap_unionall(Base.unwrap_unionall(m.sig).parameters[2:end], m.sig),
                    arg_tuple_type
                )
                $(_type_options_for_sig_arg_tuple!)(
                    new_ms_tuple_types, m_tuple_type, $(esc(ctx_global_syms_dict[:arg_type_mapping]))
                )
            end 
        end
        
        arg_name_exs = [ $((Meta.quot.(func_def[:arg_name_exs]))...) ]
        $(define_methods)(
            $(__module__), $(esc(func_name)), new_ms_tuple_types, arg_name_exs, 
            $(esc(ctx_global_syms_dict[:check_hasmethod]))
        )
    end
end=#

function ctx_gensyms()
    Dict(
        fn => gensym("ctx_" * string(fn)) for fn = fieldnames(AutoWrapContext)
    )
end
#=
function ctx_unpack_expr(ctx_syms, ctx_ex)
    exprs = [
        :( $(sym) = getfield($(ctx_ex), $(Meta.quot(fn))) )
            for (fn, sym) in pairs(ctx_syms)
    ]
    return quote $(exprs...) end
end

function ctx_copy_expr(ctx_copy_syms, ctx_syms)
    @assert length(ctx_copy_syms) == length(ctx_syms)
    exprs = [
        :( const $(csym) = deepcopy($(sym)) )
            for (csym, sym) = zip(ctx_copy_syms, ctx_syms)
    ]
    return quote $(exprs...) end
end
=#
#=
function make_fallback_noprocessing_expr(func_def, new_name = nothing, arg_types = true)
    fallback_def = copy(func_def)
    if !arg_types
        empty!(fallback_def[:args])
        append!(fallback_def[:args], fallback_def[:arg_name_exs])
    end
    if !isnothing(new_name)
        fallback_def[:name] = new_name
    end
    return ET.combinedef(fallback_def)
end

function make_fallback_noprocessing_expr_anon(func_def, arg_types = true)
    fallback_def = copy(func_def)
    if !arg_types
        empty!(fallback_def[:args])
        append!(fallback_def[:args], fallback_def[:arg_name_exs])
    end
    if haskey(fallback_def, :name)
        delete!(fallback_def, :name)
    end
    if !(fallback_def[:head] in (:(->), :function))
        fallback_def[:head] = :function
    end
    return ET.combinedef(fallback_def)
end

function make_fallback_noprocessing_expr_for_user(
    func_def, anon_name = nothing
)
    @assert !isnothing(anon_name)
    fallback_def = copy(func_def)
    pushfirst!(fallback_def[:args], :(::$(FallbackNoProcessing)))
    fallback_def[:body] = quote
        $(anon_name)($(fallback_def[:arg_name_exs]...))
    end

    return ET.combinedef(fallback_def)
end

function make_fallback_expr(func_def, fallback_noprocessing_symb, ctx_preprocessing_symb, ctx_postprocessing_symb)
    fallback_def = deepcopy(func_def)
    empty!(fallback_def[:args])
    push!(fallback_def[:args], :(::$(Fallback)))
    append!(fallback_def[:args], fallback_def[:arg_name_exs])
    fallback_def[:body] = quote
        (_args, meta) = $(ctx_preprocessing_symb)($(Expr(:tuple, fallback_def[:arg_name_exs]...)))
        #ret = $(fallback_noprocessing_symb)($(FallbackNoProcessing()), _args...)
        ret = $(fallback_noprocessing_symb)(_args...)
        return $(ctx_postprocessing_symb)(ret, meta)
    end
    return ET.combinedef(fallback_def)
end
=#
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
function signature_without_name(orig_sig::Type{<:Tuple}; extra_hygiene=false)
    sig = extra_hygiene ? ET._truly_rename_unionall(orig_sig) : orig_sig
    def = Dict{Symbol, Any}()

    #=
    opT = parameters(sig)[1]
    def[:name] = :(op::$opT)
    =#

    arg_types = ET.name_of_type.(ET.parameters(sig))#(ET.argument_types(sig))
    arg_names = [Symbol(:x, ii) for ii in eachindex(arg_types)]
    def[:args] = Expr.(:(::), arg_names, arg_types)
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

end#module