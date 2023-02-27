module AutoWrap
export AutoWrapContext
export @wrapping

import ExprTools as ET

"Fallback() is a special argument to redirect calls to the original function body."
struct Fallback end
"FallbackNoProcessing() is a special argument to redirect calls to the original function body."
struct FallbackNoProcessing end

const FALLBACK_ARG = Fallback()
const FALLBACK_NO_PROCESSING_ARG = FallbackNoProcessing()

const DEFAULT_ARG_TYPE_MAPPING = identity
const DEFAULT_PREPROCESSING_FUNCTION = (args...) -> (args, nothing)
const DEFAULT_POSTPROCESSING_FUNCTION = (ret, meta) -> ret

Base.@kwdef mutable struct AutoWrapContext
    "Name of generated macro to print error messages."
    macro_name :: Symbol = :(no_macro_name)

    "A function mapping types or type variables to types or type variables or tuples thereof."
    arg_type_mapping :: Any = DEFAULT_ARG_TYPE_MAPPING

    "A function mapping the arguments `args...` to a tuple `(_args, meta)` before they are 
    plugged into the body of the originial function definition."
    preprocessing_function :: Any = DEFAULT_PREPROCESSING_FUNCTION

    "A function mapping `(ret, meta)` to the return value of the overspecialized method, 
    where `ret` is the return value resulting from evaluating the originial function body 
    on `_args`, and `(_args, meta)` results from calling `preprocessing_function`."
    postprocessing_function :: Any = DEFAULT_POSTPROCESSING_FUNCTION

    "List of modules to look up method definitions in (or `nothing` for calling scope)."
    method_lookup_modules :: Union{Nothing, Vector{<:Module}} = nothing

    "Bool indicating whether to check for existing methods before defining them."
    check_hasmethod :: Bool = false
end

# helper inspired by ExprTools
_is_func_expr(ex) = false
_is_func_expr(ex::Expr) = (ex.head === :function || ex.head === :(=) || ex.head === :(->))

macro wrapping(ctx_expr)
    @assert(
        ctx_expr isa Symbol || Meta.isexpr(ctx_expr, :(=)),
        "`@wrapping_context`: Argument must be the name of a previously defined `AutoWrapContext`
        or an assignment like `ctx = AutoWrapContext(; ...)`."
    )
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
                ctx_expr
            end
        )
        #=
        const $(ctx_copy_var) = $(AutoWrapContext)(;
            macro_name = $(Meta.quot(macro_name)),
            arg_type_mapping = $(ctx_name).arg_type_mapping,
            preprocessing_function = $(ctx_name).preprocessing_function,
            postprocessing_function = $(ctx_name).postprocessing_function,
            method_lookup_modules = $(ctx_name).method_lookup_modules,
            check_hasmethod = $(ctx_name).check_hasmethod
        );
        =#
        const $(ctx_copy_var) = deepcopy($(ctx_expr));
        $(ctx_copy_var).macro_name = $(Meta.quot(macro_name));

        macro $(macro_name)(func_def_expr)
            $(superwrapper)(__module__, $(Meta.quot(ctx_copy_var)), func_def_expr)
        end
    end |> esc
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

# helper to recursively split a function name expression into parent module names and function name
_split_func_name_expr(name_ex::Symbol) = (nothing, name_ex)
_split_func_name_expr(name_ex::QuoteNode) = (nothing, name_ex.value)
function _split_func_name_expr(name_ex::Expr)
    @assert Meta.isexpr(name_ex, :(.))
    mod_ex = name_ex.args[1]
    submod_ex, fnname_ex = _split_func_name_expr(name_ex.args[2])
    if isnothing(submod_ex)
        return (mod_ex, fnname_ex)
    else
        return :($(mod_ex).$(submod_ex), fnname_ex)
    end
end

"""
    _is_func_name_expr_defined(eval_mod, name_ex)

Determine if `name_ex` is defined in the calling context of module `eval_mod`.
"""
function _is_func_name_expr_defined(mod, name_ex)
    supermod, fname_ex = _split_func_name_expr(name_ex) # `Base.:(*)` becomes `(:Base, :(*))`.
    if isnothing(supermod)
        return Base.eval(mod, :(Base.isdefined($(mod), $(Meta.quot(fname_ex)))))
    end
    return Base.eval(mod, :(Base.isdefined($(supermod), $(Meta.quot(fname_ex)))))
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
ensure_tuple(t::Tuple)=t
ensure_tuple(t::Vector)=t
ensure_tuple(x) = (x,)
"""
    _type_options_for_sig_arg_tuple!(unique_tuple_types, sig_tuple_type, ctx, drop_n=1)

Fill the array `unique_tuple_types` with tuple types, the parameters of which describe method
argument types. `ctx` is an `AutoWrapContext` and `drop_n` is an internal varible to filter
redundant tuples.
"""
function _type_options_for_sig_arg_tuple!(unique_tuple_types, sig_tuple_type, ctx, drop_n=1)
    sig_params = ET.parameters(sig_tuple_type)

    atype_options = Any[]
    for atype in sig_params
        # NOTE if `atype` is not a type variable, then it could have free type variables here. 
        # is this a problem? If so, we can easily rewrap (see below)
        push!(atype_options, ensure_tuple(ctx.arg_type_mapping(atype)))
    end

    for ttuple in Iterators.drop(Iterators.product( atype_options... ), drop_n)
        tuple_type = Base.rewrap_unionall( Tuple{ ttuple... }, sig_tuple_type )
        #if !(tuple_type in unique_tuple_types)
        if !(contains_type(unique_tuple_types, tuple_type))
            push!(unique_tuple_types, tuple_type)
        end
    end
    nothing
end

macro wrap(ctx_ex, func_ex)
    return superwrapper(__module__, ctx_ex, func_ex)
end

function make_fallback_noprocessing_expr(func_def, arg_name_exs)
    mdict = deepcopy(func_def)
    empty!(mdict[:args])
    push!(mdict[:args], :(::$(FallbackNoProcessing)))
    append!(mdict[:args], arg_name_exs)
    return ET.combinedef(mdict)
end

function make_fallback_expr(func_def, ctx_name, arg_name_exs)
    mdict = deepcopy(func_def)
    empty!(mdict[:args])
    push!(mdict[:args], :(::$(Fallback)))
    append!(mdict[:args], arg_name_exs)
    mdict[:body] = quote
        (_args, meta) = $(ctx_name).preprocessing_function($(arg_name_exs...))
        ret = $(func_def[:name])($(FallbackNoProcessing()), _args...)
        return $(ctx_name).postprocessing_function(ret, meta)
    end
    return ET.combinedef(mdict)
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

"""
    make_new_method_expr(fname, sig_arg_tuple_type, arg_name_exprs, ::Val{false})

Return an expression defining a method for the function with name `fname` dispatching 
on `sig_arg_tuple_type` with argument names `arg_name_exprs`.
Because of the last argument of type `::Val{true}` we do not include a check for existing 
methods.
"""
function make_new_method_expr(fname, sig_tuple_type, arg_name_exs, check_hasmethod::Val{false})
    mdict = signature_without_name(sig_tuple_type)
    mdict[:name] = fname
    _match_argnames!(mdict, arg_name_exs)       # or re-parse argument names from `mdict`
    mdict[:body] = quote
        return $(fname)($(Fallback()), $(arg_name_exs...))
    end
    return mdict, ET.combinedef(mdict)
end

"""
    make_new_method_expr(fname, sig_arg_tuple_type, arg_name_exprs, ::Val{true})

Return an expression defining a method for the function with name `fname` dispatching 
on `sig_arg_tuple_type` with argument names `arg_name_exprs`.
Because of the last argument of type `::Val{true}` we **do** include a check for existing 
methods.
"""
function make_new_method_expr(fname, sig_tuple_type, arg_name_exs, check_hasmethod::Val{true})
    func_def, func_def_expr = make_new_method_expr(fname, sig_tuple_type, arg_name_exs, Val(false))

    # retrieve argument expressions
    arg_exs = get(func_def, :args, Symbol[])
    # split expressions of the form `(a::A)` into name and type symbol components:
    arg_type_exs = _arg_type_expr.(arg_exs)
    wparams_exs = get(func_def, :whereparams, Symbol[])        

    return func_def, quote
        if !hasmethod($(fname), Tuple{$(arg_type_exs...)} where {$(wparams_exs...)})
            @eval $(func_def_expr)
        end
    end
end

"Modify `sig_dict[:args]` to match the names in `arg_name_exs`."
function _match_argnames!(sig_dict, arg_name_exs)
    old_args = deepcopy(sig_dict[:args])
    empty!(sig_dict[:args])
    for (i, arg_ex) in enumerate(old_args)
        push!(sig_dict[:args], :($(arg_name_exs[i])::$(_arg_type_expr(arg_ex))))
    end
    nothing
end

function superwrapper(eval_mod, ctx_ex, func_ex)
    # `func_ex` is an expression that comes from parsing a method definition
    # with ExprTools we parse it into a `Dict`
    func_def = ET.splitdef(func_ex)
    
    # retrieve argument expressions
    arg_exs = get(func_def, :args, Symbol[])
    # split expressions of the form `(a::A)` into name and type symbol components:
    arg_type_exs = _arg_type_expr.(arg_exs)
    arg_name_exs = _arg_name_expr.(arg_exs)

    wparams_exs = get(func_def, :whereparams, Symbol[])        
    func_name = func_def[:name]

    #fmod, fname = _split_func_name_expr(func_name)

    ctx_copy_var = gensym(ctx_ex)    # name for (newly created) context object
    
    # Evaluate type expressions in caller scope to get intended signature Tuple Type
    # Also query contex `ctx`, if we are at it...
    ctx, arg_tuple_type = Base.eval(
        eval_mod, 
        :(
            const $(ctx_copy_var) = if !Base.isconst($(eval_mod), $(Meta.quot(ctx_ex)))
                deepcopy($(ctx_ex))
            else
                $(ctx_ex)
            end;
            (
                $(ctx_copy_var),
                (Tuple{$(arg_type_exs...)} where {$(wparams_exs...)})
            )
        )
    )

    # Vector containing Tuple types corresponding to signatures of new methods to be defined
    new_ms_tuple_types = Any[]

    # generate new signature tuples for base definition
    _type_options_for_sig_arg_tuple!(new_ms_tuple_types, arg_tuple_type, ctx, 0)

    # do the same for existing methods (if there are any)
    if !isnothing(ctx.method_lookup_modules) && _is_func_name_expr_defined(eval_mod, func_name)
        defined_methods = Base.eval(eval_mod, :(methods($(func_name), $(arg_tuple_type))))

        for m in defined_methods
            m_tuple_type = typeintersect(
                Base.rewrap_unionall(Base.unwrap_unionall(m.sig).parameters[2:end], m.sig),
                arg_tuple_type
            )
            _type_options_for_sig_tuple!(new_ms_tuple_types, m_tuple_type, ctx)
        end        
    end

    # build method definitons from the type option tuples
    check_hasmethod = Val(ctx.check_hasmethod)
    method_exprs = Expr[]
    for stt in new_ms_tuple_types
        push!(method_exprs, last(make_new_method_expr(func_name, stt, arg_name_exs, check_hasmethod)))
    end

    quote
        # first, define the fallbacks
        $(make_fallback_noprocessing_expr(func_def, arg_name_exs))

        $(make_fallback_expr(func_def, ctx_copy_var, arg_name_exs))            

        $(method_exprs...)
    end |> esc
end

end # module AutoWrap
