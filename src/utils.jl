#==========================================================================================#
# Utilities for working with types and tuple types
#==========================================================================================#

# helper function to ensure that something is iterable
ensure_iterable(t::Tuple)=t
ensure_iterable(t::Vector)=t
ensure_iterable(x) = (x,)

@nospecialize
"""
    tt_union(vec_of_tuple_types1, vec_of_tuple_types2)

Return a vector that contains the set union of elements from the arguments 
`vec_of_tuple_types1` and `vec_of_tuple_types2`, but based on `===` as the comparison 
operator.
"""
function tt_union(vec_tt1::AbstractVector, vec_tt2::AbstractVector)
    # `union` uses `===`, this is a version using `==` instead (because `in` does)
    # R = Base.promote_type(S, T)
    R = Any
    len1 = length(vec_tt1)
    ret_vec = Vector{R}(undef, len1 + length(vec_tt2))   
    for (i, t) = enumerate(vec_tt1)
        ret_vec[i] = t
    end
    j = len1
    for t in vec_tt2
        if !(t in ret_vec[1:j])
            j += 1
            ret_vec[j] = t
        end
    end
    return ret_vec[1:j]
end

"""
    tt_unique(vec_of_tuple_types)

Return a vector of unique elements from `vec_of_tuple_types`, using `==` for comparisons.
"""
function tt_unique(vec_tt)
    # `unique`, but using `==` instead of `isequal`
    if !isempty(vec_tt)
        ret_vec = similar(vec_tt)
        ret_vec[1] = first(vec_tt)
        j = 1
        for t in vec_tt[2:end]
            any( s == t for s in ret_vec[1:j] ) && continue
            j += 1
            ret_vec[j] = t
        end
        return ret_vec[1:j]
    else
        return vec_tt
    end
end
@specialize

#==========================================================================================#
# Utilities for parsing method definition expressions
#==========================================================================================#

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

function sigtt_from_sigdict_expr(sigdict)
    quote
        Tuple{ typeof($(sigdict[:name])), $(sigdict[:arg_type_exs]...) } where{
            $(sigdict[:whereparams]...)
        }
    end
end

#==========================================================================================#
# Utilities defining the fallback methods or their expressions
#==========================================================================================#

"""
    generic_fallback_expr(func_def)

Given a dictionary `func_def` -- resulting from parsing a method definition -- construct 
and return an expression for a method of the same function, where
* the first argument type is supposed to be `NewDefUntyped` and
* the type restrictions are stripped from all the original argument expressions.
The argument names and method body remain the same.
"""
function generic_fallback_expr(func_def)
    fallback_def = copy(func_def)
    empty!(fallback_def[:args])
    push!(fallback_def[:args], :(::$(NewDefUntyped)))
    append!(fallback_def[:args], fallback_def[:arg_name_exs])
    return ET.combinedef(fallback_def)
end

"""
    create_typed_body_method(eval_mod, body_fn, sigtt)

Given a tuple type `sigtt` of a method signature, construct and evaluate an expression
for a method with matching signature in module `eval_mod`, except that `NewDefTyped` is 
pre-pended as the first argument type.
The new method then does nothing else than adding `NewDefUntyped()` as the first argument 
before redirecting to `body_fn`.
"""
function create_typed_body_method(eval_mod, body_fn, @nospecialize(sigtt))
    mdict = ET.signature(sigtt)
    inner_args = isempty(mdict[:args]) ? Symbol[] : _arg_name_expr.(mdict[:args])
    pushfirst!(mdict[:args], :(::$(NewDefTyped)))
    mdict[:body] = quote
        $(body_fn)( $(NewDefUntyped()), $(inner_args...) )
    end

    method_expr = ET.combinedef(mdict)
    Core.eval(eval_mod, method_expr)
end

"""
    create_wrapped_body_method(eval_mod, body_wrapper, body_fn, @nospecialize(sigtt))

Given a tuple type `sigtt` of a method signature, construct and evaluate an expression
for a method with matching signature in module `eval_mod`, except that `Wrapped` is 
pre-pended as the first argument type.
The new method redirects to `AutoWrap.eval_wrapped`, which should evaluate the function
`body_fn` according to the instructions in `body_wrapper`.
"""
function create_wrapped_body_method(eval_mod, body_wrapper, body_fn, @nospecialize(sigtt))
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

"""
    gather_existing_sigtts(func, query_sigtt, method_mods)

"""
function gather_existing_sigtts(func, query_sigtt, method_mods=nothing)
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

function define_methods_for_new_sigtts(
    eval_mod, body_fn, new_sigtts, new_method_condition
)
    # build method definitons from the type option tuples
    func_name = :((::$(typeof(body_fn))))
    stats = @timed for stt in new_sigtts
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

function _assert_ctx_ex(ctx_expr, macro_name="@macro_name")
    @assert(
        ctx_expr isa Symbol || Meta.isexpr(ctx_expr, :(=)),
        "`$(macro_name)`: Argument must be the name of a previously defined `AutoWrapContext`
        or an assignment like `ctx = AutoWrapContext(; ...)`."
    )
end


#=
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
=#