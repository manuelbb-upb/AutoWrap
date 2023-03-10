ensure_iterable(t::Tuple)=t
ensure_iterable(t::Vector)=t
ensure_iterable(x) = (x,)

#function tt_union(vec_tt1::AbstractVector{T}, vec_tt2::AbstractVector{S}) where {S,T}
@nospecialize
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
@specialize

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