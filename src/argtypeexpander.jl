DEFAULT_NEW_METHOD_CONDITION(@nospecialize(arg_tuple_type)) = true
DEFAULT_ARG_TYPE_EXPANSION(T) = T
DEFAULT_ARG_TYPE_EXPANSION(tv::TypeVar) = tv.ub

Base.@kwdef struct ArgTypeExpander{F} <: AbstractArgTypesMapping
    arg_type_expansion :: F = DEFAULT_ARG_TYPE_EXPANSION
    drop_n :: Int = 0
end
export ArgTypeExpander

function apply_type_mapping(m::ArgTypeExpander, _sigtt, query_sigtt)
    sigtt = typeintersect(
        _sigtt, query_sigtt
    )
    sig_params = ET.parameters(sigtt)
    func_t = sig_params[1]
    arg_ts = sig_params[2:end]

    type_mapping = m.arg_type_expansion
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

