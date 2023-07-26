"""
    AbstractFallbackArg

Supertype for types that define the behavior of wrapped methods via dispatch on the first
argument.
"""
abstract type AbstractFallbackArg end

struct NewDefUntyped <: AbstractFallbackArg end
struct NewDefTyped <: AbstractFallbackArg end
struct Wrapped <: AbstractFallbackArg end

#=========================================================================================#

"""
    AbstractBodyWrapper

Supertype for types that define the behavior of `eval_wrapped` via dispatch on its first
argument."""
abstract type AbstractBodyWrapper end

"""
    eval_wrapped(wrapper::AbstractBodyWrapper, body_fn, args...)

Helper function to modify calls to the function `body_fn` to behave according to what 
is intended by the wrapper/wrapping strategy `wrapper`."""
function eval_wrapped(::AbstractBodyWrapper, body_fn, args...)
    # default behavior is to just redirect calls:
    return body_fn(NewDefTyped(), args...)
end

#=========================================================================================#

abstract type AbstractNewMethodCondition end
struct NewMethodCondition <: AbstractNewMethodCondition end
check_condition(::NewMethodCondition, sigtt, mdict) = true

#=========================================================================================#

abstract type AbstractArgTypesMapping end

"Map a method signature to at least one new signature (or an iterable of signatures)."
apply_type_mapping(::AbstractArgTypesMapping, sigtt, query_sigtt) = sigtt

function handle_new_sigs(::AbstractArgTypesMapping, vec_new_sigtt, vec_prev_sigtt)
    return tt_union(vec_new_sigtt, vec_prev_sigtt)
end
function handle_existing_sigs(::AbstractArgTypesMapping, vec_new_sigtt, vec_existing_sigtt)
    return setdiff(vec_new_sigtt, vec_existing_sigtt)
end