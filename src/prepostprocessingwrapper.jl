const DEFAULT_PREPROCESSING_FUNCTION(args...) = (args, nothing)
const (DEFAULT_POSTPROCESSING_FUNCTION(ret::R, meta)::R) where R = ret

"""
    PrePostProcessingWrapper{TypedBodyFlag, A, Z}

Wrapper, where the `preprocessing_function` maps the `args...` to `(_args, meta)`.
The new arguments `_args` are then fed to the original function body, which returns `ret`.
Finally, the result of `postprocessing_function(ret, meta)` is returned by the wrapped 
function."""
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

_extra_arg(w::PrePostProcessingWrapper{true}) = NewDefTyped()
_extra_arg(w::PrePostProcessingWrapper{false}) = NewDefUntyped()
function eval_wrapped(w::PrePostProcessingWrapper, body_fn, args...)
    (_args, meta) = w.preprocessing_function(args...)
    ret = body_fn(_extra_arg(w), _args...)
    return w.postprocessing_function(ret, meta)
end