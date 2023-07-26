
Base.@kwdef struct WrappingContext
    arg_types_mapping :: AbstractArgTypesMapping = ArgTypeExpander()
    body_wrapper :: AbstractBodyWrapper = PrePostProcessingWrapper()
    new_method_condition :: AbstractNewMethodCondition = NewMethodCondition()
    method_lookup_modules :: Union{Nothing, Vector{<:Module}} = nothing
end
export WrappingContext
