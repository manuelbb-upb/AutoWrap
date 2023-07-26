module PseudoSymbolics
# Symbolics.jl was the motivation for this package, so I played around a bit here...
using Logging
import LinearAlgebra

abstract type Symbolic{T} end

wrap(x) = x
unwrap(x) = x

has_symwrapper(::Type) = false
wrapper_type(::Type) = nothing
is_wrapper_type(::Type) = false
wraps_type(::Type) = nothing
iswrapped(::Any) = false

struct Num <: Number 
    val
end

wrap(x::Number) = Num(x)
unwrap(x::Num) = x.val

has_symwrapper(::Type{<:Number}) = true
wrapper_type(::Type{<:Number}) = Num
is_wrapper_type(::Type{<:Num}) = true
wraps_type(::Type{<:Num}) = Number
iswrapped(::Num) = true

#import AutoWrap as AW
using AutoWrap
AW = AutoWrap

arg_type_mapping = function (type)
    if has_symwrapper(type)
        (type, Symbolic{<:type}, wrapper_type(type))
    else
        (type, Symbolic{<:type})
    end
end
preprocessing_function = function (args...)
    ((AW.NewDefTyped(), (iswrapped(a) ? unwrap(a) : a for a in args)...), nothing)
end

function new_method_condition(T)
    pars = Base.unwrap_unionall(T).parameters
    _pars = [ Base.rewrap_unionall(p, T) for p in pars ]
    return any( p -> p <: Num || p <: Symbolic, _pars )
end

AW.@make_macro ctx1 = AW.AutoWrapContext(;
    arg_type_mapping,
    #new_method_condition,
    preprocessing_function,
    method_lookup_modules=[@__MODULE__, Base, LinearAlgebra]
)

@ctx1_wrap function test_function(a::Integer, b::Real, c)
    return true
end

AW.@make_macro ctx2 = AW.AutoWrapContext(;
    arg_type_mapping,
    new_method_condition,
    preprocessing_function,
    method_lookup_modules=[@__MODULE__, Base, LinearAlgebra]
)

import Base: *
export *
mul(x,y) = "custom_mul"
#=
debuglogger = ConsoleLogger(stderr, Logging.Debug)
with_logger(debuglogger) do
e = @macroexpand @ctx_wrap Base.:(*)(x::Number, y::Number) = mul(x,y)
eval(e)
end
=#
@ctx2_wrap Base.:(*)(x::Number, y::Number) = mul(x,y)

end#module