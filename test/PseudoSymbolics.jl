module PseudoSymbolics
# Symbolics.jl was the motivation for this package, so I played around a bit here...

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

wrap(x::Real) = Num(x)
unwrap(x::Num) = x.val

has_symwrapper(::Type{<:Real}) = true
wrapper_type(::Type{<:Real}) = Num
is_wrapper_type(::Type{<:Num}) = true
wraps_type(::Type{<:Num}) = Real
iswrapped(::Num) = true

import AutoWrap as AW

AW.@make_macro ctx = AW.AutoWrapContext(;
    arg_type_mapping = function (type)
        if has_symwrapper(type)
            (type, Symbolic{<:type}, wrapper_type(type))
        else
            (type, Symbolic{<:type})
        end
    end,
    preprocessing_function = function (args...)
        ((iswrapped(a) ? unwrap(a) : a for a in args), nothing)
    end
)

@ctx_wrap function test_function(a::Integer, b::Real, c)
    return true
end

end#module