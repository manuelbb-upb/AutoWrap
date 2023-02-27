using Test
import AutoWrap as AW

@testset "_arg_type_expr" begin
    @test AW._arg_type_expr(:(:: arg_type)) == :(arg_type)
    @test AW._arg_type_expr(:(arg_name :: arg_type)) == :(arg_type)
    @test AW._arg_type_expr(:(arg_name :: arg_type{T})) == :(arg_type{T})
    @test AW._arg_type_expr(:(arg_name :: arg_type{T} where {T})) == :(arg_type{T} where {T})
    @test AW._arg_type_expr(:(arg_name :: Vararg{Int})) == :(Vararg{Int})
    @test AW._arg_type_expr(:(arg_name...)) == :(Vararg{Any})
    @test AW._arg_type_expr(:(arg_name :: argtype ...)) == :(Vararg{argtype})
    @test AW._arg_type_expr(:(arg_name ::argtype ...)) == :(Vararg{argtype})
    @test AW._arg_type_expr(:(arg_name ::argtype...)) == :(Vararg{argtype})
end

module PseudoSymbolics

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

AW.@wrapping ctx = AW.AutoWrapContext(;
    arg_type_mapping = function (type)
        if has_symwrapper(type)
            (type, Symbolic{type}, wrapper_type(type))
        else
            (type, Symbolic{type})
        end
    end,
    preprocessing_function = function (args...)
        ([iswrapped(a) ? unwrap(a) : a for a in args], nothing)
    end
)

@ctx_wrap function test_function(a::Int, b::Real, c)
    return true
end

end#module

import .PseudoSymbolics as PS

@test PS.test_function(1, 2, 3)
@test PS.test_function(PS.Num(1), 2, 3)