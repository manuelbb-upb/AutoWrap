module TestPackage

using AutoWrap
const AW = AutoWrap

# Test, if overwriting a method results in a precompilation warning:
function doubly_defined_func(a::Int)
    return a
end
function doubly_defined_func(b::Int)
    return 2*b
end

# simple wrapper type for upcoming tests:
struct myNumber
    val
end

# Test, if overwriting by macro results in precompilation warnings: 
make_boring(x::myNumber) = x.val
make_sexy(x::Number) = myNumber(x)

plus(x::Number, y::myNumber) = x + make_boring(y)

arg_type_mapping(T::Type{<:Number}) = (T, myNumber)
preprocessing_function(args...) = ([AW.NewDef(); [isa(a, myNumber) ? make_boring(a) : a for a in args]], nothing)

@make_macro ctx_warn = AutoWrapContext(; arg_type_mapping, preprocessing_function)

@ctx_warn_wrap plus(x::Number, y::Number) = x + y

# Test, if it does not happen for `check_hasmethod=true`
minus(x::Number, y::myNumber) = x + make_boring(y)
@make_macro ctx_nowarn = AutoWrapContext(; arg_type_mapping, preprocessing_function, check_hasmethod=true)

@ctx_nowarn_wrap minus(x::Number, y::Number) = x + y

# However, this should give no warnings:
# 1) The wrapped signature type `Tuple{Number, Number}` is expanded first, giving methods 
#    dispatching on `Tuple{Number, Number}, Tuple{myNumber, Number}, Tuple{Number, myNumber}`.
# 2) These tuple types are collected iteratively and new tuples are only accepted if not 
#    present already.
# 3) Hence, expanding the existing definitions for `Tuple{Number, Int}` and 
#    `Tuple{Number, Float64}` does not introduce new expressions...
times(x::Number, y::Int) = x * y
times(x::Number, y::Float64) = x * y

@ctx_warn_wrap times(x::Number, y::Number) = x + y
end