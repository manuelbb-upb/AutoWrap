using Test
using AutoWrap
const AW=AutoWrap;

#%%
@testset "TupleType isequal, isequal" begin
    # might break if there is progress in 
    # https://github.com/JuliaLang/julia/issues/48777

    T1 = Tuple{R1, R2} where {R1<:Real, R2<:Real}
    T2 = Tuple{Real, Real}
    T3 = Tuple{R, R} where {R<:Real}

    @test T1 == T2
    @test_broken isequal(T1, T2) && hash(T1) == hash(T2)
    @test !(T1 == T3)
    @test !isequal(T1,T3)
    @test !(T2 == T3)
    @test !isequal(T2,T3)
    
    @test T1 !== T2
    @test T1 !== T3
    @test T2 !== T3

    # make sure, that `setdiff` uses `===`
    @test let sd = setdiff([T1, T2, T3], [T1]);
        sd[1] === T2 && sd[2] === T3
    end
    @test let sd = setdiff([T1, T2, T3], [T2]);
        sd[1] === T1 && sd[2] === T3
    end
    @test let sd = setdiff([T1, T2, T3], [T3]);
        sd[1] === T1 && sd[2] === T2
    end

    # `in` uses `==`
    @test T1 in [T2, T3]
    
    # `union` also appears to use `===`
    @test all(union([T1, T2], [T3]) .=== [T1, T2, T3])
    
    ## but not `AW.tt_union`
    @test only(AW.tt_union([T1,], [T2])) === T1
    @test only(AW.tt_union([T2,], [T1])) === T2

    # `unique` uses `isequal` and the assumption that `isequal` implies 
    # same hashes. is buggy atm:
    @test_broken length(unique([T1, T2, T3])) == 2

    @test only(AW.tt_union([T1,], [T2,])) === T1
    @test only(AW.tt_union([T2,], [T1,])) === T2
end

#%%
@testset "AutoWrapContext Defaults" begin
    @test @isdefined(AutoWrapContext)   # AutoWrapContext is exported
    ctx = AutoWrapContext()
    @test ctx.arg_type_mapping == AW.DEFAULT_ARG_TYPE_MAPPING
    @test ctx.preprocessing_function == AW.DEFAULT_PREPROCESSING_FUNCTION
    @test ctx.postprocessing_function == AW.DEFAULT_POSTPROCESSING_FUNCTION
    @test ctx.method_lookup_modules === nothing 
    @test !ctx.check_hasmethod
    @test !ctx.typed_body
end
#%%
@testset "Exported Macros" begin
    @test isdefined(@__MODULE__, Symbol("@make_macro")) # wrapping macro is exported
    @test isdefined(@__MODULE__, Symbol("@wrap_with_context")) # wrapping macro is exported
    
    # macro definition not allowed in local scope:
    new_macro_expr = @macroexpand @make_macro ctx = AutoWrapContext()
    @test_throws Core.Exception eval(Meta.parse("""
    let; 
        $(new_macro_expr)
    end"""))

    custom_ctx = AutoWrapContext()

    # by default, the generated macro does not do much
    @wrap_with_context custom_ctx new_func(x::Number) = nothing

    # fallbacks are introduced:
    @test hasmethod(new_func, Tuple{AW.Wrapped, Any})
    @test hasmethod(new_func, Tuple{AW.NewDefUntyped, Any})
    @test hasmethod(new_func, Tuple{AW.NewDef, Any})
    # and the original method is defined:
    @test hasmethod(new_func, Tuple{Number})

    @test isnothing(new_func(1))
    
    @test_throws Core.Exception custom_ctx.postprocessing_function = (ret, meta) -> 1

    # because the context is copied, changing it (this way at least) should not affect 
    # the new method:
    ppf(args...) = AW.DEFAULT_PREPROCESSING_FUNCTION(args...)
    # also: atm is applied only at the moment of wrapping
    atm(T) = AW.DEFAULT_ARG_TYPE_MAPPING(T)
    custom_ctx2 = AutoWrapContext(;
        preprocessing_function = ppf,
        arg_type_mapping = atm 
    )
    @wrap_with_context custom_ctx2 new_func2(x::Number) = x
    
    @test hasmethod(new_func2, Tuple{AW.Wrapped, Any})
    @test hasmethod(new_func2, Tuple{AW.NewDefUntyped, Any})
    @test hasmethod(new_func2, Tuple{AW.NewDef, Any})
    @test hasmethod(new_func2, Tuple{Number})
    @test new_func2(1) == 1
    
    # changing `atm` now should have no effect:
    atm(T::Type{<:Number}) = (T, Missing)
    @test custom_ctx2.arg_type_mapping(Number) == (Number, Missing)
    @test !hasmethod(new_func2, Tuple{Missing})
    
    # changing ppf, unforntunately, has consequences...
    ppf(args...) = ((AW.NewDef(), nothing,), nothing)
    @test isnothing(new_func2(1))

    # the fallback for the function body accepts only `Number`s if `typed_body==true`
    custom_ctx3 = AutoWrapContext(;
        preprocessing_function = ppf,
        arg_type_mapping = atm,
        typed_body = true
    )
    @wrap_with_context custom_ctx3 new_func3(x::Number) = x
    @test hasmethod(new_func3, Tuple{Missing})  # change of atm takes effect
    @test hasmethod(new_func3, Tuple{Number})
    @test_throws MethodError new_func3(1)
  
    # `undef_ctx` is not defined, the macro cannot access it:
    @test_throws UndefVarError eval(@macroexpand @wrap_with_context undef_ctx nother_func() = 1)
end#testset
#%%

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

@testset "PseudoSymbolicsModule" begin
    include(joinpath(@__DIR__, "PseudoSymbolics.jl"))

    import .PseudoSymbolics as PS

    @test PS.test_function(1, 2, 3)
    @test PS.test_function(PS.Num(1), 2, 3)

    myNum = let typesym = gensym("myNum"), supertype = PS.Symbolic;
        @eval begin
            struct $(typesym){T} <: $(supertype){T}
                val :: T
            end
            $(typesym)
        end
    end

    @test myNum(1) isa PS.Symbolic
    @test myNum(1) isa PS.Symbolic{Int}
    @test myNum(1.0) isa PS.Symbolic{Float64}

    @test PS.test_function(myNum(1), 2, 3)
    @test PS.test_function(myNum(UInt8(1)), 2, 3)
    @test_throws MethodError PS.test_function(myNum(1.0), 2, 3)
    @test PS.test_function(myNum(1), myNum(2.0), 3)

    @test 1 * 2 == 2
    @test PS.Num(1) * 2 == "custom_mul"
end

module SafeScope
    using Test
    import Pkg
    import UUIDs
    cur_env = first(Base.load_path())
    Pkg.activate(;temp=true)
    Pkg.develop(
        Pkg.PackageSpec(;
            name="TestPackage",
            path=joinpath(@__DIR__, "TestPackage")
        )
    )

    @testset "Precompilation Warnings & Module Scope" begin
        function warn_test(output)
            return (
                occursin("WARNING: Method definition doubly_defined_func", output) &&
                occursin("WARNING: Method definition plus", output) &&
                !occursin("WARNING: Method definition minus", output) &&
                !occursin("WARNING: Method definition times", output)
            )
        end

        @test_warn warn_test Base.compilecache(
            Base.PkgId(UUIDs.UUID("58790fe2-1365-4112-aeb7-abc4dbb16099"), "TestPackage"))

        using TestPackage
        @test TestPackage.plus(1,2) == 3
        @test TestPackage.plus(1,TestPackage.myNumber(2)) == 3
        @test TestPackage.plus(TestPackage.myNumber(2), 1) == 3
        @test TestPackage.plus(TestPackage.myNumber(1), TestPackage.myNumber(2)) == 3
    end#testset
    Pkg.activate(cur_env)
end#module