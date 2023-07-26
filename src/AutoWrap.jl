module AutoWrap

export AutoWrapContext
export @make_macro, @wrap_with_context

import ExprTools as ET

include("utils.jl")

include("interfaces.jl")

include("prepostprocessingwrapper.jl")
include("argtypeexpander.jl")
include("wrappingcontext.jl")

macro contextual_wrap(ctx, func_ex)
    func_def = safe_splitdef(func_ex)
    efunc_name = :($(esc(func_def[:name])))
    ectx = :($(esc(ctx)))
    quote
        $(esc(generic_fallback_expr(func_def)))
        sigtt = $(esc(sigtt_from_sigdict_expr(func_def)))
        wrapper = $(ectx).body_wrapper
        $(create_typed_body_method)($(__module__), $(efunc_name), sigtt)
        $(create_wrapped_body_method)($(__module__), wrapper, $(efunc_name), sigtt)

        atm = $(ectx).arg_types_mapping

        new_sigtts = $(apply_type_mapping)(atm, sigtt, sigtt)
        existing_sigtts = $(gather_existing_sigtts)(
            $(efunc_name), sigtt, $(ectx).method_lookup_modules,
        )
        for esigtt in existing_sigtts
            more_sigtts = $(apply_type_mapping)(atm, esigtt, sigtt)
            new_sigtts = $(handle_new_sigs)(atm, more_sigtts, new_sigtts)
        end
        new_sigtts = $(handle_existing_sigs)(atm, new_sigtts, existing_sigtts)

        $(define_methods_for_new_sigtts)(
            $(__module__), $(efunc_name), new_sigtts, $(ectx).new_method_condition,
        )
    end
end
export @contextual_wrap

macro make_macro(ctx_expr)
    _assert_ctx_ex(ctx_expr, "@make_macro")

    ctx_name = if ctx_expr isa Symbol
        # the context is just referred to by name, e.g.
        # `@make_macro ctx`
        ctx_expr
    else
        # the context is newly created and assigned
        # `@make_macro ctx = WrappingContext(...)`
        first(ctx_expr.args)
    end

    # We are going to create a copy of the wrapping context to protect 
    # against changes
    ctx_copy_var = gensym(ctx_name)

    # `@make_macro ctx` will generate `@ctx_wrap`
    macro_name = Symbol(ctx_name, "_wrap")

    quote
        $(
            if !isa(ctx_expr, Symbol)
                # make sure, an AutoWrapContext object exists and is assigned to `$(ctx_name)`
                esc(ctx_expr)
            end
        )

        $(esc(ctx_copy_var)) = $(esc(:(deepcopy($(ctx_name)))));

        macro $(esc(macro_name))(func_def_expr)
            quote
                @contextual_wrap $($(Meta.quot(ctx_copy_var))) $(func_def_expr)
                # $($(wrap_with_context)) $($(Meta.quot(ctx_copy_var))) $(func_def_expr) $($("@" * string(macro_name)))
                #$(make_closure_expr($(__module__), $(esc(ctx_copy_var)), func_def_expr))
            end |> esc
        end
    end
end

end#module