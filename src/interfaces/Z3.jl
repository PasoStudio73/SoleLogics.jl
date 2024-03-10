#using Z3
#using Z3: Context, Solver

# Global function: Z3 API
z3not(x::String) = "(not " * x * ")"
z3and(x::String, y::String) = "(and " * x * " " * y * ")"
z3or(x::String, y::String) =  "(or " * x * " " * y * ")"
z3implies(x::String, y::String) = "(=> " * x * " " * y * ")"
z3forall(x::String, y::String) = "(forall " * x * " " * y * ")"
z3exists(x::String, y::String) = "(exists " * x * " " * y * ")"

# Logic dictionaries
dictprop = Dict{Connective,Function}([
    (¬, z3not),
    (∧, z3and),
    (∨, z3or),
    (→, z3implies),
])

dictmodal = merge(
    dictprop,
    Dict{Connective,Function}([
        (◊, z3exists),
        (□, z3forall),
    ]),
);

# Global set of variables
vars = String[]
for i in collect('z':-1:'a')
    for j in collect(100:-1:1)
        push!(vars,"$i$j")
    end
end

################################################################################################
#################################### Initial Point #############################################
################################################################################################
function z3translate(f::Formula; logic::Symbol=:prop, kwargs...)
    result = ""
    dictops = nothing

    if !(logic == :prop || logic == :modal)
        error("Possible logic: propositional (:prop) and modal (:modal)")
    end

    if logic == :prop
        dictops = dictprop
    elseif logic == :modal
        dictops = dictmodal
        result = result * "(declare-sort A 0)\n(declare-fun R (A A) Bool)\n"
    end

    freevariables = deepcopy(vars)
    currentvariable = pop!(freevariables)
    context, formula = z3subtranslate(
        f; 
        dictops = dictops, freevariables=freevariables, currentvariable=currentvariable, kwargs...,
    )

    return result * context * "(assert (forall (($(currentvariable) A)) $(formula)))"
end

################################################################################################
####################################### Formula ################################################
################################################################################################

z3subtranslate(f::Formula; kwargs...) = 
    error("Missing implementation of Z3 translation for: " * typeof(f))

################################################################################################
#################################### AnchoredFormula ###########################################
################################################################################################

z3subtranslate(f::AnchoredFormula; kwargs...) = z3subtranslate(synstruct(f); kwargs...)

################################################################################################
################################# LeftmostLinearForm ###########################################
################################################################################################

function z3subtranslate(
    f::LeftmostLinearForm{C,SS};
    dictops::Dict{Connective,Function}=dictops,
    freevariables::Vector{String}=vars,
    currentvariable::String,
    kwargs...,
) where {C<:Connective, SS<:AbstractSyntaxStructure}
    fchildren = children(f)
    op = connective(f)

    succcurrentvariable = op == ◊ || op == □ ? pop!(freevariables) : currentvariable
    firstcontext, firstprop = z3subtranslate(
        first(fchildren); 
        dictops=dictops, 
        freevariables=freevariables, 
        currentvariable=succcurrentvariable,  
        kwargs...,
    )
    
    if SoleLogics.arity(op) == 1
        if op == ¬
            return (firstcontext, dictops[op](firstprop))
        else
            x = currentvariable
            y = succcurrentvariable
            quantifiers = "((" * y * " A))"
            subformula = op == ◊ ? dictops[∧]("(R " * x * " " * y * ")", firstprop) : dictops[→]("(R " * x * " " * y * ")", firstprop)

            return (firstcontext, dictops[op](quantifiers, subformula))
        end
    elseif SoleLogics.arity(op) == 2
        secondcontext, secondprop = 
            length(fchildren) > 2 ? 
                z3subtranslate(
                    LeftmostLinearForm{C,SS}(fchildren[2:end]); 
                    dictops=dictops, 
                    freevariables=freevariables, 
                    currentvariable=succcurrentvariable, 
                    kwargs...,
                ) : 
                z3subtranslate(
                    fchildren[2]; 
                    dictops=dictops, 
                    freevariables=freevariables, 
                    currentvariable=succcurrentvariable,
                    kwargs...,
                )

        return (firstcontext * secondcontext, dictops[op](firstprop,secondprop))
    else
        error("Extend Z3 translation implementation for connectives with arity greater than 2")
    end
end

################################################################################################
##################################### SyntaxTree ###############################################
################################################################################################

z3subtranslate(f::SyntaxTree; kwargs...) = 
    error("Missing implementation of Z3 translation for: " * typeof(f))

################################################################################################
#################################### SyntaxBranch ##############################################
################################################################################################

function z3subtranslate(
    f::SyntaxBranch;
    dictops::Dict{Connective,Function}=dictops,
    freevariables::Vector{String}=vars,
    currentvariable::String,
    kwargs...,
)
    ftoken = token(f)
    fchildren = children(f)

    succcurrentvariable = ftoken == ◊ || ftoken == □ ? pop!(freevariables) : currentvariable
    firstcontext, firstprop = z3subtranslate(
        first(fchildren); 
        dictops=dictops, 
        freevariables=freevariables, 
        currentvariable=succcurrentvariable,
        kwargs...,
    )

    if SoleLogics.arity(ftoken) == 1
        if ftoken == ¬
            return (firstcontext, dictops[ftoken](firstprop))
        else
            x = currentvariable
            y = succcurrentvariable
            quantifiers = "((" * y * " A))"
            subformula = ftoken == ◊ ? dictops[∧]("(R " * x * " " * y * ")", firstprop) : dictops[→]("(R " * x * " " * y * ")", firstprop)

            return (firstcontext, dictops[ftoken](quantifiers, subformula))
        end
    elseif SoleLogics.arity(ftoken) == 2
        secondcontext, secondprop = 
            length(fchildren) > 2 ? 
                z3subtranslate(
                    SyntaxBranch(ftoken,fchildren[2:end]...);
                    dictops=dictops, 
                    freevariables=freevariables, 
                    currentvariable=succcurrentvariable,
                    kwargs...,
                ) : 
                z3subtranslate(
                    fchildren[2]; 
                    dictops=dictops, 
                    freevariables=freevariables, 
                    currentvariable=succcurrentvariable,
                    kwargs...,
                )

        return (firstcontext * secondcontext, dictops[ftoken](firstprop,secondprop))
    else
        error("Extend Z3 translation implementation for connectives with arity greater than 2")
    end
end

################################################################################################
##################################### SyntaxLeaf ###############################################
################################################################################################

z3subtranslate(f::SyntaxLeaf; kwargs...) = 
    error("Missing implementation of Z3 translation for: " * typeof(f))

z3subtranslate(f::Atom; kwargs...) = ("(declare-const " * string(value(f)) * " Bool)\n", string(value(f)))

function z3subtranslate(
    f::Literal;
    dictops::Dict{Connective,Function}=dictops,
    kwargs...,
)
    ispositive = ispos(f)
    proposition = prop(f)
    (context, subassertion) = z3subtranslate(proposition; dictops=dictops, kwargs...)

    return (context, dictops[¬](subassertion))
end

z3subtranslate(f::Top; kwargs...) = return ("(declare-const top Bool)\n", "(= top true)")


################################################################################################
################################################################################################
################################################################################################
################################################################################################
################################################################################################
################################################################################################
################################################################################################
################################################################################################
################################################################################################
################################################################################################
################################################################################################
################################################################################################
################################################################################################

#=
dictoperators = Dict{Connective,Function}([
    (¬,(x) -> Z3.not(x)),
    (∧,(x,y) -> Z3.and(x,y)),
    (∨,(x,y) -> Z3.or(x,y)),
    (→,(x,y) -> Z3.implies(x,y)),
]);

################################################################################################
####################################### Formula ################################################
################################################################################################

z3translate(f::Formula; kwargs...) = 
    error("Missing implementation of Z3 translation for: " * typeof(f))

################################################################################################
#################################### AnchoredFormula ###########################################
################################################################################################

z3translate(f::AnchoredFormula; kwargs...) = z3translate(synstruct(f); kwargs...)

################################################################################################
################################# LeftmostLinearForm ###########################################
################################################################################################

function z3translate(
    f::LeftmostLinearForm{C,SS}; 
    ctx::Context = Context(), 
    s::Solver = Solver(ctx, "QF_NRA"),
    initialpoint::Bool=true,
    dictoperators::Dict{Connective,Function}=dictoperators,
) where {C<:Connective, SS<:AbstractSyntaxStructure}
    fchildren = children(f)
    op = connective(f)

    firstprop = z3translate(first(fchildren); ctx=ctx, s=s, initialpoint=false, dictoperators=dictoperators)
    if SoleLogics.arity(op) == 1
        return initialpoint ? add(s, dictoperators[op](firstprop)) : dictoperators[op](firstprop)
    elseif SoleLogics.arity(op) == 2
        secondprop = 
            length(fchildren) > 2 ? 
                z3translate(
                    LeftmostLinearForm{C,SS}(fchildren[2:end]); 
                    ctx=ctx, s=s, initialpoint=false, dictoperators=dictoperators,
                ) : 
                z3translate(fchildren[2]; ctx=ctx, s=s, initialpoint=false, dictoperators=dictoperators)

        return initialpoint ? add(s, dictoperators[op](firstprop,secondprop)) : dictoperators[op](firstprop,secondprop)
    else
        error("Extend Z3 translation implementation for connectives with arity greater than 2")
    end
end

################################################################################################
##################################### SyntaxTree ###############################################
################################################################################################

z3translate(f::SyntaxTree; kwargs...) = 
    error("Missing implementation of Z3 translation for: " * typeof(f))

################################################################################################
#################################### SyntaxBranch ##############################################
################################################################################################

function z3translate(
    f::SyntaxBranch; 
    ctx::Context=Context(),
    s::Solver = Solver(ctx, "QF_NRA"),
    initialpoint::Bool=true,
    dictoperators::Dict{Connective,Function}=dictoperators,
)
    ftoken = token(f)
    fchildren = children(f)

    firstprop = z3translate(first(fchildren); ctx=ctx, s=s, initialpoint=false, dictoperators=dictoperators)
    if SoleLogics.arity(ftoken) == 1
        return initialpoint ? add(s, dictoperators[ftoken](firstprop)) : dictoperators[ftoken](firstprop)
    elseif SoleLogics.arity(ftoken) == 2
        secondprop = 
            length(fchildren) > 2 ? 
                z3translate(
                    SyntaxBranch(ftoken,fchildren[2:end]...); 
                    ctx=ctx, s=s, initialpoint=false, dictoperators=dictoperators,
                ) : 
                z3translate(fchildren[2]; ctx=ctx, s=s, initialpoint=false, dictoperators=dictoperators)

        return initialpoint ? add(s, dictoperators[op](firstprop,secondprop)) : dictoperators[op](firstprop,secondprop)
    else
        error("Extend Z3 translation implementation for connectives with arity greater than 2")
    end
end

################################################################################################
##################################### SyntaxLeaf ###############################################
################################################################################################

z3translate(f::SyntaxLeaf; kwargs...) = 
    error("Missing implementation of Z3 translation for: " * typeof(f))

function z3translate(
    f::Atom; 
    ctx::Context=Context(),
    s::Solver = Solver(ctx, "QF_NRA"),
    kwargs...,
)
    x = bool_const(ctx, string(value(f)))

    return x
end

function z3translate(
    f::Literal; 
    ctx::Context=Context(),
    s::Solver = Solver(ctx, "QF_NRA"),
    initialpoint::Bool=true,
    dictoperators::Dict{Connective,Function}=dictoperators,
)
    ispositive = ispos(f)
    proposition = prop(f)
    subassertion = z3translate(proposition; ctx=ctx, s=s, initialpoint=false, dictoperators=dictoperators)

    assertion = !ispositive ? Z3.not(subassertion) : subassertion

    return initialpoint ? add(s,assertion) : assertion
end

function z3translate(f::Top; ctx::Context=Context(), kwargs...)
    return bool_val(ctx,true)
end
=#