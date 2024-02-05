using Z3
using Z3: Context, Solver

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
) where {C<:Connective, SS<:AbstractSyntaxStructure}
    fchildren = children(f)
    op = findall(x->typeof(x)==C, BASE_CONNECTIVES)

    firstprop = z3translate(first(fchildren); ctx=ctx, s=s, initialpoint=false)
    if SoleLogics.arity(op) == 1
        stringop = Z3.not

        return initialpoint ? add(s, stringop(firstprop)) : stringop(firstprop)
    elseif SoleLogics.arity(op) == 2
        secondprop = 
            length(fchildren) > 2 ? 
                z3translate(
                    LeftmostLinearForm{C,SS}(fchildren[2:end]); 
                    ctx=ctx, s=s, initialpoint=false,
                ) : 
                z3translate(fchildren[2]; ctx=ctx, s=s, initialpoint=false)
        stringop = ftoken == CONJUNCTION ? Z3.and : (ftoken == DISJUNCTION ? Z3.or : Z3.implies) 

        return initialpoint ? add(s, stringop(firstprop,secondprop)) : stringop(firstprop,secondprop)
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
)
    ftoken = token(f)
    fchildren = children(f)

    firstprop = z3translate(first(fchildren); ctx=ctx, s=s, initialpoint=false)
    if SoleLogics.arity(ftoken) == 1
        stringop = Z3.not

        return initialpoint ? add(s, stringop(firstprop)) : stringop(firstprop)
    elseif SoleLogics.arity(ftoken) == 2
        secondprop = 
            length(fchildren) > 2 ? 
                z3translate(SyntaxBranch(ftoken,fchildren[2:end]...); ctx=ctx, s=s, initialpoint=false) : 
                z3translate(fchildren[2]; ctx=ctx, s=s, initialpoint=false)
        stringop = ftoken == CONJUNCTION ? Z3.and : (ftoken == DISJUNCTION ? Z3.or : Z3.implies) 

        return initialpoint ? add(s, stringop(firstprop,secondprop)) : stringop(firstprop,secondprop)
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
)
    ispositive = ispos(f)
    proposition = prop(f)
    subassertion = z3translate(proposition; ctx=ctx)

    assertion = !ispositive ? Z3.not(subassertion) : subassertion

    return initialpoint ? add(s,assertion) : assertion
end

function z3translate(f::Top; ctx::Context=Context(), kwargs...)
    return bool_val(ctx,true)
end