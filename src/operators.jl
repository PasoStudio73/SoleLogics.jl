using IterTools

#################################
#       Abstract Types          #
#################################
"""Root of Operator abstract-types tree"""
abstract type AbstractOperator{T} end

abstract type AbstractUnaryOperator{T} <: AbstractOperator{T} end
abstract type AbstractBinaryOperator{T} <: AbstractOperator{T} end

abstract type AbstractModalOperator{T} <: AbstractUnaryOperator{T} end

abstract type AbstractExistentialModalOperator{T} <: AbstractModalOperator{T} end
abstract type AbstractUniversalModalOperator{T} <: AbstractModalOperator{T} end

#################################
#       Concrete Types          #
#################################
struct UnaryOperator{T} <: AbstractUnaryOperator{T} end
UnaryOperator(s::AbstractString) = UnaryOperator{Symbol(s)}()
UnaryOperator(s::Symbol) = UnaryOperator{s}()

"""
    UNOP(op::Union{AbstractString,Symbol})
Return a new unary operator as a singleton.

# Example
```jldoctest
julia> myop = UNOP(:℘)
℘
julia> is_unary_operator(myop)
true
julia> is_modal_operator(myop)
false
```
"""
const UNOP(op::Union{AbstractString,Symbol}) = UnaryOperator(op)

struct BinaryOperator{T} <: AbstractBinaryOperator{T} end
BinaryOperator(s::AbstractString) = BinaryOperator{Symbol(s)}()
BinaryOperator(s::Symbol) = BinaryOperator{s}()

"""
    BINOP(op::Union{AbstractString,Symbol})
Return a new binary operator as a singleton.

# Example
```jldoctest
julia> myop = BINOP(:℘)
℘
julia> is_binary_operator(myop)
true
julia> is_modal_operator(myop)
false
```
"""
const BINOP(op::Union{AbstractString,Symbol}) = BinaryOperator(op)

struct ExistentialModalOperator{T} <: AbstractExistentialModalOperator{T} end
function ExistentialModalOperator(t::NTuple{N,AbstractString}) where {N}
    if length(t) > 1
        s = *(["$(x)," for x in t[1:end-1]]...) * "$(t[end])"
    else
        s = "$(t[1])"
    end
    return ExistentialModalOperator(s)
end
ExistentialModalOperator(s::AbstractString) = ExistentialModalOperator{Symbol(s)}()
ExistentialModalOperator(s::Symbol) = ExistentialModalOperator{s}()

"""
    EXMODOP(op)
Return a new existential modal operator as a singleton.

# Example
```jldoctest
julia> myop = EXMODOP(:℘)
⟨℘⟩
julia> is_modal_operator(myop)
true
julia> is_existential_modal_operator(myop)
true
```
"""
const EXMODOP(op) = ExistentialModalOperator(op)

struct UniversalModalOperator{T} <: AbstractUniversalModalOperator{T} end
function UniversalModalOperator(t::NTuple{N,AbstractString}) where {N}
    if length(t) > 1
        s = *(["$(x)," for x in t[1:end-1]]...) * "$(t[end])"
    else
        s = "$(t[1])"
    end
    return UniversalModalOperator(s)
end
UniversalModalOperator(s::AbstractString) = UniversalModalOperator{Symbol(s)}()
UniversalModalOperator(s::Symbol) = UniversalModalOperator{s}()

"""
    UNIVMODOP(op)
Return a new universal modal operator as a singleton.

# Example
```jldoctest
julia> myop = EXMODOP(:℘)
[℘]
julia> is_modal_operator(myop)
true
julia> is_universal_modal_operator(myop)
true
```
"""
const UNIVMODOP(op) = UniversalModalOperator(op)

"""Extract the symbol wrapped by an operator."""
reltype(::AbstractOperator{T}) where {T} = T

show(io::IO, op::AbstractOperator{T}) where {T} = print(io, "$(reltype(op))")

function show(io::IO, op::AbstractExistentialModalOperator{T}) where {T}
    # "⟨" and "⟩" delimeters should not be printed in the simplest case where T is :◊
    delim = ["⟨", "⟩"]
    if reltype(op) == Symbol("◊")
        delim = ["", ""]
    end

    print(io, delim[1] * "$(reltype(op))" * delim[2])
end

function show(io::IO, op::AbstractUniversalModalOperator{T}) where {T}
    # "[" and "]" delimeters should not be printed in the simplest case where T is :□
    delim = ["[", "]"]
    if reltype(op) == :□
        delim = ["", ""]
    end

    print(io, delim[1] * "$(reltype(op))" * delim[2])
end

#################################
#            Traits             #
#################################
SoleTraits.is_unary_operator(::AbstractUnaryOperator) = true
SoleTraits.is_binary_operator(::AbstractBinaryOperator) = true

SoleTraits.is_modal_operator(::AbstractModalOperator) = true
SoleTraits.is_existential_modal_operator(::AbstractExistentialModalOperator) = true
SoleTraits.is_universal_modal_operator(::AbstractUniversalModalOperator) = true

#################################
#      `Operators` wrapper      #
#         and utilities         #
#################################
"""Operators interface."""
struct Operators <: AbstractArray{AbstractOperator,1}
    ops::AbstractArray{AbstractOperator,1}
end
Base.size(ops::Operators) = (length(ops.ops))
Base.axes(ops::Operators) = (1:length(ops.ops),)
Base.IndexStyle(::Type{<:Operators}) = IndexLinear()
Base.getindex(ops::Operators, i::Int) = ops.ops[i]
Base.setindex!(ops::Operators, op::AbstractOperator, i::Int) = ops.ops[i] = op

# This could be considered a trait, consider modify SoleTraits
"""
    ariety(::AbstractOperator)
    ariety(::AbstractUnaryOperator)
    ariety(::AbstractBinaryOperator)
Return the ariety associated with an operator type.
"""
ariety(::AbstractOperator) = error("Expand code")
ariety(::AbstractUnaryOperator) = return 1
ariety(::AbstractBinaryOperator) = return 2

#################################
#    More on modal operators    #
#   and modal logic extensions  #
#################################
"""Legal strings to generate HS opearators."""
const HSRELATIONS = [
    "L",    # later
    "A",    # after
    "O",    # overlaps
    "E",    # ends
    "D",    # during
    "B",    # begins
    "L̅",    # before
    "A̅",    # met by
    "O̅",    # overlapped by
    "E̅",    # ended by
    "D̅",    # contains
    "B̅",    # begun by
    "=",     # equals/identity
]

"""Legal strings to generate HS₃ opearators."""
const HS₃RELATIONS = [
    "L",    # later
    "L̅",    # before
    "I",     # intersects
]

"""Legal strings to generate HS₇ opearators."""
const HS₇RELATIONS = [
    "L",    # later
    "AO",   # after or overlaps
    "DBE",  # during or begins or ends
    "L̅",    # before
    "A̅O̅",   # met by or overlapped by
    "D̅B̅E̅",  # contains or begun by or ended by
    "=",     # equals/identity
]

# Macro to collect all modaloperators (e.g @modaloperators HSRELATIONS 1)
"""
    modaloperators(R, d::Int)
Collect all the valid modal operators -both existential and universal- from a collection
of strings or symbols.

# Example
```jldoctest
julia> @modaloperators HSRELATIONS 1
⟨L⟩
⟨A⟩
⟨O⟩
⟨E⟩
⋮
[E̅]
[D̅]
[B̅]
julia> @modaloperators HS₃RELATIONS 2
⟨L,L⟩
⟨L̅,L⟩
⟨I,L⟩
⟨L,L̅⟩
⋮
[L,I]
[L̅,I]
[I,I]
```
"""
macro modaloperators(R, d::Int)
    quote
        rels = vec(collect(Iterators.product([$(R) for _ = 1:$(d)]...)))
        if "=" in $(R)
            rels = rels[1:end-1]
        end
        exrels = [EXMODOP(r) for r in rels]
        univrels = [UNIVMODOP(r) for r in rels]
        Operators(vcat(exrels, univrels))
    end
end

###########################
#     Definitions and     #
#       behaviours        #
###########################
"""Negation operator."""
const NEGATION = UNOP("¬")
precedence(::typeof(NEGATION)) = 30

"""Diamond operator."""
const DIAMOND = EXMODOP("◊")
precedence(::typeof(DIAMOND)) = 21

"""Box operator."""
const BOX = UNIVMODOP("□")
precedence(::typeof(BOX)) = 20

"""Conjunction operator."""
const CONJUNCTION = BINOP("∧")
precedence(::typeof(CONJUNCTION)) = 12

"""Disjunction operator."""
const DISJUNCTION = BINOP("∨")
precedence(::typeof(DISJUNCTION)) = 11

"""Implication operator."""
const IMPLICATION = BINOP("→")
precedence(::typeof(IMPLICATION)) = 10

SoleTraits.is_commutative(::typeof(CONJUNCTION)) = true
SoleTraits.is_commutative(::typeof(DISJUNCTION)) = true
