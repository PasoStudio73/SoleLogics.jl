module ManyValuedLogics

using ..SoleLogics

include("algebras/flew-algebras.jl")

export HeytingTruth, HeytingAlgebra
export precedes, succeedes, precedeq, succeedeq

include("algebras/heyting-algebras.jl")

end
