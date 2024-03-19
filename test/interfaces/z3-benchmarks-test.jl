using Z3
using Test
using SoleLogics
using SoleLogics: z3translate, dimacstosole
using BenchmarkTools

path_directories = [
    (dirname(@__FILE__) * "/benchmarks/uf50-218/", "Satisfability check: ", true), 
    (dirname(@__FILE__) * "/benchmarks/uuf50-218/", "Unsatisfability check: ", false),
]

for (path, title, issat) in path_directories
    println(title)
    results = @benchmark for file in readdir($path)
        formsole = dimacstosole($path * file)

        ctx = Context()
        s = Solver(ctx, "QF_NRA")

        formtranslate = SoleLogics.z3translate(formsole; logic=:prop)
        formstringtranslate = Z3.parse_string(ctx,formtranslate)
        Z3.add(s,first(formstringtranslate))

        res = Z3.check(s)
        @test $issat ? res == Z3.sat : res == Z3.unsat

        #=
        m = get_model(s)
        for (k, v) in consts(m)
            println("$k = $v")
        end
        =#
    end

    println(results)
    println()
end