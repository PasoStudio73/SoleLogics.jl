using Z3
using SoleLogics

p = Atom("p"); q = Atom("q"); form = ◊(p) ∧ q

ctx = Context()
s = Solver(ctx, "QF_NRA")

formtranslate = SoleLogics.z3translate(form; logic=:modal)
formstringtranslate = Z3.parse_string(ctx,formtranslate)
Z3.add(s,first(formstringtranslate))

res = Z3.check(s)

m = get_model(s)
for (k, v) in consts(m)
    println("$k = $v")
end