

include("unification_3.jl")
# include("unification_2.jl")

# include("TEST_unification_3.jl") # itself



# e1 = TAnno(TLocInt(1), TGlob("B"))
# e1 = TAnno(e1.expr, infer_type_rec(e1))
# e2 = TAnno(TLocInt(1), TGlob("A"))
# e2 = TAnno(e2.expr, infer_type_rec(e2))
# e2|>pr, e1|>pr

# e = build_anno_term_TProd(Array{TAnno}([]); dict_anno=Dict{String, TAnno}("a"=>e2, "b"=>e1))
# e|>pr # ERROR, which may be FINE


# e1 = TAnno(TLocInt(1), TLocInt(1))
# e1 = TAnno(e1.expr, infer_type_rec(e1))
# e2 = TAnno(TLocInt(2), TLocInt(1))
# e2 = TAnno(e2.expr, infer_type_rec(e2))
# e2|>pr, e1|>pr

# e = build_anno_term_TProd(Array{TAnno}([]); dict_anno=Dict{String, TAnno}("a"=>e2, "b"=>e1))
# e|>pr

# # infer_type_rec(TAnno(TLocInt(1), TGlob("A"))) |> pr_ctx
# # infer_type_rec(TAnno(TLocInt(1), TN())) |> pr_ctx
# # infer_type_rec(TAnno(TLocInt(1), TInt(3))) |> pr_ctx
# # infer_type_rec(TAnno(TInt(3), TN())) |> pr_ctx


# t1=TProd(Array{Term}([TypeUniverse(), TypeUniverse()]))
# t2 = TypeUniverse()
# robinsonUnify(t1, t2; mode=implydir_)

# e1 = TProd(Array{Term}([TAnno(TLocStr("A"), TypeUniverse()), TAnno(TLocStr("B"), TypeUniverse())]))
# e2 = TAnno(e1, TypeUniverse())
# infer_type_rec(e1) |>pr_ctx
# infer_type_rec(e2) |>pr_ctx


# TGlob   TGlob
# TLocInt   TLocInt
# TTop   TTop
# TTerm   TTerm
# TAbs   TAbs
# TProd   TProd
# TSum   TSum
# TApp   TApp
# TSumTerm   TSumTerm
# TAnno   TAnno
# TBranches   TBranches
# TFunAuto   TFunAuto
# TTermAuto   TTermAuto
# TAppAuto   TAppAuto
# TAppSwitch   TAppSwitch
# TGlobAuto   TGlobAuto

using Test

function test_unify_imply(t1, t2)
    println("Unify ", t1 |> pr, "  and  ", t2 |> pr, ":")
    rr = robinsonUnify(TAbs(t1), TAbs(t2); mode=implydir_)
    if rr |> itsLiterallyAlreadyOk
        println("apparently they are the same")
        return true
    end
    s1, s2 = rr.preSubst1, rr.preSubst2
    red1 = s1 !== nothing ? reduc(TApp([s1, TAbs(t1)])) : t1
    red2 = reduc(TApp([s2, TAbs(t2)]))
    println("reduced term: ", red1 |> pr)
    res = (red1 == red2)
    println(res)
    return res
end
function test_unify_join(t1, t2)
    println("Unify ", t1 |> pr, "  and  ", t2 |> pr, ":")
    rr = robinsonUnify(TAbs(t1), TAbs(t2); mode=join_)
    if rr |> itsLiterallyAlreadyOk
        println("apparently they are the same")
        return true
    end
    s1, s2, red = rr.preSubst1, rr.preSubst2, rr.res
    println("reduced term: ", red |> pr)
    res1 = (red == (s1 !== nothing ? reduc(TApp([s1, TAbs(t1)])) : t1))
    res2 = (red == reduc(TApp([s2, TAbs(t2)])))
    println("res1: $(res1), res2: $(res2)")
    return res1 && res2
end
function test_unify_meet(t1, t2)
    # The idea being that this works for DIFFERENT PROD LEMGTHS, too !!!
    println("Unify ", t1 |> pr, "  and  ", t2 |> pr, ":")
    rr = robinsonUnify(TAbs(t1), TAbs(t2); mode=meet_)
    if rr |> itsLiterallyAlreadyOk
        println("apparently they are the same")
        return true
    end
    s1, s2, red = rr.preSubst1, rr.preSubst2, rr.res
    println("reduced term: ", red |> pr)
    t1 = reduc(TApp([s1, TAbs(t1)]))
    t2 = reduc(TApp([s2, TAbs(t2)]))
    res1 = robinsonUnify(TAbs(red), TAbs(t1); mode=implydir_)
    res1 = !(res1 |> failed_unif_res)
    res2 = robinsonUnify(TAbs(red), TAbs(t2); mode=implydir_)
    res2 = !(res2 |> failed_unif_res)
    println("res1: $(res1), res2: $(res2)")
    return res1 && res2
end


eq_constraints(cs1, cs2) = (Set{Constraint}(cs1) .== Set{Constraint}(cs2)) |> all


@testset "unification_3" begin  # COMMENT TESTS


t1 = TAppAuto(TGlob("G0"), TLocInt(1))
t2 = TAppAuto(TGlob("G0"), TLocInt(2))
# @test simplify(t1, t2) == [SparseSubst(TLocInt(1), TLocInt(2))]
robinsonUnify(TAbs(t1), TAbs(t2))
@test test_unify_imply(t1, t2)
@test test_unify_join(t1, t2)


t1 = TProd(Array{Pair{Id, Term}}(["f"=>TLocInt(1), "g"=>TGlob("G")]))
t2 = TProd(Array{Pair{Id, Term}}(["g"=>TLocInt(2), "f"=>TGlob("F")]))
robinsonUnify(TAbs(t1), TAbs(t2)).preSubst1 |> (x->pr_T(x; is_an_arg=true))
robinsonUnify(TAbs(t1), TAbs(t2)).preSubst2 |> (x->pr_T(x; is_an_arg=true))
@test robinsonUnify(TAbs(t1), TAbs(t2)).res == TProd(Term[], Array{Pair{String, Term}}(["f" => TGlob("F", TypeUniverse()), "g" => TGlob("G", TypeUniverse())]))
@test test_unify_join(t1, t2)

reduc(TApp([TProd(Array{Pair{Id, Term}}(["f"=>TLocStr("g")])), TAbs(TLocStr("f"))]))


t1 = TAppAuto(TGlob("G0"), TLocInt(1))
t2 = TAppAuto(TGlob("G0"), TGlob("G99"))
# @test simplify(t1, t2) == [SparseSubst(TLocInt(1), TGlob("G99"))]
robinsonUnify(TAbs(t1), TAbs(t2))
@test test_unify_imply(t1, t2)
@test test_unify_join(t1, t2)


t1 = TLocInt(1)
t2 = TGlob("T")
@test test_unify_imply(t1, t2)
@test test_unify_join(t1, t2)

t1 = TLocStr("x")
t2 = TGlob("T")
robinsonUnify(t1, t2)
@test test_unify_imply(t1, t2)
@test test_unify_join(t1, t2)


t1 = TAppAuto(TAbs(TLocInt(1)), TLocInt(1))
t2 = TLocInt(2)
# @test simplify(t1, t2) == [SparseSubst(TLocInt(1), TLocInt(2))]
robinsonUnify(TAbs(t1), TAbs(t2))
@test test_unify_imply(t1, t2)
@test test_unify_join(t1, t2)

t1 = TAbs(TLocInt(1))
t2 = TAbs(TLocInt(1))
# @test simplify(t1, t2) == []
robinsonUnify(TAbs(t1), TAbs(t2))
@test test_unify_imply(t1, t2)
@test test_unify_join(t1, t2)

t1 = TAbs(TLocInt(1))
t2 = TAbs(TLocInt(2))
# simplify(t1, t2) |> failed_unif_res
robinsonUnify(TAbs(t1), TAbs(t2))
@test robinsonUnify(TAbs(t1), TAbs(t2)) |> failed_unif_res

t1 = TAbs(TLocInt(1))
t2 = TLocInt(3)
# @test simplify(t1, t2) == [SparseSubst(TAbs(TLocInt(1)), TLocInt(3))]
robinsonUnify(TAbs(t1), TAbs(t2))
@test test_unify_imply(t1, t2)
@test test_unify_join(t1, t2)

t1 = TAbs(TLocInt(1))
t2 = TGlob("G")
# @test simplify(t1, t2) == Error("Different: ∀(T1) is really different from G")
robinsonUnify(TAbs(t1), TAbs(t2))
@test robinsonUnify(TAbs(t1), TAbs(t2)) |> failed_unif_res

t1 = TGlob("F")
t2 = TGlob("G")
# @test simplify(t1, t2) == Error("Different: ∀(T1) is really different from G")
robinsonUnify(TAbs(t1), TAbs(t2); mode=implydir_)
@test robinsonUnify(TAbs(t1), TAbs(t2)) |> failed_unif_res

t1 = TAbs(TLocInt(1))
t2 = TAbs(TLocInt(1))
# simplify(t1, t2)
robinsonUnify(TAbs(t1), TAbs(t2))
@test test_unify_imply(t1, t2)
@test test_unify_join(t1, t2)

t = TAppAuto(TAbs(TLocInt(1)), TGlob("G1"))
t1 = TAppAuto(TLocInt(3), t)
t2 = TAppAuto(TLocInt(4), t)
# @test simplify(t1, t2) == [SparseSubst(TLocInt(3), TLocInt(4))]
robinsonUnify(TAbs(t1), TAbs(t2))
@test test_unify_imply(t1, t2)
@test test_unify_join(t1, t2)

t1 = TAppAuto(TGlob("G2"), TLocInt(3))
t2 = TAppAuto(TGlob("G2"), TAbs(TAppAuto(TLocInt(1), TGlob("G3"))))
# eq_constraints(simplify(t1, t2), [SparseSubst(TLocInt(3), TAbs(TApp([TProd(Array{Term}([TGlob("G3")]), TLocInt(1)])))])
# ^ Go fuck yourself, then die
robinsonUnify(TAbs(t1), TAbs(t2))
@test test_unify_imply(t1, t2)
@test test_unify_join(t1, t2)

t1 = TAppAuto(TGlob("G2"), TGlob("G3"))
t2 = TAppAuto(TGlob("G2"), TAbs(TAppAuto(TLocInt(1), TGlob("G3"))))
# simplify(t1, t2)  == Error("Different: T3 is really different from ∀([Just (T3).(T1)])")  # Globals cannot be "solved", and that's ok
robinsonUnify(TAbs(t1), TAbs(t2))
@test robinsonUnify(TAbs(t1), TAbs(t2)) |> failed_unif_res

t1 = TAbs(TAppAuto(TGlob("F"), TLocInt(1)))
t2 = TAbs(TAppAuto(TGlob("F"), TLocInt(2)))
# simplify(t1, t2) |> failed_unif_res  # LAMBDAS CANNOT BE UNIFIED (below, they are preapplied, which is a whole different discussion!!!)
robinsonUnify(TAbs(t1), TAbs(t2))
@test robinsonUnify(TAbs(t1), TAbs(t2)) |> failed_unif_res

t1 = TApp([TProd(Array{Term}([TGlob("X"), TGlob("Y")])), TAbs(TAppAuto(TGlob("F"), TLocInt(1)))])
t2 = TApp([TProd(Array{Term}([TGlob("Y"), TGlob("X")])), TAbs(TAppAuto(TGlob("F"), TLocInt(2)))])
# @test simplify(t1, t2) == SparseSubst[]
robinsonUnify(TAbs(t1), TAbs(t2))
@test test_unify_imply(t1, t2)
@test test_unify_join(t1, t2)

t1 = TApp([TProd(Array{Term}([TGlob("X"), TGlob("Y")])), TAbs(TAppAuto(TGlob("F"), TLocInt(1)))])
t2 = TApp([TProd(Array{Term}([TGlob("X"), TGlob("Y")])), TAbs(TAppAuto(TGlob("F"), TLocInt(2)))])
# @test simplify(t1, t2) == Error("Different: X is really different from Y")
robinsonUnify(TAbs(t1), TAbs(t2))
@test robinsonUnify(TAbs(t1), TAbs(t2)) |> failed_unif_res

t1 = TApp([TProd(Array{Term}([TLocInt(3), TLocInt(2)])), TAbs(TAppAuto(TGlob("F"), TLocInt(1)))])
t2 = TApp([TProd(Array{Term}([TLocInt(1), TLocInt(4)])), TAbs(TAppAuto(TGlob("F"), TLocInt(2)))])
# @test simplify(t1, t2) == [SparseSubst(TLocInt(3), TLocInt(4))]
robinsonUnify(TAbs(t1), TAbs(t2))
@test test_unify_imply(t1, t2)
@test test_unify_join(t1, t2)

t1 = TApp([TProd(Array{Term}([TGlob("X"), TLocInt(2)])), TAbs(TAppAuto(TLocInt(2), TLocInt(1)))])
t2 = TApp([TProd(Array{Term}([TLocInt(1), TLocInt(4)])), TAbs(TAppAuto(TGlob("F"), TLocInt(2)))])
# simplify(t1, t2)  == [SparseSubst(TGlob("X"), TLocInt(4)), SparseSubst(TLocInt(2), TGlob("F"))]
robinsonUnify(TAbs(t1), TAbs(t2))
@test test_unify_imply(t1, t2)
@test test_unify_join(t1, t2)

t1 = TAppAuto(TLocInt(4), TGlob("X"))
t2 = TAppAuto(TTermAuto(TLocInt(1), TLocInt(2)), TLocInt(3))
# eq_constraints(simplify(t1, t2), [SparseSubst(TLocInt(4), TTermAuto(TLocInt(1), TLocInt(2))), SparseSubst(TGlob("X"), TLocInt(3))])
# ^ Go fuck yourself, then die
robinsonUnify(TAbs(t1), TAbs(t2))
@test test_unify_imply(t1, t2)
@test test_unify_join(t1, t2)

t1 = TProd(Array{Term}([TLocInt(1), TLocInt(2)]))
t2 = TProd(Array{Term}([TLocInt(3), TLocInt(3)]))
# simplify(t1, t2)
robinsonUnify(TAbs(t1), TAbs(t2))
@test test_unify_imply(t1, t2)
@test test_unify_join(t1, t2)

t1 = TProd(Array{Term}([TLocInt(1), TLocInt(1)]))
t2 = TProd(Array{Term}([TGlob("F"), TGlob("G")])) # OUCHHHH
# eq_constraints(simplify(t1, t2), [SparseSubst(TLocInt(1), TGlob("G")), SparseSubst(TLocInt(1), TGlob("F"))])
robinsonUnify(TAbs(t1), TAbs(t2)) # Error, nice
@test robinsonUnify(TAbs(t1), TAbs(t2)) |> failed_unif_res

t1 = TProd(Array{Term}([TLocInt(1), TGlob("F")]))
t2 = TProd(Array{Term}([TGlob("G"), TLocInt(1)])) # otoh, this SHOULD keep working..
# eq_constraints(simplify(t1, t2), [SparseSubst(TLocInt(1), TGlob("G")), SparseSubst(TGlob("F"), TLocInt(1))])
robinsonUnify(TAbs(t1), TAbs(t2))
@test test_unify_imply(t1, t2)
@test test_unify_join(t1, t2)

t1 = TProd(Array{Term}([TLocInt(1), TLocInt(1)]))
t2 = TProd(Array{Term}([TLocInt(1), TTermAuto(TGlob("A"), TLocInt(1))]))
# eq_constraints(simplify(t1, t2), [SparseSubst(TLocInt(1), TLocInt(1)), SparseSubst(TLocInt(1), TTermAuto(TGlob("A"), TLocInt(1)))])
robinsonUnify(TAbs(t1), TAbs(t2)) # Recursive Error, nice!
@test robinsonUnify(TAbs(t1), TAbs(t2)) |> failed_unif_res

t1 = TProd(Array{Term}([TLocInt(1), TLocInt(1), TLocInt(2), TLocInt(2)]))
t2 = TProd(Array{Term}([TLocInt(1), TLocInt(2), TLocInt(2), TTermAuto(TGlob("A"), TTermAuto(TGlob("B"), TLocInt(1)))]))
# eq_constraints(simplify(t1, t2), [SparseSubst(TLocInt(2), TTermAuto(TGlob("A"), TTermAuto(TGlob("B"), TLocInt(1)))), SparseSubst(TLocInt(1), TLocInt(1)), SparseSubst(TLocInt(2), TLocInt(2)), SparseSubst(TLocInt(1), TLocInt(2))])
t1|>pr
t2|>pr
t1|>reduc|>pr
t2|>reduc|>pr
@test robinsonUnify(TAbs(t1), TAbs(t2)) |> failed_unif_res

t1 = TProd(Array{Term}([TLocInt(1), TLocInt(1), TLocInt(2), TLocInt(2)]))
t2 = TProd(Array{Term}([TTermAuto(TGlob("A"), TTermAuto(TGlob("B"), TGlob("C"))), TLocInt(2), TLocInt(2), TTermAuto(TGlob("A"), TTermAuto(TGlob("B"), TLocInt(1)))]))
# eq_constraints(simplify(t1, t2), [SparseSubst(TLocInt(2), TLocInt(2)), SparseSubst(TLocInt(1), TTermAuto(TGlob("A"), TTermAuto(TGlob("B"), TGlob("C")))), SparseSubst(TLocInt(2), TTermAuto(TGlob("A"), TTermAuto(TGlob("B"), TLocInt(1)))), SparseSubst(TLocInt(1), TLocInt(2))])
robinsonUnify(TAbs(t1), TAbs(t2)) #.|> pr
@test test_unify_imply(t1, t2)   #####  YESSSSS
@test test_unify_join(t1, t2)   #####  YESSSSS

t1 = TProd(Array{Term}([TLocInt(1), TLocInt(2)]))
t2 = TProd(Array{Term}([TLocInt(2), TTermAuto(TGlob("A"), TLocInt(1))]))
# repr(simplify(t1, t2)) == "SparseSubst[SparseSubst(TLocInt(2), TTermAuto(TGlob(\"A\"), TLocInt(1))), SparseSubst(TLocInt(1), TLocInt(2))]"
robinsonUnify(TAbs(t1), TAbs(t2))
@test test_unify_imply(t1, t2)
@test test_unify_join(t1, t2)

t1 = TProd(Array{Term}([TLocInt(1), TLocInt(1), TLocInt(2), TLocInt(2)]))
t2 = TProd(Array{Term}([TGlob("F"), TLocInt(3), TLocInt(3), TGlob("G")]))
# eq_constraints(simplify(t1, t2), [SparseSubst(TLocInt(2), TGlob("G")), SparseSubst(TLocInt(1), TLocInt(3)), SparseSubst(TLocInt(1), TGlob("F")), SparseSubst(TLocInt(2), TLocInt(3))])
robinsonUnify(TAbs(t1), TAbs(t2)) # Error, nice
@test robinsonUnify(TAbs(t1), TAbs(t2)) |> failed_unif_res

t1 = TAbs(TGlob("A"))
t2 =  TGlob("A")
# simplify(t1, t2) # Nope, and that's fine
robinsonUnify(t1, t2)
@test robinsonUnify(TAbs(t1), TAbs(t2)) |> failed_unif_res

t1 = TProd(Array{Term}([TLocInt(1), TLocInt(1), TLocInt(2), TLocInt(2)]))
t2 = TProd(Array{Term}([TGlob("F"), TLocInt(1), TLocInt(1), TGlob("G")]))
# eq_constraints(simplify(t1, t2), [SparseSubst(TLocInt(2), TLocInt(1)), SparseSubst(TLocInt(1), TLocInt(1)), SparseSubst(TLocInt(2), TGlob("G")), SparseSubst(TLocInt(1), TGlob("F")), ])
robinsonUnify(TAbs(t1), TAbs(t2)) # Error, nice
@test robinsonUnify(TAbs(t1), TAbs(t2)) |> failed_unif_res

t1, t2 = TLocInt(3), TAbs(TTermAuto(TGlob("A"), TLocInt(2)))
@test test_unify_imply(t1, t2.body)
@test test_unify_join(t1, t2.body)

t1 = TAbs(TTermAuto(TLocInt(1), TProd(Array{Term}([TGlob("A"), TLocInt(2)]))))
t2 = TAbs(TTermAuto(TLocInt(1), TLocInt(2)))
robinsonUnify(t1, t2)
@test test_unify_imply(t1.body, t2.body)
@test test_unify_join(t1.body, t2.body)

t1 = TAbs(TLocInt(3))
t2 = TAbs(TTermAuto(TLocInt(1), TLocInt(2)))
robinsonUnify(t1, t2)
@test test_unify_imply(t1.body, t2.body)
@test test_unify_join(t1.body, t2.body)

# function prepTransEx(l, g1, g2)
#     v1=vcat([[TLocInt(i), TLocInt(i)] for i in 1:l]...)
#     v2=vcat([[TLocInt(i), TLocInt(i)] for i in 1:l-1]...)
#     TProd(v1), TProd(vcat([TGlob(g1)], v2, [TGlob(g2)]))
# end
# t1, t2 = prepTransEx(55, "F", "F")
# robinsonUnify(TAbs(t1), TAbs(t2))
# @test test_unify_imply(t1, t2)
# @ test_unify_join(t1, t2)

# t1, t2 = prepTransEx(10, "F", "G")
# robinsonUnify(TAbs(t1), TAbs(t2))


t1 = TProd(Array{Term}([TLocInt(1), TSumTerm(1, "EQ", TProd(Array{Term}([TGlob("E"), TLocInt(2)])))]))
t2 = TProd(Array{Term}([TGlob("A"), TSumTerm(1, "EQ", TLocInt(1))]))
t1|>pr
@test test_unify_imply(t1, t2)
@test test_unify_join(t1, t2)

t1 = TProd(Array{Term}([TLocInt(1), TSumTerm(1, "EQ", TProd(Array{Term}([TGlob("E"), TLocInt(2)])))]))
t2 = TProd(Array{Term}([TGlob("A"), TLocInt(2)]))
@test test_unify_imply(t1, t2)
@test test_unify_join(t1, t2)

t1 = TProd(Array{Term}([TLocInt(1), TSumTerm(1, "EQ", TProd(Array{Term}([TGlob("E"), TLocInt(2)])))]))
t2 = TProd(Array{Term}([TGlob("A"), TSumTerm(2, "GQ", TProd(Array{Term}([TGlob("E"), TLocInt(2)])))]))
@test robinsonUnify(t1, t2) |> failed_unif_res


# K for TESTS w/ DIFFERENT NUMBER OF ITEMS NOW:
t1 = TProd(Array{Term}([TLocInt(1), TGlob("B")]))
t2 = TProd(Array{Term}([TGlob("A"), TLocInt(1), TLocInt(2)]))
@test robinsonUnify(t1, t2; mode=implydir_) |> failed_unif_res
@test test_unify_meet(t1, t2)

t1 = TProd(Array{Term}([TLocInt(1), TGlob("B"), TLocInt(2)]))
t2 = TProd(Array{Term}([TGlob("A"), TLocInt(1)]))
@test test_unify_meet(t1, t2)

t1 = TProd(Array{Term}([TGlob("A"), TGlob("B")]))
t2 = TProd(Array{Term}([TGlob("A"), TGlob("B")]))
@test robinsonUnify(t1, t2) |> itsLiterallyAlreadyOk
@test test_unify_meet(t1, t2)

t1 = TProd(Array{Term}([TGlob("A"), TGlob("B"), TGlob("C")]))
t2 = TProd(Array{Term}([TGlob("A"), TGlob("B")]))
@test robinsonUnify(t1, t2) |> itsLiterallyAlreadyOk
@test test_unify_meet(t1, t2)

t1 = TTerm(TProd(Array{Term}([TLocInt(1), TGlob("B"), TLocInt(2)])), TGlob("Z"))
t2 = TTerm(TProd(Array{Term}([TGlob("A"), TLocInt(1)])), TGlob("Z"))
@test robinsonUnify(t1, t2; mode=implydir_) |> failed_unif_res
@test test_unify_meet(t1, t2)
@test robinsonUnify(t1, t2; mode=join_).res == TTerm(TProd(Term[TGlob("A"), TGlob("B"), TLocInt(1)]), TGlob("Z"))

t1 = TTerm(TProd(Array{Term}([TLocInt(1), TGlob("B")])), TGlob("Z"))
t2 = TTerm(TProd(Array{Term}([TGlob("A"), TLocInt(1), TLocInt(2)])), TGlob("Z"))
res = robinsonUnify(t1, t2; mode=implydir_)
s1, s2 = res.preSubst1, res.preSubst2
ass_reduc(t1, s1) |> pr
ass_reduc(t2, s2) |> pr
@test ass_reduc(t2, s2) == TTerm(TProd(Term[TGlob("A"), TGlob("B"), TLocInt(1)]), TGlob("Z"))
@test test_unify_meet(t1, t2)

t1 = TTermAuto(TTerm(TProd(Array{Term}([TLocInt(1), TLocInt(2)])), TGlob("Z")), TGlob("Z"))
t2 = TTermAuto(TTerm(TProd(Array{Term}([TGlob("A"), TLocInt(2)])), TGlob("Z")), TGlob("Z"))
@test test_unify_imply(t1, t2) # ACTUALLY SECRETLY A PROBLEM !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
@test test_unify_join(t1, t2)
@test test_unify_meet(t1, t2)

t1 = TTermAuto(TTerm(TProd(Array{Term}([TLocInt(1)])), TGlob("Z")), TGlob("Z"))
t2 = TTermAuto(TTerm(TProd(Array{Term}([TGlob("A"), TLocInt(2)])), TGlob("Z")), TGlob("Z"))
@test robinsonUnify(t1, t2; mode=implydir_) |> failed_unif_res
@test test_unify_meet(t1, t2)

t1 = TTermAuto(TTerm(TProd(Array{Term}([TLocInt(1), TLocInt(2)])), TGlob("Z")), TGlob("Z"))
t2 = TTermAuto(TTerm(TProd(Array{Term}([TGlob("A")])), TGlob("Z")), TGlob("Z"))
t1 |> pr
t2 |> pr
res = robinsonUnify(t1, t2; mode=implydir_)
s1, s2 = res.preSubst1, res.preSubst2
ass_reduc(t1, s1) |> pr
ass_reduc(t2, s2) |> pr
@test ass_reduc(t1, s1) == TTerm(TProd(Term[TTerm(TProd(Term[TGlob("A"), TLocInt(1)]), TGlob("Z"))]), TGlob("Z"))
@test test_unify_meet(t1, t2)



# HARDER TESTS ON REVERSE CONSTRAINTS:
t1 = TProd(Array{Term}([TGlob("F"), TLocInt(1), TLocInt(1)]))
t2 = TProd(Array{Term}([TLocInt(1), TGlob("G")]))
# simplify(SparseSubst(t1, t2))
test_unify_imply(t1, t2) # Yeah it's false, it's fine tho
@test robinsonUnify(t1, t2; mode=meet_).res == TProd(Term[TGlob("F"), TGlob("G"), TGlob("G")])

t1 = TProd(Array{Term}([TGlob("F"), TLocInt(1), TLocInt(1)]))
t2 = TProd(Array{Term}([TLocInt(1), TGlob("G")]))
@test robinsonUnify(t1, t2).res == TProd(Term[TGlob("F"), TGlob("G")])
# # ^ SILENT DROPPING

t1 = TProd(Array{Term}([TLocInt(1), TGlob("G")]))
t2 = TProd(Array{Term}([TGlob("F"), TLocInt(1), TLocInt(1)]))
# simplify(ReverseConstraint(t2, t1))
robinsonUnify(t1, t2) # Cannot unify !!!!!!!!!!!!!!!!!!!!!!!!!!!
# ass_reduc(t1, s1) |> pr
# ass_reduc(t2, s2) |> pr


# Tests that are HARD because I DONT REALLY KNOW WHAT I WANT WRT TO TAbs SCOPING:
# t1 = TProd(Array{Term}([TLocInt(1), TGlob("F"), TProd(Array{Term}([TLocInt(2), TLocInt(3)]), TProd(Array{Term}([TLocInt(4), TProd(Array{Term}([TGlob("A"), TLocInt(5)])])])
# t2 = TProd(Array{Term}([TGlob("G"), TLocInt(6), TProd(Array{Term}([TLocInt(7), TLocInt(8)]), TProd(Array{Term}([TLocInt(9), TProd(Array{Term}([TGlob("A"), TLocInt(10)])])])
# robinsonUnify(TAbs(t1), TAbs(t2), 10,10; unify_tlocs_ctx=false)


# t1 = TProd(Array{Term}([TLocInt(1), TGlob("F"), TProd(Array{Term}([TLocInt(2), TLocInt(3)])])
# t2 = TProd(Array{Term}([TGlob("G"), TLocInt(4), TProd(Array{Term}([TLocInt(5)])])
# robinsonUnify(TAbs(t1), TAbs(t2), 5,5; unify_tlocs_ctx=false) # silently dropping


# t1 = TProd(Array{Term}([TLocInt(1), TGlob("F"), TProd(Array{Term}([TLocInt(2), TLocInt(3)])])
# t2 = TProd(Array{Term}([TGlob("G"), TLocInt(4), TLocInt(5)]) # TLocInt becomes a 2-prod
# robinsonUnify(TAbs(t1), TAbs(t2), 4,4; unify_tlocs_ctx=false)

# t1 = TProd(Array{Term}([TLocInt(1), TGlob("F"), TProd(Array{Term}([TLocInt(2), TLocInt(3)])])
# t2 = TProd(Array{Term}([TGlob("G"), TLocInt(4), TProd(Array{Term}([TLocInt(4), TGlob("B"), TLocInt(6)])]) # TLocInt CANNOT GROW, now, can it?
# robinsonUnify(TAbs(t1), TAbs(t2), 6,6; unify_tlocs_ctx=false)

# #  [\"[T1]\", \"T2\"] cannot be unified with ELocs typed [\"[T1 x T2]\", \"T3\"]
# t1 = TProd(Array{Term}([TProd(Array{Term}([TProd(Array{Term}([TGlob("A")]), TLocInt(1)])])
# t2 = TProd(Array{Term}([TProd(Array{Term}([TProd(Array{Term}([TGlob("A"), TLocInt(2)])])])
# t1 |> pr, t2|>pr
# robinsonUnify(TAbs(t1), TAbs(t2), 2,2; unify_tlocs_ctx=false)
# robinsonUnify(TAbs(t2), TAbs(t1), 2,2; unify_tlocs_ctx=false)



# Is my unification higher order or not? I sincerely don't know.....
t1 = TApp([TApp([TGlobAuto("a"), TLocStr("G")]), TLocStr("F")])
t2 = TApp([TGlobAuto("b"), TLocStr("F")])
robinsonUnify(t1, t2)  # -->  "Different: TG(a) is really different from b"

# if F==1, G==2:
t1 = TApp([TApp([TGlobAuto("a"), TLocInt(2)]), TLocInt(1)])
t2 = TApp([TGlobAuto("b"), TLocInt(1)])
robinsonUnify(t1, t2)  # --> "Different: T2(a) is really different from b"

# >> While the right answer would be "TG==TAbs(b)", or "T2==TAbs(b)" .....
# >>> Yep... Squarely First Order. That's what it says in the title, btw...





sr = ass_reduc

# Each TLocInt refers to position in the row BELOW:
t1 = TProd(Array{Term}([TTerm(TLocInt(1), TLocInt(2)), TLocInt(3)]))
t2 = TProd(Array{Term}([TLocInt(1), TLocInt(2), TLocInt(2)]))
t3 = TProd(Array{Term}([TGlob("G"), TLocInt(1)]))
t4 = TProd(Array{Term}([TTermAuto(TGlob("A"), TGlob("B"))]))
get_reduc_subst([t1, t2, t3, t4]) |> reduc |> pr == "[G->A->B x A->B]"

sr(sr(t1, t2), sr(t3, t4)) |> pr
sr(sr(t1, t2, t3), t4) |> pr
sr(t1, sr(t2, t3, t4)) |> pr



# Each TLocInt refers to position in the row BELOW:
t1 = TProd(Array{Term}([TLocInt(1), TLocInt(2), TLocInt(3), TLocInt(4), TLocInt(5)]))
t2 = TProd(Array{Term}([TLocInt(1), TLocInt(1), TLocInt(2), TLocInt(3), TLocInt(4)]))
t3 = TProd(Array{Term}([TLocInt(1), TLocInt(2), TLocInt(3), TLocInt(3)]))
t4 = TProd(Array{Term}([TLocInt(1), TLocInt(2), TLocInt(2)]))
t5 = TProd(Array{Term}([TLocInt(4), TGlob("A")]))
get_reduc_subst([t1, t2, t3, t4, t5]) |> reduc |> pr == "[T4 x T4 x A x A x A]"

res1 = sr(sr(t1, t2), sr(t3, t4, t5)) |> pr
res2 = sr(sr(t1, t2, t3, t4), t5) |> pr
res3 = sr(t1, sr(t2, t3), sr(t4, t5)) |> pr
@test res1 == res2
@test res1 == res3



# Each TLocInt refers to position in the row BELOW:
t1 = TProd(Array{Term}([TLocInt(1), TGlob("F"), TLocInt(3), TTerm(TProd(Array{Term}([TLocInt(4)])), TLocInt(5))]))
t2 = TProd(Array{Term}([TLocInt(1), TGlob("SKIPPED"), TTerm(TLocInt(2), TLocInt(3)), TLocInt(1), TLocInt(1)]))
t3 = TProd(Array{Term}([TLocInt(2), TLocInt(1), TLocInt(2)]))
t4 = TProd(Array{Term}([TLocInt(1), TTerm(TProd(Array{Term}([TLocInt(2)])), TLocInt(3))]))
t5 = TProd(Array{Term}([TLocInt(2), TGlob("Z"), TGlob("Z")]))
get_reduc_subst([t1, t2, t3, t4, t5]) |> reduc |> pr == "[Z->Z x F x T2->Z->Z x Z->Z->Z->Z]"

res1 = sr(sr(t1, t2), sr(t3, t4, t5)) |> pr
res2 = sr(sr(t1, t2, t3, t4), t5) |> pr
res3 = sr(t1, sr(t2, t3), sr(t4, t5)) |> pr
@test res1 == res2
@test res1 == res3




# TEST INFERENCE:


e = TLocInt(2)
@test infer_type_rec(e) == TTerm(TProd(Array{Term}([TLocInt(1), TLocInt(2)])), TLocInt(2))

e = TGlob("f", TTermAuto(TGlob("A"), TGlob("B")))
@test infer_type_rec(e) == TTerm(TProd(Array{Term}([])), TTermAuto(TGlob("A"), TGlob("B")))

e = TAnno(TLocInt(1), TypeOfTLocIntReturning(TGlob("A")))
@test infer_type_rec(e) == TTerm(TProd(Array{Term}([TGlob("A")])), TGlob("A"))

e = TAnno(TLocInt(2), TypeOfTLocIntReturning(TGlob("A"); n_loc=2))
@test infer_type_rec(e) == TTerm(TProd(Array{Term}([TLocInt(1), TGlob("A")])), TGlob("A"))

e = TAbs(TLocStr("1"))
@test infer_type_rec(e) == TTerm(TProd(Term[], Array{Pair{String, Term}}([])), TTerm(TProd(Term[], Array{Pair{String, Term}}(["1" => TLocInt(1)])), TLocInt(1)))

e = TProd(Array{Term}([TLocInt(2), TLocInt(2)]))
@test infer_type_rec(e) == TTerm(TProd(Array{Term}([TLocInt(1), TLocInt(2)])), TProd(Term[TLocInt(2), TLocInt(2)]))

e = TProd(Array{Term}([TLocInt(2), TAnno(TLocInt(2), TLocInt(1))]))
@test infer_type_rec(e) == TTerm(TProd(Array{Term}([TLocInt(1), TLocInt(2)])), TProd(Term[TLocInt(2), TLocInt(2)]))

e = TProd(Array{Term}([TGlobAuto("t"), TAnno(TLocInt(1), TLocInt(1))]))
infer_type_rec(e)

tglob = TTermAuto(TGlob("A"), TLocInt(2))
tanno = TTermEmpty(TTermAuto(TLocInt(1), TGlob("B")))
# tanno = TAbs(TTermAuto(TGlob("A"), TGlob("B")))
# tanno = TTermAuto(TGlob("A"), TGlob("B"))
e = TAnno(TGlob("f", tglob), tanno)
@test infer_type_rec(e) == TTerm(TProd(Array{Term}([])), TTermAuto(TGlob("A"), TGlob("B")))
infer_type_rec(e) |> pr_ctx
tanno |> pr_ctx

tt = TTermAuto(TGlob("A"), TGlob("B"))
e = TProd(Array{Term}([TGlob("f", tt), TGlob("g", tt)]))
@test infer_type_rec(e) == TTerm(TProd(Array{Term}([])), TProd(Term[TTermAuto(TGlob("A"), TGlob("B")), TTermAuto(TGlob("A"), TGlob("B"))]))

tt = TTermAuto(TLocInt(1), TGlob("B"))
e = TProd(Array{Term}([TGlob("f", tt), TGlob("g", tt)]))
@test infer_type_rec(e) == TTerm(TProd(Array{Term}([])), TProd(Term[TTerm(TProd(Term[TLocInt(1)]), TGlob("B")), TTerm(TProd(Term[TLocInt(2)]), TGlob("B"))]))
infer_type_rec(e) |> pr_ctx # == "[T1->B x T2->B]" # T2, important! GOOD
# TProd(Term[TTerm(TProd(Term[TLocInt(1)]), TGlob("B")), TTerm(TProd(Term[TLocInt(2)]), TGlob("B"))]) |> pr



# Broken because it's not clear the TAbs scope:
# e = TProd(Array{Term}([TAnno(TLocInt(1), TLocInt(3)), TAnno(TLocInt(1), TLocInt(2)), TGlob("a", TLocInt(1))]))
# @test infer_type_rec(e) == TTerm(TProd(Array{Term}([TLocInt(6)])), TProd(Term[TLocInt(6), TLocInt(6)])))
# e = TProd(Array{Term}([TAnno(TLocInt(1), TLocInt(1)), TAnno(TLocInt(1), TLocInt(2)), TAnno(TLocInt(2), TLocInt(1))]))
# @test infer_type_rec(e) == TTerm(TProd(Array{Term}([TLocInt(6), TLocInt(11)])), TProd(Term[TLocInt(6), TLocInt(6), TLocInt(11)])))
# e = TProd(Array{Term}([TAnno(TLocInt(1), TLocInt(2)), TAnno(TLocInt(1), TLocInt(3)), TAnno(TLocInt(1), TLocInt(4))]))
# @test infer_type_rec(e) == TTerm(TProd(Array{Term}([TLocInt(7)])), TProd(Term[TLocInt(7), TLocInt(7), TLocInt(7)])))




e = TAbs(TProd(Array{Term}([TLocInt(2), TAnno(TLocInt(1), TypeOfTLocIntReturning(TGlob("T")))])))
@test infer_type_rec(e) == TTerm(TProd(Array{Term}([])), TTerm(TProd(Term[TGlob("T"), TLocInt(1)]), TProd(Term[TLocInt(1), TGlob("T")])))

e = TAnno(TAbs(TGlob("b", TGlob("B"))), TTermEmpty(TTermAuto(TProd(Array{Term}([TGlob("A")])),  TGlob("B"))))
@test infer_type_rec(e) == TTerm(TProd(Array{Term}([])), TTerm(TProd(Term[TProd(Term[TGlob("A")])]), TGlob("B")))

tf = TAnno(TAbs(TGlob("b", TGlob("B"))), TTermEmpty(TTermAuto(TGlob("A"),  TGlob("B"))))
targ = TAnno(TLocInt(1), TypeOfTLocIntReturning(TGlob("A")))
e = TAppAuto(tf, targ)
e |>reduc
infer_type_rec(tf).t_out |>pr
@test infer_type_rec(tf).t_out == TTerm(TProd(Array{Term}([TGlob("A")])), TGlob("B"))
@test infer_type_rec(e).t_out == TGlob("B")

e = TAbs(TApp([TProd(Array{Term}([TLocInt(1), TLocInt(1)])), TLocInt(2)]))
infer_type_rec(e).t_out |> pr # == "[T1 x [T1 x T1]->T2]->T2"
@test infer_type_rec(e).t_out == TTerm(TProd(Array{Term}([TLocInt(1), TTerm(TProd(Array{Term}([TLocInt(1), TLocInt(1)])), TLocInt(2))])), TLocInt(2))

# e = TApp([TLocStr("a"), TAnno(TAbs(TLocStr("b")), TTerm(TProd(Array{Pair{String, Term}}(["a"=>TGlob("A")])), TGlob("B")))])
# infer_type_rec(TAnno(TAbs(TLocStr("b")), TTermAuto(TGlob("A"), TGlob("B"))))
# infer_type_rec(TAbs(TLocStr("b")))
# TODO: Fix this mess ^


a1t = TTermEmpty(TTerm(TProd(Array{Pair{String, Term}}(["1" => TLocInt(1)])), TLocInt(1)))
a2t = TTermEmpty(TTermEmpty(TGlob("B")))
a3t = TTermEmpty(TGlob("A"))
@test infer_type_(TProd(Array{Term}([])), Array{TTerm}([a1t, a2t, a3t])) == TTerm(TProd(Term[], Array{Pair{String, Term}}([])), TProd(Term[TTerm(TProd(Term[], Array{Pair{String, Term}}(["1" => TLocInt(1)])), TLocInt(1)), TTerm(TProd(Term[], Array{Pair{String, Term}}([])), TGlob("B", TypeUniverse())), TGlob("A", TypeUniverse())], Array{Pair{String, Term}}([])))


# infer_type_rec(e).t_out |> pr # == "[T1 x [T1 x T1]->T2]->T2"
# @test infer_type_rec(e).t_out == TTerm(TProd(Array{Term}([TLocInt(1), TTerm(TProd(Array{Term}([TLocInt(1), TLocInt(1)])), TLocInt(2))])), TLocInt(2))

ea = TProd(Array{Term}([TAnno(TLocInt(1), TypeOfTLocIntReturning(TGlob("A")))]))
ef1 = TGlob("f", TTermAuto(TLocInt(1), TGlob("B")))
e = TAbs(TApp([ea, ef1]))
e |> pr
e|>reduc
@test infer_type_rec(e) == TTerm(TProd(Array{Term}([])), TTerm(TProd(Term[TGlob("A")]), TGlob("B")))

infer_type_rec(e.body) |> pr_ctx

ea = TAnno(TLocInt(1), TypeOfTLocIntReturning(TGlob("A")))
ef1 = TGlob("f", TTerm(TLocInt(1), TGlob("B")))
e = TAbs(TApp([ea, ef1]))
e |> pr
infer_type_rec(e).t_out |> pr
@test infer_type_rec(e) == TTerm(TProd(Array{Term}([])), TTerm(TProd(Term[TGlob("A")]), TGlob("B")))

ea = TProd(Array{Term}([TAnno(TLocInt(1), TypeOfTLocIntReturning(TGlob("A")))]))
ef1 = TGlob("f", TTermAuto(TLocInt(1), TProd(Array{Term}([TGlob("B1"), TGlob("B2")]))))
ef2 = TGlob("g", TTermAuto(TGlob("B1"), TLocInt(1)))
e = TAbs(TApp([ea, ef1, ef2]))
e |> pr
@test infer_type_rec(e) == TTerm(TProd(Term[]), TTerm(TProd(Term[TGlob("A")]), TLocInt(1)))
# ^ I mean, unfortunately it's Not wrong ... Even if i Really wish the TLocInt's wre actually shared sometimes....
infer_type_rec(e).t_out |> pr

ea = TProd(Array{Term}([TAnno(TLocInt(1), TypeOfTLocIntReturning(TGlob("A")))]))
ef1 = TGlob("f", TTermAuto(TLocInt(1), TProd(Array{Term}([TGlob("B1"), TGlob("B2")]))))
ef2 = TGlob("g", TTerm(TLocInt(1), TLocInt(1)))
e = TAbs(TApp([ea, ef1, ef2]))
e|>pr
@test infer_type_rec(e) == TTerm(TProd(Term[]), TTerm(TProd(Term[TGlob("A")]), TProd(Term[TGlob("B1"), TGlob("B2")])))
infer_type_rec(e) |> pr_ctx

e = TApp([TLocInt(1), TAbs(TLocInt(1))])
@test infer_type_rec(e) |> (x->x.t_in) == TProd(Array{Term}([TProd(Array{Term}([TLocInt(1)]))])) # And NOTT [TProd(Array{Term}([TLocInt(1)])], plz ????


f1 = TAbs(TProd(Array{Term}([TGlobAuto("a"), TGlobAuto("b")])))
f2 = TAbs(TProd(Array{Term}([TLocInt(2), TLocInt(1)])))
f3 = TAbs(TProd(Array{Term}([TLocInt(2), TGlobAuto("c"), TLocInt(1), ])))
@test infer_type_rec(TConc([f1, f2, f3])) == TTerm(TProd(Term[], Array{Pair{String, Term}}([])), TTerm(TProd(Term[], Array{Pair{String, Term}}([])), TProd(Term[TGlob("A", TypeUniverse()), TGlob("C", TypeUniverse()), TGlob("B", TypeUniverse())], Array{Pair{String, Term}}([]))))
infer_type_rec(TConc([f1, f2, f3])) |> pr_ctx


f1 = TAbs(TProd(Array{Term}([TLocInt(2), TGlobAuto("b")])))
f2 = TAbs(TProd(Array{Term}([TLocInt(2), TLocInt(1)])))
f3 = TAbs(TProd(Array{Term}([TLocInt(2), TGlobAuto("c"), TLocInt(1), ])))
@test infer_type_rec(TConc([f1, f2, f3])) ==TTerm(TProd(Term[], Array{Pair{String, Term}}([])), TTerm(TProd(Term[TLocInt(1), TLocInt(2)], Array{Pair{String, Term}}([])), TProd(Term[TLocInt(2), TGlob("C", TypeUniverse()), TGlob("B", TypeUniverse())], Array{Pair{String, Term}}([]))))
infer_type_rec(TConc([f1, f2, f3])) |> pr_ctx


f1 = TAbs(TProd(Array{Term}([TLocInt(2), TGlobAuto("b")])))
@test infer_type_rec(TConc([TLocInt(1), f1])) == TTerm(TProd(Term[TTerm(TLocInt(1), TProd(Term[TLocInt(2), TLocInt(3)], Array{Pair{String, Term}}([])))], Array{Pair{String, Term}}([])), TTerm(TLocInt(1), TProd(Term[TLocInt(3), TGlob("B", TypeUniverse())], Array{Pair{String, Term}}([]))))
infer_type_rec(TConc([TLocInt(1), f1])) |> pr_ctx


SType |> pr
S |> pr
infer_type_rec(S) |> pr_ctx  # YES my boy... YES :)
@test infer_type_rec(S) == TTerm(TProd(Term[]), TTerm(TProd(Term[TTerm(TProd(Term[TLocInt(1)]), TTerm(TProd(Term[TLocInt(2)]), TLocInt(3))), TTerm(TProd(Term[TLocInt(1)]), TLocInt(2)), TLocInt(1)]), TLocInt(3)))


proj1_1 = TApp([TLocInt(1), TAbs(TLocInt(1))])
vec_w_proj2_1 = TProd(Array{Term}([TApp([TLocInt(1), TAbs(TLocInt(2))]), TLocInt(2)]))
proj1_1 |> pr_E
vec_w_proj2_1 |> pr_E
infer_type_rec(proj1_1) |> pr_ctx
infer_type_rec(vec_w_proj2_1) |> pr_ctx
e = TProd(Array{Term}([proj1_1, vec_w_proj2_1]))
e |> pr_E
infer_type_rec(e) |> pr_ctx  # YES my boy... YESSSS :)
@test infer_type_rec(e) |> pr_ctx == "Given [[T1 x T2] x T3], get [T1 x [T2 x T3]]"

# With letters:

t1 = TTerm(TProd(Term[], Array{Pair{String, Term}}(["1_" => TLocInt(1)])), TLocStr("1_"))
t2 = TTerm(TLocInt(1), TLocInt(2))
robinsonUnify(t1, t2)
robinsonUnify(t1, t2).res |> pr
@test test_unify_join(t1, t2)
@test test_unify_imply(t1, t2)

proj1_1 = TApp([TLocStr("1_"), TAbs(TLocStr("2_"))])
proj1_1 |> pr_E
infer_type_rec(proj1_1) |> pr_T
vec_w_proj2_1 = TProd(Array{Term}([TApp([TLocStr("1_"), TAbs(TLocStr("3_"))]), TLocStr("4_")]))
vec_w_proj2_1 |> pr_E
infer_type_rec(vec_w_proj2_1) |> pr_T

e = TProd(Array{Term}([proj1_1, vec_w_proj2_1]))
e |> pr_E
infer_type_rec(e) |> pr_ctx  # YES my boy... YESSSS :)
@test infer_type_rec(e) |> pr_ctx == "Given [4_:T3 x 1_:[3_:T2 x 2_:T1]], get [T1 x [T2 x T3]]"

"Given [1_:[2_:T1 x 3_:T2], 4_:T3], get [2_:T1 x [3_:T2 x 4_:T3]]"



# NICE THINGS YOU CAN USE AS TESTS: I NEVER PROPERLY WRITE THEM DOWN THO:
# e = TAnno(TLocStr("a"), TGlob("T"))
# infer_type_rec(e) |> pr_ctx
# # K really broken.. NOTE: before, the last  TLocInt(1) becomes TLocInt(2), in cas it can be helpful to know
# e = TProd(Term[TLocStr("a"), TAnno(TLocStr("a"), TGlob("T"))])
# infer_type_rec(e) |> pr_ctx
# TLocStr("a") |> infer_type_rec |> pr_ctx
# TAnno(TLocInt(1), TGlob("T")) |> infer_type_rec |> pr_ctx
# # The simple one
# e = TProd(Array{Term }([TLocStr("a"), TProdSingle(TLocStr("a"))]))
# infer_type_rec(e) |> pr_ctx # GREAT
# # The broken one
# e = TProd(Term[TLocStr("a"), TLocStr("x"), TLocStr("y"), TAnno(TProd(Term[TAnno(TProd(Term[TLocStr("a"), TLocStr("x")]), TAbs(TSumTerm(3, "OP", TProd(Term[TLocInt(1), TLocInt(2)])), ["1", "2"])), TAnno(TProd(Term[TLocStr("a"), TLocStr("y")]), TAbs(TSumTerm(3, "OP", TProd(Term[TLocInt(1), TLocInt(2)])), ["1", "2"]))]), TAbs(TSumTerm(4, "EQ", TProd(Term[TLocInt(1), TLocInt(2)])), ["1", "2"])), TAnno(TProd(Term[TLocStr("a")]), TAbs(TSumTerm(2, "IV", TProd(Term[TLocInt(1)])), ["1"]))])
# infer_type_rec(e) |> pr_ctx
# # A bit shorter, still broken
# e = TProd(Term[TLocStr("a"), TAnno(TProd(Term[TAnno(TProd(Term[TLocStr("a"), TLocStr("x")]), TAbs(TSumTerm(3, "OP", TProd(Term[TLocInt(1), TLocInt(2)])))), TAnno(TProd(Term[TLocStr("a"), TLocStr("y")]), TAbs(TSumTerm(3, "OP", TProd(Term[TLocInt(1), TLocInt(2)]))))]), TAbs(TSumTerm(4, "EQ", TProd(Term[TLocInt(1), TLocInt(2)]))))])
# infer_type_rec(e) |> pr_ctx
# # K starting to see the problem ...
# e = TProd(Term[TLocStr("a"), TAnno(TProd(Term[TLocStr("a")]), TAbs(TSumTerm(3, "OP", TProd(Term[TLocInt(1)]))))])
# infer_type_rec(e) |> pr_ctx
# # K really broken.. NOTE: before, the last  TLocInt(1) becomes TLocInt(2), in cas it can be helpful to know
# e = TProd(Term[TLocStr("a"), TAnno(TLocStr("a"), TAbs(TGlob("T")))])
# infer_type_rec(e) |> pr_ctx
# # K really broken.. NOTE: before, the last  TLocInt(1) becomes TLocInt(2), in cas it can be helpful to know
# e = TProd(Term[TLocStr("a"), TAnno(TLocStr("a"), TGlob("T"))])
# infer_type_rec(e) |> pr_ctx
# # K really broken.. NOTE: before, the last  TLocInt(1) becomes TLocInt(2), in cas it can be helpful to know
# e = TProd(Term[TLocInt(1), TAnno(TLocInt(1), TGlob("T"))])
# infer_type_rec(e) |> pr_ctx






# How inference handles WRONG THINGS:

e1 = TAnno(TAbs(TGlobAuto("b")), TTermAuto(TGlob("A"), TGlob("B")))
e2 = TGlobAuto("a")
e = TAppAuto(e1, e2)
e |> pr_E
infer_type_rec(e) |> pr

e1 = TAnno(TAbs(TGlobAuto("b")), TTermAuto(TGlob("A"), TGlob("B")))
e2 = TGlobAuto("c")
e = TAppAuto(e1, e2)
e |> pr_E
infer_type_rec(e) |> pr # GREAT
@test has_errors(infer_type_rec(e))


e = TProd([TAnno(TLocInt(1), TGlob("A")), TProd([TLocInt(1), TAnno(TLocInt(1), TGlob("A"))]), TAnno(TLocInt(1), TGlob("B"))])
e |> pr_E
infer_type_rec(e) |> pr # GREAT


end # COMMENT TESTS

include("unification_3.jl")




# e = TApp([TSumTerm(2, "2", TGlobAuto("b")), TBranches([TGlob("f", TLocInt(1)), TAbs()])])



# include("TEST_unification_2.jl")

