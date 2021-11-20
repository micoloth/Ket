

include("unification_3_tag.jl")
# include("unification_2.jl")

# include("TEST_unification_3.jl") # itself


# TGlobTag   TGlobTag
# TLocTag   TLocTag
# TTopTag   TTopTag
# TTermTag   TTermTag
# TAbsTag   TAbsTag
# TProdTag   TProdTag
# TSumTag   TSumTag
# TAppTag   TAppTag
# TSumTermTag   TSumTermTag
# TAnnoTag   TAnnoTag
# TBranchesTag   TBranchesTag
# TFunAutoTag   TFunAutoTag
# TTermAutoTag   TTermAutoTag
# TAppAutoTag   TAppAutoTag
# TAppSwitchTag   TAppSwitchTag
# TGlobAutoTag   TGlobAutoTag

using Test

function test_unify_imply(t1, t2)
    println("Unify ", t1 |> pr, "  and  ", t2 |> pr, ":")
    rr = robinsonUnify(TAbsTag(t1), TAbsTag(t2); mode=imply_)
    if rr isa ItsLiterallyAlreadyOk
        println("apparently they are the same")
        return true
    end
    (s1, s2, _) = rr
    red1 = reduc(TAppTag([s1, TAbsTag(t1)]))
    println("reduced term: ", red1 |> pr)
    res = (red1 == reduc(TAppTag([s2, TAbsTag(t2)])))
    println(res)
    return res
end
function test_unify_join(t1, t2)
    println("Unify ", t1 |> pr, "  and  ", t2 |> pr, ":")
    rr = robinsonUnify(TAbsTag(t1), TAbsTag(t2); mode=join_)
    if rr isa ItsLiterallyAlreadyOk
        println("apparently they are the same")
        return true
    end
    (s1, s2, red) = rr
    println("reduced term: ", red |> pr)
    res1 = (red == reduc(TAppTag([s1, TAbsTag(t1)])))
    res2 = (red == reduc(TAppTag([s2, TAbsTag(t2)])))
    println("res1: $(res1), res2: $(res2)")
    return res1 && res2
end
function test_unify_meet(t1, t2)
    # The idea being that this works for DIFFERENT PROD LEMGTHS, too !!!
    println("Unify ", t1 |> pr, "  and  ", t2 |> pr, ":")
    rr = robinsonUnify(TAbsTag(t1), TAbsTag(t2); mode=meet_)
    if rr isa ItsLiterallyAlreadyOk
        println("apparently they are the same")
        return true
    end
    (s1, s2, red) = rr
    println("reduced term: ", red |> pr)
    t1 = reduc(TAppTag([s1, TAbsTag(t1)]))
    t2 = reduc(TAppTag([s2, TAbsTag(t2)]))
    res1 = robinsonUnify(TAbsTag(red), TAbsTag(t1); mode=imply_)
    res1 = !(res1 isa Failed_unif_res)
    res2 = robinsonUnify(TAbsTag(red), TAbsTag(t2); mode=imply_)
    res2 = !(res2 isa Failed_unif_res)
    println("res1: $(res1), res2: $(res2)")
    return res1 && res2
end


eq_constraints(cs1, cs2) = (Set{Constraint}(cs1) .== Set{Constraint}(cs2)) |> all


# s1, s2 =  robinsonUnify(t1, t2)
# ass_reduc(t1, s1)
# ass_reduc(t2, s2)

# @testset "unification_2" begin  # COMMENT TESTS

include("unification_3_tag.jl")


t1 = TAppAutoTag(TGlobTag("G0"), TLocTag(1))
t2 = TAppAutoTag(TGlobTag("G0"), TLocTag(2))
# @test simplify(t1, t2) == [DirectConstraint(TLocTag(1), TLocTag(2))]
robinsonUnify(TAbsTag(t1), TAbsTag(t2))
@test test_unify_imply(t1, t2)
@test test_unify_join(t1, t2)


# t1 = TProdTag([TLocTag(1), TGlobTag("G")], ["f", "g"])
# t2 = TProdTag([TLocTag(2), TGlobTag("F")], ["g", "f"])
# robinsonUnify(TAbsTag(t1), TAbsTag(t2))[1]|> (x->pr_T(x; is_an_arg=true))
# robinsonUnify(TAbsTag(t1), TAbsTag(t2))[2]|> (x->pr_T(x; is_an_arg=true))
# robinsonUnify(TAbsTag(t1), TAbsTag(t2))[3]|> (x->pr_T(x; is_an_arg=true))

# infer_type_rec(TLocTag("f"))




t1 = TAppAutoTag(TGlobTag("G0"), TLocTag(1))
t2 = TAppAutoTag(TGlobTag("G0"), TGlobTag("G99"))
# @test simplify(t1, t2) == [DirectConstraint(TLocTag(1), TGlobTag("G99"))]
robinsonUnify(TAbsTag(t1), TAbsTag(t2))
@test test_unify_imply(t1, t2)
@test test_unify_join(t1, t2)

t1 = TAppAutoTag(TAbsTag(TLocTag(1)), TLocTag(1))
t2 = TLocTag(2)
# @test simplify(t1, t2) == [DirectConstraint(TLocTag(1), TLocTag(2))]
robinsonUnify(TAbsTag(t1), TAbsTag(t2))
@test test_unify_imply(t1, t2)
@test test_unify_join(t1, t2)

t1 = TAbsTag(TLocTag(1))
t2 = TAbsTag(TLocTag(1))
# @test simplify(t1, t2) == []
robinsonUnify(TAbsTag(t1), TAbsTag(t2))
@test test_unify_imply(t1, t2)
@test test_unify_join(t1, t2)

t1 = TAbsTag(TLocTag(1))
t2 = TAbsTag(TLocTag(2))
# simplify(t1, t2) isa Failed_unif_res
robinsonUnify(TAbsTag(t1), TAbsTag(t2))
@test robinsonUnify(TAbsTag(t1), TAbsTag(t2)) isa Failed_unif_res

t1 = TAbsTag(TLocTag(1))
t2 = TLocTag(3)
# @test simplify(t1, t2) == [DirectConstraint(TAbsTag(TLocTag(1)), TLocTag(3))]
robinsonUnify(TAbsTag(t1), TAbsTag(t2))
@test test_unify_imply(t1, t2)
@test test_unify_join(t1, t2)

t1 = TAbsTag(TLocTag(1))
t2 = TGlobTag("G")
# @test simplify(t1, t2) == Error("Different: ∀(T1) is really different from G")
robinsonUnify(TAbsTag(t1), TAbsTag(t2))
@test robinsonUnify(TAbsTag(t1), TAbsTag(t2)) isa Failed_unif_res

t1 = TAbsTag(TLocTag(1))
t2 = TAbsTag(TLocTag(1))
# simplify(t1, t2)
robinsonUnify(TAbsTag(t1), TAbsTag(t2))
@test test_unify_imply(t1, t2)
@test test_unify_join(t1, t2)

t = TAppAutoTag(TAbsTag(TLocTag(1)), TGlobTag("G1"))
t1 = TAppAutoTag(TLocTag(3), t)
t2 = TAppAutoTag(TLocTag(4), t)
# @test simplify(t1, t2) == [DirectConstraint(TLocTag(3), TLocTag(4))]
robinsonUnify(TAbsTag(t1), TAbsTag(t2))
@test test_unify_imply(t1, t2)
@test test_unify_join(t1, t2)

t1 = TAppAutoTag(TGlobTag("G2"), TLocTag(3))
t2 = TAppAutoTag(TGlobTag("G2"), TAbsTag(TAppAutoTag(TLocTag(1), TGlobTag("G3"))))
# eq_constraints(simplify(t1, t2), [DirectConstraint(TLocTag(3), TAbsTag(TAppTag([TProdTag(Array{TermTag}([TGlobTag("G3")]), TLocTag(1)])))])
# ^ Go fuck yourself, then die
robinsonUnify(TAbsTag(t1), TAbsTag(t2))
@test test_unify_imply(t1, t2)
@test test_unify_join(t1, t2)

t1 = TAppAutoTag(TGlobTag("G2"), TGlobTag("G3"))
t2 = TAppAutoTag(TGlobTag("G2"), TAbsTag(TAppAutoTag(TLocTag(1), TGlobTag("G3"))))
# simplify(t1, t2)  == Error("Different: T3 is really different from ∀([Just (T3).(T1)])")  # Globals cannot be "solved", and that's ok
robinsonUnify(TAbsTag(t1), TAbsTag(t2))
@test robinsonUnify(TAbsTag(t1), TAbsTag(t2)) isa Failed_unif_res

t1 = TAbsTag(TAppAutoTag(TGlobTag("F"), TLocTag(1)))
t2 = TAbsTag(TAppAutoTag(TGlobTag("F"), TLocTag(2)))
# simplify(t1, t2) isa Failed_unif_res  # LAMBDAS CANNOT BE UNIFIED (below, they are preapplied, which is a whole different discussion!!!)
robinsonUnify(TAbsTag(t1), TAbsTag(t2))
@test robinsonUnify(TAbsTag(t1), TAbsTag(t2)) isa Failed_unif_res

t1 = TAppTag([TProdTag(Array{TermTag}([TGlobTag("X"), TGlobTag("Y")])), TAbsTag(TAppAutoTag(TGlobTag("F"), TLocTag(1)))])
t2 = TAppTag([TProdTag(Array{TermTag}([TGlobTag("Y"), TGlobTag("X")])), TAbsTag(TAppAutoTag(TGlobTag("F"), TLocTag(2)))])
# @test simplify(t1, t2) == DirectConstraint[]
robinsonUnify(TAbsTag(t1), TAbsTag(t2))
@test test_unify_imply(t1, t2)
@test test_unify_join(t1, t2)

t1 = TAppTag([TProdTag(Array{TermTag}([TGlobTag("X"), TGlobTag("Y")])), TAbsTag(TAppAutoTag(TGlobTag("F"), TLocTag(1)))])
t2 = TAppTag([TProdTag(Array{TermTag}([TGlobTag("X"), TGlobTag("Y")])), TAbsTag(TAppAutoTag(TGlobTag("F"), TLocTag(2)))])
# @test simplify(t1, t2) == Error("Different: X is really different from Y")
robinsonUnify(TAbsTag(t1), TAbsTag(t2))
@test robinsonUnify(TAbsTag(t1), TAbsTag(t2)) isa Failed_unif_res

t1 = TAppTag([TProdTag(Array{TermTag}([TLocTag(3), TLocTag(2)])), TAbsTag(TAppAutoTag(TGlobTag("F"), TLocTag(1)))])
t2 = TAppTag([TProdTag(Array{TermTag}([TLocTag(1), TLocTag(4)])), TAbsTag(TAppAutoTag(TGlobTag("F"), TLocTag(2)))])
# @test simplify(t1, t2) == [DirectConstraint(TLocTag(3), TLocTag(4))]
robinsonUnify(TAbsTag(t1), TAbsTag(t2))
@test test_unify_imply(t1, t2)
@test test_unify_join(t1, t2)

t1 = TAppTag([TProdTag(Array{TermTag}([TGlobTag("X"), TLocTag(2)])), TAbsTag(TAppAutoTag(TLocTag(2), TLocTag(1)))])
t2 = TAppTag([TProdTag(Array{TermTag}([TLocTag(1), TLocTag(4)])), TAbsTag(TAppAutoTag(TGlobTag("F"), TLocTag(2)))])
# simplify(t1, t2)  == [DirectConstraint(TGlobTag("X"), TLocTag(4)), DirectConstraint(TLocTag(2), TGlobTag("F"))]
s1, s2 = robinsonUnify(TAbsTag(t1), TAbsTag(t2))
@test test_unify_imply(t1, t2)
@test test_unify_join(t1, t2)

t1 = TAppAutoTag(TLocTag(4), TGlobTag("X"))
t2 = TAppAutoTag(TTermAutoTag(TLocTag(1), TLocTag(2)), TLocTag(3))
# eq_constraints(simplify(t1, t2), [DirectConstraint(TLocTag(4), TTermAutoTag(TLocTag(1), TLocTag(2))), DirectConstraint(TGlobTag("X"), TLocTag(3))])
# ^ Go fuck yourself, then die
robinsonUnify(TAbsTag(t1), TAbsTag(t2))
@test test_unify_imply(t1, t2)
@test test_unify_join(t1, t2)

t1 = TProdTag(Array{TermTag}([TLocTag(1), TLocTag(2)]))
t2 = TProdTag(Array{TermTag}([TLocTag(3), TLocTag(3)]))
# simplify(t1, t2)
robinsonUnify(TAbsTag(t1), TAbsTag(t2))
@test test_unify_imply(t1, t2)
@test test_unify_join(t1, t2)

t1 = TProdTag(Array{TermTag}([TLocTag(1), TLocTag(1)]))
t2 = TProdTag(Array{TermTag}([TGlobTag("F"), TGlobTag("G")])) # OUCHHHH
# eq_constraints(simplify(t1, t2), [DirectConstraint(TLocTag(1), TGlobTag("G")), DirectConstraint(TLocTag(1), TGlobTag("F"))])
robinsonUnify(TAbsTag(t1), TAbsTag(t2)) # Error, nice
@test robinsonUnify(TAbsTag(t1), TAbsTag(t2)) isa Failed_unif_res

t1 = TProdTag(Array{TermTag}([TLocTag(1), TGlobTag("F")]))
t2 = TProdTag(Array{TermTag}([TGlobTag("G"), TLocTag(1)])) # otoh, this SHOULD keep working..
# eq_constraints(simplify(t1, t2), [DirectConstraint(TLocTag(1), TGlobTag("G")), DirectConstraint(TGlobTag("F"), TLocTag(1))])
robinsonUnify(TAbsTag(t1), TAbsTag(t2))
@test test_unify_imply(t1, t2)
@test test_unify_join(t1, t2)

t1 = TProdTag(Array{TermTag}([TLocTag(1), TLocTag(1)]))
t2 = TProdTag(Array{TermTag}([TLocTag(1), TTermAutoTag(TGlobTag("A"), TLocTag(1))]))
# eq_constraints(simplify(t1, t2), [DirectConstraint(TLocTag(1), TLocTag(1)), DirectConstraint(TLocTag(1), TTermAutoTag(TGlobTag("A"), TLocTag(1)))])
robinsonUnify(TAbsTag(t1), TAbsTag(t2)) # Recursive Error, nice!
@test robinsonUnify(TAbsTag(t1), TAbsTag(t2)) isa Failed_unif_res

t1 = TProdTag(Array{TermTag}([TLocTag(1), TLocTag(1), TLocTag(2), TLocTag(2)]))
t2 = TProdTag(Array{TermTag}([TLocTag(1), TLocTag(2), TLocTag(2), TTermAutoTag(TGlobTag("A"), TTermAutoTag(TGlobTag("B"), TLocTag(1)))]))
# eq_constraints(simplify(t1, t2), [DirectConstraint(TLocTag(2), TTermAutoTag(TGlobTag("A"), TTermAutoTag(TGlobTag("B"), TLocTag(1)))), DirectConstraint(TLocTag(1), TLocTag(1)), DirectConstraint(TLocTag(2), TLocTag(2)), DirectConstraint(TLocTag(1), TLocTag(2))])
@test robinsonUnify(TAbsTag(t1), TAbsTag(t2)) isa Failed_unif_res

t1 = TProdTag(Array{TermTag}([TLocTag(1), TLocTag(1), TLocTag(2), TLocTag(2)]))
t2 = TProdTag(Array{TermTag}([TTermAutoTag(TGlobTag("A"), TTermAutoTag(TGlobTag("B"), TGlobTag("C"))), TLocTag(2), TLocTag(2), TTermAutoTag(TGlobTag("A"), TTermAutoTag(TGlobTag("B"), TLocTag(1)))]))
# eq_constraints(simplify(t1, t2), [DirectConstraint(TLocTag(2), TLocTag(2)), DirectConstraint(TLocTag(1), TTermAutoTag(TGlobTag("A"), TTermAutoTag(TGlobTag("B"), TGlobTag("C")))), DirectConstraint(TLocTag(2), TTermAutoTag(TGlobTag("A"), TTermAutoTag(TGlobTag("B"), TLocTag(1)))), DirectConstraint(TLocTag(1), TLocTag(2))])
robinsonUnify(TAbsTag(t1), TAbsTag(t2)) .|> pr
@test test_unify_imply(t1, t2)   #####  YESSSSS
@test test_unify_join(t1, t2)   #####  YESSSSS

t1 = TProdTag(Array{TermTag}([TLocTag(1), TLocTag(2)]))
t2 = TProdTag(Array{TermTag}([TLocTag(2), TTermAutoTag(TGlobTag("A"), TLocTag(1))]))
# repr(simplify(t1, t2)) == "DirectConstraint[DirectConstraint(TLocTag(2), TTermAutoTag(TGlobTag(\"A\"), TLocTag(1))), DirectConstraint(TLocTag(1), TLocTag(2))]"
robinsonUnify(TAbsTag(t1), TAbsTag(t2))
@test test_unify_imply(t1, t2)
@test test_unify_join(t1, t2)

t1 = TProdTag(Array{TermTag}([TLocTag(1), TLocTag(1), TLocTag(2), TLocTag(2)]))
t2 = TProdTag(Array{TermTag}([TGlobTag("F"), TLocTag(3), TLocTag(3), TGlobTag("G")]))
# eq_constraints(simplify(t1, t2), [DirectConstraint(TLocTag(2), TGlobTag("G")), DirectConstraint(TLocTag(1), TLocTag(3)), DirectConstraint(TLocTag(1), TGlobTag("F")), DirectConstraint(TLocTag(2), TLocTag(3))])
robinsonUnify(TAbsTag(t1), TAbsTag(t2)) # Error, nice
@test robinsonUnify(TAbsTag(t1), TAbsTag(t2)) isa Failed_unif_res

t1 = TAbsTag(TGlobTag("A"))
t2 =  TGlobTag("A")
# simplify(t1, t2) # Nope, and that's fine
robinsonUnify(t1, t2)
@test robinsonUnify(TAbsTag(t1), TAbsTag(t2)) isa Failed_unif_res

t1 = TProdTag(Array{TermTag}([TLocTag(1), TLocTag(1), TLocTag(2), TLocTag(2)]))
t2 = TProdTag(Array{TermTag}([TGlobTag("F"), TLocTag(1), TLocTag(1), TGlobTag("G")]))
# eq_constraints(simplify(t1, t2), [DirectConstraint(TLocTag(2), TLocTag(1)), DirectConstraint(TLocTag(1), TLocTag(1)), DirectConstraint(TLocTag(2), TGlobTag("G")), DirectConstraint(TLocTag(1), TGlobTag("F")), ])
robinsonUnify(TAbsTag(t1), TAbsTag(t2)) # Error, nice
@test robinsonUnify(TAbsTag(t1), TAbsTag(t2)) isa Failed_unif_res

t1, t2 = TLocTag(3), TAbsTag(TTermAutoTag(TGlobTag("A"), TLocTag(2)))
@test test_unify_imply(t1, t2.body)
@test test_unify_join(t1, t2.body)

t1 = TAbsTag(TTermAutoTag(TLocTag(1), TProdTag(Array{TermTag}([TGlobTag("A"), TLocTag(2)]))))
t2 = TAbsTag(TTermAutoTag(TLocTag(1), TLocTag(2)))
s1, s2 = robinsonUnify(t1, t2)
@test test_unify_imply(t1.body, t2.body)
@test test_unify_join(t1.body, t2.body)

t1 = TAbsTag(TLocTag(3))
t2 = TAbsTag(TTermAutoTag(TLocTag(1), TLocTag(2)))
s1, s2 = robinsonUnify(t1, t2)
@test test_unify_imply(t1.body, t2.body)
@test test_unify_join(t1.body, t2.body)

# function prepTransEx(l, g1, g2)
#     v1=vcat([[TLocTag(i), TLocTag(i)] for i in 1:l]...)
#     v2=vcat([[TLocTag(i), TLocTag(i)] for i in 1:l-1]...)
#     TProdTag(v1), TProdTag(vcat([TGlobTag(g1)], v2, [TGlobTag(g2)]))
# end
# t1, t2 = prepTransEx(55, "F", "F")
# robinsonUnify(TAbsTag(t1), TAbsTag(t2))
# @test test_unify_imply(t1, t2)
# @ test_unify_join(t1, t2)

# t1, t2 = prepTransEx(10, "F", "G")
# robinsonUnify(TAbsTag(t1), TAbsTag(t2))


t1 = TProdTag(Array{TermTag}([TLocTag(1), TSumTermTag(1, "EQ", TProdTag(Array{TermTag}([TGlobTag("E"), TLocTag(2)])))]))
t2 = TProdTag(Array{TermTag}([TGlobTag("A"), TSumTermTag(1, "EQ", TLocTag(1))]))
t1|>pr
@test test_unify_imply(t1, t2)
@test test_unify_join(t1, t2)

t1 = TProdTag(Array{TermTag}([TLocTag(1), TSumTermTag(1, "EQ", TProdTag(Array{TermTag}([TGlobTag("E"), TLocTag(2)])))]))
t2 = TProdTag(Array{TermTag}([TGlobTag("A"), TLocTag(2)]))
@test test_unify_imply(t1, t2)
@test test_unify_join(t1, t2)

t1 = TProdTag(Array{TermTag}([TLocTag(1), TSumTermTag(1, "EQ", TProdTag(Array{TermTag}([TGlobTag("E"), TLocTag(2)])))]))
t2 = TProdTag(Array{TermTag}([TGlobTag("A"), TSumTermTag(2, "GQ", TProdTag(Array{TermTag}([TGlobTag("E"), TLocTag(2)])))]))
@test robinsonUnify(t1, t2) isa Failed_unif_res


# K for TESTS w/ DIFFERENT NUMBER OF ITEMS NOW:
t1 = TProdTag(Array{TermTag}([TLocTag(1), TGlobTag("B")]))
t2 = TProdTag(Array{TermTag}([TGlobTag("A"), TLocTag(1), TLocTag(2)]))
@test robinsonUnify(t1, t2; mode=imply_) isa Failed_unif_res
@test test_unify_meet(t1, t2)

t1 = TProdTag(Array{TermTag}([TLocTag(1), TGlobTag("B"), TLocTag(2)]))
t2 = TProdTag(Array{TermTag}([TGlobTag("A"), TLocTag(1)]))
@test test_unify_meet(t1, t2)

t1 = TProdTag(Array{TermTag}([TGlobTag("A"), TGlobTag("B")]))
t2 = TProdTag(Array{TermTag}([TGlobTag("A"), TGlobTag("B")]))
@test robinsonUnify(t1, t2) isa ItsLiterallyAlreadyOk
@test test_unify_meet(t1, t2)

t1 = TProdTag(Array{TermTag}([TGlobTag("A"), TGlobTag("B"), TGlobTag("C")]))
t2 = TProdTag(Array{TermTag}([TGlobTag("A"), TGlobTag("B")]))
@test robinsonUnify(t1, t2) isa ItsLiterallyAlreadyOk
@test test_unify_meet(t1, t2)

t1 = TTermTag(TProdTag(Array{TermTag}([TLocTag(1), TGlobTag("B"), TLocTag(2)])), TGlobTag("Z"))
t2 = TTermTag(TProdTag(Array{TermTag}([TGlobTag("A"), TLocTag(1)])), TGlobTag("Z"))
@test robinsonUnify(t1, t2; mode=imply_) isa Failed_unif_res
@test test_unify_meet(t1, t2)
@test robinsonUnify(t1, t2; mode=join_)[3] == TTermTag(TProdTag(TermTag[TGlobTag("A"), TGlobTag("B"), TLocTag(1)]), TGlobTag("Z"))

t1 = TTermTag(TProdTag(Array{TermTag}([TLocTag(1), TGlobTag("B")])), TGlobTag("Z"))
t2 = TTermTag(TProdTag(Array{TermTag}([TGlobTag("A"), TLocTag(1), TLocTag(2)])), TGlobTag("Z"))
s1, s2 = robinsonUnify(t1, t2; mode=imply_)
ass_reduc(t1, s1) |> pr
ass_reduc(t2, s2) |> pr
@test ass_reduc(t2, s2) == TTermTag(TProdTag(TermTag[TGlobTag("A"), TGlobTag("B"), TLocTag(1)]), TGlobTag("Z"))
@test test_unify_meet(t1, t2)

t1 = TTermAutoTag(TTermTag(TProdTag(Array{TermTag}([TLocTag(1), TLocTag(2)])), TGlobTag("Z")), TGlobTag("Z"))
t2 = TTermAutoTag(TTermTag(TProdTag(Array{TermTag}([TGlobTag("A"), TLocTag(2)])), TGlobTag("Z")), TGlobTag("Z"))
@test test_unify_imply(t1, t2) # ACTUALLY SECRETLY A PROBLEM !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
@test test_unify_join(t1, t2)
@test test_unify_meet(t1, t2)

t1 = TTermAutoTag(TTermTag(TProdTag(Array{TermTag}([TLocTag(1)])), TGlobTag("Z")), TGlobTag("Z"))
t2 = TTermAutoTag(TTermTag(TProdTag(Array{TermTag}([TGlobTag("A"), TLocTag(2)])), TGlobTag("Z")), TGlobTag("Z"))
@test robinsonUnify(t1, t2; mode=imply_) isa Failed_unif_res
@test test_unify_meet(t1, t2)

t1 = TTermAutoTag(TTermTag(TProdTag(Array{TermTag}([TLocTag(1), TLocTag(2)])), TGlobTag("Z")), TGlobTag("Z"))
t2 = TTermAutoTag(TTermTag(TProdTag(Array{TermTag}([TGlobTag("A")])), TGlobTag("Z")), TGlobTag("Z"))
t1 |> pr
t2 |> pr
s1, s2 = robinsonUnify(t1, t2; mode=imply_)
ass_reduc(t1, s1) |> pr
ass_reduc(t2, s2) |> pr
@test ass_reduc(t1, s1) == TTermTag(TProdTag(TermTag[TTermTag(TProdTag(TermTag[TGlobTag("A"), TLocTag(1)]), TGlobTag("Z"))]), TGlobTag("Z"))
@test test_unify_meet(t1, t2)



# HARDER TESTS ON REVERSE CONSTRAINTS:
t1 = TProdTag(Array{TermTag}([TGlobTag("F"), TLocTag(1), TLocTag(1)]))
t2 = TProdTag(Array{TermTag}([TLocTag(1), TGlobTag("G")]))
# simplify(DirectConstraint(t1, t2))
test_unify_imply(t1, t2) # Yeah it's false, it's fine tho
@test robinsonUnify(t1, t2; mode=meet_)[3] == TProdTag(TermTag[TGlobTag("F"), TGlobTag("G"), TGlobTag("G")])

t1 = TProdTag(Array{TermTag}([TGlobTag("F"), TLocTag(1), TLocTag(1)]))
t2 = TProdTag(Array{TermTag}([TLocTag(1), TGlobTag("G")]))
@test robinsonUnify(t1, t2)[3] == TProdTag(TermTag[TGlobTag("F"), TGlobTag("G")])
# # ^ SILENT DROPPING

t1 = TProdTag(Array{TermTag}([TLocTag(1), TGlobTag("G")]))
t2 = TProdTag(Array{TermTag}([TGlobTag("F"), TLocTag(1), TLocTag(1)]))
# simplify(ReverseConstraint(t2, t1))
s1, s2 = robinsonUnify(t1, t2) # Cannot unify !!!!!!!!!!!!!!!!!!!!!!!!!!!
# ass_reduc(t1, s1) |> pr
# ass_reduc(t2, s2) |> pr


# Tests that are HARD because I DONT REALLY KNOW WHAT I WANT WRT TO TAbsTag SCOPING:
# t1 = TProdTag(Array{TermTag}([TLocTag(1), TGlobTag("F"), TProdTag(Array{TermTag}([TLocTag(2), TLocTag(3)]), TProdTag(Array{TermTag}([TLocTag(4), TProdTag(Array{TermTag}([TGlobTag("A"), TLocTag(5)])])])
# t2 = TProdTag(Array{TermTag}([TGlobTag("G"), TLocTag(6), TProdTag(Array{TermTag}([TLocTag(7), TLocTag(8)]), TProdTag(Array{TermTag}([TLocTag(9), TProdTag(Array{TermTag}([TGlobTag("A"), TLocTag(10)])])])
# robinsonUnify(TAbsTag(t1), TAbsTag(t2), 10,10; unify_tlocs_ctx=false)


# t1 = TProdTag(Array{TermTag}([TLocTag(1), TGlobTag("F"), TProdTag(Array{TermTag}([TLocTag(2), TLocTag(3)])])
# t2 = TProdTag(Array{TermTag}([TGlobTag("G"), TLocTag(4), TProdTag(Array{TermTag}([TLocTag(5)])])
# robinsonUnify(TAbsTag(t1), TAbsTag(t2), 5,5; unify_tlocs_ctx=false) # silently dropping


# t1 = TProdTag(Array{TermTag}([TLocTag(1), TGlobTag("F"), TProdTag(Array{TermTag}([TLocTag(2), TLocTag(3)])])
# t2 = TProdTag(Array{TermTag}([TGlobTag("G"), TLocTag(4), TLocTag(5)]) # TLocTag becomes a 2-prod
# robinsonUnify(TAbsTag(t1), TAbsTag(t2), 4,4; unify_tlocs_ctx=false)

# t1 = TProdTag(Array{TermTag}([TLocTag(1), TGlobTag("F"), TProdTag(Array{TermTag}([TLocTag(2), TLocTag(3)])])
# t2 = TProdTag(Array{TermTag}([TGlobTag("G"), TLocTag(4), TProdTag(Array{TermTag}([TLocTag(4), TGlobTag("B"), TLocTag(6)])]) # TLocTag CANNOT GROW, now, can it?
# robinsonUnify(TAbsTag(t1), TAbsTag(t2), 6,6; unify_tlocs_ctx=false)

# #  [\"[T1]\", \"T2\"] cannot be unified with ELocs typed [\"[T1 x T2]\", \"T3\"]
# t1 = TProdTag(Array{TermTag}([TProdTag(Array{TermTag}([TProdTag(Array{TermTag}([TGlobTag("A")]), TLocTag(1)])])
# t2 = TProdTag(Array{TermTag}([TProdTag(Array{TermTag}([TProdTag(Array{TermTag}([TGlobTag("A"), TLocTag(2)])])])
# t1 |> pr, t2|>pr
# robinsonUnify(TAbsTag(t1), TAbsTag(t2), 2,2; unify_tlocs_ctx=false)
# robinsonUnify(TAbsTag(t2), TAbsTag(t1), 2,2; unify_tlocs_ctx=false)






sr = ass_reduc

# Each TLocTag refers to position in the row BELOW:
t1 = TProdTag(Array{TermTag}([TTermTag(TLocTag(1), TLocTag(2)), TLocTag(3)]))
t2 = TProdTag(Array{TermTag}([TLocTag(1), TLocTag(2), TLocTag(2)]))
t3 = TProdTag(Array{TermTag}([TGlobTag("G"), TLocTag(1)]))
t4 = TProdTag(Array{TermTag}([TTermAutoTag(TGlobTag("A"), TGlobTag("B"))]))
get_reduc_subst([t1, t2, t3, t4]) |> reduc |> pr == "[G->A->B x A->B]"

sr(sr(t1, t2), sr(t3, t4)) |> pr
sr(sr(t1, t2, t3), t4) |> pr
sr(t1, sr(t2, t3, t4)) |> pr



# Each TLocTag refers to position in the row BELOW:
t1 = TProdTag(Array{TermTag}([TLocTag(1), TLocTag(2), TLocTag(3), TLocTag(4), TLocTag(5)]))
t2 = TProdTag(Array{TermTag}([TLocTag(1), TLocTag(1), TLocTag(2), TLocTag(3), TLocTag(4)]))
t3 = TProdTag(Array{TermTag}([TLocTag(1), TLocTag(2), TLocTag(3), TLocTag(3)]))
t4 = TProdTag(Array{TermTag}([TLocTag(1), TLocTag(2), TLocTag(2)]))
t5 = TProdTag(Array{TermTag}([TLocTag(4), TGlobTag("A")]))
get_reduc_subst([t1, t2, t3, t4, t5]) |> reduc |> pr == "[T4 x T4 x A x A x A]"

res1 = sr(sr(t1, t2), sr(t3, t4, t5)) |> pr
res2 = sr(sr(t1, t2, t3, t4), t5) |> pr
res3 = sr(t1, sr(t2, t3), sr(t4, t5)) |> pr
@test res1 == res2
@test res1 == res3



# Each TLocTag refers to position in the row BELOW:
t1 = TProdTag(Array{TermTag}([TLocTag(1), TGlobTag("F"), TLocTag(3), TTermTag(TProdTag(Array{TermTag}([TLocTag(4)])), TLocTag(5))]))
t2 = TProdTag(Array{TermTag}([TLocTag(1), TGlobTag("SKIPPED"), TTermTag(TLocTag(2), TLocTag(3)), TLocTag(1), TLocTag(1)]))
t3 = TProdTag(Array{TermTag}([TLocTag(2), TLocTag(1), TLocTag(2)]))
t4 = TProdTag(Array{TermTag}([TLocTag(1), TTermTag(TProdTag(Array{TermTag}([TLocTag(2)])), TLocTag(3))]))
t5 = TProdTag(Array{TermTag}([TLocTag(2), TGlobTag("Z"), TGlobTag("Z")]))
get_reduc_subst([t1, t2, t3, t4, t5]) |> reduc |> pr == "[Z->Z x F x T2->Z->Z x Z->Z->Z->Z]"

res1 = sr(sr(t1, t2), sr(t3, t4, t5)) |> pr
res2 = sr(sr(t1, t2, t3, t4), t5) |> pr
res3 = sr(t1, sr(t2, t3), sr(t4, t5)) |> pr
@test res1 == res2
@test res1 == res3




# TEST INFERENCE:


e = TLocTag(2)
@test infer_type_rec(e) == TTermTag(TProdTag(Array{TermTag}([TLocTag(1), TLocTag(2)])), TLocTag(2))

e = TGlobTag("f", TTermAutoTag(TGlobTag("A"), TGlobTag("B")))
@test infer_type_rec(e) == TTermTag(TProdTag(Array{TermTag}([])), TTermAutoTag(TGlobTag("A"), TGlobTag("B")))

e = TAnnoTag(TLocTag(1), TGlobTag("A"))
@test infer_type_rec(e) == TTermTag(TProdTag(Array{TermTag}([TGlobTag("A")])), TGlobTag("A"))

e = TAnnoTag(TLocTag(2), TGlobTag("A"))
@test infer_type_rec(e) == TTermTag(TProdTag(Array{TermTag}([TLocTag(1), TGlobTag("A")])), TGlobTag("A"))


e = TProdTag(Array{TermTag}([TLocTag(2), TLocTag(2)]))
@test infer_type_rec(e) == TTermTag(TProdTag(Array{TermTag}([TLocTag(1), TLocTag(2)])), TProdTag(TermTag[TLocTag(2), TLocTag(2)]))

e = TProdTag(Array{TermTag}([TLocTag(2), TAnnoTag(TLocTag(2), TLocTag(1))]))
@test infer_type_rec(e) == TTermTag(TProdTag(Array{TermTag}([TLocTag(1), TLocTag(2)])), TProdTag(TermTag[TLocTag(2), TLocTag(2)]))

e = TProdTag(Array{TermTag}([TGlobAutoTag("t"), TAnnoTag(TLocTag(1), TLocTag(1))]))
infer_type_rec(e)

tglob = TAbsTag(TTermAutoTag(TGlobTag("A"), TLocTag(2)))
tanno = TAbsTag(TTermAutoTag(TLocTag(1), TGlobTag("B")))
# tanno = TAbsTag(TTermAutoTag(TGlobTag("A"), TGlobTag("B")))
# tanno = TTermAutoTag(TGlobTag("A"), TGlobTag("B"))
e = TAnnoTag(TGlobTag("f", tglob), tanno)
@test infer_type_rec(e) == TTermTag(TProdTag(Array{TermTag}([])), TTermAutoTag(TGlobTag("A"), TGlobTag("B")))


tt = TTermAutoTag(TGlobTag("A"), TGlobTag("B"))
e = TProdTag(Array{TermTag}([TGlobTag("f", tt), TGlobTag("g", tt)]))
e|>pr
@test infer_type_rec(e) == TTermTag(TProdTag(Array{TermTag}([])), TProdTag(TermTag[TTermAutoTag(TGlobTag("A"), TGlobTag("B")), TTermAutoTag(TGlobTag("A"), TGlobTag("B"))]))

tt = TAbsTag(TTermAutoTag(TLocTag(1), TGlobTag("B")))
e = TProdTag(Array{TermTag}([TGlobTag("f", tt), TGlobTag("g", tt)]))
@test infer_type_rec(e) == TTermTag(TProdTag(Array{TermTag}([])), TProdTag(TermTag[TTermTag(TProdTag(TermTag[TLocTag(1)]), TGlobTag("B")), TTermTag(TProdTag(TermTag[TLocTag(2)]), TGlobTag("B"))]))
infer_type_rec(e).t_out |> pr # == "[T1->B x T2->B]" # T2, important! GOOD
# TProdTag(TermTag[TTermTag(TProdTag(TermTag[TLocTag(1)]), TGlobTag("B")), TTermTag(TProdTag(TermTag[TLocTag(2)]), TGlobTag("B"))]) |> pr



# Broken because it's not clear the TAbsTag scope:
# e = TProdTag(Array{TermTag}([TAnnoTag(TLocTag(1), TLocTag(3)), TAnnoTag(TLocTag(1), TLocTag(2)), TGlobTag("a", TLocTag(1))]))
# @test infer_type_rec(e) == TTermTag(TProdTag(Array{TermTag}([TLocTag(6)])), TProdTag(TermTag[TLocTag(6), TLocTag(6)])))
# e = TProdTag(Array{TermTag}([TAnnoTag(TLocTag(1), TLocTag(1)), TAnnoTag(TLocTag(1), TLocTag(2)), TAnnoTag(TLocTag(2), TLocTag(1))]))
# @test infer_type_rec(e) == TTermTag(TProdTag(Array{TermTag}([TLocTag(6), TLocTag(11)])), TProdTag(TermTag[TLocTag(6), TLocTag(6), TLocTag(11)])))
# e = TProdTag(Array{TermTag}([TAnnoTag(TLocTag(1), TLocTag(2)), TAnnoTag(TLocTag(1), TLocTag(3)), TAnnoTag(TLocTag(1), TLocTag(4))]))
# @test infer_type_rec(e) == TTermTag(TProdTag(Array{TermTag}([TLocTag(7)])), TProdTag(TermTag[TLocTag(7), TLocTag(7), TLocTag(7)])))




e = TAbsTag(TProdTag(Array{TermTag}([TLocTag(2), TAnnoTag(TLocTag(1), TGlobTag("T"))])))
@test infer_type_rec(e) == TTermTag(TProdTag(Array{TermTag}([])), TTermTag(TProdTag(TermTag[TGlobTag("T"), TLocTag(1)]), TProdTag(TermTag[TLocTag(1), TGlobTag("T")])))

e = TAnnoTag(TAbsTag(TGlobTag("b", TGlobTag("B"))), TTermAutoTag(TProdTag(Array{TermTag}([TGlobTag("A")])),  TGlobTag("B")))
@test infer_type_rec(e) == TTermTag(TProdTag(Array{TermTag}([])), TTermTag(TProdTag(TermTag[TProdTag(TermTag[TGlobTag("A")])]), TGlobTag("B")))


tf = TAnnoTag(TAbsTag(TGlobTag("b", TGlobTag("B"))), TTermAutoTag(TGlobTag("A"),  TGlobTag("B")))
targ = TAnnoTag(TLocTag(1), TGlobTag("A"))
e = TAppAutoTag(tf, targ)
infer_type_rec(tf).t_out |>pr
@test infer_type_rec(e) == TTermTag(TProdTag(Array{TermTag}([TGlobTag("A")])), TGlobTag("B"))

e = TAbsTag(TAppTag([TProdTag(Array{TermTag}([TLocTag(1), TLocTag(1)])), TLocTag(2)]))
infer_type_rec(e).t_out |> pr # == "[T1 x [T1 x T1]->T2]->T2"
@test infer_type_rec(e).t_out == TTermTag(TProdTag(Array{TermTag}([TLocTag(1), TTermTag(TProdTag(Array{TermTag}([TLocTag(1), TLocTag(1)])), TLocTag(2))])), TLocTag(2))


ea = TProdTag(Array{TermTag}([TAnnoTag(TLocTag(1), TGlobTag("A"))]))
ef1 = TGlobTag("f", TTermAutoTag(TLocTag(1), TGlobTag("B")))
e = TAbsTag(TAppTag([ea, ef1]))
e |> pr
@test infer_type_rec(e) == TTermTag(TProdTag(Array{TermTag}([])), TTermTag(TProdTag(TermTag[TGlobTag("A")]), TGlobTag("B")))
infer_type_rec(e).t_out |> pr

ea = TAnnoTag(TLocTag(1), TGlobTag("A"))
ef1 = TGlobTag("f", TTermTag(TLocTag(1), TGlobTag("B")))
e = TAbsTag(TAppTag([ea, ef1]))
e |> pr
infer_type_rec(e).t_out |> pr
@test infer_type_rec(e) == TTermTag(TProdTag(Array{TermTag}([])), TTermTag(TProdTag(TermTag[TGlobTag("A")]), TGlobTag("B")))

ea = TProdTag(Array{TermTag}([TAnnoTag(TLocTag(1), TGlobTag("A"))]))
ef1 = TGlobTag("f", TTermAutoTag(TLocTag(1), TProdTag(Array{TermTag}([TGlobTag("B1"), TGlobTag("B2")]))))
ef2 = TGlobTag("g", TTermAutoTag(TGlobTag("B1"), TLocTag(1)))
e = TAbsTag(TAppTag([ea, ef1, ef2]))
e |> pr
@test infer_type_rec(e) == TTermTag(TProdTag(TermTag[]), TTermTag(TProdTag(TermTag[TGlobTag("A")]), TLocTag(1)))
# ^ I mean, unfortunately it's Not wrong ... Even if i Really wish the TLocTag's wre actually shared sometimes....
infer_type_rec(e).t_out |> pr

ea = TProdTag(Array{TermTag}([TAnnoTag(TLocTag(1), TGlobTag("A"))]))
ef1 = TGlobTag("f", TTermAutoTag(TLocTag(1), TProdTag(Array{TermTag}([TGlobTag("B1"), TGlobTag("B2")]))))
ef2 = TGlobTag("g", TTermTag(TLocTag(1), TLocTag(1)))
e = TAbsTag(TAppTag([ea, ef1, ef2]))
e|>pr
@test infer_type_rec(e) == TTermTag(TProdTag(TermTag[]), TTermTag(TProdTag(TermTag[TGlobTag("A")]), TProdTag(TermTag[TGlobTag("B1"), TGlobTag("B2")])))
infer_type_rec(e) |> pr_ctx

e = TAppTag([TLocTag(1), TAbsTag(TLocTag(1))])
@test infer_type_rec(e) |> (x->x.t_in) == TProdTag(Array{TermTag}([TProdTag(Array{TermTag}([TLocTag(1)]))])) # And NOTT [TProdTag(Array{TermTag}([TLocTag(1)])], plz ????



proj1_1 = TAppTag([TLocTag(1), TAbsTag(TLocTag(1))])
vec_w_proj2_1 = TProdTag(Array{TermTag}([TAppTag([TLocTag(1), TAbsTag(TLocTag(2))]), TLocTag(2)]))
proj1_1 |> pr
vec_w_proj2_1 |> pr
infer_type_rec(proj1_1) |> pr_ctx
infer_type_rec(vec_w_proj2_1) |> pr_ctx
e = TProdTag(Array{TermTag}([proj1_1, vec_w_proj2_1]))
e |> pr
infer_type_rec(e) |> pr_ctx  # YES my boy... YESSSS :)
@test infer_type_rec(e) |> pr_ctx == "Given [[T1 x T2], T3], get [T1 x [T2 x T3]]"


SType |> pr
S |> pr
infer_type_rec(S) |> pr_ctx  # YES my boy... YES :)
@test infer_type_rec(S) == TTermTag(TProdTag(TermTag[]), TTermTag(TProdTag(TermTag[TTermTag(TProdTag(TermTag[TLocTag(1)]), TTermTag(TProdTag(TermTag[TLocTag(2)]), TLocTag(3))), TTermTag(TProdTag(TermTag[TLocTag(1)]), TLocTag(2)), TLocTag(1)]), TLocTag(3)))


# How inference handles WRONG THINGS:

e1 = TAnnoTag(TAbsTag(TGlobAutoTag("b")), TTermAutoTag(TGlobTag("A"), TGlobTag("B")))
e2 = TGlobAutoTag("a")
e = TAppAutoTag(e1, e2)
infer_type_rec(e)|>pr

e1 = TAnnoTag(TAbsTag(TGlobAutoTag("b")), TTermAutoTag(TGlobTag("A"), TGlobTag("B")))
e2 = TGlobAutoTag("c")
e = TAppAutoTag(e1, e2)
infer_type_rec(e)|>pr # GREAT


e = TProdTag([TAnnoTag(TLocTag(1), TGlobTag("A")), TProdTag([TLocTag(1), TAnnoTag(TLocTag(1), TGlobTag("A"))]), TAnnoTag(TLocTag(1), TGlobTag("B"))])
e|> pr_E
infer_type_rec(e)|>pr # GREAT


# end # COMMENT TESTS





# e = TAppTag([TSumTermTag(2, "2", TGlobAutoTag("b")), TBranchesTag([TGlobTag("f", TLocTag(1)), TAbsTag()])])



# include("TEST_unification_2.jl")
