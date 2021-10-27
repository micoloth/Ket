

include("unification_3.jl")
# include("unification_2.jl")

# include("TEST_unification_3.jl") # itself

using Test

function test_unify_imply(t1, t2)
    println("Unify ", t1 |> pr, "  and  ", t2 |> pr, ":")
    rr = robinsonUnify(TForall(t1), TForall(t2); mode=imply_)
    if rr isa ItsLiterallyAlreadyOk
        println("apparently they are the same")
        return true
    end
    (s1, s2, _) = rr
    red1 = reduc(TApp([s1, TForall(t1)]))
    println("reduced term: ", red1 |> pr)
    res = (red1 == reduc(TApp([s2, TForall(t2)])))
    println(res)
    return res
end
function test_unify_join(t1, t2)
    println("Unify ", t1 |> pr, "  and  ", t2 |> pr, ":")
    rr = robinsonUnify(TForall(t1), TForall(t2); mode=join_)
    if rr isa ItsLiterallyAlreadyOk
        println("apparently they are the same")
        return true
    end
    (s1, s2, red) = rr
    println("reduced term: ", red |> pr)
    res1 = (red == reduc(TApp([s1, TForall(t1)])))
    res2 = (red == reduc(TApp([s2, TForall(t2)])))
    println("res1: $(res1), res2: $(res2)")
    return res1 && res2
end
function test_unify_meet(t1, t2)
    # The idea being that this works for DIFFERENT PROD LEMGTHS, too !!!
    println("Unify ", t1 |> pr, "  and  ", t2 |> pr, ":")
    rr = robinsonUnify(TForall(t1), TForall(t2); mode=meet_)
    if rr isa ItsLiterallyAlreadyOk
        println("apparently they are the same")
        return true
    end
    (s1, s2, red) = rr
    println("reduced term: ", red |> pr)
    t1 = reduc(TApp([s1, TForall(t1)]))
    t2 = reduc(TApp([s2, TForall(t2)]))
    res1 = robinsonUnify(TForall(red), TForall(t1); mode=imply_)
    res1 = !(res1 isa Error)
    res2 = robinsonUnify(TForall(red), TForall(t2); mode=imply_)
    res2 = !(res2 isa Error)
    println("res1: $(res1), res2: $(res2)")
    return res1 && res2
end


eq_constraints(cs1, cs2) = (Set{Constraint}(cs1) .== Set{Constraint}(cs2)) |> all


# s1, s2 =  robinsonUnify(t1, t2)
# ass_reduc(t1, s1)
# ass_reduc(t2, s2)

@testset "unification_2" begin  # COMMENT TESTS

t1 = TAppAuto(TGlob("G0"), TLoc(1))
t2 = TAppAuto(TGlob("G0"), TLoc(2))
# @test simplify(t1, t2) == [DirectConstraint(TLoc(1), TLoc(2))]
robinsonUnify(TForall(t1), TForall(t2))
@test test_unify_imply(t1, t2)
@test test_unify_join(t1, t2)

t1 = TAppAuto(TGlob("G0"), TLoc(1))
t2 = TAppAuto(TGlob("G0"), TGlob("G99"))
# @test simplify(t1, t2) == [DirectConstraint(TLoc(1), TGlob("G99"))]
robinsonUnify(TForall(t1), TForall(t2))
@test test_unify_imply(t1, t2)
@test test_unify_join(t1, t2)

t1 = TAppAuto(TForall(TLoc(1)), TLoc(1))
t2 = TLoc(2)
# @test simplify(t1, t2) == [DirectConstraint(TLoc(1), TLoc(2))]
robinsonUnify(TForall(t1), TForall(t2))
@test test_unify_imply(t1, t2)
@test test_unify_join(t1, t2)

t1 = TForall(TLoc(1))
t2 = TForall(TLoc(1))
# @test simplify(t1, t2) == []
robinsonUnify(TForall(t1), TForall(t2))
@test test_unify_imply(t1, t2)
@test test_unify_join(t1, t2)

t1 = TForall(TLoc(1))
t2 = TForall(TLoc(2))
# simplify(t1, t2) isa Error
robinsonUnify(TForall(t1), TForall(t2))
@test robinsonUnify(TForall(t1), TForall(t2)) isa Error

t1 = TForall(TLoc(1))
t2 = TLoc(3)
# @test simplify(t1, t2) == [DirectConstraint(TForall(TLoc(1)), TLoc(3))]
robinsonUnify(TForall(t1), TForall(t2))
@test test_unify_imply(t1, t2)
@test test_unify_join(t1, t2)

t1 = TForall(TLoc(1))
t2 = TGlob("G")
# @test simplify(t1, t2) == Error("Different: ∀(T1) is really different from G")
robinsonUnify(TForall(t1), TForall(t2))
@test robinsonUnify(TForall(t1), TForall(t2)) isa Error

t1 = TForall(TLoc(1))
t2 = TForall(TLoc(1))
# simplify(t1, t2)
robinsonUnify(TForall(t1), TForall(t2))
@test test_unify_imply(t1, t2)
@test test_unify_join(t1, t2)

t = TAppAuto(TForall(TLoc(1)), TGlob("G1"))
t1 = TAppAuto(TLoc(3), t)
t2 = TAppAuto(TLoc(4), t)
# @test simplify(t1, t2) == [DirectConstraint(TLoc(3), TLoc(4))]
robinsonUnify(TForall(t1), TForall(t2))
@test test_unify_imply(t1, t2)
@test test_unify_join(t1, t2)

t1 = TAppAuto(TGlob("G2"), TLoc(3))
t2 = TAppAuto(TGlob("G2"), TForall(TAppAuto(TLoc(1), TGlob("G3"))))
# eq_constraints(simplify(t1, t2), [DirectConstraint(TLoc(3), TForall(TApp([TProd([TGlob("G3")]), TLoc(1)])))])
# ^ Go fuck yourself, then die
robinsonUnify(TForall(t1), TForall(t2))
@test test_unify_imply(t1, t2)
@test test_unify_join(t1, t2)

t1 = TAppAuto(TGlob("G2"), TGlob("G3"))
t2 = TAppAuto(TGlob("G2"), TForall(TAppAuto(TLoc(1), TGlob("G3"))))
# simplify(t1, t2)  == Error("Different: T3 is really different from ∀([Just (T3).(T1)])")  # Globals cannot be "solved", and that's ok
robinsonUnify(TForall(t1), TForall(t2))
@test robinsonUnify(TForall(t1), TForall(t2)) isa Error

t1 = TForall(TAppAuto(TGlob("F"), TLoc(1)))
t2 = TForall(TAppAuto(TGlob("F"), TLoc(2)))
# simplify(t1, t2) isa Error  # LAMBDAS CANNOT BE UNIFIED (below, they are preapplied, which is a whole different discussion!!!)
robinsonUnify(TForall(t1), TForall(t2))
@test robinsonUnify(TForall(t1), TForall(t2)) isa Error

t1 = TApp([TProd([TGlob("X"), TGlob("Y")]), TForall(TAppAuto(TGlob("F"), TLoc(1)))])
t2 = TApp([TProd([TGlob("Y"), TGlob("X")]), TForall(TAppAuto(TGlob("F"), TLoc(2)))])
# @test simplify(t1, t2) == DirectConstraint[]
robinsonUnify(TForall(t1), TForall(t2))
@test test_unify_imply(t1, t2)
@test test_unify_join(t1, t2)

t1 = TApp([TProd([TGlob("X"), TGlob("Y")]), TForall(TAppAuto(TGlob("F"), TLoc(1)))])
t2 = TApp([TProd([TGlob("X"), TGlob("Y")]), TForall(TAppAuto(TGlob("F"), TLoc(2)))])
# @test simplify(t1, t2) == Error("Different: X is really different from Y")
robinsonUnify(TForall(t1), TForall(t2))
@test robinsonUnify(TForall(t1), TForall(t2)) isa Error

t1 = TApp([TProd([TLoc(3), TLoc(2)]), TForall(TAppAuto(TGlob("F"), TLoc(1)))])
t2 = TApp([TProd([TLoc(1), TLoc(4)]), TForall(TAppAuto(TGlob("F"), TLoc(2)))])
# @test simplify(t1, t2) == [DirectConstraint(TLoc(3), TLoc(4))]
robinsonUnify(TForall(t1), TForall(t2))
@test test_unify_imply(t1, t2)
@test test_unify_join(t1, t2)

t1 = TApp([TProd([TGlob("X"), TLoc(2)]), TForall(TAppAuto(TLoc(2), TLoc(1)))])
t2 = TApp([TProd([TLoc(1), TLoc(4)]), TForall(TAppAuto(TGlob("F"), TLoc(2)))])
# simplify(t1, t2)  == [DirectConstraint(TGlob("X"), TLoc(4)), DirectConstraint(TLoc(2), TGlob("F"))]
s1, s2 = robinsonUnify(TForall(t1), TForall(t2))
@test test_unify_imply(t1, t2)
@test test_unify_join(t1, t2)

t1 = TAppAuto(TLoc(4), TGlob("X"))
t2 = TAppAuto(TTermAuto(TLoc(1), TLoc(2)), TLoc(3))
# eq_constraints(simplify(t1, t2), [DirectConstraint(TLoc(4), TTermAuto(TLoc(1), TLoc(2))), DirectConstraint(TGlob("X"), TLoc(3))])
# ^ Go fuck yourself, then die
robinsonUnify(TForall(t1), TForall(t2))
@test test_unify_imply(t1, t2)
@test test_unify_join(t1, t2)

t1 = TProd([TLoc(1), TLoc(2)])
t2 = TProd([TLoc(3), TLoc(3)])
# simplify(t1, t2)
robinsonUnify(TForall(t1), TForall(t2))
@test test_unify_imply(t1, t2)
@test test_unify_join(t1, t2)

t1 = TProd([TLoc(1), TLoc(1)])
t2 = TProd([TGlob("F"), TGlob("G")]) # OUCHHHH
# eq_constraints(simplify(t1, t2), [DirectConstraint(TLoc(1), TGlob("G")), DirectConstraint(TLoc(1), TGlob("F"))])
robinsonUnify(TForall(t1), TForall(t2)) # Error, nice
@test robinsonUnify(TForall(t1), TForall(t2)) isa Error

t1 = TProd([TLoc(1), TGlob("F")])
t2 = TProd([TGlob("G"), TLoc(1)]) # otoh, this SHOULD keep working..
# eq_constraints(simplify(t1, t2), [DirectConstraint(TLoc(1), TGlob("G")), DirectConstraint(TGlob("F"), TLoc(1))])
robinsonUnify(TForall(t1), TForall(t2))
@test test_unify_imply(t1, t2)
@test test_unify_join(t1, t2)

t1 = TProd([TLoc(1), TLoc(1)])
t2 = TProd([TLoc(1), TTermAuto(TGlob("A"), TLoc(1))])
# eq_constraints(simplify(t1, t2), [DirectConstraint(TLoc(1), TLoc(1)), DirectConstraint(TLoc(1), TTermAuto(TGlob("A"), TLoc(1)))])
robinsonUnify(TForall(t1), TForall(t2)) # Recursive Error, nice!
@test robinsonUnify(TForall(t1), TForall(t2)) isa Error

t1 = TProd([TLoc(1), TLoc(1), TLoc(2), TLoc(2)])
t2 = TProd([TLoc(1), TLoc(2), TLoc(2), TTermAuto(TGlob("A"), TTermAuto(TGlob("B"), TLoc(1)))])
# eq_constraints(simplify(t1, t2), [DirectConstraint(TLoc(2), TTermAuto(TGlob("A"), TTermAuto(TGlob("B"), TLoc(1)))), DirectConstraint(TLoc(1), TLoc(1)), DirectConstraint(TLoc(2), TLoc(2)), DirectConstraint(TLoc(1), TLoc(2))])
@test robinsonUnify(TForall(t1), TForall(t2)) isa Error

t1 = TProd([TLoc(1), TLoc(1), TLoc(2), TLoc(2)])
t2 = TProd([TTermAuto(TGlob("A"), TTermAuto(TGlob("B"), TGlob("C"))), TLoc(2), TLoc(2), TTermAuto(TGlob("A"), TTermAuto(TGlob("B"), TLoc(1)))])
# eq_constraints(simplify(t1, t2), [DirectConstraint(TLoc(2), TLoc(2)), DirectConstraint(TLoc(1), TTermAuto(TGlob("A"), TTermAuto(TGlob("B"), TGlob("C")))), DirectConstraint(TLoc(2), TTermAuto(TGlob("A"), TTermAuto(TGlob("B"), TLoc(1)))), DirectConstraint(TLoc(1), TLoc(2))])
robinsonUnify(TForall(t1), TForall(t2)) .|> pr
@test test_unify_imply(t1, t2)   #####  YESSSSS
@test test_unify_join(t1, t2)   #####  YESSSSS

t1 = TProd([TLoc(1), TLoc(2)])
t2 = TProd([TLoc(2), TTermAuto(TGlob("A"), TLoc(1))])
# repr(simplify(t1, t2)) == "DirectConstraint[DirectConstraint(TLoc(2), TTermAuto(TGlob(\"A\"), TLoc(1))), DirectConstraint(TLoc(1), TLoc(2))]"
robinsonUnify(TForall(t1), TForall(t2))
@test test_unify_imply(t1, t2)
@test test_unify_join(t1, t2)

t1 = TProd([TLoc(1), TLoc(1), TLoc(2), TLoc(2)])
t2 = TProd([TGlob("F"), TLoc(3), TLoc(3), TGlob("G")])
# eq_constraints(simplify(t1, t2), [DirectConstraint(TLoc(2), TGlob("G")), DirectConstraint(TLoc(1), TLoc(3)), DirectConstraint(TLoc(1), TGlob("F")), DirectConstraint(TLoc(2), TLoc(3))])
robinsonUnify(TForall(t1), TForall(t2)) # Error, nice
@test robinsonUnify(TForall(t1), TForall(t2)) isa Error

t1 = TForall(TGlob("A"))
t2 =  TGlob("A")
# simplify(t1, t2) # Nope, and that's fine
robinsonUnify(t1, t2)
@test robinsonUnify(TForall(t1), TForall(t2)) isa Error

t1 = TProd([TLoc(1), TLoc(1), TLoc(2), TLoc(2)])
t2 = TProd([TGlob("F"), TLoc(1), TLoc(1), TGlob("G")])
# eq_constraints(simplify(t1, t2), [DirectConstraint(TLoc(2), TLoc(1)), DirectConstraint(TLoc(1), TLoc(1)), DirectConstraint(TLoc(2), TGlob("G")), DirectConstraint(TLoc(1), TGlob("F")), ])
robinsonUnify(TForall(t1), TForall(t2)) # Error, nice
@test robinsonUnify(TForall(t1), TForall(t2)) isa Error

t1, t2 = TLoc(3), TForall(TTermAuto(TGlob("A"), TLoc(2)))
@test test_unify_imply(t1, t2.body)
@test test_unify_join(t1, t2.body)

t1 = TForall(TTermAuto(TLoc(1), TProd([TGlob("A"), TLoc(2)])))
t2 = TForall(TTermAuto(TLoc(1), TLoc(2)))
s1, s2 = robinsonUnify(t1, t2)
@test test_unify_imply(t1.body, t2.body)
@test test_unify_join(t1.body, t2.body)

t1 = TForall(TLoc(3))
t2 = TForall(TTermAuto(TLoc(1), TLoc(2)))
s1, s2 = robinsonUnify(t1, t2)
@test test_unify_imply(t1.body, t2.body)
@test test_unify_join(t1.body, t2.body)

# function prepTransEx(l, g1, g2)
#     v1=vcat([[TLoc(i), TLoc(i)] for i in 1:l]...)
#     v2=vcat([[TLoc(i), TLoc(i)] for i in 1:l-1]...)
#     TProd(v1), TProd(vcat([TGlob(g1)], v2, [TGlob(g2)]))
# end
# t1, t2 = prepTransEx(55, "F", "F")
# robinsonUnify(TForall(t1), TForall(t2))
# @test test_unify_imply(t1, t2)
# @ test_unify_join(t1, t2)

# t1, t2 = prepTransEx(10, "F", "G")
# robinsonUnify(TForall(t1), TForall(t2))


t1 = TProd([TLoc(1), TSumTerm("EQ", TProd([TGlob("E"), TLoc(2)]))])
t2 = TProd([TGlob("A"), TSumTerm("EQ", TLoc(1))])
t1|>pr
@test test_unify_imply(t1, t2)
@test test_unify_join(t1, t2)

t1 = TProd([TLoc(1), TSumTerm("EQ", TProd([TGlob("E"), TLoc(2)]))])
t2 = TProd([TGlob("A"), TLoc(2)])
@test test_unify_imply(t1, t2)
@test test_unify_join(t1, t2)

t1 = TProd([TLoc(1), TSumTerm("EQ", TProd([TGlob("E"), TLoc(2)]))])
t2 = TProd([TGlob("A"), TSumTerm("GQ", TProd([TGlob("E"), TLoc(2)]))])
@test robinsonUnify(t1, t2) isa Error



# K for TESTS w/ DIFFERENT NUMBER OF ITEMS NOW:
t1 = TProd([TLoc(1), TGlob("B")])
t2 = TProd([TGlob("A"), TLoc(1), TLoc(2)])
@test robinsonUnify(t1, t2; mode=imply_) isa Error
@test test_unify_meet(t1, t2)

t1 = TProd([TLoc(1), TGlob("B"), TLoc(2)])
t2 = TProd([TGlob("A"), TLoc(1)])
@test test_unify_meet(t1, t2)

t1 = TProd([TGlob("A"), TGlob("B")])
t2 = TProd([TGlob("A"), TGlob("B")])
@test robinsonUnify(t1, t2) isa ItsLiterallyAlreadyOk
@test test_unify_meet(t1, t2)

t1 = TProd([TGlob("A"), TGlob("B"), TGlob("C")])
t2 = TProd([TGlob("A"), TGlob("B")])
@test robinsonUnify(t1, t2) isa ItsLiterallyAlreadyOk
@test test_unify_meet(t1, t2)

t1 = TTerm(TProd([TLoc(1), TGlob("B"), TLoc(2)]), TGlob("Z"))
t2 = TTerm(TProd([TGlob("A"), TLoc(1)]), TGlob("Z"))
@test robinsonUnify(t1, t2; mode=imply_) isa Error
@test test_unify_meet(t1, t2)
@test robinsonUnify(t1, t2; mode=join_)[3] == TTerm(TProd(Type_[TGlob("A"), TGlob("B"), TLoc(1)]), TGlob("Z"))

t1 = TTerm(TProd([TLoc(1), TGlob("B")]), TGlob("Z"))
t2 = TTerm(TProd([TGlob("A"), TLoc(1), TLoc(2)]), TGlob("Z"))
s1, s2 = robinsonUnify(t1, t2; mode=imply_)
ass_reduc(t1, s1) |> pr
ass_reduc(t2, s2) |> pr
@test ass_reduc(t2, s2) == TTerm(TProd(Type_[TGlob("A"), TGlob("B"), TLoc(1)]), TGlob("Z"))
@test test_unify_meet(t1, t2)

t1 = TTermAuto(TTerm(TProd([TLoc(1), TLoc(2)]), TGlob("Z")), TGlob("Z"))
t2 = TTermAuto(TTerm(TProd([TGlob("A"), TLoc(2)]), TGlob("Z")), TGlob("Z"))
@test test_unify_imply(t1, t2) # ACTUALLY SECRETLY A PROBLEM !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
@test test_unify_join(t1, t2)
@test test_unify_meet(t1, t2)

t1 = TTermAuto(TTerm(TProd([TLoc(1)]), TGlob("Z")), TGlob("Z"))
t2 = TTermAuto(TTerm(TProd([TGlob("A"), TLoc(2)]), TGlob("Z")), TGlob("Z"))
@test robinsonUnify(t1, t2; mode=imply_) isa Error
@test test_unify_meet(t1, t2)

t1 = TTermAuto(TTerm(TProd([TLoc(1), TLoc(2)]), TGlob("Z")), TGlob("Z"))
t2 = TTermAuto(TTerm(TProd([TGlob("A")]), TGlob("Z")), TGlob("Z"))
t1 |> pr
t2 |> pr
s1, s2 = robinsonUnify(t1, t2; mode=imply_)
ass_reduc(t1, s1) |> pr
ass_reduc(t2, s2) |> pr
@test ass_reduc(t1, s1) == TTerm(TProd(Type_[TTerm(TProd(Type_[TGlob("A"), TLoc(1)]), TGlob("Z"))]), TGlob("Z"))
@test test_unify_meet(t1, t2)



# HARDER TESTS ON REVERSE CONSTRAINTS:
t1 = TProd([TGlob("F"), TLoc(1), TLoc(1)])
t2 = TProd([TLoc(1), TGlob("G")])
# simplify(DirectConstraint(t1, t2))
test_unify_imply(t1, t2) # Yeah it's false, it's fine tho
@test robinsonUnify(t1, t2; mode=meet_)[3] == TProd(Type_[TGlob("F"), TGlob("G"), TGlob("G")])

t1 = TProd([TGlob("F"), TLoc(1), TLoc(1)])
t2 = TProd([TLoc(1), TGlob("G")])
@test robinsonUnify(t1, t2)[3] == TProd(Type_[TGlob("F"), TGlob("G")])
# # ^ SILENT DROPPING

t1 = TProd([TLoc(1), TGlob("G")])
t2 = TProd([TGlob("F"), TLoc(1), TLoc(1)])
# simplify(ReverseConstraint(t2, t1))
s1, s2 = robinsonUnify(t1, t2) # Cannot unify !!!!!!!!!!!!!!!!!!!!!!!!!!!
# ass_reduc(t1, s1) |> pr
# ass_reduc(t2, s2) |> pr


# Tests that are HARD because I DONT REALLY KNOW WHAT I WANT WRT TO TFORALL SCOPING:
# t1 = TProd([TLoc(1), TGlob("F"), TProd([TLoc(2), TLoc(3)]), TProd([TLoc(4), TProd([TGlob("A"), TLoc(5)])])])
# t2 = TProd([TGlob("G"), TLoc(6), TProd([TLoc(7), TLoc(8)]), TProd([TLoc(9), TProd([TGlob("A"), TLoc(10)])])])
# robinsonUnify(TForall(t1), TForall(t2), 10,10; unify_tlocs_ctx=false)


# t1 = TProd([TLoc(1), TGlob("F"), TProd([TLoc(2), TLoc(3)])])
# t2 = TProd([TGlob("G"), TLoc(4), TProd([TLoc(5)])])
# robinsonUnify(TForall(t1), TForall(t2), 5,5; unify_tlocs_ctx=false) # silently dropping


# t1 = TProd([TLoc(1), TGlob("F"), TProd([TLoc(2), TLoc(3)])])
# t2 = TProd([TGlob("G"), TLoc(4), TLoc(5)]) # TLoc becomes a 2-prod
# robinsonUnify(TForall(t1), TForall(t2), 4,4; unify_tlocs_ctx=false)

# t1 = TProd([TLoc(1), TGlob("F"), TProd([TLoc(2), TLoc(3)])])
# t2 = TProd([TGlob("G"), TLoc(4), TProd([TLoc(4), TGlob("B"), TLoc(6)])]) # TLoc CANNOT GROW, now, can it?
# robinsonUnify(TForall(t1), TForall(t2), 6,6; unify_tlocs_ctx=false)

# #  [\"[T1]\", \"T2\"] cannot be unified with ELocs typed [\"[T1 x T2]\", \"T3\"]
# t1 = TProd([TProd([TProd([TGlob("A")]), TLoc(1)])])
# t2 = TProd([TProd([TProd([TGlob("A"), TLoc(2)])])])
# t1 |> pr, t2|>pr
# robinsonUnify(TForall(t1), TForall(t2), 2,2; unify_tlocs_ctx=false)
# robinsonUnify(TForall(t2), TForall(t1), 2,2; unify_tlocs_ctx=false)






sr = ass_reduc

# Each TLoc refers to position in the row BELOW:
t1 = TProd([TTerm(TLoc(1), TLoc(2)), TLoc(3)])
t2 = TProd([TLoc(1), TLoc(2), TLoc(2)])
t3 = TProd([TGlob("G"), TLoc(1)])
t4 = TProd([TTermAuto(TGlob("A"), TGlob("B"))])
get_reduc_subst([t1, t2, t3, t4]) |> reduc |> pr == "[G->A->B x A->B]"

sr(sr(t1, t2), sr(t3, t4)) |> pr
sr(sr(t1, t2, t3), t4) |> pr
sr(t1, sr(t2, t3, t4)) |> pr



# Each TLoc refers to position in the row BELOW:
t1 = TProd([TLoc(1), TLoc(2), TLoc(3), TLoc(4), TLoc(5)])
t2 = TProd([TLoc(1), TLoc(1), TLoc(2), TLoc(3), TLoc(4)])
t3 = TProd([TLoc(1), TLoc(2), TLoc(3), TLoc(3)])
t4 = TProd([TLoc(1), TLoc(2), TLoc(2)])
t5 = TProd([TLoc(4), TGlob("A")])
get_reduc_subst([t1, t2, t3, t4, t5]) |> reduc |> pr == "[T4 x T4 x A x A x A]"

res1 = sr(sr(t1, t2), sr(t3, t4, t5)) |> pr
res2 = sr(sr(t1, t2, t3, t4), t5) |> pr
res3 = sr(t1, sr(t2, t3), sr(t4, t5)) |> pr
@test res1 == res2
@test res1 == res3



# Each TLoc refers to position in the row BELOW:
t1 = TProd([TLoc(1), TGlob("F"), TLoc(3), TTerm(TProd([TLoc(4)]), TLoc(5))])
t2 = TProd([TLoc(1), TGlob("SKIPPED"), TTerm(TLoc(2), TLoc(3)), TLoc(1), TLoc(1)])
t3 = TProd([TLoc(2), TLoc(1), TLoc(2)])
t4 = TProd([TLoc(1), TTerm(TProd([TLoc(2)]), TLoc(3))])
t5 = TProd([TLoc(2), TGlob("Z"), TGlob("Z")])
get_reduc_subst([t1, t2, t3, t4, t5]) |> reduc |> pr == "[Z->Z x F x T2->Z->Z x Z->Z->Z->Z]"

res1 = sr(sr(t1, t2), sr(t3, t4, t5)) |> pr
res2 = sr(sr(t1, t2, t3, t4), t5) |> pr
res3 = sr(t1, sr(t2, t3), sr(t4, t5)) |> pr
@test res1 == res2
@test res1 == res3




# TEST INFERENCE:


include("unification_3.jl")

e = ELoc(2)
@test infer_type_rec(e) == TTerm(TProd([TLoc(1), TLoc(2)]), TLoc(2))

e = EGlob("f", TTermAuto(TGlob("A"), TGlob("B")))
@test infer_type_rec(e) == TTerm(TProd([]), TTermAuto(TGlob("A"), TGlob("B")))

e = EAnno(ELoc(1), TGlob("A"))
@test infer_type_rec(e) == TTerm(TProd([TGlob("A")]), TGlob("A"))

e = EAnno(ELoc(2), TGlob("A"))
@test infer_type_rec(e) == TTerm(TProd([TLoc(1), TGlob("A")]), TGlob("A"))


e = EProd([ELoc(2), ELoc(2)])
@test infer_type_rec(e) == TTerm(TProd([TLoc(1), TLoc(2)]), TProd(Type_[TLoc(2), TLoc(2)]))

e = EProd([ELoc(2), EAnno(ELoc(2), TLoc(1))])
@test infer_type_rec(e) == TTerm(TProd([TLoc(1), TLoc(2)]), TProd(Type_[TLoc(2), TLoc(2)]))

e = EProd([EGlobAuto("t"), EAnno(ELoc(1), TLoc(1))])
infer_type_rec(e)

tglob = TForall(TTermAuto(TGlob("A"), TLoc(2)))
tanno = TForall(TTermAuto(TLoc(1), TGlob("B")))
# tanno = TForall(TTermAuto(TGlob("A"), TGlob("B")))
# tanno = TTermAuto(TGlob("A"), TGlob("B"))
e = EAnno(EGlob("f", tglob), tanno)
@test infer_type_rec(e) == TTerm(TProd([]), TTermAuto(TGlob("A"), TGlob("B")))


tt = TTermAuto(TGlob("A"), TGlob("B"))
e = EProd([EGlob("f", tt), EGlob("g", tt)])
e|>pr
@test infer_type_rec(e) == TTerm(TProd([]), TProd(Type_[TTermAuto(TGlob("A"), TGlob("B")), TTermAuto(TGlob("A"), TGlob("B"))]))

tt = TForall(TTermAuto(TLoc(1), TGlob("B")))
e = EProd([EGlob("f", tt), EGlob("g", tt)])
@test infer_type_rec(e) == TTerm(TProd([]), TProd(Type_[TTerm(TProd(Type_[TLoc(1)]), TGlob("B")), TTerm(TProd(Type_[TLoc(2)]), TGlob("B"))]))
infer_type_rec(e).t_out |> pr # == "[T1->B x T2->B]" # T2, important! GOOD
# TProd(Type_[TTerm(TProd(Type_[TLoc(1)]), TGlob("B")), TTerm(TProd(Type_[TLoc(2)]), TGlob("B"))]) |> pr



# Broken because it's not clear the TForall scope:
# e = EProd([EAnno(ELoc(1), TLoc(3)), EAnno(ELoc(1), TLoc(2)), EGlob("a", TLoc(1))])
# @test infer_type_rec(e) == TTerm(TProd([TLoc(6)]), TProd(Type_[TLoc(6), TLoc(6)]))
# e = EProd([EAnno(ELoc(1), TLoc(1)), EAnno(ELoc(1), TLoc(2)), EAnno(ELoc(2), TLoc(1))])
# @test infer_type_rec(e) == TTerm(TProd([TLoc(6), TLoc(11)]), TProd(Type_[TLoc(6), TLoc(6), TLoc(11)]))
# e = EProd([EAnno(ELoc(1), TLoc(2)), EAnno(ELoc(1), TLoc(3)), EAnno(ELoc(1), TLoc(4))])
# @test infer_type_rec(e) == TTerm(TProd([TLoc(7)]), TProd(Type_[TLoc(7), TLoc(7), TLoc(7)]))




e = EAbs(EProd([ELoc(2), EAnno(ELoc(1), TGlob("T"))]))
@test infer_type_rec(e) == TTerm(TProd([]), TTerm(TProd(Type_[TGlob("T"), TLoc(1)]), TProd(Type_[TLoc(1), TGlob("T")])))

e = EAnno(EAbs(EGlob("b", TGlob("B"))), TTermAuto(TProd([TGlob("A")]),  TGlob("B")))
@test infer_type_rec(e) == TTerm(TProd([]), TTerm(TProd(Type_[TProd(Type_[TGlob("A")])]), TGlob("B")))


tf = EAnno(EAbs(EGlob("b", TGlob("B"))), TTermAuto(TGlob("A"),  TGlob("B")))
targ = EAnno(ELoc(1), TGlob("A"))
e = EAppAuto(tf, targ)
infer_type_rec(tf).t_out |>pr
@test infer_type_rec(e) == TTerm(TProd([TGlob("A")]), TGlob("B"))

e = EAbs(EApp([EProd([ELoc(1), ELoc(1)]), ELoc(2)]))
infer_type_rec(e).t_out |> pr # == "[T1 x [T1 x T1]->T2]->T2"
@test infer_type_rec(e).t_out == TTerm(TProd([TLoc(1), TTerm(TProd([TLoc(1), TLoc(1)]), TLoc(2))]), TLoc(2))


ea = EProd([EAnno(ELoc(1), TGlob("A"))])
ef1 = EGlob("f", TTermAuto(TLoc(1), TGlob("B")))
e = EAbs(EApp([ea, ef1]))
e |> pr
@test infer_type_rec(e) == TTerm(TProd([]), TTerm(TProd(Type_[TGlob("A")]), TGlob("B")))
infer_type_rec(e).t_out |> pr

ea = EAnno(ELoc(1), TGlob("A"))
ef1 = EGlob("f", TTerm(TLoc(1), TGlob("B")))
e = EAbs(EApp([ea, ef1]))
e |> pr
infer_type_rec(e).t_out |> pr
@test infer_type_rec(e) == TTerm(TProd([]), TTerm(TProd(Type_[TGlob("A")]), TGlob("B")))

ea = EProd([EAnno(ELoc(1), TGlob("A"))])
ef1 = EGlob("f", TTermAuto(TLoc(1), TProd([TGlob("B1"), TGlob("B2")])))
ef2 = EGlob("g", TTermAuto(TGlob("B1"), TLoc(1)))
e = EAbs(EApp([ea, ef1, ef2]))
e |> pr
@test infer_type_rec(e) == TTerm(TProd(Type_[]), TTerm(TProd(Type_[TGlob("A")]), TLoc(1)))
# ^ I mean, unfortunately it's Not wrong ... Even if i Really wish the TLoc's wre actually shared sometimes....
infer_type_rec(e).t_out |> pr

ea = EProd([EAnno(ELoc(1), TGlob("A"))])
ef1 = EGlob("f", TTermAuto(TLoc(1), TProd([TGlob("B1"), TGlob("B2")])))
ef2 = EGlob("g", TTerm(TLoc(1), TLoc(1)))
e = EAbs(EApp([ea, ef1, ef2]))
e|>pr
@test infer_type_rec(e) == TTerm(TProd(Type_[]), TTerm(TProd(Type_[TGlob("A")]), TProd(Type_[TGlob("B1"), TGlob("B2")])))
infer_type_rec(e) |> pr_ctx

e = EApp([ELoc(1), EAbs(ELoc(1))])
@test infer_type_rec(e) |> (x->x.t_in) == TProd([TProd([TLoc(1)])]) # And NOTT [TProd([TLoc(1)])], plz ????



proj1_1 = EApp([ELoc(1), EAbs(ELoc(1))])
vec_w_proj2_1 = EProd([EApp([ELoc(1), EAbs(ELoc(2))]), ELoc(2)])
proj1_1 |> pr
vec_w_proj2_1 |> pr
infer_type_rec(proj1_1) |> pr_ctx
infer_type_rec(vec_w_proj2_1) |> pr_ctx
e = EProd([proj1_1, vec_w_proj2_1])
e |> pr
infer_type_rec(e) |> pr_ctx  # YES my boy... YESSSS :)
@test infer_type_rec(e) |> pr_ctx == "Given [[T1 x T2], T3], get [T1 x [T2 x T3]]"


SType |> pr
S |> pr
infer_type_rec(S) |> pr_ctx  # YES my boy... YES :)
@test infer_type_rec(S) == TTerm(TProd(Type_[]), TTerm(TProd(Type_[TTerm(TProd(Type_[TLoc(1)]), TTerm(TProd(Type_[TLoc(2)]), TLoc(3))), TTerm(TProd(Type_[TLoc(1)]), TLoc(2)), TLoc(1)]), TLoc(3)))



end # COMMENT TESTS





# e = EApp([ESumTerm(2, EGlobAuto("b")), EBranches([EGlob("f", TLoc(1)), EAbs()])])



# include("TEST_unification_2.jl")
