

include("unification_3.jl")
pr_redall(x::TAnno) = reduc(x; reduc_type=true) |> (x->pr_E(x; topLevel=true))

E1T = TGlob("T1")
E1() = E1T
IVT = TProd(Array{Term}([TLocInt(1)]))
IV(t::Term) = TApp([TProd(Array{Term}([t])), TAbs(IVT)]) |> reduc
OPT = TProd(Array{Term}([TLocInt(1), TLocInt(2)]))
OP(t1::Term, t2::Term) = TApp([TProd(Array{Term}([t1, t2])), TAbs(OPT)]) |> reduc

TT = TSum(Vector{Pair{String, Term}}(["e1"=>E1(), "b"=>TGlob("B")]))





# These were always on the Type level:
E1T = TSumTerm(1, "E1", TProd(Array{Term}([])))
IVT = TSumTerm(2, "IV", TProd(Array{Term}([TLocInt(1)])))
OPT = TSumTerm(3, "OP", TProd(Array{Term}([TLocInt(1), TLocInt(2)])))
# ^ Important note: What i'm doing here, is SHAMELESSLY EXPLOITING the fact that Term is ALREADY recursive (So very much not consistent, im sure?)
EQT = TSumTerm(4, "EQ", TProd(Array{Term}([TLocInt(1), TLocInt(2)]))) # This is WRONG, cuz you can say e.g. EQ(EQ(_,_), EQ(_,_)), but this can WAIT
E1() = E1T
IV(t::Term) = TApp([TProd(Array{Term}([t])), TAbs(IVT)]) |> reduc
OP(t1::Term, t2::Term) = TApp([TProd(Array{Term}([t1, t2])), TAbs(OPT)]) |> reduc
EQ(t1::Term, t2::Term) = TApp([TProd(Array{Term}([t1, t2])), TAbs(EQT)]) |> reduc
E1T |> pr_T, IVT |> pr_T, OPT |> pr_T, EQT |> pr_T

# You want these  FUNCTIONS:
twoargs = TProd(Array{Term}([TLocInt(1), TLocInt(2)]))
e1F = TAnno(TAbs(TGlob("e", E1())), TTermEmpty(E1()))
ivF = TAnno(TAbs(TProd(Array{Term}([TLocInt(1)]))), TTermEmpty(TTermAuto(TLocInt(1), IV(TLocInt(1)))))
opF = TAnno(TAbs(TProd(Array{Term}([TLocInt(1), TLocInt(2)]))), TTermEmpty(TTerm(TProd(Array{Term}([TLocInt(1), TLocInt(2)])), OP(TLocInt(1), TLocInt(2)))))
eqF = TAnno(TAbs(TProd(Array{Term}([TLocInt(1), TLocInt(2)]))), TTermEmpty(TTerm(TProd(Array{Term}([TLocInt(1), TLocInt(2)])), EQ(TLocInt(1), TLocInt(2)))))
e1F |> infer_type_rec |> reduc |> pr_ctx
ivF |> infer_type_rec |> reduc |> pr_ctx
opF |> infer_type_rec |> reduc |> pr_ctx
eqF |> infer_type_rec |> reduc |> pr_ctx

# And this UTILITIES, done in the RIGTH WAY of doing it:
e1() = TAnnoAuto(TGlob("e", E1()))
iv(e::TAnno) = build_anno_term_TApp([build_anno_term_TProd([e]), ivF]) |> (x->reduc(x; reduc_type=true))
op(e1::TAnno, e2::TAnno) = build_anno_term_TApp([build_anno_term_TProd([e1, e2]), opF]) |> (x->reduc(x; reduc_type=true))
eq(e1::TAnno, e2::TAnno) = build_anno_term_TApp([build_anno_term_TProd([e1, e2]), eqF]) |> (x->reduc(x; reduc_type=true))


# # TESTS/ examples:
OP(IV(E1()), E1()) |> reduc |> pr
TAbs(OP(TLocInt(2), TLocInt(3))) |> reduc |> pr
TAnno(TProd(Array{Term}([e1()])), IV(E1())) |> pr_redall
iv(e1()) |> pr_redall
iv(e1()) |> infer_type_rec |> pr_ctx
op(iv(e1()), e1()) |> pr # I mean, it sucks but it's Not wrong...
TAnno(op(iv(e1()), e1()),  OP(IV(E1()), E1())) |> pr
fp = TAbs(TLocInt(2)) # This is supposed to be SECOND PROJECTION
TApp([op(TAnnoAuto(TGlobAuto("a")), TAnnoAuto(TGlobAuto("b"))), fp]) |> reduc |> pr
TApp([op(TAnnoAuto(TGlobAuto("a")), TAnnoAuto(TGlobAuto("b"))), fp]) |> pr


# First possibility (easy): with EQUALITY PRESERVING FUNCTIONS.

# LEFT INVERIBILITY: OP(inv(a), a) == e()
invsx_fw = TAnno(build_anno_term_TAbs(e1()), TTermEmpty(TTermAuto(OP(IV(TLocInt(1)), TLocInt(1)), E1())))
invsx_fw |> infer_type_rec |> reduc |> pr_ctx
invsx_fw |> pr_redall

# THE FOLLOWING IS NOT ACTUALLY A FUNCTION THAT EXISTS , so it's VERY RIGTH THAT DOESNT TYPECHECK.
# You can ofc make a function that RETURNA AN EQUALITY!!
# invsx_bw = TAnno(build_anno_term_TAbs(op(iv(TLocInt(1)), TLocInt(1))), TTermEmpty(TTermAuto(E1(), OP(IV(TLocInt(1)), TLocInt(1)))))
# invsx_bw |> infer_type_rec |> reduc |> pr_ctx
# invsx_bw |> pr_redall

# RIGHT INVERIBILITY: OP(a, inv(a)) == a
invdx_fw = TAnno(build_anno_term_TAbs(e1()), TTermEmpty(TTermAuto(OP(TLocInt(1), IV(TLocInt(1))), E1())))
invdx_fw |> infer_type_rec |> reduc |> pr_ctx
invdx_fw |> pr_redall

# THE FOLLOWING IS NOT ACTUALLY A FUNCTION THAT EXISTS , so it's VERY RIGTH THAT DOESNT TYPECHECK.
# You can ofc make a function that RETURNA AN EQUALITY!!
# invdx_bw = TAnno(build_anno_term_TAbs(op(TLocInt(1), iv(TLocInt(1)))), TTermEmpty(TTermAuto(E1(), OP(TLocInt(1), IV(TLocInt(1))))))
# invdx_bw |> infer_type_rec |> reduc |> pr_ctx
# invdx_bw |> pr_redall

# RIGHT NULLITY: OP(a, e()) == a
nuldx_fw = TAnno(TAbs(TApp([TLocInt(1), TAbs(TLocInt(1))])), TTermEmpty(TTermAuto(OP(TLocInt(1), E1()), TLocInt(1))))
nuldx_fw |> infer_type_rec |> reduc |> pr_ctx
nuldx_fw |> pr_redall

nuldx_bw = TAnno(TAbs(op(TAnnoAuto(TLocInt(1)), e1())), TTermEmpty(TTermAuto(TLocInt(1), OP(TLocInt(1), E1()))))
nuldx_bw |> infer_type_rec |> reduc |> pr_ctx
nuldx_bw |> pr_redall

# LEFT NULLITY: OP(e(), a) == a
nulsx_fw = TAnno(TAbs(TAnnoAuto(TLocInt(2))), TTermEmpty(TTerm(OP(E1(), TLocInt(1)), TLocInt(1))))
nulsx_fw |> infer_type_rec |> reduc |> pr_ctx
nulsx_fw |> pr_redall

nulsx_bw = TAnno(TAbs(op(e1(), TAnnoAuto(TLocInt(1)))), TTermEmpty(TTermAuto(TLocInt(1), OP(E1(), TLocInt(1)))))
nulsx_bw |> infer_type_rec |> reduc |> pr_ctx
nulsx_bw |> pr_redall


# TRANSITIVITY: OP(OP(a,b),c) == OP(a,OP(b,c))
proj1_1, proj2_1 = TAnnoAuto(TApp([TLocInt(1), TAbs(TLocInt(1))])), TAnnoAuto(TApp([TLocInt(1), TAbs(TLocInt(2))]))
assdx = TAnno(
    TAbs(op(proj1_1, op(proj2_1, TAnnoAuto(TLocInt(2))))),
    TTermEmpty(TTerm(OP(OP(TLocInt(1), TLocInt(2)), TLocInt(3)), OP(TLocInt(1), OP(TLocInt(2), TLocInt(3))))))
proj1_1 |> pr_redall
proj2_1 |> pr_redall
assdx |> reduc |> pr_E
assdx |> infer_type_rec |> reduc |> pr_ctx
assdx |> pr_redall

# ... The other TRANSITIVITY ...


# APPLICATION TO BOTH SIDES OF EQUALITY
p1(term) = TApp([term, TAbs(TLocInt(1))])
p2(term) = TApp([term, TAbs(TLocInt(2))])
appleq = TAnno(
    TAbs(eq(TAnnoAuto(TAppAuto(TLocInt(2), p1(TLocInt(1)))), TAnnoAuto(TAppAuto(TLocInt(2), p2(TLocInt(1)))))),
    TTermEmpty(TTerm(TProd([EQ(TLocInt(1), TLocInt(1)), TTermAuto(TLocInt(1), TLocInt(2))]), EQ(TLocInt(2), TLocInt(2))))
)
appleq.expr |> infer_type_rec |> pr_ctx
appleq |> infer_type_rec |> reduc |> pr_ctx
appleq |> pr_redall

# ... TRANSITIVITY OF EQUALITY (even if it doesn't matter) .......






## STATE: You keep a list of OBTAINED FORMULAE, and each one has a list of PREUNIFIED FUNCTIONS

# struct Preunified_func
#     func::Term
#     subst::TProd
#     # Only inward, ofc  # OPTIMIZATION: keep the PRESUBSTITUTED FUNCTIONS,
#     # AND/OR use subst on the FUNCTION OUTPUT TYPE, that should work!
#     good_ideaness::Float
# end

# struct BranchStart
#     formula::Term
#     closeness::float
#     preunified_funcs::Array{Preunified_func}
# end


# state::Array{BranchStart}



# THE GOAL/ OBJECTIVE:
TGlobAnno(s::String) = TAnnoAuto(TGlobAuto(s))

e_Start = eq(op(TGlobAnno("a"), TGlobAnno("x")), op(TGlobAnno("a"), TGlobAnno("y")))
e_Start_anno = TAnnoAuto(e_Start)
e_Start |> infer_type_rec |> reduc |> pr_ctx
e_Start_anno |> (x->pr_E(x; topLevel=true))

e_Stop = eq(TGlobAnno("x"), TGlobAnno("y"))
e_Stop |> infer_type_rec |> reduc |> pr_ctx

e_env = TProd(Array{Term}([TGlobAnno("a"), TGlobAnno("x"), TGlobAnno("y"), e_Start]))
e_env |> infer_type_rec |> reduc |> pr_ctx

add_to_env(env::TProd, f::Term) = TProd(vcat(env.data, [TApp([env, f]) |> reduc]))

env2 = add_to_env(e_env, TAbs(iv(TLocInt(1))))
env2 |> pr_E
env2 |> infer_type_rec |> reduc |> pr_ctx # Yeee!


#
# ...
#

# Something including the fact that you can extract the Partial function op(T1, _) I'm afraid ....

# Something else about the Applying to both sides of equality, which i currently do'nt have at all ...




# partial1(func::Union{TAbs, TAnno}, val::Term) = TApp([TProd(Array{Term}([TLocInt(1), val])), func])
# partial2(func::Union{TAbs, TAnno}, val::Term) = TApp([TProd(Array{Term}([val, TLocInt(2)])), func])
# partial1_delay(func::Union{TAbs, TAnno}, val::Term) = TApp([TProd(Array{Term}([TPost(1, TLocInt(1)), val])), func])
# partial2_delay(func::Union{TAbs, TAnno}, val::Term) = TApp([TProd(Array{Term}([val, TPost(1, TLocInt(2))])), func])

# partial1(func::TAnno, val::TAnno) = build_anno_term_TApp([build_anno_term_TProd(Array{TAnno}([TAnnoAuto(TLocInt(1)), val])), func])
# partial2(func::TAnno, val::TAnno) = build_anno_term_TApp([build_anno_term_TProd(Array{TAnno}([val, TAnnoAuto(TLocInt(2))])), func])
# partial1_delay(func::TAnno, val::TAnno) = build_anno_term_TApp([build_anno_term_TProd(Array{TAnno}([TPost(1, TAnnoAuto(TLocInt(1))), val])), func])
# partial2_delay(func::TAnno, val::TAnno) = build_anno_term_TApp([build_anno_term_TProd(Array{TAnno}([val, TPost(1, TAnnoAuto(TLocInt(2)))])), func])


function getTInOfFunction(t::TAnno)  # Supposed to be one of the Functions you apply ...
    # >>>>> IDEA: IMPORTANT: it's supposed to be the TAnno of a TAbs, which is a >>> TTermEmpty <<< !!!
    t.type |> (x->x.t_out) |> (x->x.t_in) |> reduc  #  |> pr
    # t |> infer_type_rec |> (x->x.t_out) |> (x->x.t_in) |> reduc  #  |> pr
    # ^ I'm not sure y this requires an additional t_out, but K .....
end

# CHECK THAT YOU APPLY ASSDX, of type "[]->OP([OP([T1 x T2]) x T3])->OP([T1 x OP([T2 x T3])])",
# TO ee, that's "Given [T1 x T2 x T3], get OP([OP([T1 x T2]) x T3])"
ee = op(op(TAnnoAuto(TLocInt(1)), TAnnoAuto(TLocInt(2))), TAnnoAuto(TLocInt(3)))
eeT = ee |> infer_type_rec
eeT |> pr_ctx
getTInOfFunction(assdx) |> pr
robinsonUnify(eeT.t_out, getTInOfFunction(assdx); mode=implydir_).res |> pr

# Check that you cannot do the same if ee is wrong:
ee = iv(TAnnoAuto(TLocInt(1)))
eeT = ee |> infer_type_rec
eeT |> pr_ctx
robinsonUnify(eeT.t_out, getTInOfFunction(assdx); mode=implydir_)






# # APPLY THE INVERSE OF a TO BOTH SIDES OF start:
args = build_anno_term_TProd(Array{TAnno}([t, TAnnoAuto(TLocInt(1))])) |> (x->reduc(x; reduc_type=true))
pinv = build_anno_term_TAbs(build_anno_term_TApp(Array{TAnno}([args, opF])))
pinv |> infer_type_rec |> reduc |> pr_ctx
pinv |> pr_redall

# CHECK THAT YOU APPLY APPLEQ, of type "Given [], get [EQ([T1 x T1]) x [T1]->T2]->EQ([T2 x T2])",
# TO e_Start_anno x pinv, of   "Given [], get EQ([OP([A x X]) x OP([A x Y])])"
# and "Given [], get [T1]->OP([IV([A]) x T1])" respectively
e_Start_anno |> (x->pr_E(x; topLevel=true))
appleq |> infer_type_rec |> reduc |> pr_ctx
pinv |> (x->pr_E(x; topLevel=true))
estartxpinv = build_anno_term_TProd([e_Start_anno, pinv])
estartxpinv |> infer_type_rec |> reduc |> pr_ctx
robinsonUnify(estartxpinv.type.t_out, getTInOfFunction(appleq); mode=implydir_).res |> pr
# you CAN'T, which is unfortunatly CORRECT...

estartxpinv.type |> pr_ctx, appleq.type |> pr_ctx

