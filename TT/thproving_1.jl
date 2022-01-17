include("unification_3.jl")
pr_redall(x::TAnno) = reduc(x; reduc_type=true) |> pr_E

# These were always on the Type level:
E1T = TSumTerm(1, "E1", TProd([]))
IVT = TAbs(TSumTerm(2, "IV", TProd([TLoc(1)])))
OPT = TAbs(TSumTerm(3, "OP", TProd([TLoc(1), TLoc(2)])))
# ^ Important note: What i'm doing here, is SHAMELESSLY EXPLOITING the fact that Term is ALREADY recursive (So very much not consistent, im sure?)
eqT = TAbs(TSumTerm(4, "EQ", TProd([TLoc(1), TLoc(2)]))) # This is WRONG, cuz you can say e.g. EQ(EQ(_,_), EQ(_,_)), but this can WAIT.
E1() = E1T
IV(e::Term) = TApp([TProd([e]), IVT])
OP(E1::Term, e2::Term) = TApp([TProd([E1, e2]), OPT])
EQ(E1::Term, e2::Term) = TApp([TProd([E1, e2]), eqT])
E1T |> pr_T, IVT |> pr_T, OPT |> pr_T, eqT |> pr_T

# You want to be able to build Expressions out of this, too: # These were Exprs:
e1E() = TGlob("e", E1())
ivE(e::Term) = TAnno(TProd([e]), IVT)
opE(E1::Term, e2::Term) = TAnno(TProd([E1, e2]), OPT)
eqE(E1::Term, e2::Term) = TAnno(TProd([E1, e2]), eqT)
include("unification_2.jl")

pr_ty(e) = (r = e |> infer_type_rec; (r isa Error ? r : r |> (x->x.res_type) |> pr))
pr_ty_red(e) = (r = e |> infer_type_rec; (r isa Error ? r : r |> (x->x.res_type) |> reduc |> pr))
# pr_ty(e) = e.infer_type_rec.{Error->x, _->x.res_type.pr}
# pr_ty(e) = e.infer_type_rec.{Error->nthg, x->x.res_type.pr}
# pr_ty(e) = e.infer_type_rec.?res_type.?pr
# pr_ty(e) = e.infer_type_rec.?{x.res_type.pr}

# Texp = TGlob("EXP")
# e1E = TGlob("e1", TTerm(TProd([]), Texp))
# ivE = TGlob("iv", TTerm(TProd([Texp]), Texp))
# opE = TGlob("op", TTerm(TProd([Texp, Texp]), Texp))
# e1() = TApp([TProd([]), e1E])
# iv(e::Expr) = TApp([TProd([e]), ivE])
# op(e1::Expr, e2::Expr) = TApp([TProd([e1, e2]), opE])
# ee = op(iv(e1()), e1())
# ee |> pr
# infer_type_rec(ee).res_type |> pr # == "EXP", YES!!


e1T = TSumTerm("e1", TProd([]))
ivT = TAbs(TSumTerm("iv", TProd([TLocInt(1)])))
opT = TAbs(TSumTerm("op", TProd([TLocInt(1), TLocInt(2)])))
# ^ Important note: What i'm doing here, is SHAMELESSLY EXPLOITING the fact that Term is ALREADY recursive (So very much not consistent, im sure?)
eqT = TAbs(TSumTerm("EQ", TProd([TLocInt(1), TLocInt(2)]))) # This is WRONG, cuz you can say e.g. eq(eq(_,_), eq(_,_)), but this can WAIT.
e1() = e1T
iv(e::Term) = TApp([TProd([e]), ivT])
op(e1::Term, e2::Term) = TApp([TProd([e1, e2]), opT])
eq(e1::Term, e2::Term) = TApp([TProd([e1, e2]), eqT])



# TESTS/ examples:
OP(IV(E1()), E1()) |> reduc |> pr
TAbs(OP(TLoc(2), TLoc(3))) |> reduc |> pr
TAnno(TProd([e1E()]), IV(E1())) |> pr_redall
ivE(e1E()) |> pr_redall
ivE(e1E()) |> infer_type_rec |> pr_ctx
opE(ivE(e1E()), e1E()) |> pr # I mean, it sucks but it's Not wrong...
TAnno(opE(ivE(e1E()), e1E()),  OP(IV(E1()), E1())) |> pr
fp = TAbs(TLoc(2)) # This is supposed to be SECOND PROJECTION
ee = op(iv(e1()), e1())
TAbs(op(TLocInt(2), TLocInt(3))) |> reduc
TAnno(TProd([e1E()]), iv(e1())) |> pr_ty
ivE(e1E()) |> pr_ty
opE(ivE(e1E()), e1E()) |> pr_ty
opE(ivE(e1E()), e1E()) |> pr # I mean, it sucks but it's Not wrong...
TAnno(opE(ivE(e1E()), e1E()),  op(iv(e1()), e1())) |> pr_ty
fp = TAbs(TLocInt(2)) # This is supposed to be SECOND PROJECTION
TApp([opE(TGlobAuto("a"), TGlobAuto("b")), fp]) |> reduc |> pr
TApp([opE(TGlobAuto("a"), TGlobAuto("b")), fp]) |> pr


# First possibility (easy): with EQUALITY PRESERVING FUNCTIONS.

# LEFT INVERIBILITY: OP(inv(a), a) == e()
invsx_fw = TAnno(TAbs(e1E()), TAbs(TTermAuto(OP(IV(TLoc(1)), TLoc(1)), E1())))
invsx_fw |> infer_type_rec |> reduc |> pr
invsx_fw |> pr_redall

invsx_bw = TAnno(TAbs(opE(ivE(TLoc(1)), TLoc(1))), TAbs(TTermAuto(E1(), OP(IV(TLoc(1)), TLoc(1)))))
invsx_bw |> infer_type_rec |> reduc |> pr
invsx_bw |> pr_redall

# RIGHT INVERIBILITY: OP(a, inv(a)) == a
invdx_fw = TAnno(TAbs(e1E()), TAbs(TTermAuto(OP(TLoc(1), IV(TLoc(1))), E1())))
invdx_fw |> infer_type_rec |> reduc |> pr
invdx_fw |> pr_redall

invdx_bw = TAnno(TAbs(opE(TLoc(1), ivE(TLoc(1)))), TAbs(TTermAuto(E1(), OP(TLoc(1), IV(TLoc(1))))))
invdx_bw |> infer_type_rec |> reduc |> pr
invdx_bw |> pr_redall

# RIGHT NULLITY: OP(a, e()) == a
nuldx_fw = TAnno(TAbs(TLoc(1)), TAbs(TTerm(OP(TLoc(1), E1()), TLoc(1))))
nuldx_fw |> infer_type_rec |> reduc |> pr
nuldx_fw |> pr_redall
nuldx = TAnno(TAbs(TLocInt(1)), TAbs(TTerm(op(TLocInt(1), e1()), TLocInt(1))))
nulsx = TAnno(TAbs(TLocInt(2)), TAbs(TTerm(op(e1(), TLocInt(1)), TLocInt(1))))
nuldx |> pr_ty
nulsx |> pr_ty

# op(op(a,b),c) --> op(a,op(b,c))
proj1_1, proj2_1 = TApp([TLocInt(1), TAbs(TLocInt(1))]), TApp([TLocInt(1), TAbs(TLocInt(2))])
assdx = TAnno(
    TAbs(opE(proj1_1, opE(proj2_1, TLocInt(2)))),
    TAbs(TTerm(op(op(TLocInt(1), TLocInt(2)), TLocInt(3)), op(TLocInt(1), op(TLocInt(2), TLocInt(3))))))

e = infer_type_rec(assdx)
# What's the problem here?
# > Imean does this ever even happen?
# > "ELocs typed [\"[T1]\", \"T2\"] cannot be unified with ELocs typed [\"[T1 x T2]\", \"T3\"], with error 'Different lengths: 1 < 2, so you cannot even drop.'"
# ^ This is because: The SECOND is the correct INFERRED type of the ARGUMENT INTO opE(proj2_1, TLocInt(2)),
# ^ while the first thing, is: the CORRECT INFERRED type of the ARGUMENT INTO proj1_1, THAT WOULD BE [\"[T1]\"] (YES)- Augmented to [\"[T1]\", \"T2\"] by the Prod augmentation procedure.
# ^ Ok but this is DUMB, because: it's really NOT ABOUT AUGMENTING, it's about BEING CONTRAVARIANT ALL THE WAY DOWN!!

# ^ ALSO, now that i think about it: There's a whole thing about finding the MEET/JOIN of 2 types instead of a simple arrow !!!

nuldx_bw = TAnno(TAbs(opE(TLoc(1), e1E())), TAbs(TTermAuto(TLoc(1), OP(TLoc(1), E1()))))
nuldx_bw |> infer_type_rec |> reduc |> pr
nuldx_bw |> pr_redall

# LEFT NULLITY: OP(e(), a) == a
nulsx_fw = TAnno(TAbs(TLoc(2)), TAbs(TTerm(OP(E1(), TLoc(1)), TLoc(1))))
nulsx_fw |> infer_type_rec |> reduc |> pr
nulsx_fw |> pr_redall

nulsx_bw = TAnno(TAbs(opE(e1E(), TLoc(1))), TAbs(TTermAuto(TLoc(1), OP(E1(), TLoc(1)))))
nulsx_bw |> infer_type_rec |> reduc |> pr
nulsx_bw |> pr_redall


# TRANSITIVITY: OP(OP(a,b),c) == OP(a,OP(b,c))
proj1_1, proj2_1 = TApp([TLoc(1), TAbs(TLoc(1))]), TApp([TLoc(1), TAbs(TLoc(2))])
assdx = TAnno(
    TAbs(opE(proj1_1, opE(proj2_1, TLoc(2)))),
    TAbs(TTerm(OP(OP(TLoc(1), TLoc(2)), TLoc(3)), OP(TLoc(1), OP(TLoc(2), TLoc(3))))))
assdx |> infer_type_rec |> reduc |> pr
assdx |> pr_redall

# ...

# Simmetry of equality
# ...

# Transitivity of equality (even if it doesn't matter)


# APPLICATION TO BOTH SIDES OF EQUALITY

e = TApp([TLocInt(1), TAbs(TLocInt(1))])
infer_type_rec(e)
# |> (x->x.arg_types) == [TLocInt(1)] # And NOTT [TProd([TLocInt(1)])], plz ????
# infer_type_rec(TLocInt(1))
# infer_type_rec(TAbs(TLocInt(1)))

# I recall, EQ(OP(TGlob("A"), TGlob("X")), OP(TGlob("A"), TGlob("Y")))
# should become EQ(TGlob("X"), TGlob("Y")) ...



## STATE: You keep a list of OBTAINED FORMULAE, and each one has a list of PREUNIFIED FUNCTIONS

struct Preunified_func
    func::Term
    subst::TProd
    # Only inward, ofc  # OPTIMIZATION: keep the PRESUBSTITUTED FUNCTIONS,
    # AND/OR use subst on the FUNCTION OUTPUT TYPE, that should work!
    good_ideaness::float
end

struct BranchStart
    formula::Term
    closeness::float
    preunified_funcs::Array{Preunified_func}
end


state::Array{BranchStart}


