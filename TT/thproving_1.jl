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


# You want to be able to build Expressions out of this, too:
e1E() = TGlob("e", e1())
ivE(e::Expr) = TAnno(TProd([e]), ivT)
opE(e1::Expr, e2::Expr) = TAnno(TProd([e1, e2]), opT)
eqE(e1::Expr, e2::Expr) = TAnno(TProd([e1, e2]), eqT)

# TESTS/ examples:
ee = op(iv(e1()), e1())
TAbs(op(TLocInt(2), TLocInt(3))) |> reduc
TAnno(TProd([e1E()]), iv(e1())) |> pr_ty
ivE(e1E()) |> pr_ty
opE(ivE(e1E()), e1E()) |> pr_ty
opE(ivE(e1E()), e1E()) |> pr # I mean, it sucks but it's Not wrong...
TAnno(opE(ivE(e1E()), e1E()),  op(iv(e1()), e1())) |> pr_ty
fp = TAbs(TLocInt(2)) # This is supposed to be SECOND PROJECTION
TApp([opE(TGlobAuto("a"), TGlobAuto("b")), fp]) |> reduc |> pr
TApp([opE(TGlobAuto("a"), TGlobAuto("b")), fp]) |> pr_ty


# First possibility (easy): with EQUALITY PRESERVING FUNCTIONS.

invdx = TAnno(TAbs(e1E()), TTermAuto(op(iv(e1()), e1()), e1()))
invdx |> pr
invdx |> pr_ty

invsx = TAnno(TAbs(opE(ivE(e1E()), e1E())), TTermAuto(e1(), op(iv(e1()), e1())))
invsx |> pr
invsx |> pr_ty
invsx |> pr_ty_red

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










############

e = TApp([TLocInt(1), TAbs(TLocInt(1))])
infer_type_rec(e)
# |> (x->x.arg_types) == [TLocInt(1)] # And NOTT [TProd([TLocInt(1)])], plz ????
# infer_type_rec(TLocInt(1))
# infer_type_rec(TAbs(TLocInt(1)))






assdx.type|>reduc|>pr
assdx.expr|>reduc|>pr




