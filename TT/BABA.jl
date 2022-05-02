
include("unification_3.jl")








t1 = TAbs(TProd(Array{Term}([TLocInt(1), TPostOne(TLocInt(1)), TAppAuto(TLocInt(1), TPostOne(TLocInt(1)))]))) # IT'S THETHING: a tAbs returning a TAbs.....
t1|>pr, t1|>pr_E
infer_type_rec(t1) |>pr_ctx


targ_lev1 = TGlob("A")
app = TAppAuto(t1, targ_lev1)
reduc(app) |>pr

targ_lev2 = TGlob("B")
app = TAppAuto(TAppAuto(t1, targ_lev1), targ_lev2)  # Two TApp's, ASSOCIATED LIKE THIS, which is VERY DIFFERENT from a TConc !!
reduc(app) |>pr

