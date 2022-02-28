
include("unification_3.jl")

e1 = TGlobAuto("a")
T = TSum(Vector{Pair{String, Term}}(["a"=>TGlob("A"), "b"=>TGlob("B")]))
e = TAnno(e1, TTermAutoCtx(T)) # THIS DOESNT WORK: a:A is NOT of type A+B
infer_type_rec(e) |> pr_ctx

e1 = TGlobAuto("a")
T = TSum(Vector{Pair{String, Term}}(["a"=>TGlob("A"), "b"=>TGlob("B")]))
e = TApp([e1, TGlob("f",  TTerm(T, TGlob("C")))]) # THIS DOESNT WORK: a:A does NOT go into type A+B
infer_type_rec(e) |> pr_ctx


e1 = TSumTerm(1, "a", TGlobAuto("a"))
T = TSum(Vector{Pair{String, Term}}(["a"=>TGlob("A"), "b"=>TGlob("B")]))
e = TAnno(e1, TTermAutoCtx(T))
infer_type_rec(e) |> pr_ctx  # OF COURSE this works..

e1 = TSumTerm(1, "a", TGlobAuto("a"))
T = TSum(Vector{Pair{String, Term}}(["a"=>TGlob("A"), "b"=>TGlob("B")]))
e = TApp([e1, TGlob("f",  TTerm(T, TGlob("C")))])   # OF COURSE this works..
infer_type_rec(e) |> pr_ctx


e1 = TSumTerm(2, "b", TGlobAuto("a")) # it's a A term, but TAGGED WITH THE WRONG LABEL!
T = TSum(Vector{Pair{String, Term}}(["a"=>TGlob("A"), "b"=>TGlob("B")]))
e = TAnno(e1, TTermAutoCtx(T))
infer_type_rec(e) |> pr_ctx  # Error, i guess...

e1 = TSumTerm(2, "b", TGlobAuto("a")) # it's a A term, but TAGGED WITH THE WRONG LABEL!
T = TSum(Vector{Pair{String, Term}}(["a"=>TGlob("A"), "b"=>TGlob("B")]))
e = TApp([e1, TGlob("f",  TTerm(T, TGlob("C")))])   # Error, i guess...
infer_type_rec(e) |> pr_ctx




# TESTING TInd:
T = TInd(TSum(Vector{Pair{String, Term}}(["l"=>TGlob("A"), "b"=>TProd(Array{Term}([TIndVar(), TIndVar()]))])))

tree = TSumTerm(1, "b", TProd(Array{Term}([TSumTerm(1, "l", TGlobAuto("a")), TSumTerm(1, "b", TProd(Array{Term}([TSumTerm(1, "l", TGlobAuto("a")), TSumTerm(1, "l", TGlobAuto("a"))])))])))
infer_type_rec(tree) |> pr_ctx

anno_tree = TAnno(tree, TTermEmpty(T))
infer_type_rec(anno_tree) |> pr_ctx



# TESTING POLYMORPHIS:
aa = TAbs(TProd(Array{Term}([TLocInt(1), TLocInt(1)])))
infer_type_rec(aa) |> pr_ctx

e = TProd(Array{Term}([TAppAuto(aa, TGlobAuto("a")), TAppAuto(aa, TGlobAuto("b"))]))
infer_type_rec(e) |> pr_ctx


TAnnoAuto(TGlobAuto("a"))
TAnnoAutoCtx(TGlobAuto("a"))
TAnnoEmpty(TGlobAuto("a"))
TAnnoAuto(TGlobAuto("a"))

infer_type_rec(TAnno(TLocInt(1), TTermAutoCtx(TGlob("B")))) |> pr_ctx


t1 = TTermAutoCtx(TProd(Array{Term}([TLocInt(1), TLocInt(2)])))
t1|>pr
tb = TProd(Array{Term}([TGlob("B"), TGlob("B")]))
tt = util_AnnoTypeOfObjReturning(t1, tb)
tt |> pr