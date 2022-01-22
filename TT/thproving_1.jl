

include("unification_3.jl")
pr_redall(x::TAnno) = reduc(x; reduc_type=true) |> (x->pr_E(x; topLevel=true))

# These were always on the Type level:
E1T = TSumTerm(1, "E1", TProd(Array{Term}([])))
IVT = TAbs(TSumTerm(2, "IV", TProd(Array{Term}([TLocInt(1)]))))
OPT = TAbs(TSumTerm(3, "OP", TProd(Array{Term}([TLocInt(1), TLocInt(2)]))))
# ^ Important note: What i'm doing here, is SHAMELESSLY EXPLOITING the fact that Term is ALREADY recursive (So very much not consistent, im sure?)
EQT = TAbs(TSumTerm(4, "EQ", TProd(Array{Term}([TLocInt(1), TLocInt(2)])))) # This is WRONG, cuz you can say e.g. EQ(EQ(_,_), EQ(_,_)), but this can WAIT.
E1() = E1T
IV(e::Term) = TApp([TProd(Array{Term}([e])), IVT])
OP(E1::Term, e2::Term) = TApp([TProd(Array{Term}([E1, e2])), OPT])
EQ(E1::Term, e2::Term) = TApp([TProd(Array{Term}([E1, e2])), EQT])
E1T |> pr_T, IVT |> pr_T, OPT |> pr_T, EQT |> pr_T

# You want to be able to build Expressions out of this, too: # These were Exprs:
e1() = TGlob("e", E1())
iv(e::Term) = TAnno(TProd(Array{Term}([e])), IVT)
op(e1::Term, e2::Term) = TAnno(TProd(Array{Term}([e1, e2])), OPT)
eq(e1::Term, e2::Term) = TAnno(TProd(Array{Term}([e1, e2])), EQT)



# TESTS/ examples:
OP(IV(E1()), E1()) |> reduc |> pr
TAbs(OP(TLocInt(2), TLocInt(3))) |> reduc |> pr
TAnno(TProd(Array{Term}([e1()])), IV(E1())) |> pr_redall
iv(e1()) |> pr_redall
iv(e1()) |> infer_type_rec |> pr_ctx
op(iv(e1()), e1()) |> pr # I mean, it sucks but it's Not wrong...
TAnno(op(iv(e1()), e1()),  OP(IV(E1()), E1())) |> pr
fp = TAbs(TLocInt(2)) # This is supposed to be SECOND PROJECTION
TApp([op(TGlobAuto("a"), TGlobAuto("b")), fp]) |> reduc |> pr
TApp([op(TGlobAuto("a"), TGlobAuto("b")), fp]) |> pr


# First possibility (easy): with EQUALITY PRESERVING FUNCTIONS.

# LEFT INVERIBILITY: OP(inv(a), a) == e()
invsx_fw = TAnno(TAbs(e1()), TTermAuto(OP(IV(TLocInt(1)), TLocInt(1)), E1()))
invsx_fw |> infer_type_rec |> reduc |> pr
invsx_fw |> pr_redall

invsx_bw = TAnno(TAbs(op(iv(TLocInt(1)), TLocInt(1))), TTermAuto(E1(), OP(IV(TLocInt(1)), TLocInt(1))))
invsx_bw |> infer_type_rec |> reduc |> pr
invsx_bw |> pr_redall

# RIGHT INVERIBILITY: OP(a, inv(a)) == a
invdx_fw = TAnno(TAbs(e1()), TTermAuto(OP(TLocInt(1), IV(TLocInt(1))), E1()))
invdx_fw |> infer_type_rec |> reduc |> pr
invdx_fw |> pr_redall

invdx_bw = TAnno(TAbs(op(TLocInt(1), iv(TLocInt(1)))), TTermAuto(E1(), OP(TLocInt(1), IV(TLocInt(1)))))
invdx_bw |> infer_type_rec |> reduc |> pr
invdx_bw |> pr_redall

# RIGHT NULLITY: OP(a, e()) == a
nuldx_fw = TAnno(TAbs(TLocInt(1)), TAbs(TTerm(OP(TLocInt(1), E1()), TLocInt(1))))
nuldx_fw |> infer_type_rec |> reduc |> pr
nuldx_fw |> pr_redall

nuldx_bw = TAnno(TAbs(op(TLocInt(1), e1())), TTermAuto(TLocInt(1), OP(TLocInt(1), E1())))
nuldx_bw |> infer_type_rec |> reduc |> pr
nuldx_bw |> pr_redall

# LEFT NULLITY: OP(e(), a) == a
nulsx_fw = TAnno(TAbs(TLocInt(2)), TAbs(TTerm(OP(E1(), TLocInt(1)), TLocInt(1))))
nulsx_fw |> infer_type_rec |> reduc |> pr
nulsx_fw |> pr_redall

nulsx_bw = TAnno(TAbs(op(e1(), TLocInt(1))), TTermAuto(TLocInt(1), OP(E1(), TLocInt(1))))
nulsx_bw |> infer_type_rec |> reduc |> pr
nulsx_bw |> pr_redall


# TRANSITIVITY: OP(OP(a,b),c) == OP(a,OP(b,c))
proj1_1, proj2_1 = TApp([TLocInt(1), TAbs(TLocInt(1))]), TApp([TLocInt(1), TAbs(TLocInt(2))])
assdx = TAnno(
    TAbs(op(proj1_1, op(proj2_1, TLocInt(2)))),
    TTerm(OP(OP(TLocInt(1), TLocInt(2)), TLocInt(3)), OP(TLocInt(1), OP(TLocInt(2), TLocInt(3)))))
assdx |> infer_type_rec |> reduc |> pr
assdx |> pr_redall

# ...

p1, p2 = TAbs(TLocInt(1)), TAbs(TLocInt(2))
symeq = TAnno(
    TAbs(eq(TAppAuto(p2, TAppAuto(p1, TLocInt(1))), TAppAuto(p2, TAppAuto(p2, TLocInt(1))))),
    TTerm(TProd([EQ(TLocInt(1), TLocInt(1)), TTerm(TLocInt(1), TLocInt(2))]), EQ(TLocInt(2), TLocInt(2)))
)
TAbs(eq(TAppAuto(p2, TAppAuto(p1, TLocInt(1))), TAppAuto(p2, TAppAuto(p2, TLocInt(1))))) |> infer_type_rec |> reduc |> pr_ctx
symeq |> infer_type_rec |> reduc |> pr_ctx
symeq |> pr_redall

# Transitivity of equality (even if it doesn't matter)


# APPLICATION TO BOTH SIDES OF EQUALITY


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



# THE GOAL/ OBJECTIVE:

e_Start = eq(op(TLocInt(1), TLocInt(2)), op(TLocInt(1), TLocInt(3)))
e_Start |> infer_type_rec |> reduc |> pr_ctx

e_Stop = eq(TLocInt(2), TLocInt(3))
e_Stop |> infer_type_rec |> reduc |> pr_ctx

e_env = TProd(Array{Term}([TLocInt(1), TLocInt(2), TLocInt(3), e_Start]))
e_env |> infer_type_rec |> reduc |> pr_ctx

add_to_env(env::TProd, f::Term) = TProd(vcat(env.data, [TApp([env, f]) |> reduc]))

env2 = add_to_env(e_env, TAbs(iv(TLocInt(1))))
env2 |> infer_type_rec |> reduc |> pr_ctx # Yeee!


#
# ...
#

# Something including the fact that you can extract the Partial function op(T1, _) I'm afraid ....

# Something else about the Applying to both sides of equality, which i currently do'nt have at all ...




der = TApp(Array{Term}([]))
e_Start |> infer_type_rec |> reduc |> pr_ctx





partial


ee = op(op(TLocInt(1), TLocInt(2)), TLocInt(3))
eeT = infer_type_rec(ee)
eeT |> pr_ctx
robinsonUnify(eeT.t_out, getTInOfFunction(assdx); mode=implydir_)

ee = iv(TLocInt(1))
eeT = infer_type_rec(ee)
eeT |> pr_ctx
robinsonUnify(eeT.t_out, getTInOfFunction(assdx); mode=implydir_)





function getTInOfFunction(t::TAnno)  # Supposed to be one of the Functions you apply ...
    t.type |> (x->x.t_in) |> reduc  #  |> pr
    # t |> infer_type_rec |> (x->x.t_out) |> (x->x.t_in) |> reduc  #  |> pr
    # ^ I'm not sure y this requires an additional t_out, but K .....
end

pr_ctx