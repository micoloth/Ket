# TO UNIF
# [I'm afraid, first order] unification- Screw it, I'm going first order

# from https://github.com/jozefg/higher-order-unification/


# IMPORTANT idea on how to code CONTINUATIONS: And what types/constructions must be involved:
# IF you have a f:A->B function, you (can) ALSO have such a function: fc:C->B, where C stands for "CONFIRMATION/CONTINUATION",
# and where Such a function is GENERATED like this: if C(confirmation) is just a Constant that confirms a CANDIDATE a,
# fc={a.b}, where you CAN, OR NOT, precompute a.b.
# Otherwise, if a DEPENDS (in some known way ca:C->A ofc) from a param c,
# fc={x.ca.ab}, where you can STILL precompose ca.ab, and it MIGTH still be useful if ca STILL has some "pieces-of-a-like" internal state !!
# Really, the only problem is tho: That before you had a B, now you have C->B !!! Or at most, a (B + C->B) ....
# And so here we return to our favourite problems: IS THERE a match<> from (B + C->B) to B ?  How/when do/can you convert from B to 1->B and/or viceversa?
# What is the meaning of the "NTHG" function ????


# TGlob   TGlob
# TLoc   TLoc
# TTop   TTop
# TTerm   TTerm
# TAbs   TAbs
# TProd   TProd
# TSum   TSum
# TApp   TApp
# TSumTerm   TSumTerm
# TAnno   TAnno
# TBranches   TBranches

include("mylambda1_tag.jl")


abstract type Constraint end
struct DirectConstraint <: Constraint # (->)
    t1::Term
    t2::Term
end
struct ReverseConstraint <: Constraint# (Meaning <-)
    t1::Term
    t2::Term
end
struct EqConstraint <: Constraint # Should be equal.
    t1::TLoc
    t2::Term
end
struct ErrorConstraint <: Constraint
    c::Constraint
    error::Error
end
Base.:(==)(a::EqConstraint, b::EqConstraint) = (a.t1 == b.t1) && (a.t2 == b.t2)
Base.:(==)(a::DirectConstraint, b::DirectConstraint) = (a.t1 == b.t1) && (a.t2 == b.t2)
Base.:(==)(a::ReverseConstraint, b::ReverseConstraint) = (a.t1 == b.t1) && (a.t2 == b.t2)
reduc(c::DirectConstraint) = DirectConstraint(reduc(c.t1), reduc(c.t2))
reduc(c::ReverseConstraint) = ReverseConstraint(reduc(c.t1), reduc(c.t2))
reduc(c::EqConstraint) = EqConstraint(reduc(c.t1), reduc(c.t2))
reduc(c::ErrorConstraint) = ErrorConstraint(reduc(c.c), c.error)


get_string(a::Array{ErrorConstraint}) = a .|> (x -> "Can't unify $(x.c.t1 |>pr) and $(x.c.t2 |>pr): $(x.error)") |> (x -> join(x, ", "))

Error = String
Imply_res = Union{Array{Constraint},ErrorConstraint}

pr(c::Constraint)::String = pr(c.t1) * "==" * pr(c.t2)


#a join b  ==  a v b  ==  a<avb, b<avb  ==  a CAN BECOME a join b, b CAN BECOME a join b

struct MeetJoin_rec_res
    res_type::Term # OR would be better if each one had its own?  --> NOTE: maybe i can still template it?
    cs::Array{EqConstraint}
end

err_msg_app(t1::TApp, t2::TApp) = "Different bodies: $(length(t1.ops_dot_ordered)) != $(length(t2.ops_dot_ordered))"
err_msg_lambdas(t1::TAbs, t2::TAbs) = "Different lambdas $(pr(t1)) != $(pr(t2)): I know I'm being picky, but impossible to tell if these are the same: $([t1.body, t2.body])"
err_msg_sumtags(t1::TSumTerm, t2::TSumTerm) = "For now, you can NEVER unify different tags: $(t1.tag_name) != $(t2.tag_name)"
err_msg_terms(t1::Term, t2::Term) = "Different: $(pr(t1)) is really different from $(pr(t2))"
err_msg_prods(t1::TProd, t2::TProd) = "Different lengths: $(length(t1.data)) < $(length(t2.data)), so you cannot even drop."
err_msg_prods_tags(t1::TProd, t2::TProd) = "Some tags are in second, not in first: $(keys(t1.data_tags)) < $(keys(t2.data_tags)), so you cannot even drop them."
err_msg_sums(t1::TSum, t2::TSum) = "Different lengths: $(length(t1.data)) > $(length(t2.data)), so if you are in the last case you are screwed.."
err_msg_tags(t1::TProd, t2::TProd) = "You cant unify var_tags: $(t1) != $(t2)."

function meetjoin_rec_unify_(t1::TApp, t2::TApp, do_meet::Bool)::MeetJoin_rec_res
    if length(t1.ops_dot_ordered) != length(t2.ops_dot_ordered)
        return MeetJoin_rec_res(TermwError(t1, Error(err_msg_app(t1, t2))), Array{Constraint}[])
    end
    all_ress = [meetjoin_rec_unify_(f1, f2, do_meet) for (f1, f2) in zip(t1.ops_dot_ordered, t2.ops_dot_ordered)]
    MeetJoin_rec_res(TApp(all_ress .|> x -> x.res_type), vcat((all_ress .|> x -> x.cs)...))
end

concat_(t::TProd...) = TProd(vcat((t .|> (x -> x.data))...), merge((t .|> (x -> x.data_tags))...))
subdict(d::Dict{Id,Term}, keys::Set{Id}) = Dict{Id,Term}(k => d[k] for k in keys)

function meetjoin_rec_unify_(t1::TProd, t2::TProd, do_meet::Bool)::MeetJoin_rec_res
    t1l, t2l = t1.data |> length, t2.data |> length
    shared_tags = intersect(keys(t1.data_tags), keys(t2.data_tags)) # To let it be ordered
    tags_1_not_2 = setdiff(keys(t1.data_tags), keys(t2.data_tags))
    tags_2_not_1 = setdiff(keys(t2.data_tags), keys(t1.data_tags))
    shared_res = Dict{Id,MeetJoin_rec_res}(tt => meetjoin_rec_unify_(t1.data_tags[tt], t2.data_tags[tt], do_meet) for tt in shared_tags)
    shared_res_types = Dict{Id,Term}(tt => shared_res[tt].res_type for tt in shared_tags)
    res_types_tags = merge(shared_res_types, subdict(t1.data_tags, tags_1_not_2), subdict(t2.data_tags, tags_2_not_1))
    res_tags_cs = vcat((values(shared_res) .|>  x -> x.cs)...)

    t1l, t2l = t1.data |> length, t2.data |> length
    all_ress = [meetjoin_rec_unify_(f1, f2, do_meet) for (f1, f2) in zip(t1.data, t2.data)] # Potentially turn into a monad (not really urgent tho)
    res_data_types = Array{Term}(all_ress .|> x -> x.res_type)
    res_data_cs = vcat((all_ress .|> x -> x.cs)...)
    if t1l != t2l && do_meet
        additional_elems = (t1l > t2l) ? (t1.data[(t2l+1):end]) : (t2.data[(t1l+1):end])
        res_data_types = vcat(res_data_types, additional_elems)
    end
    MeetJoin_rec_res(TProd(res_data_types, res_types_tags), vcat(res_tags_cs, res_data_cs))
end


function meetjoin_rec_unify_(t1::TSum, t2::TSum, do_meet)::MeetJoin_rec_res
    all_ress = [meetjoin_rec_unify_(f1, f2, do_meet) for (f1, f2) in zip(t1.data, t2.data)] # Potentially turn into a monad (not really urgent tho)
    res_types = all_ress .|> x -> x.res_type
    errors = findall((x -> x isa TermwError), res_types)
    t1l, t2l = t1.data |> length, t2.data |> length
    if t1l != t2l && !do_meet
        additional_elems = (t1l > t2l) ? (t1.data[(t2l+1):end]) : (t2.data[(t1l+1):end])
        res_types = vcat(res_types, additional_elems)
    end
    res_type = TSum(res_type)
    if length(errors) > 0
        res_type = TermwError(res_type, "E" * join(errors .|> string, ""))
    end
    MeetJoin_rec_res(res_type, vcat((all_ress .|> x -> x.cs)...))
end


function meetjoin_rec_unify_(t1::TAbs, t2::TAbs, do_meet)::MeetJoin_rec_res
    println("Simplyfing two Foralls:")
    # FOR NOW, these will be REALLY PICKY
    if t1 == t2
        MeetJoin_rec_res(t1, Array{Constraint}[])
    else
        MeetJoin_rec_res(TermwError(t1, Error(err_msg_lambdas(t1, t2))), Array{Constraint}[])
    end
end

function meetjoin_rec_unify_(t1::TTerm, t2::TTerm, do_meet)::MeetJoin_rec_res
    res_out = meetjoin_rec_unify_(t1.t_out, t2.t_out, do_meet)
    res_in = meetjoin_rec_unify_(t1.t_in, t2.t_in, !do_meet)
    MeetJoin_rec_res(TTerm(res_in.res_type, res_out.res_type), vcat(res_out.cs, res_in.cs))
end

function meetjoin_rec_unify_(t1::TSumTerm, t2::TSumTerm, do_meet)::MeetJoin_rec_res
    if t1.tag != t2.tag
        return MeetJoin_rec_res(TermwError(t1, Error(err_msg_sumtags(t1, t2))), Array{Constraint}[])
        # ^ You MIGHT want to return constraints for t1 and t2 all the same, but i'm NOT doing it...
    else
        res = meetjoin_rec_unify_(t1.data, t2.data, do_meet) # Wait.... Is this even right? How does a type-level sum play with type-level Locs ???
        return MeetJoin_rec_res(TSumTerm(t1.tag, t1.tag_name, res.res_type), res.cs)
    end
end
function meetjoin_rec_unify_(t1::Term, t2::TSumTerm, do_meet)::MeetJoin_rec_res
    # This behaviour is pretty weird admiddetly, and it simply says: SCREW TAG, essentially
    if (t1 isa TLoc)
        MeetJoin_rec_res(t1, Array{Constraint}([EqConstraint(t1, t2)]))
    else
        res = meetjoin_rec_unify_(t1, t2.data, do_meet) # Wait.... Is this even right? How does a type-level sum play with type-level Locs ???
        MeetJoin_rec_res(TSumTerm(t2.tag, t1.tag_name, res.res_type), res.cs)
    end
end
function meetjoin_rec_unify_(t1::TSumTerm, t2::Term, do_meet)::MeetJoin_rec_res
    # This behaviour is pretty weird admiddetly, and it simply says: SCREW TAG, essentially
    if (t2 isa TLoc)
        MeetJoin_rec_res(t2, Array{Constraint}([EqConstraint(t2, t1)]))
    else
        res = meetjoin_rec_unify_(t1.data, t2, do_meet) # Wait.... Is this even right? How does a type-level sum play with type-level Locs ???
        MeetJoin_rec_res(TSumTerm(t1.tag, t1.tag_name, res.res_type), res.cs)
    end
end

function meetjoin_rec_unify_(t1::TLoc, t2::TLoc, do_meet)::MeetJoin_rec_res
    if t1.var == t2.var # t1.var == t2.var
        MeetJoin_rec_res(t2, Array{Constraint}([]))
    else
        MeetJoin_rec_res(t2, Array{Constraint}([EqConstraint(t1, t2)]))
    end
end
function meetjoin_rec_unify_(t1::TLocStr, t2::TLocStr, do_meet)::MeetJoin_rec_res
    if t1.var_tag == t2.var_tag # t1.var == t2.var
        MeetJoin_rec_res(t2, Array{Constraint}([]))
    else
        MeetJoin_rec_res(t2, Array{Constraint}([ErrorConstraint(EqConstraint(t1, t2), err_msg_tags(t1, t2))]))# Uhhh How about return an error ??? ???
    end
end

function meetjoin_rec_unify_(t1::Term, t2::Term, do_meet)::MeetJoin_rec_res # base case
    if t1 == t2
        MeetJoin_rec_res(t1, Array{Constraint}([]))
    elseif t1 isa TLoc
        MeetJoin_rec_res(t1, Array{Constraint}([EqConstraint(t1, t2)]))
    elseif t2 isa TLoc
        MeetJoin_rec_res(t2, Array{Constraint}([EqConstraint(t2, t1)]))
    else
        MeetJoin_rec_res(TermwError(t1, Error(err_msg_terms(t1, t2))), Array{Constraint}[])
    end
end

function imply_unify_(t1::TApp, t2::TApp)::Imply_res
    if length(t1.ops_dot_ordered) != length(t2.ops_dot_ordered)
        ErrorConstraint(DirectConstraint(t1, t2), Error(err_msg_app(t1, t2)))
    else
        Array{Constraint}([DirectConstraint(s1, s2) for (s1, s2) in zip(t1.ops_dot_ordered, t2.ops_dot_ordered)])
    end
end

function imply_unify_(t1::TProd, t2::TProd)::Imply_res
    if length(t1.data) < length(t2.data)
        return ErrorConstraint(DirectConstraint(t1, t2), Error(err_msg_prods(t1, t2)))
    end
    cs_data = Array{Constraint}([DirectConstraint(s1, s2) for (s1, s2) in zip(t1.data, t2.data)])
    shared_tags = intersect(keys(t1.data_tags), keys(t2.data_tags)) # To let it be ordered
    if length(setdiff(keys(t2.data_tags), keys(t1.data_tags))) > 0
        return ErrorConstraint(DirectConstraint(t1, t2), Error(err_msg_prods_tags(t1, t2)))
    end
    cs_tags = Array{Constraint}([DirectConstraint(t1.data_tags[tt], t2.data_tags[tt]) for tt in shared_tags])
    return vcat(cs_data, cs_tags)
end

function imply_unify_(t1::TAbs, t2::TAbs)::Imply_res
    println("Simplyfing two Foralls:")
    # FOR NOW, these will be REALLY PICKY
    if t1 == t2
        Array{Constraint}([])
    else
        ErrorConstraint(DirectConstraint(t1, t2), Error(err_msg_lambdas(t1, t2)))
    end
    # Only accepted case: All constraints are about TLoc only and THE SAME
    # cons = DirectConstraint(t1.body, t2.body)
    # cons = simplify(cons)
    # is_same(c::Constraint) = (c.t1 isa TLoc) && (c.t1 == c.t2)
    # if typeof(cons) == Error
    #     Error("Different lambdas: with this error: $(cons)")
    # elseif length(cons) == 0 || (cons .|> is_same |> all)
    #     Array{Constraint}([])
    # else
    #     Error("Different lambdas $(pr(t1)) != $(pr(t2)): I know I'm being picky, but impossible to simplify this part: $(cons)")
    # end
end

function imply_unify_(t1::TTerm, t2::TTerm)::Imply_res
    Array{Constraint}([
        DirectConstraint(t1.t_out, t2.t_out),
        ReverseConstraint(t1.t_in, t2.t_in)])
end

function imply_unify_(t1::TLoc, t2::TLoc)::Imply_res
    Array{Constraint}([DirectConstraint(t1, t2)])
end

function imply_unify_(t1::TSum, t2::TSum)::Imply_res
    if length(t1.data) > length(t2.data)
        ErrorConstraint(DirectConstraint(t1, t2), Error(err_msg_sums(t1, t2)))
    else
        Array{Constraint}([DirectConstraint(s1, s2) for (s1, s2) in zip(t1.data, t2.data)])
    end
end

function imply_unify_(t1::TSumTerm, t2::TSumTerm)::Imply_res
    if t1.tag != t2.tag
        ErrorConstraint(DirectConstraint(t1, t2), Error(err_msg_sumtags(t1, t2)))
    else
        Array{Constraint}([DirectConstraint(t1.data, t2.data)])
    end
end
function imply_unify_(t1::Term, t2::TSumTerm)::Imply_res
    # This behaviour is pretty weird admiddetly, and it simply says: SCREW TAG, essentially
    if (t1 isa TLoc)
        Array{Constraint}([DirectConstraint(t1, t2)])
    else
        Array{Constraint}([DirectConstraint(t1, t2.data)])
    end
end
function imply_unify_(t1::TSumTerm, t2::Term)::Imply_res
    # This behaviour is pretty weird admiddetly, and it simply says: SCREW TAG, essentially
    if (t2 isa TLoc)
        Array{Constraint}([DirectConstraint(t1, t2)])
    else
        Array{Constraint}([DirectConstraint(t1.data, t2)])
    end
end
function imply_unify_(t1::Term, t2::Term)::Imply_res # base case
    if t1 == t2
        Array{Constraint}([])
    elseif typeof(t1) === TLoc || typeof(t2) === TLoc
        Array{Constraint}([DirectConstraint(t1, t2)])
    else
        ErrorConstraint(DirectConstraint(t1, t2), Error(err_msg_terms(t1, t2)))
    end
end

swap(c::DirectConstraint) = ReverseConstraint(c.t2, c.t1)
swap(c::ReverseConstraint) = DirectConstraint(c.t2, c.t1)
swap(c::ErrorConstraint) = ErrorConstraint(swap(c.c), c.error)
imply_unify_(c::DirectConstraint)::Imply_res = imply_unify_(c.t1, c.t2)
function imply_unify_(c::ReverseConstraint)::Imply_res
    res = imply_unify_(c.t2, c.t1)
    (res isa ErrorConstraint) ? (res |> swap) : Array{Constraint}(res .|> swap)
end









# Unify: solve f(x) = g(y) in the sense of finding x AND y,
# EXCEPT it WONT fail if post-applying some DROPPINGs here and there will help.
# It WONT RETURN THEM, either. See above.

# idea: in NO CASE x=f(x) can be solved, (if types_ are REDUCED), because we handle RecursiveTypes Differently!!
function check_not_recursive(tloc::TLoc, tt::Term)::Bool
    for v in usedLocsSet(tt) # THIS IS DIFFERENT IN VAR VS VAR_TAG
        if tloc.var_tag == v
            return false
        end # THIS IS DIFFERENT IN VAR VS VAR_TAG
    end
    for v in usedLocs(tt) # THIS IS DIFFERENT IN VAR VS VAR_TAG
        if tloc.var == v
            return false
        end # THIS IS DIFFERENT IN VAR VS VAR_TAG
    end
    return true
end

get_reduc_subst(t::Array{TProd}) = TApp(vcat([t[end]], t[end-1:-1:1] .|> (x -> TAbs(x))))
get_reduc_subst(t::Array{Term}) = TApp(vcat([t[end]], t[end-1:-1:1] .|> (x -> TAbs(x))))
# IMPORTANT: ALL EXCEPT (potentially) the >FIRST< should be TPRODS !!!!!

# ASSOCIATIVE OPERATION to compose the above:
ass_smart_reduc(t...) = (length(t) <= 1) ? (collect(t)) : ([get_reduc_subst(collect(t)) |> reduc])
# TODO: change "[reduc()]" in "smart_reduc" !!
ass_reduc(t::TProd...)::TProd = (length(t) == 1) ? (t[1]) : (get_reduc_subst(collect(t)) |> reduc)
ass_reduc(t1::Term, ts::TProd...)::Term = (length(ts) == 0) ? (t1) : (get_reduc_subst(vcat([t1], collect(ts))) |> reduc)

ass_reduc(c::EqConstraint, ts::TProd...) = EqConstraint(ass_reduc(c.t1, ts...), ass_reduc(c.t2, ts...))
ass_reduc(c::DirectConstraint, ts::TProd...) = DirectConstraint(ass_reduc(c.t1, ts...), ass_reduc(c.t2, ts...))
ass_reduc(c::ReverseConstraint, ts::TProd...) = ReverseConstraint(ass_reduc(c.t1, ts...), ass_reduc(c.t2, ts...))
ass_reduc(c::ErrorConstraint, ts::TProd...) = ErrorConstraint(ass_reduc(c.c, ts...), c.error)

id_data(current_arity) = Array{Term}([TLoc(i) for i in 1:current_arity])
id_tags(current_tags) = Dict{Id,Term}(i => TLocStr(i) for i in current_tags)

struct Arity
    data::Int
    tags::Set{String}
end
get_arity_obj(t::Term) = Arity(t |> arity, t |> usedLocsSet)


function get_subst_prod_data(tloc::TLoc, tt::Term, curr_arity::Arity)::TProd
    # resulting_arity = curr_arity.data - 1
    # you have ALREADY TESTED that tt does not contain tloc, that's the whole point !!!!
    prod = vcat(
        Array{Term}([TLoc(i) for i = 1:(tloc.var-1)]),
        Array{Term}([TLoc(0)]), # Placeholder, complete nonsense, it's getting replaced
        Array{Term}([TLoc(i) for i in (tloc.var:curr_arity.data-1)])
    )
    prod[tloc.var] = ass_reduc(tt, TProd(prod))
    TProd(prod, id_tags(curr_arity.tags))
end  # THIS IS DIFFERENT IN VAR VS VAR_TAG #
function get_subst_prod_tag(tloc::TLocStr, tt::Term, curr_arity::Arity)::TProd
    # you have ALREADY TESTED that tt does not contain tloc, that's the whole point !!!!
    subst = id_tags(curr_arity.tags)
    subst[tloc.var_tag] = tt # i'm PRETENDING THAT tt DOES NOT CONTAIN var_tag
    TProd(id_data(curr_arity.data), subst)
end  # THIS IS DIFFERENT IN VAR VS VAR_TAG #


function share_ctx_tlocs_names(t1::TAbs, t2::TAbs, t1arity::Index, t2arity::Index)
    s1 = TProd(Array{Term}([TLoc(i) for i = 1:t1arity]))
    s2 = TProd(Array{Term}([TLoc(i) for i = (t1arity+1):(t1arity+t2arity)]))
    TApp([s1, t1]), TApp([s2, t2])
end
function share_ctx_tlocs_names_get_substs(t1arity::Index, t2arity::Index)
    s1 = TProd(Array{Term}([TLoc(i) for i = 1:t1arity]))
    s2 = TProd(Array{Term}([TLoc(i) for i = (t1arity+1):(t1arity+t2arity)]))
    s1, s2
end

struct ItsLiterallyAlreadyOk end

function get_first_pair_of_matching_indices(v::Array) #  This changed !!!
    for i = 1:length(v)
        for j = i+1:length(v)
            if v[i] == v[j]
                return (i, j)
            end
        end
    end
    nothing
end
function get_loc_loc_constraint(v)
    for i = 1:length(v)
        if !(v[i] isa ErrorConstraint) && (v[i].t1 isa TLoc && v[i].t2 isa TLoc)
            return i
        end
    end
    nothing
end

@enum Unify_mode meet_ = 1 join_ = 2 imply_ = 3
Succeded_unif_res = Tuple{TProd,TProd,Term}
Failed_unif_res = Tuple{TProd,TProd,Term,Array{ErrorConstraint}}

function do_the_subst_thing!(var_obj, tt, current_arity, current_total_subst, STACK, ERRORSTACK; data::Bool = true)
    new_subst = data ? get_subst_prod_data(var_obj, tt, current_arity) : get_subst_prod_tag(var_obj, tt, current_arity)
    current_total_subst = Array{TProd}(ass_smart_reduc(current_total_subst..., new_subst))
    current_arity = Arity(arity(current_total_subst[end]), usedLocsSet(current_total_subst[end])) # The beauty of this is this is Enough... I HOPE LOL
    for i = 1:length(STACK)
        STACK[i] = ass_reduc(STACK[i], new_subst)
    end
    for i = 1:length(ERRORSTACK)
        ERRORSTACK[i] = ass_reduc(ERRORSTACK[i], new_subst)
    end
    # ^ Really, this is the EASY way:
    # EACH EqConstraint GETS >ALL< SUBSTS, ONE BY ONE, FROM THE MOMENT IT ENTERS THE STACK ONWARD.
    # A Better way would be: TRACK When each Contraint enters the stack. When you Consider that contraint,
    # apply to it the PREASSOCIATED CURRENT_TOTAL_SUBST of the substs it missed After it was created !!!
    # (wait.. That doesnt sound easy, as that means you can NEVER preassociate anything ?)
    current_arity, current_total_subst
end

function robinsonUnify(t1::TAbs, t2::TAbs, t1arity::Arity, t2arity::Arity; unify_tlocs_ctx::Bool = true, mode::Unify_mode = join_)::Union{Succeded_unif_res,Failed_unif_res,ItsLiterallyAlreadyOk}
    there_are_errors::Bool = false

    # 1. Share TLocs
    if unify_tlocs_ctx # THIS IS DIFFERENT IN VAR VS VAR_TAG # IS IT ENOUGH TO NOT DO THIS ???? #
        current_arity = Arity(t1arity.data + t2arity.data, union(t1arity.tags, t2arity.tags))
        t1, t2 = share_ctx_tlocs_names(t1, t2, t1arity.data, t2arity.data)
    else
        # This means Sharing of names has ALREADY HAPPENED !!!
        current_arity = Arity(max(t1arity.data, t2arity.data), union(t1arity.tags, t2arity.tags))
        t1, t2 = t1.body, t2.body
    end

    # 2. unify term and/or produce Eqconstraints
    if mode == imply_
        STACK = Array{Constraint}([DirectConstraint(t1, t2)])
        ERRORSTACK = Array{ErrorConstraint}([])
    else
        t1, t2 = reduc(t1), reduc(t2)
        res = meetjoin_rec_unify_(t1, t2, mode == meet_)
        res_type::Term, STACK = res.res_type, res.cs
        ERRORSTACK = Array{ErrorConstraint}(filter(x -> x isa ErrorConstraint, STACK))
        STACK = filter(x -> !(x isa ErrorConstraint), STACK)
        # NOTE: meetjoin_rec_unify_ WILL return ErrorConstraint's now, about tags.
        if has_errors(res_type)
            there_are_errors = true
        end
    end

    # 3. Solve all constraints:
    current_total_subst = Array{TProd}([]) # SMART_REDUCED VERSION # (Can be a single [TProd] or the whole list)
    # ^ Still, to pass into get_reduc_subst IN THIS ORDER

    # 3.1 Remove all loc-loc constraint first
    while (i = get_loc_loc_constraint(STACK)) !== nothing
        l1, l2 = STACK[i].t1.var, STACK[i].t2.var
        # ^ it WILL break if these are not Ints, which is Exactly what i want. There should be no such constraints between strings.
        deleteat!(STACK, i)
        if l1 == l2
            continue
        end # cannot hurt can it?
        current_arity, current_total_subst = do_the_subst_thing!(TLoc(max(l1, l2)), TLoc(min(l1, l2)), current_arity, current_total_subst, STACK, ERRORSTACK; data = true)
    end

    # 3.2 This while loop is Important for Meeting, while it can be Skipped for directional case
    # POSSIBLE OPTIMIZATION: Keep the TLocs in STACK Sorted, or even in a Dict ofc
    if mode != imply_
        while (ij = get_first_pair_of_matching_indices(STACK .|> (x -> x.t1.var))) !== nothing  # changed !!  get_first_pair_of_matching_indices too !
            tloc, ct1, ct2 = STACK[ij[1]].t1, STACK[ij[1]].t2, STACK[ij[2]].t2
            deleteat!(STACK, ij[2])
            deleteat!(STACK, ij[1])
            if !check_not_recursive(tloc, ct1)
                push!(ERRORSTACK, ErrorConstraint(EqConstraint(tloc, ct1), Error("$(tloc) == $(ct1) is not a thing (recursive)")))
                continue
            end
            if !check_not_recursive(tloc, ct2)
                push!(ERRORSTACK, ErrorConstraint(EqConstraint(tloc, ct2), Error("$(tloc) == $(ct2) is not a thing (recursive)")))
                continue
            end
            res = meetjoin_rec_unify_(ct1, ct2, mode == meet_)
            # Wait.. Are you COMPLETELY SURE you NEVER want a !MODE here ??? ??? ??? ???
            if has_errors(res_type)
                there_are_errors = true
            end
            push!(STACK, EqConstraint(tloc, res.res_type))
            if res.res_type isa TermwError
                there_are_errors = true # : wtf?? I'm missing smthg here .... Where does it go?
            else
                append!(STACK, res.cs)
            end
        end
    end

    # 3.3 Substitute away all the constrains, one by one
    while (length(STACK) > 0)
        c = pop!(STACK)
        ct1, ct2 = c.t1, c.t2
        if !(ct1 isa TLoc || ct2 isa TLoc) && !(ct1 isa TLocStr || ct2 isa TLocStr)
            @assert mode == imply_
            cs_inside = imply_unify_(reduc(c))
            if cs_inside isa ErrorConstraint
                push!(ERRORSTACK, cs_inside)
            else
                append!(STACK, cs_inside)
            end
            continue
        elseif ct1 isa TLocStr && ct2 isa TLocStr
            # NOTE: it would be NICE if i reworked Imply_ mode so that this DOESNT happen ... println("Does locloc Still happen? Ever ????? (Here, w/ $(ct1) and $(ct2))")
            if !(ct1.var_tag == ct2.var_tag) # cannot hurt can it?
                # throw(DomainError("This never happens.. Right.. Right?? $(ct1) required to be $(ct2)"))
                push!(ERRORSTACK, ErrorConstraint(c, "You are asking to unify these names, which is not a thing"))
            end
            # var, tt = ct1.var, ct2 # it's ARBITRARY since these names have no meaning anyway
        elseif ct1 isa TLoc && ct2 isa TLoc
            # NOTE: it would be NICE if i reworked Imply_ mode so that this DOESNT happen ... println("Does locloc Still happen? Ever ????? (Here, w/ $(ct1) and $(ct2))")
            if !(ct1.var == ct2.var)
                current_arity, current_total_subst = do_the_subst_thing!(ct1, ct2, current_arity, current_total_subst, STACK, ERRORSTACK; data = true)
            end
        elseif ct1 isa TLocStr
            @assert !(ct2 isa TLoc)
            if !check_not_recursive(ct1, ct2)
                push!(ERRORSTACK, ErrorConstraint(EqConstraint(ct1, ct2), Error("$(ct1) == $(ct2) is not a thing (recursive)")))
                continue
            end
            current_arity, current_total_subst = do_the_subst_thing!(ct1, ct2, current_arity, current_total_subst, STACK, ERRORSTACK; data = false)
        elseif ct2 isa TLocStr
            @assert !(ct1 isa TLoc)
            if !check_not_recursive(ct2, ct1)
                push!(ERRORSTACK, ErrorConstraint(EqConstraint(ct2, ct1), Error("$(ct2) == $(ct1) is not a thing (recursive)")))
                continue
            end
            current_arity, current_total_subst = do_the_subst_thing!(ct2, ct1, current_arity, current_total_subst, STACK, ERRORSTACK; data = false)
        elseif ct1 isa TLoc
            @assert !(ct2 isa TLocStr)
            if !check_not_recursive(ct1, ct2)
                push!(ERRORSTACK, ErrorConstraint(EqConstraint(ct1, ct2), Error("$(ct1) == $(ct2) is not a thing (recursive)")))
                continue
            end
            current_arity, current_total_subst = do_the_subst_thing!(ct1, ct2, current_arity, current_total_subst, STACK, ERRORSTACK; data = true)
        elseif ct2 isa TLoc
            @assert !(ct1 isa TLocStr)
            if !check_not_recursive(ct2, ct1)
                push!(ERRORSTACK, ErrorConstraint(EqConstraint(ct2, ct1), Error("$(ct2) == $(ct1) is not a thing (recursive)")))
                continue
            end
            current_arity, current_total_subst = do_the_subst_thing!(ct2, ct1, current_arity, current_total_subst, STACK, ERRORSTACK; data = true)
        end
    end

    if length(current_total_subst) == 0 && !there_are_errors && length(ERRORSTACK) == 0
        return ItsLiterallyAlreadyOk()
    elseif length(current_total_subst) == 0
        res_type = if (mode == imply_)
            TGlob("O")
        else
            res_type
        end
        return Failed_unif_res([TProd(Array{Term}([])), TProd(Array{Term}([])), res_type, ERRORSTACK])
    end
    final_subst = ass_reduc(current_total_subst...)
    subst1 = TProd(final_subst.data[1:t1arity.data], final_subst.data_tags)
    subst2 = if unify_tlocs_ctx
        TProd(final_subst.data[(t1arity.data+1):(t1arity.data+t2arity.data)], final_subst.data_tags)
    else
        TProd(final_subst.data[1:t2arity.data], final_subst.data_tags)
    end
    # subst1, subst2 = final_subst, final_subst
    res_type = if (mode == imply_)
        TGlob("O") # Why nothing: USE >>t2<< ( The Original one, NOT the Shared version)
    else
        ass_reduc(res_type, final_subst)
    end

    if there_are_errors || length(ERRORSTACK) > 0
        return Failed_unif_res([subst1, subst2, res_type, ERRORSTACK])
    else
        return Succeded_unif_res([subst1, subst2, res_type])
    end
end

# The following handles ALL THE CONFUSION ARISING FROM having or not having the Forall() at random.
robinsonUnify(t1::TAbs, t2::Term, t1arity::Arity, t2arity::Arity; unify_tlocs_ctx::Bool = true, mode::Unify_mode = join_) = robinsonUnify(t1, TAbs(t2), t1arity, t2arity; unify_tlocs_ctx = unify_tlocs_ctx, mode = mode)
robinsonUnify(t1::Term, t2::TAbs, t1arity::Arity, t2arity::Arity; unify_tlocs_ctx::Bool = true, mode::Unify_mode = join_) = robinsonUnify(TAbs(t1), t2, t1arity, t2arity; unify_tlocs_ctx = unify_tlocs_ctx, mode = mode)
function robinsonUnify(t1::Term, t2::Term, t1arity::Arity, t2arity::Arity; unify_tlocs_ctx::Bool = true, mode::Unify_mode = join_)
    if (t1arity == 0) && (t2arity == 0)
        return true #(t1 == t2) ? (TProd([]), TProd([])) : Error(" Not unifiable: $(t1) != $(t2)")
    else
        return robinsonUnify(TAbs(t1), TAbs(t2), t1arity::Arity, t2arity::Arity; unify_tlocs_ctx = unify_tlocs_ctx, mode = mode)
    end
end


# All cases WITHOUT precomputed tarities:
robinsonUnify(t1::TAbs, t2::TAbs; unify_tlocs_ctx::Bool = true, mode::Unify_mode = join_) = robinsonUnify(t1, t2, t1.body |> get_arity_obj, t2.body |> get_arity_obj; unify_tlocs_ctx = unify_tlocs_ctx, mode = mode)
robinsonUnify(t1::TAbs, t2::Term; unify_tlocs_ctx::Bool = true, mode::Unify_mode = join_) = robinsonUnify(t1, TAbs(t2), t1.body |> get_arity_obj, t2 |> get_arity_obj; unify_tlocs_ctx = unify_tlocs_ctx, mode = mode)
robinsonUnify(t1::Term, t2::TAbs; unify_tlocs_ctx::Bool = true, mode::Unify_mode = join_) = robinsonUnify(TAbs(t1), t2, t1 |> get_arity_obj, t2.body |> get_arity_obj; unify_tlocs_ctx = unify_tlocs_ctx, mode = mode)
robinsonUnify(t1::Term, t2::Term; unify_tlocs_ctx::Bool = true, mode::Unify_mode = join_) = robinsonUnify(TAbs(t1), TAbs(t2), t1 |> get_arity_obj, t2 |> get_arity_obj; unify_tlocs_ctx = unify_tlocs_ctx, mode = mode)




# Type inference

# IMPORTANT: I'm using TTerm's for carrying around contexts, but PLEASE make sure it's always TTerm OF A TPROD...

TTermEmpty(res_type::Term) = TTerm(TProd(Array{Term}([])), res_type)

function infer_type_(term::TLoc)::Term
    TTerm(TProd(Array{Term}([TLoc(i) for i = 1:term.var])), TLoc(term.var))
end #  (but also kinda this is right)
function infer_type_(term::TLocStr)::Term
    return TTerm(TProd(Dict{Id,Term}(term.var_tag => TLoc(1))), term)  # TAbs(TLoc(term.var)) was an idea i tried
end #  (but also kinda this is right)
function infer_type_(term::TGlob)::Term
    if term.type isa TAbs
        return TTermEmpty(term.type.body)
        # ^ This is because TTerm's are Naked (no Forall) for some reason- BOY will this become a mess
    else
        return TTermEmpty(term.type)
    end
end
function infer_type_(term::TTop)::Term
    return TTermEmpty(TTop())
end
function infer_type_(term::TAnno, t_computed::TTerm)::Term # IMPORTANT: if an error comes up, THIS FUNCTION will turn res into TermwError
    substs = robinsonUnify(t_computed.t_out, term.type, mode = imply_)
    if substs isa ItsLiterallyAlreadyOk
        return TTerm(t_computed.t_in, term.type)
    end
    term_type = if term.type isa TAbs
        term.type.body
    else
        term.type
    end   # Oh fuck what am i doing
    args = if (t_computed.t_in.data |> length == 0)
        TProd(Array{Term}([]))
    else
        ass_reduc(t_computed.t_in, substs[1])
    end  # HOPEFULLY this is a Type, NOT a body
    res = TTerm(args, ass_reduc(term_type, substs[2]))
    if substs isa Failed_unif_res
        res = TermwError(res, Error("Wrong annotation: " * get_string(subst[4])))
    end
    # NOTE^ :  mode=imply_ doesnt even return a res_type, even less one with an error! Of course
    res
end

function infer_type_(term::TProd, ts_computed::Array{TTerm})::Term # IMPORTANT: if an error comes up, THIS FUNCTION will turn res into TermwError
    # IDEA: This checking that all args are the same, really belongs to the DIAGONAL FUNCTOR of terms,
    # but this is a hodgepodge, so that's fine.
    # @assert length(term.data) == length(ts_computed) "$(length(term.data)) != $(length(ts_computed)) in $(term.data) != $(ts_computed)"
    # ^ i REALLY WANT to have this, except that HORRIBLE HACK in infer(TApp) passes an EMPTY EPROD here...

    # IDEA: if max_eargs_length == 0, you STILL have to UNIFY the TLocs, which is currenty done by
    # JUST RUNNING robinsonUnify on the Empty prods, and using that behaviour.
    unified_RES_types::Array{Term} = Array{Term}([ts_computed[1].t_out])
    args, full_arity = ts_computed[1].t_in, Arity(ts_computed[1] |> arity, ts_computed[1] |> usedLocsSet)
    all_errors = Array{ErrorConstraint}([])
    for t in ts_computed[2:end]
        s1, s2 = share_ctx_tlocs_names_get_substs(full_arity.data, t |> arity)
        args, t = ass_reduc(args, s1), ass_reduc(t, s2)
        unified_RES_types = unified_RES_types .|> (x -> ass_reduc(x, s1))
        #  # Not sharing vars
        full_arity = Arity(max(args |> arity, t |> arity), union(args |> usedLocsSet, t |> usedLocsSet))
        res = robinsonUnify(
            TAbs(args), TAbs(t.t_in), full_arity, full_arity;
            unify_tlocs_ctx = false, mode = meet_)
        # if res isa Failed_unif_res
        #     return Error("ELocs typed $(t.arg_types .|> pr) cannot be unified into ELocs typed $(args.arg_types .|> pr), with error '$(res)'")
        if res isa ItsLiterallyAlreadyOk
            push!(unified_RES_types, t.t_out)
            full_arity = Arity(max(args |> arity, t |> arity), union(args |> usedLocsSet, t |> usedLocsSet))
            continue
        end
        if res isa Failed_unif_res
            s1, s2, meeted, errors = res
            append!(all_errors, errors)
            # : if has_errors(meeted) # Dunno what to do :(
        else
            s1, s2, meeted = res
        end
        args = meeted
        unified_RES_types = unified_RES_types .|> (x -> ass_reduc(x, s1)) # if they BECAME EQUAL to the stuff "args" comes from, this should work.. No?
        push!(unified_RES_types, ass_reduc(t.t_out, s2))
        full_arity = Arity(max(s1 |> arity, s2 |> arity), union(s1 |> usedLocsSet, s2 |> usedLocsSet)) # god i HOPE this makes sense.....
    end
    res = TTerm(args, TProd(Array{Term}(unified_RES_types)))
    if length(all_errors) > 0 # Or there's some error into res !!
        res = TermwError(res, Error("Impossible to unify args of this prod: " * get_string(all_errors)))
    end
    res
end

function infer_type_(term::TAbs, t_computed::TTerm)::Term
    return TTerm(TProd(Array{Term}([])), t_computed)
end
function infer_type_(term::TSumTerm, t_computed::TTerm)::Term
    arT, tag = t_computed |> arity, term.tag
    types = vcat([TLoc(n) for n = (arT+1):(arT+tag-1)], [t_computed.t_out])
    return TTerm(t_computed.t_in, TAbs(TSum(types)))
end
function infer_type_(term::TBranches, t_computed::TTerm)::Term
    arT, tag = t_computed |> arity, term.tag
    types = vcat([TLoc(n) for n = (arT+1):(arT+tag-1)], [t_computed.t_out])
    return TTerm(t_computed.t_in, TAbs(TSum(types)))
end


function infer_type_(term::TApp, ts_computed::Array{TTerm})::Term
    # First, fix TLoc's by SQUASHING THEM TO BE TTERMS.
    # Idea: - TAbs come as TTErms (TTerm with NO dependencies)  - ELocs come as InfRes WITH the dependency  - NONE of the TTerm have a Forall around cuz it's how it is in this mess
    ts_computed_2 = Array{TTerm}([ts_computed[1]])
    for t in ts_computed[2:end]
        fake_tterm = TAbs(TTerm(TLoc(1), TLoc(2)))
        tterm_subst = robinsonUnify(t.t_out, fake_tterm, t |> get_arity_obj, fake_tterm.body |> get_arity_obj; mode = imply_)
        # NOTE^ :  mode=imply_ doesnt even return a res_type, even less one with an error! Of course
        if tterm_subst isa Failed_unif_res
            return TermwError(TApp(ts_computed .|> (x -> x.t_out)), Error("Calling non function: " * get_string(tterm_subst[4]))) #y'know what? Yes this is violent.. I don't care
        elseif tterm_subst isa ItsLiterallyAlreadyOk
            push!(ts_computed_2, t)
        else
            push!(ts_computed_2, ass_reduc(t, tterm_subst[1])) # t.t_out SHOULD be nothing else but a TTerm... RIGTH?
        end
    end
    # ^ Each of these still has ITS OWN TLoc's

    # Second, Unify the context of the TLocs:
    all_w_unified_args = infer_type_(TProd(Array{Term}([])), ts_computed_2)
    # ^ REUSING the TProd inference, HACKING the fact that Term is NOT used
    # What comes out is a: TTerm(TProd(Array{Term}([...])), TProd(Array{Term}(([TTerm(), ...]))))
    full_arity = all_w_unified_args |> get_arity_obj
    # ^Can i compute this in some smarter way?  # Dunno !
    args, tterms = all_w_unified_args.t_in, all_w_unified_args.t_out.data
    # ^ ts_computed_out becomes array and args remains TProd.. What a mess
    all_errors = Array{ErrorConstraint}([])
    # Third, actually unify all in/outs:
    prev_out = tterms[1] #  fix when app is not a mess anymore
    for i = 2:length(tterms)
        next_in = tterms[i].t_in # YES this always exists now
        substs = robinsonUnify(
            TAbs(prev_out), TAbs(next_in), full_arity, full_arity; unify_tlocs_ctx = false, mode = imply_)
        # : i DONT LIKE these TAbs, it's WRONG, but, it's the only way of accessing unify_tlocs_ctx atm
        # NOTE^ :  mode=imply_ doesnt even return a res_type, even less one with an error! Of course
        if substs isa ItsLiterallyAlreadyOk
            prev_out = tterms[i].t_out
        else
            if substs isa Failed_unif_res
                append!(all_errors, substs[4])
            end
            (s1, s2) = substs
            # ^ Wait.. Are you telling me, if unify_tlocs_ctx=false, s1 and s2 are ALWAYS the same ???  # # Man, this is a crazy world..
            tterms = ass_reduc(TProd(Array{Term}(tterms)), s1).data
            # ^ the LENGTH of tterms DOES NOT CHANGE HERE
            # ^ Also Maybe you can SKIP updating all of them but who cares
            args = ass_reduc(args, s1) # Keep track of the Arg types, too
            full_arity = s1 |> get_arity_obj
            prev_out = tterms[i].t_out
            # Error("Mismatched app: get out type $(prev_out |> pr) but required type $(next_in |> pr), with error '$()'")
        end
    end
    res = TTerm(args, tterms[end].t_out)
    if length(all_errors) > 0
        res = TermwError(res, Error("Type of the application don't match: " * get_string(all_errors)))
    end
    # Returns the OUTPUT type instead of the composed TTerm type cuz this is a mess
    res
end



# Silly categorical-algebra-ish recursive wrapup:
function infer_type_rec(term::TLoc)::Term
    return infer_type_(term)
end
function infer_type_rec(term::TLocStr)::Term
    return infer_type_(term)
end
function infer_type_rec(term::TGlob)::Term
    return infer_type_(term)
end
function infer_type_rec(term::TTop)::Term
    return infer_type_(term)
end
function infer_type_rec(term::TAnno)::Term # IMPORTANT: if an error comes up, THIS FUNCTION will turn res into TermwError
    tt = infer_type_rec(term.expr)
    # return (tt isa Error) ? tt : infer_type_(term, tt)
    return infer_type_(term, tt)
end
function infer_type_rec(term::TAbs)::Term
    tt = infer_type_rec(term.body)
    return (tt isa Error) ? tt : infer_type_(term, tt)
end
function infer_type_rec(term::TProd)::Term
    tts::Array{Union{TTerm,Error}} = infer_type_rec.(term.data)
    # for tt in tts if tt isa Error return tt end end
    return infer_type_(term, Array{TTerm}(tts))
end
function infer_type_rec(term::TSumTerm)::Term
    tt = infer_type_rec(term.data)
    return (tt isa Error) ? tt : infer_type_(term, tt)
end
function infer_type_rec(term::TBranches)::Term
    tts = infer_type_rec.(term.ops_chances)
    # for tt in tts if tt isa Error return tt end end
    return infer_type_(term, Array{TTerm}(tts))
end
function infer_type_rec(term::TApp)::Term # IMPORTANT: if an error comes up, THIS FUNCTION will turn res into TermwError
    tts::Array{Union{TTerm,Error}} = infer_type_rec.(term.ops_dot_ordered)
    # for tt in tts if tt isa Error return tt end end
    return infer_type_(term, Array{TTerm}(tts))
end


# *unification*, thproving_1.jl, mylambda1_dep.jl