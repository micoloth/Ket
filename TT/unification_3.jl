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



# a join b  ==  a v b  ==  a<avb, b<avb  ==  a CAN BECOME a join b, b CAN BECOME a join b


include("mylambda1.jl")


struct SparseSubst
    t1::TLoc
    t2::Term
end
Base.:(==)(a::SparseSubst, b::SparseSubst) = (a.t1 == b.t1) && (a.t2 == b.t2)
reduc(c::SparseSubst) = SparseSubst(reduc(c.t1), reduc(c.t2))
pr(c::SparseSubst)::String = pr(c.t1) * "==" * pr(c.t2)

Error = String
struct ErrorConstraint
    t1::Term
    t2::Term
    error::Error
end
ErrorC(t1::Term, t2::Term, msg)::ErrorConstraint = ErrorConstraint(t1, t2, msg(t1, t2))
pr(a::Array{ErrorConstraint}) = a .|> (x -> "Can't unify $(x.t1 |>pr) and $(x.t2 |>pr): $(x.error)") |> (x -> join(x, ", "))

struct RecUnifyRes
    preSubst::Array{SparseSubst} # I'm gonna REGRET that this is one array instead of 2 substs... # BUT, for now it's like this.
    postSubst1::Term
    postSubst2::Term
    res::Term # OR would be better if each one had its own?  --> NOTE: maybe i can still template it?
    errors::Array{ErrorConstraint}
end
RecUnifyRes(res::Term) = RecUnifyRes([], TLocInt(1), TLocInt(1), res, [])
RecUnifyRes(res::Term, preSubst::Array{SparseSubst}) = RecUnifyRes(preSubst, TLocInt(1), TLocInt(1), res, [])
RecUnifyRes(res::Term, e::ErrorConstraint) = RecUnifyRes([], TLocInt(1), TLocInt(1), res, [e])
RecUnifyResErr(res::Term, e::ErrorConstraint) = RecUnifyRes([], TLocInt(1), TLocInt(1), TermwError(res, e.error), [e])
merge_res(rs::Array{RecUnifyRes}, how) = merge_res(rs, how(Array{Term}(rs .|> x->x.res)))
merge_res(rs::Array{RecUnifyRes}, res::Term) = RecUnifyRes(vcat((rs.|> x->x.preSubst)...), TLocInt(1), TLocInt(1), res, vcat((rs.|> x->x.errors)...))


err_msg_app(t1::TApp, t2::TApp) = "Different bodies: $(length(t1.ops_dot_ordered)) != $(length(t2.ops_dot_ordered))"
err_msg_lambdas(t1::TAbs, t2::TAbs) = "Different lambdas $(pr(t1)) != $(pr(t2)): I know I'm being picky, but impossible to tell if these are the same: $([t1.body, t2.body])"
err_msg_sumtags(t1::TSumTerm, t2::TSumTerm) = "For now, you can NEVER unify different tags: $(t1.tag_name) != $(t2.tag_name)"
err_msg_terms(t1::Term, t2::Term) = "Different: $(pr(t1)) is really different from $(pr(t2))"
err_msg_prods(t1::TProd, t2::TProd) = "Different lengths: $(length(t1.data)) < $(length(t2.data)), so you cannot even drop."
err_msg_prods_tags(t1::TProd, t2::TProd) = "Some tags are in second, not in first: $(t1.data_tags .|> (x->x[1]))) < $(t2.data_tags .|> (x->x[1]))), so you cannot even drop them."
err_msg_sums(t1::TSum, t2::TSum) = "Different lengths: $(length(t1.data)) > $(length(t2.data)), so if you are in the last case you are screwed.."
err_msg_tags(t1::TProd, t2::TProd) = "You cant unify var_tags: $(t1) != $(t2)."
err_msg_intsum(t1::TIntSum, t2::TIntSum) = "Different lengths: $(length(t1.ns)) > $(length(t2.ns)), so impossible to tell if these are the same..."
err_msg_intprod(t1::TIntProd, t2::TIntProd) = "Different lengths: $(length(t1.ns)) > $(length(t2.ns)), so impossible to tell if these are the same..."
err_msg_append(t1::TAppend, t2::TAppend) = "Different lengths: $(length(t1.prods)) > $(length(t2.prods)), so impossible to tell if these are the same..."
err_msg_int(t1::TInt, t2::TInt) = "$(t1.n) > $(t2.n), so as types, you really cant do this coercion.."
err_msg_ttop(t1::Term, t2::TTop) = "A generic $(t2) cannot be forced to be a $(t1|>pr)..."
err_msg_ttop(t1::TTop, t2::Term) = "A generic $(t1) cannot be forced to be a $(t2|>pr)..."
err_msg_strings(t1::Term, t2::Term) = "Different strings"
err_msg_recursive(tloc, t) = Error("$(tloc) == $(t) is not a thing (recursive)")


append!([1,2], [1,3], [3,4])


@enum Unify_mode meet_ = 1 join_ = 2 implydir_ = 3 implyrev_ = 4
flip_dic = Dict{Unify_mode, Unify_mode}(meet_=> join_, join_=>meet_, implydir_=>implyrev_, implyrev_=>implydir_)
flip(m::Unify_mode) = flip_dic[m]
reverse_dic = Dict{Unify_mode, Unify_mode}(meet_=> meet_, join_=>join_, implydir_=>implyrev_, implyrev_=>implydir_)
reverse(m::Unify_mode) = reverse_dic[m]

function rec_unify_(t1::TApp, t2::TApp, mode::Unify_mode)::RecUnifyRes
    if length(t1.ops_dot_ordered) != length(t2.ops_dot_ordered)
        RecUnifyResErr(t2, ErrorC(t1, t2, err_msg_app))
    else
        all_ress = [rec_unify_(f1, f2, mode) for (f1, f2) in zip(t1.ops_dot_ordered, t2.ops_dot_ordered)]
        merge_res(all_ress, TApp) # DEFAULT postSubst's !!!
    end
end

function rec_unify_(t1::TConc, t2::TConc, mode::Unify_mode)::RecUnifyRes
    if length(t1.ops_dot_ordered) != length(t2.ops_dot_ordered)
        return RecUnifyResErr(t1, ErrorC(t1, t2, err_msg_app))
    end
        all_ress = [rec_unify_(f1, f2, mode) for (f1, f2) in zip(t1.ops_dot_ordered, t2.ops_dot_ordered)]
        merge_res(all_ress, TConc) # DEFAULT postSubst's !!!
end

# CURRENTLY WORNG: concat_(t::TProd...) = TProd(vcat((t .|> (x -> x.data))...), merge((t .|> (x -> x.data_tags))...))
subdict(d::Dict{Id,Term}, keys::Set{Id}) = Dict{Id,Term}(k => d[k] for k in keys)

function rec_unify_(t1::TProd, t2::TProd, mode::Unify_mode)::RecUnifyRes
    data_dict_1, data_dict_2 = Dict{Id, Term}(t1.data_tags), Dict{Id, Term}(t2.data_tags)
    tags_1_not_2, tags_2_not_1 = setdiff(keys(data_dict_1), keys(data_dict_2)), setdiff(keys(data_dict_2), keys(data_dict_1))
    t1l, t2l = t1.data |> length, t2.data |> length
    if mode==implydir_ && (length(t1.data) < length(t2.data) || tags_2_not_1 |> length >0)
        return RecUnifyResErr(t2, ErrorC(t1, t2, err_msg_prods))
    elseif mode==implyrev_ && (length(t1.data) > length(t2.data) || tags_1_not_2 |> length >0)
        return RecUnifyResErr(t2, ErrorC(t1, t2, err_msg_prods))
    end
    shared_tags = intersect(keys(data_dict_1), keys(data_dict_2))
    shared_res = Dict{Id,RecUnifyRes}(tag => rec_unify_(data_dict_1[tag], data_dict_2[tag], mode) for tag in shared_tags)
    shared_res_types = Dict{Id,Term}(tag => res.res for (tag, res) in shared_res)
    res_types_tags = merge(shared_res_types, subdict(data_dict_1, tags_1_not_2), subdict(data_dict_2, tags_2_not_1))
    res_tags_cs::Array{SparseSubst} = vcat((values(shared_res) .|>  x -> x.preSubst)...)
    res_tags_errs::Array{ErrorConstraint} = vcat((values(shared_res) .|>  x -> x.errors)...)

    all_ress = [rec_unify_(f1, f2, mode) for (f1, f2) in zip(t1.data, t2.data)] # Potentially turn into a monad (not really urgent tho)
    # IMPORTANT: zip stops @ the LEAST number of elems!
    res_data_types = Array{Term}(all_ress .|> x -> x.res)
    res_data_cs::Array{SparseSubst} = vcat((all_ress .|> x -> x.preSubst)...)
    res_data_errs::Array{ErrorConstraint} = vcat((all_ress .|> x -> x.errors)...)
    if t1l != t2l && mode==meet_
        additional_elems = (t1l > t2l) ? (t1.data[(t2l+1):end]) : (t2.data[(t1l+1):end])
        res_data_types = vcat(res_data_types, additional_elems)
    end
    RecUnifyRes(vcat(res_tags_cs, res_data_cs), TLocInt(1), TLocInt(1), TProd(res_data_types, [res_types_tags...]), vcat(res_data_errs, res_tags_errs))
    # ^ HERE you can improve postSubst's a lot !!!
end


function rec_unify_(t1::TSum, t2::TSum, mode::Unify_mode)::RecUnifyRes
    t1l, t2l = t1.data |> length, t2.data |> length
    if t1l > t2l && mode==implydir_
        return RecUnifyResErr(t1, ErrorC(t1, t2, err_msg_sums))
    end
    all_ress = [rec_unify_(f1, f2, mode) for (f1, f2) in zip(t1.data, t2.data)] # Potentially turn into a monad (not really urgent tho)
    # IMPORTANT: ^ zip stops @ the LEAST number of elems!
    res_types = all_ress .|> x -> x.res
    errors = findall((x -> x isa TermwError), res_types)
    if t1l != t2l && (mode==join_ || mode==meet_)
        additional_elems = (t1l > t2l) ? (t1.data[(t2l+1):end]) : (t2.data[(t1l+1):end])
        res_types = vcat(res_types, additional_elems)
    end
    res_type = TSum(res_type)
    if length(errors) > 0
        res_type = TermwError(res_type, "E" * join(errors .|> string, ""))
    end
    merge_res(all_ress, res_type)
end


function rec_unify_(t1::TAbs, t2::TAbs, mode::Unify_mode)::RecUnifyRes
    println("Simplyfing two Foralls:")
    # FOR NOW, these will be REALLY PICKY
    if t1 == t2
        RecUnifyRes(t1)
    else
        RecUnifyResErr(t1, ErrorC(t1, t2, err_msg_lambdas))
    end
    # Only accepted case: All constraints are about TLocInt only and THE SAME
    # cons = DirectConstraint(t1.body, t2.body)
    # cons = simplify(cons)
    # is_same(c::Constraint) = (c.t1 isa TLocInt) && (c.t1 == c.t2)
    # if typeof(cons) == Error
    #     Error("Different lambdas: with this error: $(cons)")
    # elseif length(cons) == 0 || (cons .|> is_same |> all)
    #     Array{SparseSubst}([])
    # else
    #     Error("Different lambdas $(pr(t1)) != $(pr(t2)): I know I'm being picky, but impossible to simplify this part: $(cons)")
    # end
end

function rec_unify_(t1::TTerm, t2::TTerm, mode::Unify_mode)::RecUnifyRes
    res_out = rec_unify_(t1.t_out, t2.t_out, mode)
    res_in = rec_unify_(t1.t_in, t2.t_in, flip(mode))
    RecUnifyRes(TTerm(res_in.res, res_out.res), vcat(res_out.preSubst, res_in.preSubst))
end
function rec_unify_(t1::TSumTerm, t2::TSumTerm, mode::Unify_mode)::RecUnifyRes
    if t1.tag != t2.tag
        return RecUnifyResErr(t1, ErrorC(t1, t2, err_msg_sumtags))
        # ^ You MIGHT want to return constraints for t1 and t2 all the same, but i'm NOT doing it...
    else
        res = rec_unify_(t1.data, t2.data, mode) # Wait.... Is this even right? How does a type-level sum play with type-level Locs ???
        return RecUnifyRes(TSumTerm(t1.tag, t1.tag_name, res.res), res.preSubst)
    end
end
function rec_unify_(t1::TLoc, t2::TSumTerm, mode::Unify_mode)::RecUnifyRes
    # This behaviour is pretty weird admiddetly, and it simply says: SCREW TAG, essentially
    RecUnifyRes(t1, Array{SparseSubst}([SparseSubst(t1, t2)]))
end
function rec_unify_(t1::Term, t2::TSumTerm, mode::Unify_mode)::RecUnifyRes
    res = rec_unify_(t1, t2.data, mode) # Wait.... Is this even right? How does a type-level sum play with type-level Locs ???
    RecUnifyRes(TSumTerm(t2.tag, t2.tag_name, res.res), res.preSubst)
end
function rec_unify_(t1::TSumTerm, t2::TLoc, mode::Unify_mode)::RecUnifyRes
    # This behaviour is pretty weird admiddetly, and it simply says: SCREW TAG, essentially
    RecUnifyRes(t2, Array{SparseSubst}([SparseSubst(t2, t1)]))
    # TODOTODO: This relies HEAVILY on the fact that names have been UNIFIED between t1 and t2. Is this ALWAYS what we want ???
end
function rec_unify_(t1::TSumTerm, t2::Term, mode::Unify_mode)::RecUnifyRes
    res = rec_unify_(t1.data, t2, mode) # Wait.... Is this even right? How does a type-level sum play with type-level Locs ???
    RecUnifyRes(TSumTerm(t1.tag, t1.tag_name, res.res), res.preSubst)
end
function rec_unify_(t1::TLoc, t2::TLoc, mode::Unify_mode)::RecUnifyRes
    if t1.var == t2.var # t1.var == t2.var
        RecUnifyRes(t2)
    elseif t1 isa TLocStr && t2 isa TLocStr
        RecUnifyResErr(t2, ErrorC(t1, t2, err_msg_tags))# Uhhh How about return an error ??? ???
        # ^ For some reason, i DONT want to substitute away var tags for now ...
    elseif t1 isa TLocStr  # prefer substituting away numbers wrt strings
        RecUnifyRes(t1, Array{SparseSubst}([SparseSubst(t2, t1)]))
        # TODOTODO: This relies HEAVILY on the fact that names have been UNIFIED between t1 and t2. Is this ALWAYS what we want ???
    elseif t2 isa TLocStr  # prefer substituting away numbers wrt strings
        RecUnifyRes(t2, Array{SparseSubst}([SparseSubst(t1, t2)]))
        # TODOTODO: This relies HEAVILY on the fact that names have been UNIFIED between t1 and t2. Is this ALWAYS what we want ???
    else
        RecUnifyRes(TLocInt(min(t1.var,t2.var)), Array{SparseSubst}([SparseSubst(TLocInt(max(t1.var,t2.var)), TLocInt(min(t1.var,t2.var)))]))
    end
end
function rec_unify_(t1::TLoc, t2::Term, mode::Unify_mode)::RecUnifyRes
    if !check_not_recursive(t1, t2)
        RecUnifyResErr(t2, ErrorC(t1, t2, err_msg_recursive))
    else
        RecUnifyRes(t2, Array{SparseSubst}([SparseSubst(t1, t2)]))
    end
end
function rec_unify_(t1::Term, t2::TLoc, mode::Unify_mode)::RecUnifyRes
    if !check_not_recursive(t2, t1)
        RecUnifyResErr(t1, ErrorC(t2, t1, err_msg_recursive))
    else
        RecUnifyRes(t1, Array{SparseSubst}([SparseSubst(t2, t1)]))
    end
    # TODOTODO: This relies HEAVILY on the fact that names have been UNIFIED between t1 and t2. Is this ALWAYS what we want ???
end


function rec_unify_(t1::Term, t2::TTop, mode::Unify_mode)::RecUnifyRes
    if mode === meet_ RecUnifyRes(t1)
    elseif mode === join_ RecUnifyRes(t2)
    elseif mode === implydir_ RecUnifyRes(t2)
    elseif mode === implyrev_ RecUnifyResErr(t1, ErrorC(t1, t2, err_msg_ttop))
    end
end
function rec_unify_(t1::TTop, t2::Term, mode::Unify_mode)::RecUnifyRes
    rec_unify_(t2, t1, reverse(mode))
end
function rec_unify_(t1::TInt, t2::TInt, mode::Unify_mode)::RecUnifyRes
    if mode === meet_ RecUnifyRes(TInt(min(t1.n, t2.n)))
    elseif mode === join_ RecUnifyRes(TInt(max(t1.n, t2.n)))
    elseif mode === implydir_
        t1.n >= t2.n ? RecUnifyRes(t2) : RecUnifyResErr(t2, ErrorC(t1, t2, err_msg_int))
    elseif mode === implyrev_
        t1.n <= t2.n ? RecUnifyRes(t1) : RecUnifyResErr(t1, ErrorC(t1, t2, err_msg_int))
    end
end
function rec_unify_(t1::TInt, t2::TN, mode::Unify_mode)::RecUnifyRes# VERY VERY CRUCIAL !!!
    if mode === meet_ RecUnifyRes(t1)
    elseif mode === join_ RecUnifyRes(t2)
    elseif mode === implydir_ RecUnifyRes(t2)
    elseif mode === implyrev_ RecUnifyResErr(t1, ErrorC(t1, t2, err_msg_ttop))
    end
end
function rec_unify_(t1::TN, t2::TInt, mode::Unify_mode)::RecUnifyRes
    rec_unify_(t2, t1, reverse(mode))
end
function rec_unify_(t1::TStr, t2::TStr, mode::Unify_mode)::RecUnifyRes
    if t1.s == t2.s RecUnifyRes(t1)
    else RecUnifyRes(t1, ErrorC(t1, t2, err_msg_strings))
    end
end
function rec_unify_(t1::TN, t2::TN, mode::Unify_mode)::RecUnifyRes
    RecUnifyRes(TN())
end
function rec_unify_(t1::TS, t2::TS, mode::Unify_mode)::RecUnifyRes
    RecUnifyRes(TS())
end
function rec_unify_(t1::TIntSum, t2::TIntSum, mode::Unify_mode)::RecUnifyRes
    if length(t1.ns) != length(t2.ns)
        return RecUnifyResErr(t1, ErrorC(t1, t2, err_msg_intsum))
    end
    all_ress = [rec_unify_(f1, f2, mode) for (f1, f2) in zip(t1.ns, t2.ns)]
    RecUnifyRes(TIntSum(all_ress .|> x -> x.res), vcat((all_ress .|> x -> x.preSubst)...))
end
function rec_unify_(t1::TIntProd, t2::TIntProd, mode::Unify_mode)::RecUnifyRes
    if length(t1.ns) != length(t2.ns)
        return RecUnifyResErr(t1, ErrorC(t1, t2, err_msg_intprod))
    end
    all_ress = [rec_unify_(f1, f2, mode) for (f1, f2) in zip(t1.ns, t2.ns)]
    RecUnifyRes(TIntProd(all_ress .|> x -> x.res), vcat((all_ress .|> x -> x.preSubst)...))
end
function rec_unify_(t1::TAppend, t2::TAppend, mode::Unify_mode)::RecUnifyRes
    if length(t1.prods) != length(t2.prods)
        return RecUnifyResErr(t1, ErrorC(t1, t2, err_msg_append))
    end
    all_ress = [rec_unify_(f1, f2, mode) for (f1, f2) in zip(t1.prods, t2.prods)]
    RecUnifyRes(TAppend(all_ress .|> x -> x.res), vcat((all_ress .|> x -> x.preSubst)...))
end

function rec_unify_(t1::Term, t2::Term, mode::Unify_mode)::RecUnifyRes # base case
    if t1 == t2
        RecUnifyRes(t1)
    else
        RecUnifyResErr(t1, ErrorC(t1, t2, err_msg_terms))
    end
end



# Unify: solve f(x) = g(y) in the sense of finding x AND y,
# EXCEPT it WONT fail if post-applying some DROPPINGs here and there will help.
# It WONT RETURN THEM, either. See above.

# idea: in NO CASE x=f(x) can be solved, (if types_ are REDUCED), because we handle RecursiveTypes Differently!!
function check_not_recursive(tloc::TLocStr, tt::Term)::Bool
    for v in usedLocsSet(tt)
        if tloc.var == v
            return false
        end
    end
    return true
end

function check_not_recursive(tloc::TLocInt, tt::Term)::Bool
    for v in usedLocs(tt)
        if tloc.var == v
            return false
        end
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



function ass_reduc(c::SparseSubst, ts::TProd...)
    tloc = ass_reduc(c.t1, ts...)
    @assert tloc isa TLoc
    SparseSubst(tloc, ass_reduc(c.t2, ts...))
end
ass_reduc(c::ErrorConstraint, ts::TProd...) = ErrorConstraint(ass_reduc(c.t1, ts...), ass_reduc(c.t2, ts...), c.error)

id_data(current_arity) = Array{Term}([TLocInt(i) for i in 1:current_arity])
id_tags(current_tags) = Array{Pair{Id, Term}}([i => TLocStr(i) for i in current_tags])
id_tags_tanned(current_tags_w_type::Array{Pair{Id, Term}}) = Array{Pair{Id, TAnno}}([k => Tanno(TLocStr(k), type) for (k,type) in current_tags_w_type])

struct Arity
    data::Int
    tags::Set{String}
end
get_arity_obj(t::Term) = Arity(t |> arity, t |> usedLocsSet)


function get_full_subst(tloc::TLocInt, tt::Term, curr_arity::Arity)::TProd
    # resulting_arity = curr_arity.data - 1
    # you have ALREADY TESTED that tt does not contain tloc, that's the whole point !!!!
    prod = vcat(
        Array{Term}([TLocInt(i) for i = 1:(tloc.var-1)]),
        Array{Term}([TLocInt(0)]), # Placeholder, complete nonsense, it's getting replaced
        Array{Term}([TLocInt(i) for i in (tloc.var:curr_arity.data-1)])
    )
    prod = TProd(prod, id_tags(curr_arity.tags))
    prod.data[tloc.var] = ass_reduc(tt, prod)
    prod
end  # THIS IS DIFFERENT IN VAR VS VAR_TAG #
function get_full_subst(tloc::TLocStr, tt::Term, curr_arity::Arity)::TProd
    # you have ALREADY TESTED that tt does not contain tloc, that's the whole point !!!!
    subst = id_tags(curr_arity.tags)
    subst[findfirst(subst.|> (x->x[1]==tloc.var))] = (tloc.var=>tt) # i'm PRETENDING THAT tt DOES NOT CONTAIN var
    TProd(id_data(curr_arity.data), subst)
end  # THIS IS DIFFERENT IN VAR VS VAR_TAG #
get_full_subst(s::SparseSubst, curr_arity::Arity) = get_full_subst(s.t1, s.t2, curr_arity)

function share_ctx_tlocs_names_get_substs(t1arity::Arity, t2arity::Arity)
    s1 = TProd(Array{Term}([TLocInt(i) for i = 1:t1arity.data]), id_tags(t1arity.tags))
    s2 = TProd(Array{Term}([TLocInt(i) for i = (t1arity.data+1):(t1arity.data+t2arity.data)]), id_tags(t2arity.tags))
    s1, s2
end

struct UnifyRes
    preSubst1::Union{TProd, Nothing}
    preSubst2::Union{TProd, Nothing}
    postSubst1::Union{Term, Nothing}
    postSubst2::Union{Term, Nothing}
    res::Term
    errors::Array{ErrorConstraint}
end
itsLiterallyAlreadyOk(u::UnifyRes) = u.preSubst1===nothing && u.preSubst2===nothing
failed_unif_res(u::UnifyRes) = u.errors|>length >0 || has_errors(u.res)
# TODO: FIX: the fact that  has_errors(u.res) is needed is an ERROR, it means that somewhere drops some ErrorConstraints ....

function do_the_subst_thing!(subst::SparseSubst, current_arity, current_total_subst, STACK, ERRORSTACK)
    if !check_not_recursive(subst.t1, subst.t2)
        # TODO: GOAL: I REALLY WANT TO REMOVE THIS, AND INCLUDE >>ALL<< LOC-LOC CONSTRAINS (in both directions) IN 3.1 STEP !!!
        push!(ERRORSTACK, ErrorC(subst.t1, subst.t2, err_msg_recursive))
        return current_arity, current_total_subst
    end
    new_subst = get_full_subst(subst, current_arity)
    current_total_subst = Array{TProd}(ass_smart_reduc(current_total_subst..., new_subst))
    current_arity = Arity(arity(current_total_subst[end]), usedLocsSet(current_total_subst[end])) # The beauty of this is this is Enough... I HOPE LOL
    for i = 1:length(STACK) STACK[i] = ass_reduc(STACK[i], new_subst) end
    # for i = 1:length(ERRORSTACK) ERRORSTACK[i] = ass_reduc(ERRORSTACK[i], new_subst) end
    # ^ Really, this is the EASY way:
    # EACH EqConstraint GETS >ALL< SUBSTS, ONE BY ONE, FROM THE MOMENT IT ENTERS THE STACK ONWARD.
    # A Better way would be: TRACK When each Contraint enters the stack. When you Consider that contraint,
    # apply to it the PREASSOCIATED CURRENT_TOTAL_SUBST of the substs it missed After it was created !!!
    # (wait.. That doesnt sound easy, as that means you can NEVER preassociate anything ?)
    current_arity, current_total_subst
end


function get_first_pair_of_matching_indices(v::Array)
    for i = 1:length(v)
        for j = i+1:length(v)
            if v[i] == v[j]
                return (i, j)
            end
        end
    end
    nothing
end

function robinsonUnify(t1::TAbs, t2::TAbs, t1arity::Arity, t2arity::Arity; unify_tlocs_ctx::Bool = true, mode::Unify_mode = join_)::UnifyRes

    current_total_subst = Array{TProd}([]) # SMART_REDUCED VERSION # (Can be a single [TProd] or the whole list)
    t1, t2 = t1.body|>reduc, t2.body|>reduc

    # 1. Share TLocs
    if unify_tlocs_ctx # THIS IS DIFFERENT IN VAR VS VAR_TAG # IS IT ENOUGH TO NOT DO THIS ???? #
        current_arity = Arity(t1arity.data + t2arity.data, union(t1arity.tags, t2arity.tags))
        s1, s2 = share_ctx_tlocs_names_get_substs(t1arity, t2arity)
        t2 = ass_reduc(t2, s2) # s1 SHOULD always be Id
    else
        # This means Sharing of names has ALREADY HAPPENED !!!
        current_arity = Arity(max(t1arity.data, t2arity.data), union(t1arity.tags, t2arity.tags))
    end

    # 2. unify term and/or produce Eqconstraints
    res = rec_unify_(t1, t2, mode)
    res_type::Term, STACK, ERRORSTACK = res.res, res.preSubst, res.errors

    # 3. Solve all constraints: Substitute away all the constrains, one by one
    # ^ Still, to pass into get_reduc_subst IN THIS ORDER

    # 3.1 Turn each x=A, x=B into x= meet(say)(A, B)
    while (ij = get_first_pair_of_matching_indices(STACK .|> (x -> x.t1.var))) !== nothing
        tloc, ct1, ct2 = STACK[ij[1]].t1, STACK[ij[1]].t2, STACK[ij[2]].t2
        deleteat!(STACK, ij[2])
        deleteat!(STACK, ij[1])
        unif_res = rec_unify_(ct1, ct2, mode)
        # ^ Wait.. Are you COMPLETELY SURE you NEVER want a !MODE here ??? ??? ??? ???
        push!(STACK, SparseSubst(tloc, unif_res.res))
        if length(unif_res.errors) > 0 append!(ERRORSTACK, unif_res.errors)
        else append!(STACK, unif_res.preSubst)
        end
    end

    # 3.2 simply subst away each constraint.
    while (length(STACK) > 0)
        c = pop!(STACK)
        if c.t1 == c.t2 continue
        elseif c.t1 isa TLocStr && c.t2 isa TLocStr # THIS I DONT WANT, for now:
            push!(ERRORSTACK, ErrorConstraint(c.t1, c.t2, "You are asking to unify these names, which is not a thing"))
            # var, tt = c.t1.var, c.t2 # it's ARBITRARY since these names have no meaning anyway
        else  # i MIGHT want to use DIFFERENT prioritization of who to subst, but NOT NOW.
            current_arity, current_total_subst = do_the_subst_thing!(c, current_arity, current_total_subst, STACK, ERRORSTACK)
        end
    end

    # 4. Cook up result
    s1, s2, res_type = if length(current_total_subst) == 0 && unify_tlocs_ctx
            nothing, (s2.data|> length == 0 ? nothing : s2), res_type
    elseif length(current_total_subst) == 0 && !unify_tlocs_ctx
            nothing, nothing, res_type
    elseif unify_tlocs_ctx
        final_subst = ass_reduc(current_total_subst...);
        ass_reduc(s1, final_subst), ass_reduc(s2, final_subst), ass_reduc(res_type, final_subst)
    else
        final_subst = ass_reduc(current_total_subst...);
        final_subst, final_subst, ass_reduc(res_type, final_subst)
    end
    UnifyRes(s1, s2, nothing, nothing, res_type, ERRORSTACK)
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


InferResTerm = Union{TTerm, TermwError}

InferResTermIn = TTerm
# InferResTermIn = Union{TTerm, TTermwError} # !!!

function infer_type_(term::TLocInt)::InferResTerm
    TTerm(TProd(Array{Term}([TLocInt(i) for i in 1:term.var])), TLocInt(term.var))
end #  (but also kinda this is right)
function infer_type_(term::TLocStr)::InferResTerm
    return TTerm(TProd(Array{Pair{Id, Term}}([term.var => TLocInt(1)])), TLocInt(1))  # TAbs(TLocInt(term.var)) was an idea i tried
end #  (but also kinda this is right)
function infer_type_(term::TGlob)::InferResTerm
    if term.type isa TAbs
        return TTermEmpty(term.type.body)
        # ^ This is because TTerm's are Naked (no Forall) for some reason- BOY will this become a mess
    else
        return TTermEmpty(term.type)
    end
end
function infer_type_(term::TTop)::InferResTerm
    return TTermEmpty(TTop())
end
function infer_type_(term::TInt)::InferResTerm
    return TTermEmpty(term) # ????????????????????????????????????????????
end
function infer_type_(term::TN)::InferResTerm
    return TTermEmpty(TN()) # ????????????????????????????????????????????
end
function infer_type_(term::TStr)::InferResTerm
    return TTermEmpty(TS())
end
function infer_type_(term::TS)::InferResTerm
    return TTermEmpty(TS())
end
function infer_type_rec(term::TS)::InferResTerm
    return infer_type_(term)
end


function infer_type_(term::TAnno, t_computed::InferResTermIn)::InferResTerm # IMPORTANT: if an error comes up, THIS FUNCTION will turn res into TermwError
    unif_res = robinsonUnify(t_computed.t_out, term.type, mode = implydir_)
    if itsLiterallyAlreadyOk(unif_res)
        return TTerm(t_computed.t_in, term.type)
    end
    term_type = if term.type isa TAbs term.type.body
            else term.type end   # Oh fuck what am i doing
    args = if (t_computed.t_in.data |> length == 0) TProd(Array{Term}([]))
            else ass_reduc(t_computed.t_in, unif_res.preSubst1) end  # HOPEFULLY this is a Type, NOT a body
    res = if !(failed_unif_res(unif_res)) TTerm(args, ass_reduc(term_type, unif_res.preSubst2))
            else TermwError(TTerm(args, term_type), Error("Wrong annotation: " * pr(unif_res.errors))) end
    # NOTE^ :  mode=implydir_ doesnt even return a res_type, even less one with an error! Of course
    res
end

function infer_type_(term::TProd, ts_computed::Array{InferResTermIn})::InferResTerm # IMPORTANT: if an error comes up, THIS FUNCTION will turn res into TermwError
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
        s1, s2 = share_ctx_tlocs_names_get_substs(full_arity, t |> get_arity_obj)
        args, t = ass_reduc(args, s1), ass_reduc(t, s2)
        unified_RES_types = unified_RES_types .|> (x -> ass_reduc(x, s1))
        #  # Not sharing vars
        full_arity = Arity(max(s1 |> arity, s2 |> arity), union(s1 |> usedLocsSet, s2 |> usedLocsSet))
        unif_res = robinsonUnify(TAbs(args), TAbs(t.t_in), full_arity, full_arity; unify_tlocs_ctx = false, mode = meet_)
        if itsLiterallyAlreadyOk(unif_res)
            push!(unified_RES_types, t.t_out)
            args = unif_res.res
        else
            s1, s2, args, errors = unif_res.preSubst1, unif_res.preSubst2, unif_res.res, unif_res.errors
            append!(all_errors, errors)
            unified_RES_types = unified_RES_types .|> (x -> ass_reduc(x, s1)) # if they BECAME EQUAL to the stuff "args" comes from, this should work.. No?
            push!(unified_RES_types, ass_reduc(t.t_out, s2))
            full_arity = Arity(max(s1 |> arity, s2 |> arity), union(s1 |> usedLocsSet, s2 |> usedLocsSet)) # god i HOPE this makes sense.....
        end
    end
    res = TTerm(args, TProd(Array{Term}(unified_RES_types)))
    if length(all_errors) > 0 # Or there's some error into res !!
        res = TermwError(res, Error("Impossible to unify args of this prod: " * pr(all_errors)))
    end
    res
end

function infer_type_(term::TAbs, t_computed::InferResTermIn)::InferResTerm
    return TTerm(TProd(Array{Term}([])), t_computed)
end
function infer_type_(term::TSumTerm, t_computed::InferResTermIn)::InferResTerm
    arT, tag = t_computed |> arity, term.tag
    types = vcat([TLocInt(n) for n = (arT+1):(arT+tag-1)], [t_computed.t_out])
    return TTerm(t_computed.t_in, TAbs(TSum(types)))
end
function infer_type_(term::TBranches, t_computed::InferResTermIn)::InferResTerm
    arT, tag = t_computed |> arity, term.tag
    types = vcat([TLocInt(n) for n = (arT+1):(arT+tag-1)], [t_computed.t_out])
    return TTerm(t_computed.t_in, TAbs(TSum(types)))
end

function unify_funcs_to_tterms_(ts_computed)
    ts_computed_2 = Array{TTerm}([])
    for t in ts_computed
        fake_tterm = TTerm(TLocInt(1), TLocInt(2))
        unif_res = robinsonUnify(t.t_out, fake_tterm, t |> get_arity_obj, fake_tterm |> get_arity_obj; mode = implydir_)
        # NOTE^ :  mode=implydir_ doesnt even return a res_type, even less one with an error! Of course
        if failed_unif_res(unif_res)
            return TermwError(TConc(ts_computed .|> (x -> x.t_out)), Error("Calling non function: " * pr(unif_res.errors))) #y'know what? Yes this is violent.. I don't care
        elseif itsLiterallyAlreadyOk(unif_res)
            push!(ts_computed_2, t)
        else
            push!(ts_computed_2, ass_reduc(t, unif_res.preSubst1)) # t.t_out SHOULD be nothing else but a TTerm... RIGTH?
        end
    end
    ts_computed_2
end
function CHECK_unify_terms_to_N_(ts_computed)
    # Checks that the TOut's are SUBTYPES of N !!!!!
    ts_computed_2 = Array{TTerm}([])
    for t in ts_computed
        fake_tterm = TN()
        unif_res = robinsonUnify(t.t_out, fake_tterm, t |> get_arity_obj, fake_tterm |> get_arity_obj; mode = implydir_)
        # NOTE^ :  mode=implydir_ doesnt even return a res_type, even less one with an error! Of course
        if failed_unif_res(unif_res)
            return TermwError(TConc(ts_computed .|> (x -> x.t_out)), Error("Calling non function: " * pr(unif_res.errors))) #y'know what? Yes this is violent.. I don't care
        else # Dont change bloody anything. If it can be N, IT'S OK!!!
            push!(ts_computed_2, t) # t.t_out SHOULD be nothing else but a TTerm... RIGTH?
        end
    end
    ts_computed_2
end


function infer_type_(term::TApp, ts_computed::Array{InferResTermIn})::InferResTerm
    # First, fix TLocInt's by SQUASHING THEM TO BE TTERMS.
    # Idea: - TAbs come as TTErms (TTerm with NO dependencies)  - ELocs come as InfRes WITH the dependency  - NONE of the TTerm have a Forall around cuz it's how it is in this mess
    funcs_ts_to_tterms = unify_funcs_to_tterms_(ts_computed[2:end])
    if funcs_ts_to_tterms isa TermwError return funcs_ts_to_tterms end  #y'know what? Yes this is violent.. I don't care
    ts_computed_2 = vcat(Array{TTerm}([ts_computed[1]]), funcs_ts_to_tterms)
    # ^ Each of these still has ITS OWN TLocInt's

    # Second, Unify the context of the TLocs:
    all_w_unified_args = infer_type_(TProd(Array{Term}([])), ts_computed_2)
    # ^ Yes, believe it or not this unifies the CONTEXTS
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
        unif_res = robinsonUnify(
            TAbs(prev_out), TAbs(next_in), full_arity, full_arity; unify_tlocs_ctx = false, mode = implydir_)
        # : i DONT LIKE these TAbs, it's WRONG, but, it's the only way of accessing unify_tlocs_ctx atm
        # NOTE^ :  mode=implydir_ doesnt even return a res_type, even less one with an error! Of course
        if failed_unif_res(unif_res)
            append!(all_errors, unif_res.errors)
            append!(all_errors, unif_res.res|>errors.|>(x->ErrorConstraint(unif_res.res, unif_res.res, x)))
        end
        if itsLiterallyAlreadyOk(unif_res )
            prev_out = tterms[i].t_out
        else
            (s1, s2) = (unif_res.preSubst1, unif_res.preSubst2)
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
        res = TermwError(res, Error("Type of the application don't match: " * pr(all_errors)))
    end
    # Returns the OUTPUT type instead of the composed TTerm type cuz this is a mess
    res
end

function infer_type_(term::TConc, ts_computed::Array{InferResTermIn})::InferResTerm
    # First, fix TLocInt's by SQUASHING THEM TO BE TTERMS.
    # Idea: - TAbs come as TTErms (TTerm with NO dependencies)  - ELocs come as InfRes WITH the dependency  - NONE of the TTerm have a Forall around cuz it's how it is in this mess
    ts_computed_2 = unify_funcs_to_tterms_(ts_computed)
    if ts_computed_2 isa TermwError return ts_computed_2 end  #y'know what? Yes this is violent.. I don't care

    # ^ Each of these still has ITS OWN TLocInt's

    # Second, Unify the context of the TLocs:
    all_w_unified_args = infer_type_(TProd(Array{Term}([])), ts_computed_2)
    # ^ Yes, believe it or not this unifies the CONTEXTS
    # ^ REUSING the TProd inference, HACKING the fact that Term is NOT used
    # What comes out is a: TTerm(TProd(Array{Term}([...])), TProd(Array{Term}(([TTerm(), ...]))))
    full_arity = all_w_unified_args |> get_arity_obj
    # ^Can i compute this in some smarter way?  # Dunno !
    args, tterms = all_w_unified_args.t_in, all_w_unified_args.t_out.data
    # ^ ts_computed_out becomes array and args remains TProd.. What a mess
    all_errors = Array{ErrorConstraint}([])
    # Third, actually unify all in/outs:
    prev_out = tterms[1].t_out #  the ONLY DIFFERENCE (apart from call to unify_funcs_to_tterms_) with TApp
    for i = 2:length(tterms)
        next_in = tterms[i].t_in # YES this always exists now
        unif_res = robinsonUnify(
            TAbs(prev_out), TAbs(next_in), full_arity, full_arity; unify_tlocs_ctx = false, mode = implydir_)
        # : i DONT LIKE these TAbs, it's WRONG, but, it's the only way of accessing unify_tlocs_ctx atm
        # NOTE^ :  mode=implydir_ doesnt even return a res_type, even less one with an error! Of course
        if failed_unif_res(unif_res)
            append!(all_errors, unif_res.errors)
            append!(all_errors, unif_res.res|>errors.|>(x->ErrorConstraint(unif_res.res, unif_res.res, x)))
        end
        if itsLiterallyAlreadyOk(unif_res)
            prev_out = tterms[i].t_out
        else
            (s1, s2) = (unif_res.preSubst1, unif_res.preSubst2)
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
    res = TTerm(args, TTerm(tterms[1].t_in, tterms[end].t_out))
    if length(all_errors) > 0
        res = TermwError(res, Error("Type of the application don't match: " * pr(all_errors)))
    end
    # Returns the OUTPUT type instead of the composed TTerm type cuz this is a mess
    res
end

function infer_type_(term::TIntSum, ts_computed::Array{InferResTermIn})::InferResTerm
    # First, CHECK THAT ALL TOut's CAN be N:
    ts_computed_2 = CHECK_unify_terms_to_N_(ts_computed)
    if ts_computed_2 isa TermwError return ts_computed_2 end  #y'know what? Yes this is violent.. I don't care
    # ^ Each of these still has ITS OWN TLocInt's

    # Second, Unify the context of the TLocs:
    all_w_unified_args = infer_type_(TProd(Array{Term}([])), ts_computed_2)
    # ^ Yes, believe it or not this unifies the CONTEXTS  # ^ REUSING the TProd inference, HACKING the fact that Term is NOT used
    all_w_unified_args # Wait... Is this right ????????
end
function infer_type_(term::TIntProd, ts_computed::Array{InferResTermIn})::InferResTerm
    # First, CHECK THAT ALL TOut's CAN be N:
    ts_computed_2 = CHECK_unify_terms_to_N_(ts_computed)
    if ts_computed_2 isa TermwError return ts_computed_2 end  #y'know what? Yes this is violent.. I don't care
    # ^ Each of these still has ITS OWN TLocInt's

    # Second, Unify the context of the TLocs:
    all_w_unified_args = infer_type_(TProd(Array{Term}([])), ts_computed_2)
    # ^ Yes, believe it or not this unifies the CONTEXTS  # ^ REUSING the TProd inference, HACKING the fact that Term is NOT used
    all_w_unified_args # Wait... Is this right ????????
end
function infer_type_(term::TAppend, ts_computed::Array{InferResTermIn})::InferResTerm
    # First, CHECK THAT ALL TOut's CAN be N:
    ts_computed_2 = CHECK_unify_terms_to_N_(ts_computed)
    if ts_computed_2 isa TermwError return ts_computed_2 end  #y'know what? Yes this is violent.. I don't care
    # ^ Each of these still has ITS OWN TLocInt's

    # Second, Unify the context of the TLocs:
    all_w_unified_args = infer_type_(TProd(Array{InferResTerm}([])), ts_computed_2)
    # ^ Yes, believe it or not this unifies the CONTEXTS  # ^ REUSING the TProd inference, HACKING the fact that Term is NOT used
    all_w_unified_args # Wait... Is this right ????????
end
function infer_type_(term::TTerm, t_computed_in::InferResTermIn, t_computed_out::InferResTermIn)::InferResTerm
    # First, CHECK THAT ALL TOut's CAN be TypeUniverses:
    # I'm TMPORARELY NOT DOING THIS UNTIL I FIGURE OUT MANY THINGS
    # ts_computed_2 = CHECK_unify_terms_to_N_(ts_computed)
    # if ts_computed_2 isa TermwError return ts_computed_2 end
    # y'know what? Yes this is violent.. I don't care
    # ^ Each of these still has ITS OWN TLocInt's

    # Second, Unify the context of the TLocs:
    all_w_unified_args = infer_type_(TProd(Array{Term}([])), [t_computed_in, t_computed_out])
    # ^ Yes, believe it or not this unifies the CONTEXTS  # ^ REUSING the TProd inference, HACKING the fact that Term is NOT used
    TTerm(all_w_unified_args.t_in, TypeUniverse()) # Wait... Is this right ????????
end



# Silly categorical-algebra-ish recursive wrapup:
function infer_type_rec(term::TLocInt)::InferResTerm
    return infer_type_(term)
end
function infer_type_rec(term::TLocStr)::InferResTerm
    return infer_type_(term)
end
function infer_type_rec(term::TGlob)::InferResTerm
    return infer_type_(term)
end
function infer_type_rec(term::TTop)::InferResTerm
    return infer_type_(term)
end
function infer_type_rec(term::TInt)::InferResTerm
    return infer_type_(term)
end
function infer_type_rec(term::TStr)::InferResTerm
    return infer_type_(term)
end
function infer_type_rec(term::TN)::InferResTerm
    return infer_type_(term)
end
function infer_type_rec(term::TS)::InferResTerm
    return infer_type_(term)
end
function infer_type_rec(term::TIntSum)::InferResTerm
    tts::Array{InferResTerm} = infer_type_rec.(term.ns)
    return infer_type_(term, Array{InferResTermIn}(tts))
end
function infer_type_rec(term::TIntProd)::InferResTerm
    tts::Array{InferResTerm} = infer_type_rec.(term.ns)
    return infer_type_(term, Array{InferResTermIn}(tts))
end
function infer_type_rec(term::TAppend)::InferResTerm
    tts::Array{InferResTerm} = infer_type_rec.(term.prods)
    return infer_type_(term, Array{InferResTermIn}(tts))
end
function infer_type_rec(term::TAnno)::InferResTerm # IMPORTANT: if an error comes up, THIS FUNCTION will turn res into TermwError
    tt = infer_type_rec(term.expr)
    res = (tt isa TermwError) ? infer_type_(term, tt.term) : infer_type_(term, tt)
    if res isa TermwError res elseif tt isa TermwError TermwError(res, "Fail-") else res end
end
function infer_type_rec(term::TAbs)::InferResTerm
    tt = infer_type_rec(term.body)
    res = (tt isa TermwError) ? infer_type_(term, tt.term) : infer_type_(term, tt)
    if res isa TermwError res elseif tt isa TermwError TermwError(res, "Fail-") else res end
end
function infer_type_rec(term::TSumTerm)::InferResTerm
    tt = infer_type_rec(term.data)
    res = (tt isa TermwError) ? infer_type_(term, tt.term) : infer_type_(term, tt)
    if res isa TermwError res elseif tt isa TermwError TermwError(res, "Fail-") else res end
end
function infer_type_rec(term::TProd)::InferResTerm
    tts::Array{InferResTerm} = infer_type_rec.(term.data)
    tts_terms = [if t isa TermwError t.term else t end for t in tts]
    res = infer_type_(term, Array{InferResTermIn}(tts_terms))
    if res isa TermwError res elseif any(tts .|> (x->x isa TermwError)) TermwError(res, "Fail-") else res end
end
function infer_type_rec(term::TBranches)::InferResTerm
    tts = infer_type_rec.(term.ops_chances)
    tts_terms = [if t isa TermwError t.term else t end for t in tts]
    res = infer_type_(term, Array{InferResTermIn}(tts_terms))
    if res isa TermwError res elseif any(tts .|> (x->x isa TermwError)) TermwError(res, "Fail-") else res end
end
function infer_type_rec(term::TApp)::InferResTerm # IMPORTANT: if an error comes up, THIS FUNCTION will turn res into TermwError
    tts::Array{InferResTerm} = infer_type_rec.(term.ops_dot_ordered)
    tts_terms = [if t isa TermwError t.term else t end for t in tts]
    res = infer_type_(term, Array{InferResTermIn}(tts_terms))
    if res isa TermwError res elseif any(tts .|> (x->x isa TermwError)) TermwError(res, "Fail-") else res end
end
function infer_type_rec(term::TConc)::InferResTerm # IMPORTANT: if an error comes up, THIS FUNCTION will turn res into TermwError
    tts::Array{InferResTerm} = infer_type_rec.(term.ops_dot_ordered)
    tts_terms = [if t isa TermwError t.term else t end for t in tts]
    res = infer_type_(term, Array{InferResTermIn}(tts_terms))
    if res isa TermwError res elseif any(tts .|> (x->x isa TermwError)) TermwError(res, "Fail-") else res end
end
function infer_type_rec(term::TConc)::InferResTerm # IMPORTANT: if an error comes up, THIS FUNCTION will turn res into TermwError
    tts::Array{InferResTerm} = infer_type_rec.(term.ops_dot_ordered)
    tts_terms = [if t isa TermwError t.term else t end for t in tts]
    res = infer_type_(term, Array{InferResTermIn}(tts_terms))
    if res isa TermwError res elseif any(tts .|> (x->x isa TermwError)) TermwError(res, "Fail-") else res end
end


InferResTAnno = TAnno # No error handling, for now

# Silly categorical-algebra-ish recursive wrapup:
# function build_anno_term_TLoc(TLocInt)::InferResTAnno  return infer_type_(term) end
# function build_anno_term_TLocStr(TLocStr)::InferResTAnno  return infer_type_(term) end
# function build_anno_term_TGlob(TGlob)::InferResTAnno return infer_type_(term) end
# function build_anno_term_TTop(TTop)::InferResTAnno return infer_type_(term) end
# function build_anno_term_TInt(TInt)::InferResTAnno return infer_type_(term) end
# function build_anno_term_TN(TN)::InferResTAnno return infer_type_(term) end
# function build_anno_term_TStr(TStr)::InferResTAnno return infer_type_(term) end
# function build_anno_term_TS(TS)::InferResTAnno return infer_type_(term) end
# function build_anno_term_TS(TS)::InferResTAnno  return infer_type_(term) end
function build_anno_term_TAbs(term_anno::TAnno)::InferResTAnno # it's the body, ofc
    res = TAbs(term_anno.expr)
    TAnno(res, infer_type_(res, term_anno.type))
end
function build_anno_term_TAnno(term_anno::TAnno, type_anno::TAnno)::InferResTAnno # IMPORTANT: if an error comes up, THIS FUNCTION will turn res into TermwError
    # if type_anno.type.t_out !==TypeUniverse()
    #     throw(DomainError("Whats going on here ???????? with term $(term_anno|>pr) written to be of type: $(type_anno|>pr), which is not a TypeUniverse at all, tho ..."))
    # end
    res = TAnno(term_anno.expr, type_anno.expr)
    TAnno(term_anno.expr, infer_type_(res, term_anno.type))
end

function build_anno_term_TProd(terms_anno::Array{TAnno}; dict_anno::Array{Pair{String, TAnno}}=Array{Pair{String, TAnno}}([]))::InferResTAnno # IMPORTANT: if an error comes up, THIS FUNCTION will turn res into TermwError
    if length(dict_anno) > 0
        (keys, vals) = collect(zip(dict_anno...))
        original_length = length(terms_anno)
        res = TProd(terms_anno .|> x->x.expr, Array{Pair{String, Term}}([s=>t.expr for (s,t) in dict_anno]))
        res_type = infer_type_(res, Array{InferResTermIn}(vcat(terms_anno, [vals...]) .|> x->x.type))
        if res_type isa TermwError
            restored_prod = TProd(res_type.term.t_out.data[1:original_length], Array{Pair{String, Term}}([s=>t for (s,t) in zip(keys, res_type.term.t_out.data[(original_length+1):end])]))
            res_type = TermwError(TTerm(res_type.term.t_in, restored_prod), res_type.error)
        else
            restored_prod = TProd(res_type.t_out.data[1:original_length], Array{Pair{String, Term}}([s=>t for (s,t) in zip(keys, res_type.t_out.data[(original_length+1):end])]))
            res_type = TTerm(res_type.t_in, restored_prod)
        end
        return TAnno(res, res_type)
    else
        res = TProd(Array{Term}(terms_anno .|> x->x.expr))
        return TAnno(res, infer_type_(res, terms_anno .|> x->x.type))
    end
end

# build_anno_term_TProd(Array{TAnno}([]); dict_anno=[
#     Pair{String, TAnno}("a", TAnno(TGlobAuto("aa"), TGlobAutoCtx("AA").type)),
#     Pair{String, TAnno}("b", TAnno(TGlobAuto("bb"), TGlobAutoCtx("BB").type)),
#     ])|> pr_E



function build_anno_term_TSumTerm(tag, tag_name, term_anno::TAnno)::InferResTAnno
    res = TSumTerm(tag, tag_name, term_anno.expr)
    TAnno(res, infer_type_(res, term_anno.type))
end
# function build_anno_term_TBranches(term_anno::TAnno)::InferResTAnno
#     res = TBranches()
#     TAnno(res, infer_type_(res, terms_anno .|> x->x.type))
# end
function build_anno_term_TApp(terms_anno::Array{TAnno})::InferResTAnno
    res = TApp(terms_anno .|> x->x.expr)
    TAnno(res, infer_type_(res, terms_anno .|> x->x.type))
end
function build_anno_term_TConc(terms_anno::Array{TAnno})::InferResTAnno
    res = TConc(terms_anno .|> x->x.expr)
    TAnno(res, infer_type_(res, terms_anno .|> x->x.type))
end
function build_anno_term_TIntSum(terms_anno::Array{TAnno})::InferResTAnno
    res = TIntSum(terms_anno .|> x->x.expr)
    TAnno(res, infer_type_(res, terms_anno .|> x->x.type))
end
function build_anno_term_TIntProd(terms_anno::Array{TAnno})::InferResTAnno
    res = TIntProd(terms_anno .|> x->x.expr)
    TAnno(res, infer_type_(res, terms_anno .|> x->x.type))
end
function build_anno_term_TAppend(terms_anno::Array{TAnno})::InferResTAnno
    res = TAppend(terms_anno .|> x->x.expr)
    TAnno(res, infer_type_(res, terms_anno .|> x->x.type))
end
function build_anno_term_TTerm(term_anno_in::TAnno, term_anno_out::TAnno; make_auto=true)::InferResTAnno
    if (term_anno_in.expr isa TProd && term_anno_in.expr.data |> length !=1) || make_auto==false
        res = TTerm(term_anno_in.expr, term_anno_out.expr)
    else
        res = TTermAuto(term_anno_in.expr, term_anno_out.expr)
    end
    TAnno(res, infer_type_(res, term_anno_in.type, term_anno_out.type))
end