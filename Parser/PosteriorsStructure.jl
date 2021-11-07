include("SyntaxInst.jl")

struct SomeChancewIndex{T}
    chance::T
    index::Int
    P::Real  #//posterior, OBVIOUSLY
end

struct someOtherReturn
	syntax::SyntaxCore
	type::Temp_Type
	P::Real
end
gettypeThatHasSynt(r::someOtherReturn) = r.type


struct PosteriorStucture2
	marginalsNormalizer::Real
	marginalsUnn::Dict{SyntaxCore, Real}

	PofChoices::Dict{SyntaxChoice, Array{Real}}
	# //should they be unnormalized within each one SyntaxChoice* ??

	# epsilon::Real = 0.01
end
function updateCaches(ps::PosteriorStucture2)
    # //for (auto s : marginalsUnn)
    # //	s.first->setMarginal(s.second/ marginalsNormalizer);
    return
end
function updateMap(ps::PosteriorStucture2, obj::SyntaxInst)
    return
end

function getBestPosteriors(ps::PosteriorStucture2, child::SyntaxCore)  #Dict{float, SyntaxCore*>
    # Dict{float, SyntaxCore*> res;
    # for (auto parentChance : allSyntaxes)
    # {
    # 	float P = getPosterior(parentChance, child);
    # 	if (P > ps.epsilon)
    # 	{
    # 		res
    # 	}
    # }
    return
end

P_Type = Array{Tuple{Real, Tuple{SyntaxCore, Int}}} # std::multimap<float, std::pair<SyntaxCore, int>>

struct PosteriorsStructure

	posteriorsBaked::Dict{SyntaxCore, P_Type} #  //pB[Child][PosteriorProb]=Parent
	marginals::Dict{SyntaxCore, Real}
	choicesLikelyhood::Dict{SyntaxChoice, Dict{SyntaxCore, Real}} # //cL[Parent][Child]=Likelyhood
	stripLambdas::Dict{SyntaxStrip, Real} #  //sL[Strip]=Lambda
	bindings::Dict{SyntaxCore, Array{Temp_Type}}
	allSyntaxes::Dict{String, SyntaxCore}
	epsilon::Real
end

PosteriorsStructure() = PosteriorsStructure(
    Dict{SyntaxCore, P_Type}(),
    Dict{SyntaxCore, Real}(),
    Dict{SyntaxChoice, Dict{SyntaxCore, Real}}(), # //cL[Parent][Child]=Likelyhood
    Dict{SyntaxStrip, Real}(), #  //sL[Strip]=Lambda
    Dict{SyntaxCore, Array{Temp_Type}}(),
    Dict{String, SyntaxCore}(),
    0.0
    )

getSyntax(ps::PosteriorsStructure, s::String)::SyntaxCore = ps.allSyntaxes[s]

function addSyntax!(ps::PosteriorsStructure, s::String, obj::SyntaxCore)
    ps.allSyntaxes[s] =obj
end


function initializeMarginals(ps::PosteriorsStructure)
    for (_, s) in ps.allSyntaxes ps.marginals[s] = 1.0/ length(ps.allSyntaxes) end
end

function initializeChoices(ps::PosteriorsStructure)
    for (n, s) in ps.allSyntaxes
        if s isa SyntaxChoice
            for ss in s.list
                if !(s in keys(ps.choicesLikelyhood))
                    ps.choicesLikelyhood[s] = Dict{SyntaxCore, Real}(ss=> 1.0 / length(s.list))
                else
                    ps.choicesLikelyhood[s][ss] = 1.0 / length(s.list)
                end
            end
        end
    end
end

# function initializeStrips(ps::PosteriorsStructure)
#     for (n, s) in ps.allSyntaxes
#         if s[2] in SyntaxStrip
#             ps.stripLambdas[s] = 0.6
#         end
#     end
# end

function push_dict(d, key, elem)
    if !(key in keys(d))
        d[key] = P_Type([elem])
    else
        push!(d[key][ss], elem)
    end
end

function initializePosteriors(ps::PosteriorsStructure)
    for (n, parent) in ps.allSyntaxes
        if parent isa SyntaxStruct
            for (i, child) in enumerate(parent.list)
                posterior::Real = ps.marginals[parent] / ps.marginals[child]
                push_dict(ps.posteriorsBaked, child, (posterior, (parent,i-1)))
            end
        elseif parent isa SyntaxChoice
            for (i, child) in enumerate(parent.list)
                posterior::Real = ps.marginals[parent] / ps.marginals[child] * ps.choicesLikelyhood[parent][child]
                push_dict(ps.posteriorsBaked, child, (posterior, (parent,i-1)))
            end
        elseif parent isa SyntaxStrip
            # //for (auto child : parent->)
            # //{
            # //	float posterior = ps.marginals[SyntaxCore{ parent }] / ps.marginals[child] * choicesLikelyhood[parent][child];
            # //	posteriorsBaked[child].emplace(posterior, parent);  -1 !!!!!!!!
            # //}
        end
    end
    # sort!(ps.posteriorsBaked; by=(x->x[1]))
end

getMarginal(ps::PosteriorsStructure, s::SyntaxCore) = ps.marginals[s]
# //float PofTypeGivenString(SyntaxField* obj, s::String) { return 0.333; }

function getAllSyntaxProductsWithIndexFor(ps::PosteriorsStructure, s::SyntaxCore)::Array{SomeChancewIndex{SyntaxProduct}}
    v = Array{SomeChancewIndex{SyntaxProduct}}([])
    for (p, (synt, idx)) in get(ps.posteriorsBaked, s, [])
        if p > ps.epsilon
            if !(synt isa SyntaxProduct) continue end
            push!(v, SomeChancewIndex{SyntaxProduct}(synt, idx, p))
        end
    end
    return v
end

function getAllSyntaxChoicesWithIndexFor(ps::PosteriorsStructure, s::SyntaxCore)::Array{SomeChancewIndex{SyntaxChoice}}
    v = Array{SomeChancewIndex{SyntaxChoice}}([])
    for (p, (synt, idx)) in get(ps.posteriorsBaked, s, [])
        if p > ps.epsilon && synt isa SyntaxChoice
            push!(v, SomeChancewIndex{SyntaxChoice}(synt, idx, p))
        end
    end
    return v
end

function getAllSyntaxBindingsFor(ps::PosteriorsStructure, s::SyntaxCore)::Array{someOtherReturn}
    v = Array{someOtherReturn}([])
    for i in get(ps.bindings, s,[])
        push!(v, someOtherReturn(s, i, 1 )) # //im pushing THE LIKELYHOOD in now just because
        # //i mean, Just because every syntax is only owned by one type^^ .
    end
    return v
end

function getTerminal(ps::PosteriorsStructure, s::String)::Tuple{Union{SyntaxTerm, Nothing}, Real}
    t::Union{SyntaxTerm, Nothing} = get(ps.allSyntaxes, s, nothing)
    if (t !==nothing && t isa SyntaxTerm)
        return (t, getMarginal(ps, t))
    else
        return (nothing, 0.0)
    end
end

function getBindings(ps::PosteriorsStructure, s::SyntaxCore)::Array{Temp_Type}
    ts = get(ps.bindings, s, nothing)
    return (ts !== nothing) ? ts : Array{Temp_Type}([])
end
