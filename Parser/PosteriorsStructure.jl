
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

	epsilon::Real = 0.01
end
function updateCaches(ps::PosteriorStucture2)
    # //for (auto s : marginalsUnn)
    # //	s.first->setMarginal(s.second/ marginalsNormalizer);
    return
end
function updateMap(ps::PosteriorStucture2, obj::SyntaxInst)
    return
end

function getBestPosteriors(ps::PosteriorStucture2, SyntaxCore* child)  #Dict{float, SyntaxCore*>
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
	tripLambdas::Dict{SyntaxStrip, Real} #  //sL[Strip]=Lambda
	bindings::Dict{SyntaxCore, Array{Temp_Type}}
	allSyntaxes::Dict{String, SyntaxCoreOwning}
	epsilon::Real = 0.00
end

getSyntax(ps::PosteriorsStructure, s::String)::SyntaxCore = ps.allSyntaxes[s]

function addSyntax!(ps::PosteriorsStructure, s::String, obj::SyntaxCoreOwning)
    ps.allSyntaxes[s] =obj
end


function initializeMarginals(ps::PosteriorsStructure)
    for (_, s) in ps.allSyntaxes ps.marginals[s] = 1.0/ length(ps.allSyntaxes) end
end

function initializeChoices(ps::PosteriorsStructure)
    for (n, s) in ps.allSyntaxes
        if s isa SyntaxChoice
            for ss in getChoices(s)
                ps.choicesLikelyhood[s][ss] = 1.0 / length(getChoices(s))
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

function initializePosteriors(ps::PosteriorsStructure)
    for (n, s) in ps.allSyntaxes
        if s isa SyntaxStruct
            parent::SyntaxStruct = s
            for (i, child) in enumerate(getObjs(parent))
                posterior::Real = ps.marginals[parent] / marginals[child]
                push!(ps.posteriorsBaked[child], (posterior, (parent,i)))
            end
        elseif s isa SyntaxChoice
            parent::SyntaxChoice = s
            for (i, child) in enumerate(getChoices(parent))
                posterior::Real = ps.marginals[parent] / ps.marginals[child] * ps.choicesLikelyhood[parent][child]
                push!(ps.posteriorsBaked[child], (posterior, (parent,i)))
            end
        elseif s isa SyntaxStrip
            parent::SyntaxStrip = s
            # //for (auto child : parent->)
            # //{
            # //	float posterior = marginals[SyntaxCore{ parent }] / marginals[child] * choicesLikelyhood[parent][child];
            # //	posteriorsBaked[child].emplace(posterior, parent);
            # //}
        end
    end
    sort!(ps.posteriorsBaked; by=(x->x[1]))
end

getMarginal(ps::PosteriorsStructure, s::SyntaxCore) = ps.marginals[s]
# //float PofTypeGivenString(SyntaxField* obj, s::String) { return 0.333; }

function getAllSyntaxProductsWithIndexFor(ps::PosteriorsStructure, s::SyntaxCore)::Array{SomeChancewIndex{SyntaxProduct}}
    v = Array{SomeChancewIndex{SyntaxProduct}}([])
    for (p, (synt, idx)) in ps.posteriorsBaked[s]
        if p > ps.epsilon
            res_synt::SyntaxProduct
            if synt isa SyntaxStruct res_synt = SyntaxProduct(synt)
            elseif synt isa SyntaxStrip res_synt = SyntaxProduct(synt)
            else continue end

            push!(v, SomeChancewIndex{SyntaxProduct}(res_synt, idx, p))
        end
    end
    return v
end

function getAllSyntaxChoicesWithIndexFor(ps::PosteriorsStructure, s::SyntaxCore)::Array{SomeChancewIndex{SyntaxChoice}}
    v = Array{SomeChancewIndex{SyntaxChoice}}([])
    for (p, (synt, idx)) in ps.posteriorsBaked[s]
        if p > ps.epsilon && synt isa SyntaxChoice
            push!(v, SomeChancewIndex{SyntaxChoice}(synt, idx, p))
        end
    end
    return v
end

function getAllSyntaxBindingsFor(ps::PosteriorsStructure, s::SyntaxCore)::Array{someOtherReturn}
    v = Array{someOtherReturn}([])
    for i in ps.bindings[s]
        push!(v, someOtherReturn(s, i, 1 )) # //im pushing THE LIKELYHOOD in now just because
        # //i mean, Just because every syntax is only owned by one type^^ .
    end
    return v
end

function getTerminal(ps::PosteriorsStructure, s::String)::Tuple{SyntaxTerm, Real}
    t = get!(ps.allSyntaxes, s, nothing)
    if (t !==nothing && t isa SyntaxTerm)
        return (t, getMarginal(ps, t))
    else
        return (nothing, 0.0)
    end
end

function getBindings(ps::PosteriorsStructure, s::SyntaxCore)::Array{Temp_Type}
    ts = get!(ps.bindings, s, nothing)
    return (ts !== nothing) ? ts : Array{Temp_Type}([])
end
