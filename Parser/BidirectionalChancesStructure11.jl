
include("SyntaxInst.jl")

mutable struct HangingChance10
	previouses::Array{HangingChance10}
	nexts::Array{HangingChance10}
	chance::SyntaxProduct
	object::SyntaxInst
	indexInChance::Int  # //in strips it is the code
	length::Int  # //of object

	marginalOfChance::Real
	MarginalOfCurrObjName::Real
	POfThisIfGoingForward::Real
	POfThisIfGoingBackward::Real
end
function HangingChance10(
    chance::SyntaxProduct, object::SyntaxInst, indexInChance::Int,
    length::Int, marginalOfChance::Real, MarginalOfCurrObjName::Real)
    HangingChance10(
        Array{HangingChance10}([]), Array{HangingChance10}([]),
        chance, object, indexInChance, length, marginalOfChance, MarginalOfCurrObjName,
        getP(object) / marginalOfChance, getP(object) / marginalOfChance,
    )
end

getTo(hc::HangingChance10, from::Int) = from + hc.length
getFrom(hc::HangingChance10, to::Int) = to - hc.length

has_ended_strip_w_no_after(hc::HangingChance10) = hc.chance isa SyntaxStrip && hc.chance.after === nothing && hc.indexInChance == 2 && isempty(hc.nexts) && !isempty(hc.previouses)
has_justbegun_strip_w_no_before(hc::HangingChance10) = hc.chance isa SyntaxStrip && hc.chance.before === nothing && hc.indexInChance == 2 && isempty(hc.previouses) && !isempty(hc.nexts)
hasEnded(hc::HangingChance10)::Bool = getPossibleNexts(hc.chance, getName(hc.object), hc.indexInChance) |> isempty || has_ended_strip_w_no_after(hc)
hasJustBegun(hc::HangingChance10)::Bool = getPossiblePreviouses(hc.chance, getName(hc.object), hc.indexInChance) |> isempty || has_justbegun_strip_w_no_before(hc)
# SyntaxProduct getChance() { return chance; }
# int getIndexInChance() { return indexInChance; }
# float getPForward() { return POfThisIfGoingForward; }
# float getPBackward() { return POfThisIfGoingBackward;	}



struct SyntaxInstOwner
    s::SyntaxInst
end
trace(sio::SyntaxInstOwner; top=false) = trace(sio.s; top=top)
getName(obj::SyntaxInstOwner) = getName(obj.s)


make_SyntaxInstProduct(s::SyntaxStruct, p::Real)  = SyntaxInstStruct(s, [], p)
make_SyntaxInstProduct(s::SyntaxStrip, p::Real)  = SyntaxInstStrip(s, [], p)
make_SyntaxInstProduct(s::SyntaxStruct, list::Array{SyntaxInst}, p::Real)  = SyntaxInstStruct(s, list, p)
make_SyntaxInstProduct(s::SyntaxStrip, list::Array{SyntaxInst}, p::Real)  = SyntaxInstStrip(s, list, p)

a = vcat(Array{Int}([])...)

AAH_Type = Array{Array{HangingChance10}}

function getEndingChancesForward(hc::HangingChance10)::AAH_Type
    # Scan graph to find all CHAINS OF NEXTS that end up in an ENDING!!
    @assert !(!isempty(hc.nexts) && hasEnded(hc)) "Just in case- please remove this at some point"
    if isempty(hc.nexts) && hasEnded(hc)
        return AAH_Type([[hc]])
    else
        #TODO: Look at some tag Can_Get_To_An_Ending!!
        res = AAH_Type(vcat([getEndingChancesForward(n) for n in hc.nexts]...))
        res = [vcat([hc], chain) for chain in res]
        return res
    end
end
function getBeginningChancesBackward(hc::HangingChance10)::AAH_Type
    # Scan graph to find all CHAINS OF PREVIOUSES that end up in a Beginning!!
    @assert !(!isempty(hc.previouses) && hasJustBegun(hc)) "Just in case- please remove this at some point"
    if isempty(hc.previouses) && hasJustBegun(hc)
        return AAH_Type([[hc]])
    else
        res = AAH_Type(vcat([getBeginningChancesBackward(n) for n in hc.previouses]...))
        # if  hc.previouses is still empty, it returns the Empty Array !!!
        res = [vcat(chain, [hc]) for chain in res]
        return res
    end
end


mutable struct SizeWBuild
    l::Int
    sp::SyntaxInstProduct
end

struct SizeWBounds
    from::Int
    to::Int
    s::SyntaxInstProduct
end

function getAllFinalObjsLinked(hc::HangingChance10, hc_from::Int, hc_to::Int)::Array{SizeWBounds}
    @assert hc_to - hc_from == hc.length "Yep- hc_to - hc_from == hc.length, $(hc_to) - $(hc_from) == $(hc.length)"
    buildswSizes = Array{SizeWBounds}([])
    all_chains_fw = getEndingChancesForward(hc)
    if isempty(all_chains_fw) return buildswSizes end
    all_chains_bw = getBeginningChancesBackward(hc)
    if isempty(all_chains_bw) return buildswSizes end

    for (chainbw, chainfw) in Base.product(all_chains_bw, all_chains_fw)
        length_fw = chainfw .|> (x->x.length) |> sum  # it CONTAINS hc !!!
        length_bw = chainbw .|> (x->x.length) |> sum  # it CONTAINS hc !!!
        from, to = hc_to - length_bw, hc_from + length_fw  # ^ That's why

        chain = vcat(chainbw[1:(end-1)], [hc], chainfw[2:end])
        list = Array{SyntaxInst}(chain .|> (x->x.object))
        # //UPDATE PROB HERE, PLEASE: >>HOPEFULLY THIS IS NOT COMPLETELY WRONG::<<
        P = chain .|> (x->getP(x.object) / hc.MarginalOfCurrObjName) |> prod
        push!(buildswSizes, SizeWBounds(
            from, to, make_SyntaxInstProduct(hc.chance, list, P)))
    end
    buildswSizes
end

getWhatNeedsBefore(hc::HangingChance10)::Array{SyntaxCore} = getPossiblePreviouses(hc.chance, getName(hc.object), hc.indexInChance)
getWhatNeedsNext(hc::HangingChance10)::Array{SyntaxCore} = getPossibleNexts(hc.chance, getName(hc.object), hc.indexInChance)
needsBefore(hc::HangingChance10, obj::SyntaxCore)::Bool = obj in getWhatNeedsBefore(hc)
needsNext(hc::HangingChance10, obj::SyntaxCore)::Bool = obj in getWhatNeedsNext(hc)
function fields_needsBefore_obj(hc::HangingChance10, obj::SyntaxInstObject)::Array{SyntaxField}
    v =  getWhatNeedsBefore(hc)
    return filter(x-> x isa SyntaxField && can_be_a(getType(x), getInferredType(obj).t_out), v)
end
function fields_needsNext_obj(hc::HangingChance10, obj::SyntaxInstObject)::Array{SyntaxField}
    v = getWhatNeedsNext(hc)
    return filter(x-> x isa SyntaxField && can_be_a(getType(x), getInferredType(obj).t_out), v)
end


function linkWithThisPrevious!(hc::HangingChance10, prev::HangingChance10) # God i HOPE references work as they sauy they do ...
    push!(hc.previouses, prev)
    push!(prev.nexts, hc)
    prev.POfThisIfGoingBackward += hc.POfThisIfGoingBackward #//WRONG, WRONG. DON'T EVEN BOTHER CHECKING IT, ITS WRONG
    hc.POfThisIfGoingForward += prev.POfThisIfGoingForward * hc.POfThisIfGoingForward#//JESUS, WTF
end

function linkWithThisNext!(hc::HangingChance10, next::HangingChance10) # God i HOPE references work as they sauy they do ...
    push!(hc.nexts, next)
    push!(next.previouses, hc)
    next.POfThisIfGoingForward += hc.POfThisIfGoingForward #//WRONG, WRONG. DON'T EVEN BOTHER CHECKING IT, ITS WRONG
    hc.POfThisIfGoingBackward += next.POfThisIfGoingBackward * hc.POfThisIfGoingBackward#//JESUS, WTF
end

isThisStep(hc::HangingChance10, c::SyntaxProduct, index::Int)::Bool = (c == hc.chance && hc.indexInChance == index)



function getOneLongFieldNext(hc:: HangingChance10, s::SyntaxCore)::Union{HangingChance10, Nothing}
    iter = filter((t->(t.length==1 && getName(t.object) ==s)), hc.nexts)
    return length(iter) == 0 ? nothing : iter[1]
end
function getOneLongFieldPrev(hc:: HangingChance10, s::SyntaxCore)::Union{HangingChance10, Nothing}
    iter = filter((t->(t.length==1 && getName(t.object) ==s)), hc.previouses)
    return length(iter) == 0 ? nothing : iter[1]
end


mutable struct ChancesStructure10 # // dove chunkVector[i] è un temp il cui ULTIMO ELEMENTO è in i
						  #// MA SOPRATTUTTO, dove InsertAt[i] vuol dire che: finisce in i ESCLUSO, i.e. i è il _FROM_ _DEL_ _NEXT_.

    endings::Array{Array{HangingChance10}} # //the objs in [0] are: the ones whose _FROM_ _OF_ _NEXT_ , _i.e._ _ESCLUDED_ _TO_ is in 1. That is: when to_at(1)(meaning Excluded to) is searched, this is Shifted to [0].
    beginnings::Array{Array{HangingChance10}}  # the objs in [0] are: the ones where the FROM (of THIS, i.e. _TO_ _OF_ _PREV_) is at 0. That is, when you search from_at(1), this is Shifted to [0].
end
ChancesStructure10() = ChancesStructure10([], [])

function chancesNeedingThisNext(cs::ChancesStructure10, from_of_si::Int, si::SyntaxInstOwner)::Array{HangingChance10}
    res = Array{HangingChance10}([])
    if from_of_si == 0 return res end #// Excluded, BUT UNCHECKED
    for hc in cs.endings[from_of_si]
        if needsNext(hc, si.s.name)
            #//there ARE _IS_ _A_ _ISSUES_ here.....   ???
            push!(res, hc)
        end
    end
    return res
end
function chancesNeedingThisPreviously(cs::ChancesStructure10, to_of_si::Int, si::SyntaxInstOwner)::Array{HangingChance10}
    res = Array{HangingChance10}([])
    if to_of_si == length(cs.beginnings) return res end #// Excluded, BUT UNCHECKED
    for hc in cs.beginnings[to_of_si+1]
        if needsBefore(hc, si.s.name)
            #//there ARE _IS_ _A_ _ISSUES_ here..... ???
            push!(res, hc)
        end
    end
    return res
end
function chancesNeedingThisNext_obj(cs::ChancesStructure10, from_of_si::Int, sio::SyntaxInstObject)::Array{Tuple{HangingChance10, SyntaxField}}
    res = Array{Tuple{HangingChance10, SyntaxField}}([])
    if from_of_si == 0 return res end #// Excluded, BUT UNCHECKED
    for hc in cs.endings[from_of_si]
        for field in fields_needsNext_obj(hc, sio) push!(res, (hc, field)) end
    end
    return res
end
function chancesNeedingThisPreviously_obj(cs::ChancesStructure10, to_of_si::Int, sio::SyntaxInstObject)::Array{Tuple{HangingChance10, SyntaxField}}
    res = Array{Tuple{HangingChance10, SyntaxField}}([])
    if to_of_si == length(cs.beginnings) return res end #// Excluded, BUT UNCHECKED
    for hc in cs.beginnings[to_of_si+1]
        for field in fields_needsBefore_obj(hc, sio) push!(res, (hc, field)) end
    end
    return res
end
function chancesNeedingThisNext_hc(cs::ChancesStructure10, from_of_hc::Int, new_hc::HangingChance10)::Array{HangingChance10}
    res = Array{HangingChance10}([])
    if from_of_hc == 0 return res end #// Excluded, BUT UNCHECKED
    for hc in cs.endings[from_of_hc] # from_of_hc -1 BECAUSE SHIFTED, +1 cuz Julia
        @assert !(hc.chance == new_hc.chance && hc.indexInChance == getPrevIndex(new_hc.chance, new_hc.indexInChance) && !needsNext(hc, getName(new_hc.object))) "hahahahahah"
        if hc.chance == new_hc.chance && hc.indexInChance == getPrevIndex(new_hc.chance, new_hc.indexInChance) && !(new_hc in hc.nexts) # If already there, skip
            push!(res, hc) end
    end
    return res
end
function chancesNeedingThisPreviously_hc(cs::ChancesStructure10, to_of_hc::Int, new_hc::HangingChance10)::Array{HangingChance10}
    res = Array{HangingChance10}([])
    if to_of_hc == length(cs.beginnings) return res end #// Excluded, BUT UNCHECKED
    for hc in cs.beginnings[to_of_hc+1]
        @assert !(hc.chance == new_hc.chance && hc.indexInChance == getNextIndex(new_hc.chance, new_hc.indexInChance) && !needsBefore(hc, getName(new_hc.object))) "hahahahahah"
        if hc.chance == new_hc.chance && hc.indexInChance == getNextIndex(new_hc.chance, new_hc.indexInChance) && !(new_hc in hc.previouses) # If already there, skip
            push!(res, hc) end
    end
    return res
end




function reshape(cs::ChancesStructure10, from::Int, to::Int, howMuch::Int) #//to EXCLUDED
    # if (howMuch < to - from)
    #     for i in from:(from + howMuch-1)
    #         cs.endings[i+1] = []
    #         cs.beginnings[i+1] = []
    #     end
    #     for i in to:(length(cs.endings)-1)
    #         cs.endings[i+1] = [c for c in cs.endings[i+1] if getFrom(c, i) >= to ]
    #     end
    #     cs.endings = vcat(cs.endings[1:(from + howMuch)], cs.endings[(to+1):end])
    #     for i in 0:(from-1)
    #         cs.beginnings[i+1] = [c for c in cs.beginnings[i+1] if getTo(c, i) < from ]
    #     end
    #     cs.beginnings = vcat(cs.beginnings[1:(from + howMuch)], cs.beginnings[(to+1):end])
    # else
    #     for i in from:(length(cs.endings)-1)
    #         cs.endings[i+1] = [c for c in cs.endings[i+1] if getFrom(c, i) >= to ]
    #     end
    #     tt = Array{Array{Array{HangingChance10}}}(undef,  howMuch - (to - from))
    #     for i in 1:length(tt) tt[i] = [] end
    #     cs.endings = vcat(cs.endings[1:to], tt, cs.endings[(to+1):end])
    #     for i in 0:(to-1)
    #         cs.beginnings[i+1] = [c for c in cs.beginnings[i+1] if getTo(c, i) < from ]
    #     end
    #     tt = Array{Array{Array{HangingChance10}}}(undef,  howMuch - (to - from))
    #     for i in 1:length(tt) tt[i] = [] end
    #     cs.beginnings = vcat(cs.beginnings[1:to], tt, cs.beginnings[(to+1):end])
    # end
    @assert from==0 && to==0
    cs.beginnings = Array{Array{Array{HangingChance10}}}(undef,  howMuch - (to - from))
    for i in 1:howMuch cs.beginnings[i] = [] end
    cs.endings = Array{Array{Array{HangingChance10}}}(undef,  howMuch - (to - from))
    for i in 1:howMuch cs.endings[i] = [] end
end

function addBeginning(cs::ChancesStructure10, hc::HangingChance10, fromOfHc::Int)
    push!(cs.beginnings[fromOfHc+1], hc) # cuz of Julia
end
function addEnding(cs::ChancesStructure10, hc::HangingChance10, toOfHc::Int)
    # toOfHc EXCLUDED. This means it can NEVER be 0, cuz that'd be a ghost hc. So we SHIF IT LEFT, ie cs.endings[toOfHc-1], to not waste space. +1 cuz Julia!!!
    push!(cs.endings[toOfHc], hc)
end
