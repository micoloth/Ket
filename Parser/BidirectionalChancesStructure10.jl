
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
hasEnded(hc::HangingChance10)::Bool = getPossibleNexts(hc.chance, getName(hc.object), hc.indexInChance+1) |> isempty  # +1, apparently
hasJustBegun(hc::HangingChance10)::Bool = getPossiblePreviouses(hc.chance, getName(hc.object), hc.indexInChance) |> isempty
# SyntaxProduct getChance() { return chance; }
# int getIndexInChance() { return indexInChance; }
# float getPForward() { return POfThisIfGoingForward; }
# float getPBackward() { return POfThisIfGoingBackward;	}



struct SyntaxInstOwner
    s::SyntaxInst
    involvedChances::Array{HangingChance10}
end
SyntaxInstOwner(s::SyntaxInst) = SyntaxInstOwner(s, Array{HangingChance10}([]))
trace(sio::SyntaxInstOwner) = trace(sio.s)
getName(obj::SyntaxInstOwner) = getName(obj.s)


make_SyntaxInstProduct(s::SyntaxStruct, p::Real)  = SyntaxInstStruct(s, [], p)
make_SyntaxInstProduct(s::SyntaxStrip, p::Real)  = SyntaxInstStrip(s, [], p)


mutable struct SizeWBuild
    l::Int
    sp::SyntaxInstProduct
end


function getFinalObjsFromEnd(hc::HangingChance10)::Array{SizeWBuild}
    if (hasJustBegun(hc))
        newTemp = make_SyntaxInstProduct(hc.chance, hc.marginalOfChance)
        push_struct!(newTemp, hc.object, hc.indexInChance, hc.MarginalOfCurrObjName)
        tempList = Array{SizeWBuild}([SizeWBuild(hc.length, newTemp)])
        return tempList
    else
        buildswSizes = Array{SizeWBuild}([])
        for p in hc.previouses
            # if p  # btw "if (p)",  SHOULD HAVE BEEN CHECKED ALREADY!!.
                append!(buildswSizes, getFinalObjsFromEnd(p))
            # end
        end
        for v in buildswSizes
            v.l += hc.length
            push_struct!(v.sp, hc.object, hc.indexInChance, hc.MarginalOfCurrObjName);
        end
    end
    return buildswSizes
end

function find_linked_prev_chances_that_are_beginning(hc::HangingChance10, from_of_hc::Int)::Array{Tuple{HangingChance10, Int}}
    @assert !(!isempty(hc.previouses) && hasJustBegun(hc)) "Just in case- please remove this at some point"
    if isempty(hc.previouses) && hasJustBegun(hc)
        return Array{Tuple{HangingChance10, Int}}([(hc, from_of_hc)])
    else
        linked_prev_chances_that_are_beginning = Array{Tuple{HangingChance10, Int}}([])
        for p in hc.previouses
                append!(linked_prev_chances_that_are_beginning, find_linked_prev_chances_that_are_beginning(p, from_of_hc - p.length))
        end
    end
    return linked_prev_chances_that_are_beginning
end


# //this one, COULD BE BETTER
function getFinalObjsFromStart(hc::HangingChance10)::Array{SizeWBuild}
    if hasEnded(hc)
        newTemp = make_SyntaxInstProduct(hc.chance, hc.marginalOfChance)
        insert_front!(newTemp, hc.object, hc.indexInChance, hc.MarginalOfCurrObjName);
        tempList =  Array{SizeWBuild}([SizeWBuild(hc.length, newTemp)])
        return tempList
    else
        buildswSizes = Array{SizeWBuild}([])
        for p in hc.nexts
            # if p #  // btw "if (p)", SHOULD HAVE BEEN CHECKED ALREADY!!.
                append!(buildswSizes,getFinalObjsFromStart(p))
            # end
        end
        for v in buildswSizes
            v.l += hc.length;
            insert_front!(v.sp, hc.object, hc.indexInChance, hc.MarginalOfCurrObjName)
        end
    end
    return buildswSizes
end

function find_linked_next_chances_that_are_end(hc::HangingChance10, to_of_hc::Int)::Array{Tuple{HangingChance10, Int}}
    @assert !(!isempty(hc.nexts) && hasEnded(hc)) "Just in case- please remove this at some point"
    if isempty(hc.nexts) && hasEnded(hc)
        return Array{Tuple{HangingChance10, Int}}([(hc, to_of_hc)])
    else
        linked_next_chance_that_is_end = Array{Tuple{HangingChance10, Int}}([])
        for p in hc.nexts
                append!(linked_next_chance_that_is_end, find_linked_next_chances_that_are_end(p, to_of_hc + p.length))
        end
    end
    return linked_next_chance_that_is_end
end




getWhatNeedBefore(hc::HangingChance10)::Array{SyntaxCore} = getPossiblePreviouses(hc.chance, getName(hc.object), hc.indexInChance)
getWhatNeedNext(hc::HangingChance10)::Array{SyntaxCore} = getPossibleNexts(hc.chance, getName(hc.object), hc.indexInChance+1) # +1, apparently
needsBefore(hc::HangingChance10, obj::SyntaxCore)::Bool = obj in getWhatNeedBefore(hc)
needsNext(hc::HangingChance10, obj::SyntaxCore)::Bool = obj in getWhatNeedNext(hc)


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

function makeNextOutOfThisWith(hc::HangingChance10, newObj::SyntaxInstOwner, size::Int, marginalOfNewobjName::Real)::Union{HangingChance10, Nothing}
    # //next line finds needed HangingChance (**) in current it.involvedChances <<. 		//RIGHT NOW, THE ASSUMPTION IS THERES _ONLY_ _ONE_ .
    iter = filter((t->isThisStep(t, hc.chance, hc.indexInChance + 1)), newObj.involvedChances)
    @assert length(iter) < 2 "Should be only one needed HangingChance (**) in current it.involvedChances, not $(iter)"
    if length(iter) == 1
        if !(iter[1] in hc.nexts) linkWithThisNext!(hc, iter[1]) end
        # //THERE IS ROOM FOR UPDATING currentPOfThisChanceToBeConsidered HERE
        # //UPDATE: this SHOULD be done inside linkWithThisNext!. Dont trust it too much tho
        return nothing
    else
        temp = HangingChance10(hc.chance, newObj.s, hc.indexInChance + 1, size, hc.marginalOfChance, marginalOfNewobjName) #//,newobj.P * qualcosa??
        push!(newObj.involvedChances, temp)
        linkWithThisNext!(hc, temp)
        # //THERE IS ROOM FOR UPDATING currentPOfThisChanceToBeConsidered HERE --
        #     //UPDATE: this SHOULD be done inside linkWithThisNext!. Dont trust it too much tho
        return temp
    end
end


function makePrevOutOfThisWith(hc::HangingChance10, newObj::SyntaxInstOwner, size::Int, marginalOfNewobjName::Real)::Union{HangingChance10, Nothing}
    # //next line finds needed HangingChance (**) in current it.involvedChances <<. 		//RIGHT NOW, THE ASSUMPTION IS THERES _ONLY_ _ONE_ .
    iter = filter((t->isThisStep(t, hc.chance, hc.indexInChance - 1)), newObj.involvedChances)
    @assert length(iter) < 2 "Should be only one needed HangingChance (**) in current it.involvedChances, not $(iter)"
    if length(iter) == 1
        if !(iter[1] in hc.previouses) linkWithThisPrevious!(hc, iter[1]) end
        # //THERE IS ROOM FOR UPDATING currentPOfThisChanceToBeConsidered HERE
        #     //UPDATE: this SHOULD be done inside linkWithThisPrevious!. Dont trust it too much tho
        return nothing
    else
        temp = HangingChance10(hc.chance, newObj.s, hc.indexInChance - 1, size, hc.marginalOfChance, marginalOfNewobjName) #//,newobj.P * qualcosa??
        push!(newObj.involvedChances, temp)
        linkWithThisPrevious!(hc, temp)
        # //THERE IS ROOM FOR UPDATING currentPOfThisChanceToBeConsidered HERE
        #     //UPDATE: this SHOULD be done inside linkWithThisPrevious!. Dont trust it too much tho
        return temp
    end
end

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

    beginnings::Array{Array{HangingChance10}} # //the objs in [0] are: the ones whose _FROM_ _OF_ _NEXT_ , _i.e._ _ESCLUDED_ _TO_ is in 1. That is: when to_at(1)(meaning Excluded to) is searched, this is Shifted to [0].
    endings::Array{Array{HangingChance10}}  # the objs in [0] are: the ones where the FROM (of THIS, i.e. _TO_ _OF_ _PREV_) is at 0. That is, when you search from_at(1), this is Shifted to [0].
end
ChancesStructure10() = ChancesStructure10([], [])

objsWhereFromOfNextShouldBe(cs::ChancesStructure10, i::Int)::Array{HangingChance10} = (i != 0) ? (cs.beginnings[i]) : (Array{HangingChance10}([])) #// Excluded, BUT UNCHECKED
objsWhereToOfPrevShouldBe(cs::ChancesStructure10, i::Int)::Array{HangingChance10} = (i != length(cs.endings)) ? (cs.endings[i+1]) : (Array{HangingChance10}([])) # //Excluded, BUT UNCHECKED

function reshape(cs::ChancesStructure10, from::Int, to::Int, howMuch::Int) #//to EXCLUDED
    if (howMuch < to - from)
        for i in from:(from + howMuch-1)
            cs.beginnings[i+1] = []
            cs.endings[i+1] = []
        end
        for i in to:(length(cs.beginnings)-1)
            cs.beginnings[i+1] = [c for c in cs.beginnings[i+1] if getFrom(c, i) >= to ]
        end
        cs.beginnings = vcat(cs.beginnings[1:(from + howMuch)], cs.beginnings[(to+1):end])
        for i in 0:(from-1)
            cs.endings[i+1] = [c for c in cs.endings[i+1] if getTo(c, i) < from ]
        end
        cs.endings = vcat(cs.endings[1:(from + howMuch)], cs.endings[(to+1):end])
    else
        for i in from:(length(cs.beginnings)-1)
            cs.beginnings[i+1] = [c for c in cs.beginnings[i+1] if getFrom(c, i) >= to ]
        end
        tt = Array{Array{Array{HangingChance10}}}(undef,  howMuch - (to - from))
        for i in 1:length(tt) tt[i] = [] end
        cs.beginnings = vcat(cs.beginnings[1:to], tt, cs.beginnings[(to+1):end])
        for i in 0:(to-1)
            cs.endings[i+1] = [c for c in cs.endings[i+1] if getTo(c, i) < from ]
        end
        tt = Array{Array{Array{HangingChance10}}}(undef,  howMuch - (to - from))
        for i in 1:length(tt) tt[i] = [] end
        cs.endings = vcat(cs.endings[1:to], tt, cs.endings[(to+1):end])
    end
end

function addBeginning(cs::ChancesStructure10, temp::HangingChance10, fromOfNext::Int)
    push!(cs.beginnings[fromOfNext], temp)
end
function addEnding(cs::ChancesStructure10, temp::HangingChance10, fromOfThis::Int)
    push!(cs.endings[fromOfThis+1], temp)
end
