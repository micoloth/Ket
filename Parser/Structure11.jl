include("StackOfChances.jl")
include("FinishedsStructure10.jl")
include("PosteriorsStructure.jl")
include("BidirectionalChancesStructure11.jl")

#include"ScopedTypeInference.h"

struct ScopedTypeInference #//Boi: this class, will GROW............
# //note 1: this is the Wrong way to handle sum types
# //note 2: yeah, a MATRIX will happen here!!
# //note 3: this class might become a DAC !!!
	allDefinitions::Array{Tuple{String, Term}}
end
ScopedTypeInference() = ScopedTypeInference([])
function can_be_a(request::Term, chance::Term)::Bool # These are the TYPES! ofc
    if (request === chance) true
    elseif failed_unif_res(robinsonUnify(chance, request; mode=implydir_))
        false
    else
        true
    end
end



mutable struct Structure11
	finisheds::FinishedsStructure10
	hangings::ChancesStructure10
	stack::StackOfChances
	scopedTypeInference::ScopedTypeInference
    inputVec::Array{String}
    posteriorsStructure::PosteriorsStructure
end

Structure11() = Structure11(FinishedsStructure10(), ChancesStructure10(), StackOfChances(), ScopedTypeInference(), [], PosteriorsStructure())


size(S::Structure11) = size(S.finisheds)
trace(S::Structure11) = trace(S.finisheds)
function reshape(S::Structure11, from::Int, to::Int, howMuch::Int)
    reshape(S.hangings, from, to, howMuch);
    reshape(S.finisheds, from, to, howMuch);
end



function makeNewNextFromSynt(hc_prev::HangingChance10, newObj::SyntaxInstOwner, size::Int, marginalOfNewobjName::Real)::HangingChance10
    new_hc = HangingChance10(hc_prev.chance, newObj.s, getNextIndex(hc_prev.chance, hc_prev.indexInChance, newObj.s.name), size, hc_prev.marginalOfChance, marginalOfNewobjName) #//,newobj.P * qualcosa??
    linkWithThisNext!(hc_prev, new_hc)
    # //THERE IS ROOM FOR UPDATING currentPOfThisChanceToBeConsidered HERE --
    #     //UPDATE: this SHOULD be done inside linkWithThisNext!. Dont trust it too much tho
    return new_hc
end
function makeNewPrevFromSynt(hc_next::HangingChance10, newObj::SyntaxInstOwner, size::Int, marginalOfNewobjName::Real)::HangingChance10
    new_hc = HangingChance10(hc_next.chance, newObj.s, getPrevIndex(hc_next.chance, hc_next.indexInChance, newObj.s.name), size, hc_next.marginalOfChance, marginalOfNewobjName) #//,newobj.P * qualcosa??
    linkWithThisPrevious!(hc_next, new_hc)
    # //THERE IS ROOM FOR UPDATING currentPOfThisChanceToBeConsidered HERE
    #     //UPDATE: this SHOULD be done inside linkWithThisPrevious!. Dont trust it too much tho
    return new_hc
end
function makeObjFieldAsChance_goingForward(S::Structure11, what_field::SyntaxField, objectFound::SyntaxInstObject, hChance::HangingChance10, objfound_from::Int, objfound_to::Int, PMarginal::Real)
    temp1 = SyntaxInstField(what_field, objectFound, 0.5)
    # //first comment: LOL, you HERE is where computing the P GETS SERIOUS.......
    # //second comment: Note the nice symmetry with below.
    temp2 = SyntaxInstOwner(temp1) # Useless, i'd say
    add(S.finisheds, objfound_from, objfound_to, temp2) # //u are goddam right, it DOESNT go into the stack //i see we all agree on this rn
    temp3 = makeNewNextFromSynt(hChance, temp2, objfound_to - objfound_from, PMarginal) #  // well, i THINK it's co???
    temp3
end
function makeObjFieldAsChance_goingBackward(S::Structure11, what_field::SyntaxField, objectFound::SyntaxInstObject, hChance::HangingChance10, objfound_from::Int, objfound_to::Int, PMarginal::Real)
    temp1 = SyntaxInstField(what_field, objectFound, 0.5)
    # //first comment: LOL, you HERE is where computing the P GETS SERIOUS.......
    # //second comment: Note the nice symmetry with below.
    temp2 = SyntaxInstOwner(temp1) # Useless, i'd say
    temp3 = makeNewPrevFromSynt(hChance, temp2, objfound_to - objfound_from, PMarginal) #  // well, i THINK it's co???
    add(S.finisheds, objfound_from, objfound_to, temp2) # //u are goddam right, it DOESNT go into the stack //i see we all agree on this rn
    temp3
end
function makeObjSimpleStringAsChance_goingForward(S::Structure11, what_SimpleString::SyntaxSimpleString, text::String, hChance::HangingChance10, objfound_from::Int, objfound_to::Int, PMarginal::Real)
    temp1 = SyntaxInstSimpleString(what_SimpleString, text, 0.5)
    # //first comment: LOL, you HERE is where computing the P GETS SERIOUS.......
    # //second comment: Note the nice symmetry with below.
    temp2 = SyntaxInstOwner(temp1) # Useless, i'd say
    add(S.finisheds, objfound_from, objfound_to, temp2) # //u are goddam right, it DOESNT go into the stack //i see we all agree on this rn
    temp3 = makeNewNextFromSynt(hChance, temp2, objfound_to - objfound_from, PMarginal) #  // well, i THINK it's co???
    temp3
end
function makeObjSimpleStringAsChance_goingBackward(S::Structure11, what_SimpleString::SyntaxSimpleString, text::String, hChance::HangingChance10, objfound_from::Int, objfound_to::Int, PMarginal::Real)
    temp1 = SyntaxInstSimpleString(what_SimpleString, text, 0.5)
    # //first comment: LOL, you HERE is where computing the P GETS SERIOUS.......
    # //second comment: Note the nice symmetry with below.
    temp2 = SyntaxInstOwner(temp1) # Useless, i'd say
    temp3 = makeNewPrevFromSynt(hChance, temp2, objfound_to - objfound_from, PMarginal) #  // well, i THINK it's co???
    add(S.finisheds, objfound_from, objfound_to, temp2) # //u are goddam right, it DOESNT go into the stack //i see we all agree on this rn
    temp3
end
function makeReferenceFieldChance_goingForward(S::Structure11, what_field::SyntaxField, chance::StackableChance)
    # // do i need th second check? Actually: What does it even do, i wonder?
    temp1 = SyntaxInstReference(getType(what_field), S.inputVec[chance.to+1], 0.5)
    # //first comment: LOL, you HERE is where computing the P GETS SERIOUS.......
    temp2 = SyntaxInstField(what_field, temp1, 0.5)
    # //second comment: possibly even more serious
    temp4 = SyntaxInstOwner(temp2)
    temp5 = makeNewNextFromSynt(chance.what, temp4, 1, getMarginal(S.posteriorsStructure, what_field))
    # //wait.. But what good does temp->prob even do here then^^
    add(S.finisheds, chance.to, chance.to + 1, temp4)
    # //not only this does not go into the stack(as an AlreadyFinished)-- I DON'T WANT TO PUT IT INTO THE FINISHED EITHER..... //
    temp5
end
function makeReferenceFieldChance_goingBackward(S::Structure11, what_field::SyntaxField, chance::StackableChance)
    # // do i need th second check? Actually: What does it even do, i wonder?
    temp1 = SyntaxInstReference(getType(what_field), S.inputVec[chance.from], 0.5)
    # //first comment: LOL, you HERE is where computing the P GETS SERIOUS.......
    temp2 = SyntaxInstField(what_field, temp1, 0.5)
    # //second comment: possibly even more serious
    temp4 = SyntaxInstOwner(temp2)
    temp5 = makeNewPrevFromSynt(chance.what, temp4, 1, getMarginal(S.posteriorsStructure, what_field))
    # //wait.. But what good does temp->prob even do here then^^
    add(S.finisheds, chance.from - 1, chance.from, temp4)
    # //not only this does not go into the stack(as an AlreadyFinished)-- I DON'T WANT TO PUT IT INTO THE FINISHED EITHER..... //
    temp5
end

function dechoiced_syntaxCore(s::SyntaxInst)
    if s isa SyntaxInstChoice dechoiced_syntaxCore(s.choice)
    elseif s isa SyntaxInstObject dechoiced_syntaxCore(s.syntax)
    else s.name
    end
end

function processObjectFound(S::Structure11, chanceF::StackableObject)
    obj::SyntaxInstObject = chanceF.whatObject
    dechoiced_SC = dechoiced_syntaxCore(obj.syntax) # For a dumb additional check about boundless strips, thanks i hate it
    println( "having object: " , getInferredTerm(obj)|>pr_E , " at " , chanceF.from , "-" , chanceF.to - 1 , " (included)")
    # margOfObjName::Real = getP(obj.name) # //JESUS, WHAT A FUCKING MESS.............................................
    add(S.finisheds, chanceF.from, chanceF.to, SyntaxInstOwner(obj))  #//to EXCLUDED,


    presentProductChances_goingBack = chancesNeedingThisPreviously_obj(S.hangings, chanceF.to, chanceF.whatObject)
    presentProductChances_goingForward = chancesNeedingThisNext_obj(S.hangings, chanceF.from, chanceF.whatObject)
    created_stackable_chances = Array{StackableChance}([])
    for (hc_prev, needed_field) in presentProductChances_goingForward
        if dechoiced_SC isa SyntaxStrip && dechoiced_SC.after === nothing && dechoiced_SC == hc_prev.chance
            println("Ok this sometimes happens too. Thanks god!")
            continue end # DONT add obj that come from a finished syntaxStrips w no boundaries as objects of a bigger syntaxStrip of the same kind. Terrible idea.
        new_created_hc = makeObjFieldAsChance_goingForward(S, needed_field, chanceF.whatObject, hc_prev, chanceF.from, chanceF.to, getMarginal(S.posteriorsStructure, needed_field))
        push!(created_stackable_chances, StackableChance(new_created_hc ,chanceF.from,chanceF.to, true, false, false))
    end
    for (hc_next, needed_field) in presentProductChances_goingBack
        if dechoiced_SC isa SyntaxStrip && dechoiced_SC.before === nothing && dechoiced_SC == hc_next.chance
            println("Ok this sometimes happens too. Thanks god!")
            continue end # DONT add obj that come from a finished syntaxStrips w no boundaries as objects of a bigger syntaxStrip of the same kind. Terrible idea.
        # Only create a new Field if you cannot link to one you already have:
        created_stackable_chances_same = filter(x->counts_as_the_same(x.what, hc_next), created_stackable_chances)
        if length(created_stackable_chances_same) > 0
            for c in created_stackable_chances_same
                linkWithThisNext!(c.what, hc_next) #c.what->hc_next
                c.goBackward = true
                println("Ok Also, sometimes this happens. Nice!")
            end
        else
            new_created_hc = makeObjFieldAsChance_goingBackward(S, needed_field, chanceF.whatObject, hc_next, chanceF.from, chanceF.to, getMarginal(S.posteriorsStructure, needed_field))
            push!(created_stackable_chances, StackableChance(new_created_hc ,chanceF.from,chanceF.to, false, true, false ))  #wait.. But what good does temp->prob even do here then
        end
    end
    for ss in created_stackable_chances
        insert!(S.stack, ss.what.POfThisIfGoingForward, ss) # //wait.. But what good does temp->prob even do here Then
    end
end

function processFinishedSyntax(S::Structure11, chanceF::StackableFinishedSyntax)
    obj::SyntaxInstOwner = chanceF.whatFinished
    println( "having synt: " , obj|>getName|>getString , " at " , chanceF.from , "-" , chanceF.to - 1 , " (included)")

    for x in at(S.finisheds, chanceF.from, chanceF.to)
        if deepEqual(obj.s, x.s)
            # throw(DomainError("OK THIS ACTUALLY ACTUALLY HAPPENEDDDD: $(obj.s|>trace),     $(x.s|>trace)"))
            println("OK THIS ACTUALLY ACTUALLY HAPPENEDDDD: $(obj.s|>trace),     $(x.s|>trace)")
            return
        end
    end
    # //^ THE IDEA WAS _EXACTLY_ NOT TO HAVE TO DO THIS ...............................................................

    add(S.finisheds, chanceF.from, chanceF.to, obj) # //to EXCLUDED

    margOfObjName = getMarginal(S.posteriorsStructure, getName(obj)) # //JESUS, WHAT A FUCKING MESS.............................................

    presentProductChances_goingForward = chancesNeedingThisNext(S.hangings, chanceF.from, chanceF.whatFinished)
    presentProductChances_goingBack = chancesNeedingThisPreviously(S.hangings, chanceF.to, chanceF.whatFinished)
    allSyntProds = getAllSyntaxProductsWithIndexFor(S.posteriorsStructure, getName(obj))
    for synt_with_index::SomeChancewIndex{SyntaxProduct} in allSyntProds
        new_hc = HangingChance10(synt_with_index.chance, obj.s, synt_with_index.index, chanceF.to - chanceF.from, synt_with_index.P, margOfObjName)
        insert!(S.stack, new_hc.POfThisIfGoingForward + new_hc.POfThisIfGoingBackward, StackableChance(new_hc, chanceF.from, chanceF.to, true, true, false))

        # Even more importantly: Are you SURE that ANY hc_bw or hc_fw WILL be triggered here in this loop, at some SyntaxProduct ?
        for hc_prev::HangingChance10 in presentProductChances_goingForward
            if hc_prev.chance == new_hc.chance && new_hc.indexInChance in getNextIndexes(hc_prev.chance, hc_prev.indexInChance)
                linkWithThisPrevious!(new_hc, hc_prev)
            end
        end
        for hc_next::HangingChance10 in presentProductChances_goingBack
            if hc_next.chance == new_hc.chance && new_hc.indexInChance in getPrevIndexes(hc_next.chance, hc_next.indexInChance)
                linkWithThisNext!(new_hc, hc_next)
            end
        end
        if new_hc.previouses|>length >0 || new_hc.nexts|>length >0
            for foundFinished::SizeWBounds in getAllFinalObjsLinked(new_hc, chanceF.from, chanceF.to)
                insert!(S.stack, getP(foundFinished.s), StackableFinishedSyntax(SyntaxInstOwner(foundFinished.s), foundFinished.from, foundFinished.to))
            end
        end
    end

    for thingy::SomeChancewIndex{SyntaxChoice} in getAllSyntaxChoicesWithIndexFor(S.posteriorsStructure, getName(obj))
        # //THIS IS IMPORTANT:
        actualP::Real = thingy.P * getP(chanceF)

        temp1 = SyntaxInstOwner(SyntaxInstChoice(thingy.chance, thingy.index, obj.s, actualP))
        temp2 = StackableFinishedSyntax(temp1, chanceF.from, chanceF.to)
        pp = getP(temp2)
        insert!(S.stack, pp, temp2)
    end

    for thingy::SyntWithItsBuilderFunc in getAllSyntaxBindingsFor(S.posteriorsStructure, getName(obj))
        # temp1 = buildTypeThatHasSyntInst(obj.s, thingy.builder_func)
        temp1 = thingy.builder_func(obj.s)
        temp2 = SyntaxInstObject(obj.s, thingy.P, temp1)
        insert!(S.stack, getP(temp2), StackableObject(temp2, chanceF.from, chanceF.to))
    end
end



function processChance(S::Structure11, chance::StackableChance)

    if chance.goBackward && !chance.alreadyAdded addBeginning(S.hangings, chance.what, chance.from) end
    if chance.goForward && !chance.alreadyAdded addEnding(S.hangings, chance.what, chance.to) end
    # The idea of this change^ was: when a chance gets preocessed, it links with PAST begs/ends that are ALREADY ADDED.
    # Only when it gets processed it gets added itself.
    # Then, FUTURE chances link to it. NO OVERLAPPINGS.

    # OTOH, before it happened that: a chance gets added to beginnings.
    # Then, a Next chance links to it. Then, IT(the first) gets processed, and links to the Next. So it's duble!!

    # OTOHOTOH, my beautiful reasoning breaks when dealing with Found stuff/variables: that's why:
    # a FINISHED stuff currently creates its own Chances, BUT:
    # a FOUND stuff, either has to STICK to a BEGINNING/END, or, as it stands, it's LOST!!!
    # WORSE: now, where a Reference is created, it's NOT added to beginnings/endings, so:
    # when another chance tries to do it from the other side, it CREATES IT AGAIN!!

    linkedWithAnything = false
    if ((chance.goForward && hasEnded(chance.what) && length(chancesNeedingThisPreviously_hc(S.hangings, chance.to, chance.what))==0)
        || (chance.goBackward && hasJustBegun(chance.what)) && length(chancesNeedingThisNext_hc(S.hangings, chance.from, chance.what))==0)
        linkedWithAnything = true
    end
    if (chance.goForward && !hasEnded(chance.what) && chance.to < size(S))
        for hc_next in chancesNeedingThisPreviously_hc(S.hangings, chance.to, chance.what)
            linkWithThisNext!(chance.what, hc_next)
            linkedWithAnything = true
        end
    end
    if chance.goBackward && !hasJustBegun(chance.what) && chance.from > 0
        for hc_prev in chancesNeedingThisNext_hc(S.hangings, chance.from, chance.what)
            linkWithThisPrevious!(chance.what, hc_prev)
            linkedWithAnything = true
        end
    end
    if linkedWithAnything
        for foundFinished::SizeWBounds in getAllFinalObjsLinked(chance.what, chance.from, chance.to)
            insert!(S.stack, getP(foundFinished.s), StackableFinishedSyntax(SyntaxInstOwner(foundFinished.s), foundFinished.from, foundFinished.to))
        end
    end


    if (chance.goForward && !hasEnded(chance.what) && chance.to < size(S))
        new_hc_obj_created_somehow = Array{HangingChance10}([])
        for possibleNeeded in getWhatNeedsNext(chance.what)
            for (fin, to_new) in all_objects_beginning_at_that_can_be_a(S.finisheds, UInt(chance.to), possibleNeeded)# This JUST RETURNS EMPTY if possibleNeeded not SyntaxField
                push!(new_hc_obj_created_somehow, makeObjFieldAsChance_goingForward(S, possibleNeeded, fin, chance.what, chance.to,to_new, 1))
            end
            # //careful here: # USE A WORD AS A VARIABLE:
            if (possibleNeeded isa SyntaxField && getOneLongFieldNext(chance.what, possibleNeeded)===nothing && !occursin(S.inputVec[chance.to+1], "()[]-><{}:=.,;:_\"'+-/\\_|") # TODO: is this right? Or should be ! ?
                    && !any(chance.what.nexts .|> (x->x.object.name == possibleNeeded && x.object.objectFound isa SyntaxInstReference && x.object.objectFound.text == S.inputVec[chance.to+1])))
                push!(new_hc_obj_created_somehow, makeReferenceFieldChance_goingForward(S, possibleNeeded, chance))
            elseif (possibleNeeded isa SyntaxSimpleString && !occursin(S.inputVec[chance.to+1], "()[]-><{}:=.,;:_\"'+-/\\_|")
                && !any(chance.what.nexts .|> (x->x.object.name == possibleNeeded && x.object.text == S.inputVec[chance.to+1])))
                push!(new_hc_obj_created_somehow, makeObjSimpleStringAsChance_goingForward(S, possibleNeeded, S.inputVec[chance.to+1], chance.what, chance.to,chance.to + 1, 1))
            end
        end
        for new_hc_obj in new_hc_obj_created_somehow
            addEnding(S.hangings, new_hc_obj, chance.to+1)
            insert!(S.stack, new_hc_obj.POfThisIfGoingForward, StackableChance(new_hc_obj, chance.to,chance.to + new_hc_obj.length, true, false, true))
        end
    end
    if chance.goBackward && !hasJustBegun(chance.what) && chance.from > 0
        new_hc_obj_created_somehow = Array{HangingChance10}([])
        for possibleNeeded in getWhatNeedsBefore(chance.what)
            for (fin, from_new) in all_objects_ending_at_that_can_be_a(S.finisheds, UInt(chance.from), possibleNeeded)# This JUST RETURNS EMPTY if possibleNeeded not SyntaxField
                push!(new_hc_obj_created_somehow, makeObjFieldAsChance_goingBackward(S, possibleNeeded, fin, chance.what, from_new, chance.from, 1))
            end
            # //careful here: # USE A WORD AS A VARIABLE:
            if (possibleNeeded isa SyntaxField && getOneLongFieldPrev(chance.what, possibleNeeded) ===nothing && !occursin(S.inputVec[chance.from], "()[]-><{}:=.,;:_\"'+-/\\_|") # chance.from -1, +1 cuz Julia
                && !any(chance.what.previouses .|> (x->x.object.name == possibleNeeded && x.object.objectFound isa SyntaxInstReference && x.object.objectFound.text == S.inputVec[chance.from])))
                push!(new_hc_obj_created_somehow, makeReferenceFieldChance_goingBackward(S, possibleNeeded, chance))
            elseif (possibleNeeded isa SyntaxSimpleString && !occursin(S.inputVec[chance.from], "()[]-><{}:=.,;:_\"'+-/\\_|") # chance.from -1, +1 cuz Julia
                && !any(chance.what.previouses .|> (x->x.object.name == possibleNeeded && x.object.text == S.inputVec[chance.from])))
                push!(new_hc_obj_created_somehow, makeObjSimpleStringAsChance_goingBackward(S, possibleNeeded, S.inputVec[chance.from], chance.what, chance.from-1, chance.from, 1))# chance.from -1, +1 cuz Julia
            end
        end
        for new_hc_obj in new_hc_obj_created_somehow
            insert!(S.stack, new_hc_obj.POfThisIfGoingBackward, StackableChance(new_hc_obj, chance.from - new_hc_obj.length, chance.from, false, true, true))
            addBeginning(S.hangings, new_hc_obj, chance.from-1)
        end
    end
end

getBestTotalFound(S::Structure11) = getBestTotalFound(S.finisheds)

function insertTerminal(S::Structure11, from::Int, to::Int, what::SyntaxTerm, P::Real)
    temp1 = SyntaxInstOwner(SyntaxInstTerm(what, P))
    temp2 = StackableFinishedSyntax(temp1, from,to)
    if size(S) < to
        ss = size(S)
        reshape(S.finisheds, ss, ss, to-ss)
        reshape(S.hangings, ss, ss, to-ss)
    end
    insert!(S.stack, P, temp2)
end

function insertGlobal(S::Structure11, from::Int, to::Int, s::String, what::TAnno, P::Real)
    temp1 = SyntaxInstOwner(SyntaxInstObject(SyntaxInstReference(what, s, P), P, what)) # GOD this is wasteful... It really sucks ahahaha
    if size(S) < to
        ss = size(S)
        reshape(S.finisheds, ss, ss, to-ss)
        reshape(S.hangings, ss, ss, to-ss)
    end
    add(S.finisheds, from, to, temp1 )
end

process_(S::Structure11, t::StackableChance) = processChance(S, t)
process_(S::Structure11, t::StackableFinishedSyntax) = processFinishedSyntax(S, t)
process_(S::Structure11, t::StackableObject) = processObjectFound(S, t)

printt(s::StackableChance) = "$(s.from) to $(s.to): Chance for $(getString(s.what.chance)), current: $(trace(s.what.object))"
printt(s::StackableFinishedSyntax) = "$(s.from) to $(s.to): Finished $(trace(s.whatFinished.s))"
printt(s::StackableObject) = "$(s.from) to $(s.to): Found: $(trace(s.whatObject.syntax)) (inferred to a $(s.whatObject.inferred_obj.expr|>typeof) obj, $(s.whatObject.inferred_obj.expr|>pr_E) of type $(s.whatObject.inferred_obj.type|>pr))"
# chance|>printt
#S.stack.stack|>length
# S.stack.stack[1][2]|>printt
# S.stack.stack[2][2]|>printt
# S.stack.stack[3][2]|>printt

function doTheBestYouCan(S::Structure11)
    goOn = true
    while goOn
        # if (0 == 1)//stack.peekBestScore() < posteriorsStructure.epsilon)
        #     goOn = false
        #     continue
        # end
        chance = getBest!(S.stack)
        if chance !== nothing
            process_(S, chance)
            if chance.from == 0 && chance.to == size(S) && (chance isa StackableObject) goOn = false end
        else goOn = false
        end
    end
end

getBestObjects(S::Structure11)::Array{SyntaxInstObject} = getBestObjects(S, 0, size(S.finisheds))
getBestObjects(S::Structure11, from, to)::Array{SyntaxInstObject} = at(S.finisheds, from, to) .|> (x->x.s) |> y->filter(x->x isa SyntaxInstObject, y)


function getBestOptions(S::Structure11; n_candidates::Int=7)
    ambiguity=false
    results = Set{SyntaxInstObject}([])
    for s in size(S.finisheds):-1:1
        positions = [(i, i+s) for i in 0:(size(S.finisheds)-s)]
        for (from,to) in positions
            objs = getBestObjects(S, from, to)
            if length(objs) > 1 ambiguity = true end
            for obj in objs union!(results, getMainComponents(obj, 3)) end
            if length(results)>n_candidates return results end
        end
    end
    if ambiguity println("Ambiguity !!!") end
    results
end


results = Set{Int}([])
union!(results, [3,4,4])




score(s::SyntaxInstObject, from::Int, to::Int) = to - from # For now, just prefer the long ones
# function getBests(S::Structure11) = filter(x->x.s isa SyntaxInstObject, at(S.finisheds, 0, size(S.finisheds)))






