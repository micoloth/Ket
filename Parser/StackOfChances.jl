
include("BidirectionalChancesStructure10.jl")

abstract type StackableBoid end


struct StackableChance <: StackableBoid # //posterior=chance|occurrence, likelyhood=occurrence|chance
	what::Union{HangingChance10, Nothing}
	# //NOT ANYMORE: //it was not a great idea because in the case this is a Object syntaxInstCore, you maybe want to ONLY TRIGGER TYPE CREATION WHEN YOU >ADD< IT, not when chance is presented
    from::Int
    to::Int
	goForward::Bool
	goBackward::Bool
end
getP(s::StackableChance) = (s.goForward ? getPForward(s.what) : 0.0) + (s.goBackward ? getPBackward(s.what) : 0.0)
empty(s::StackableChance)::Bool = s.what === nothing
# int getFrom() { return from; }
# int getTo() { return to; }



struct StackableFinishedSyntax <: StackableBoid
    whatFinished::SyntaxInstObj
	from::Int
	to::Int
    function StackableFinishedSyntax(whatFinished::SyntaxInstObj, from::Int, to::Int)
        @assert !(whatFinished isa SyntaxInstStruct) || !isempty(whatFinished.list)
        return new(whatFinished, from, to)
    end
end
getP(s::StackableFinishedSyntax) = getP(s.whatFinished.s)
empty(s::StackableFinishedSyntax)::Bool = false

# int getFrom() { return from; }
# int getTo() { return to; }
# float getP() { return whatFinished.getP(); }
# int empty() { return 0; }

struct StackableObject <: StackableBoid
    whatFinished::SyntaxInstObject
    from::Int
    to::Int
end
getP(s::StackableObject) = getP(s.whatFinished)
empty(s::StackableObject)::Bool = false


mutable struct StackOfChances
    stack::Array{Tuple{Real, StackableBoid}} # This was a multimap
end
StackOfChances() = StackOfChances([])


function getBest!(s::StackOfChances)::Union{Nothing, StackableBoid}
    if isempty(s.stack) return nothing
    elseif !empty(s.stack[end][2])
        obj = s.stack[end][2]
        s.stack = s.stack[1:(end-1)]
        return obj
    else
        s.stack = s.stack[1:(end-1)]
        return getBest(s::StackOfChances)
    end
end
peekBestScore(s::StackOfChances)= (!isempty(s.stack)) ? s.stack[end][1] : -1
function insert!(s::StackOfChances, p::Real, obj::StackableBoid)
    push!(s.stack, (p, obj))
    sort!(s.stack; by= x->x[1], rev=true)
end

