# it REQUIRES that you included ("mylambda1.jl") at Some Point!!!


abstract type SyntaxCore end
abstract type SyntaxProduct <: SyntaxCore end

struct SyntaxTerm <: SyntaxCore
	name::String  # //it's ALSO THE STRING ITSELF
end
struct SyntaxSimpleString <: SyntaxCore
	name::String
end

struct SyntaxField <: SyntaxCore
	name::String  # //field name
	type::Term # //the TYPE OF THE OBJECT, of course (ie it requires to parse out a NEW obj che è >>:<< type<.  //// ( oppure, a new aobj who is :T where T >>isA<< type<. )
end
getType(s::SyntaxField) = s.type
Base.:(==)(a::SyntaxField, b::SyntaxField) = (a.name == b.name) && (a.type === b.type)

struct SyntaxChoice <: SyntaxCore
	list::Array{SyntaxCore}
end
getSize(s::SyntaxChoice) = length(s.list)

struct SyntaxStruct <: SyntaxProduct
	list::Array{SyntaxCore}
end
getSize(s::SyntaxStruct) = length(s.list)

struct SyntaxStrip <: SyntaxProduct
	before::Union{SyntaxCore, Nothing}
	object::SyntaxCore
	comma::SyntaxCore
	after::Union{SyntaxCore, Nothing}
end
SyntaxStrip(obj::SyntaxCore, comma::SyntaxCore) = SyntaxStrip(nothing, obj, comma, nothing)

getString(s::SyntaxTerm)::String = s.name
getString(s::SyntaxSimpleString)::String = "STRING"
getString(s::SyntaxField)::String = "#F{$(s.name):$(s.type|>pr_T)}"  # //gets FIELD name
getString(s::SyntaxChoice)::String = "#C(" * join(s.list .|> getString, " or ") * ")"
getString(s::SyntaxStruct)::String = join(s.list .|> getString, " ")
getString(s::SyntaxStrip)::String = if s.before === nothing "#S[$(s.object|>getString) $(s.comma |> getString)]"
		else "#S[$(s.before|>getString) $(s.object|>getString) $(s.comma |> getString) $(s.after |> getString)]" end


function getPossibleNexts(s::SyntaxStruct, last::SyntaxCore, iic_last::Int)::Array{SyntaxCore}
    # STARTS FROM 0 (meaning its the ZERO BASED POSITION IN LIST)
    @assert !(iic_last >= length(s.list) || iic_last < 0) "bad: index in getPossibleNexts was iic_last=$(iic_last), list length $( length(s.list) )"
	if (iic_last == length(s.list) -1)
		return Array{SyntaxCore}([])
	elseif (iic_last == 0)
		return Array{SyntaxCore}([s.list[1+1]])
	elseif (last != s.list[iic_last+1])
		throw(DomainError("oi: s.list[$(iic_last)] = $(s.list[iic_last+1]) was expected to be $(last).\n\nThis in the context of s.list $(s.list.|>getString)"))
	else
		return Array{SyntaxCore}([s.list[iic_last+1+1]])
    end
end
function getPossiblePreviouses(s::SyntaxStruct, first::SyntaxCore, iic_first::Int)::Array{SyntaxCore}
    # STARTS FROM 0  (meaning its the ZERO BASED POSITION IN LIST)
    @assert !(iic_first >= length(s.list)+1 || iic_first < 0) "bad: index in getPossiblePreviouses was iic_first=$(iic_first), list length $( length(s.list) )"
	if (iic_first == 0)
		return Array{SyntaxCore}([])
	elseif (iic_first == length(s.list))
		return Array{SyntaxCore}([s.list[end]])
	elseif (first != s.list[iic_first+1])
		throw(DomainError("oi: s.list[$(iic_first+1)] = $(s.list[iic_first+1]) was expected to be $(first).\n\nThis in the context of s.list $(s.list.|>getString)"))
	else
		return Array{SyntaxCore}([s.list[iic_first+1-1]])
    end
end

function getPossibleNexts(s::SyntaxStrip, last::SyntaxCore, iic_last::Int)::Array{SyntaxCore}  #// iic_last EXCLUDED, === pos where NEXT should be!!!
	# iic is the Tag, which is ONE-based!
    if (last == s.after)
		@assert iic_last == 4
		return Array{SyntaxCore}([])
	elseif (last == s.object)
		@assert iic_last == 2
		return s.after !== nothing ? Array{SyntaxCore}([s.comma, s.after]) : Array{SyntaxCore}([s.comma])
	elseif (last == s.comma || last == s.before)
		@assert iic_last == 1 || iic_last == 3 "Asking next of $(iic_last)"
		return Array{SyntaxCore}([s.object])
	else
		return s.before !== nothing ? Array{SyntaxCore}([s.before]) : Array{SyntaxCore}([])
    end
end
function getPossiblePreviouses(s::SyntaxStrip, first::SyntaxCore, iic_first::Int)::Array{SyntaxCore} #//iic_first INCLUDED, === index of FIRST USED (i.e. first)
	if (first == s.before)
		@assert iic_first == 1
		return Array{SyntaxCore}([])
	elseif (first == s.object)
		@assert iic_first == 2
		return s.before !== nothing ? Array{SyntaxCore}([s.comma,s.before]) : Array{SyntaxCore}([s.comma,])
	elseif (first == s.comma || first == s.after)
		@assert iic_first == 3 || iic_first == 4 "Asking prev of $(iic_first)"
		return Array{SyntaxCore}([s.object])
	else
		return s.after !== nothing ? Array{SyntaxCore}([s.after]) : Array{SyntaxCore}([])
    end
end


function getPrevIndexes(s::SyntaxCore, i::Int)::Array{Int}
    if s isa SyntaxStruct return [i - 1]
	elseif s isa SyntaxStrip Dict(3=>[2], 4=>[2], 2=>[1,3], 1=>[])[i] end
end
function getNextIndexes(s::SyntaxCore, i::Int)::Array{Int}
    if s isa SyntaxStruct return  [i + 1]
    elseif s isa SyntaxStrip Dict(3=>[2],1=>[2], 2=>[3,4], 4=>[])[i] end
end

function getPrevIndex(s::SyntaxCore, i::Int, newSyntaxCoreThatShouldBeTheNewIndex::SyntaxCore)::Int
	# THIS WHOLE THING IS DUMB. Have you noticed?   # PLEASE REMOVE !!!!
    if s isa SyntaxStruct return i - 1
	elseif s isa SyntaxStrip
		idxs = getPrevIndexes(s, i)
		if 1 in idxs && newSyntaxCoreThatShouldBeTheNewIndex == s.before return 1
		elseif 2 in idxs && newSyntaxCoreThatShouldBeTheNewIndex == s.object return 2
		elseif 3 in idxs && newSyntaxCoreThatShouldBeTheNewIndex == s.comma return 3
		end
	end
end
function getNextIndex(s::SyntaxCore, i::Int, newSyntaxCoreThatShouldBeTheNewIndex::SyntaxCore)::Int
	# THIS WHOLE THING IS DUMB. Have you noticed?   # PLEASE REMOVE !!!!
    if s isa SyntaxStruct return i + 1
    elseif s isa SyntaxStrip
		idxs = getNextIndexes(s, i)
		if 4 in idxs && newSyntaxCoreThatShouldBeTheNewIndex == s.after return 1
		elseif 2 in idxs && newSyntaxCoreThatShouldBeTheNewIndex == s.object return 2
		elseif 3 in idxs && newSyntaxCoreThatShouldBeTheNewIndex == s.comma return 3
		end
	end
end