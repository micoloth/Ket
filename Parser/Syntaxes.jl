include("STSP_Types.jl")

abstract type SyntaxCore end
abstract type SyntaxProduct <: SyntaxCore end

struct SyntaxTerm <: SyntaxCore
	name::String  # //it's ALSO THE STRING ITSELF
end

struct SyntaxField <: SyntaxCore
	name::String  # //field name
	type::Temp_Type # //the TYPE OF THE OBJECT, of course (ie it requires to parse out a NEW obj che è >>:<< type<.  //// ( oppure, a new aobj who is :T where T >>isA<< type<. )
end
getType(s::SyntaxField) = s.type

struct SyntaxChoice <: SyntaxCore
	list::Array{SyntaxCore}
end
getSize(s::SyntaxChoice) = length(s.list)

struct SyntaxStruct <: SyntaxProduct
	list::Array{SyntaxCore}
end
getSize(s::SyntaxStruct) = length(s.list)

struct SyntaxStrip <: SyntaxProduct
	before::SyntaxCore
	object::SyntaxCore
	comma::SyntaxCore
	after::SyntaxCore
end

getString(s::SyntaxTerm)::String = s.name
getString(s::SyntaxField)::String = "#F{$(s.name):$(s.type|>trace)}"  # //gets FIELD name
getString(s::SyntaxChoice)::String = "#C(" * join(s.list .|> getString, " or ") * ")"
getString(s::SyntaxStruct)::String = join(s.list .|> getString, " ")
getString(s::SyntaxStrip)::String = "#S[$(s.before|>getString) $(s.object|>getString) $(s.comma |> getString) $(s.after |> getString)]"


function getPossibleNexts(s::SyntaxStruct, last::SyntaxCore, to::Int)::Array{SyntaxCore}
    # STARTS FROM 0  #// to EXCLUDED, === pos where NEXT should be!!!
    @assert !(to >= length(s.list) + 1 || to < 0) "bad: index in getPossibleNexts was to=$(to), list length $( length(s.list) )"
	if (to == length(s.list))
		return Array{SyntaxCore}([])
	elseif (to == 0)
		return Array{SyntaxCore}([s.list[1]])
	elseif (last != s.list[to])
		throw(DomainError("oi: s.list[$(to)] = $(s.list[to]) was expected to be $(last).\n\nThis in the context of s.list $(s.list.|>getString)"))
	else
		return Array{SyntaxCore}([s.list[to+1]])
    end
end
function getPossiblePreviouses(s::SyntaxStruct, first::SyntaxCore, from::Int)::Array{SyntaxCore}
    # STARTS FROM 0  #//from INCLUDED, === index of FIRST USED (i.e. first)
    @assert !(from >= length(s.list) + 1 || from < 0) "bad: index in getPossiblePreviouses was from=$(from), list length $( length(s.list) )"
	if (from == 0)
		return Array{SyntaxCore}([])
	elseif (from == length(s.list))
		return Array{SyntaxCore}([s.list[end]])
	elseif (first != s.list[from+1])
		throw(DomainError("oi: s.list[$(from+1)] = $(s.list[from+1]) was expected to be $(first).\n\nThis in the context of s.list $(s.list.|>getString)"))
	else
		return Array{SyntaxCore}([s.list[from]])
    end
end


function getPossibleNexts(s::SyntaxStrip, last::SyntaxCore, to::Int)::Array{SyntaxCore}  #// to EXCLUDED, === pos where NEXT should be!!!
    if (last == s.after)
		return Array{SyntaxCore}([])
	elseif (last == s.object)
		return Array{SyntaxCore}([s.comma,s.after])
	elseif (last == s.comma || last == s.before)
		return Array{SyntaxCore}([s.object])
	else
		return Array{SyntaxCore}([s.before])
    end
end
function getPossiblePreviouses(s::SyntaxStrip, first::SyntaxCore, from::Int)::Array{SyntaxCore} #//from INCLUDED, === index of FIRST USED (i.e. first)
	if (first == s.before)
		return Array{SyntaxCore}([])
	elseif (first == s.object)
		return Array{SyntaxCore}([s.comma,s.before])
	elseif (first == s.comma || first == s.after)
		return Array{SyntaxCore}([s.object])
	else
		return Array{SyntaxCore}([s.after])
    end
end
