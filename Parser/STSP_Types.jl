
abstract type Temp_Type end



struct Temp_TypeBase <: Temp_Type
	name::String
end

struct Temp_TypeFunc <: Temp_Type
	first::Temp_Type
	second::Temp_Type
end

struct Temp_TypeSum <: Temp_Type
	objs::Dict{String, Temp_Type}
end
Temp_TypeSum(v::Array{Temp_Type}) = Temp_TypeSum(Dict(string(i)=>e for (i,e) in enumerate(v)))

struct Temp_TypeProd <: Temp_Type
	objs::Dict{String, Temp_Type}
end
Temp_TypeProd(v::Array{Temp_Type}) = Temp_TypeProd(Dict(string(i)=>e for (i,e) in enumerate(v)))

struct Temp_TypeInt <: Temp_Type
	obj::Int
end

# Bool  Temp_Type::operator==(VariantTypes t)const { return t == obj; }
# Bool  Temp_Type::operator==(Temp_Type t)const { return t.obj == obj; }
# Bool  Temp_Type::operator!=(Temp_Type t)const { return t.obj != obj; }
# Bool Temp_Type::operator==(Temp_TypeBase* t)const { return std::holds_alternative<Temp_TypeBase*>(obj) && t == std::get<Temp_TypeBase*>(obj); }
# Bool Temp_Type::operator==(Temp_TypeFunc* t)const { return std::holds_alternative<Temp_TypeFunc*>(obj) && t == std::get<Temp_TypeFunc*>(obj); }
# Bool Temp_Type::operator==(Temp_TypeSum* t)const { return std::holds_alternative<Temp_TypeSum*>(obj) && t == std::get<Temp_TypeSum*>(obj); }
# Bool Temp_Type::operator==(Temp_TypeProd* t)const { return std::holds_alternative<Temp_TypeProd*>(obj) && t == std::get<Temp_TypeProd*>(obj); }




trace(s::Temp_TypeBase, topLevel::Bool = true)::String = s.name
trace(s::Temp_TypeFunc, topLevel::Bool = true)::String = trace(s.first, topLevel) * "->" * trace(s.second, topLevel)
trace(s::Temp_TypeSum, topLevel::Bool = true)::String = if (!topLevel) "aSumType"
	else "(" * join([trace(i.second, false) for i in s.objs], " + ") * ")"
	end
trace(s::Temp_TypeProd, topLevel::Bool = true)::String =if (!topLevel) "aProdType"
else "(" * join([trace(i.second, false) for i in s.objs], " x ") * ")"
end
trace(s::Temp_TypeInt, topLevel::Bool = true)::String = string(s.obj)


