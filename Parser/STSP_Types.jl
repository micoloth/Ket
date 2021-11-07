
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




# std::string trace(Bool topLevel =true) const;
# std::string trace(Bool topLevel = true) const { return name; }
# std::string trace(Bool topLevel = true) const { return first.trace(topLevel) + "->" + second.trace(topLevel); }
# std::string trace(Bool topLevel=true) const
# {
#     if (!topLevel) { return "aSumType"; }
#     std::string s = "(";
#     for (auto i : objs)
#         s += i.second.trace(false) + " + ";
#     s.pop_back();
#     s.pop_back();
#     s.pop_back();
#     return s += ")";
# }
# std::string trace(Bool topLevel = true) const
# {
#     if (!topLevel) { return "aProdType"; }

#     std::string s = "(";
#     for (auto i : objs)
#         s += i.second.trace(false) + " x ";
#     s.pop_back();
#     s.pop_back();
#     s.pop_back();
#     return s += ")";
# }
# std::string Temp_Type::trace(Bool topLevel) const { return std::visit([&](auto t)->std::string {return t->trace(topLevel); }, obj); }


