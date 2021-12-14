

include("TT/unification_3.jl")
include("TT/mylambda1.jl")
include("Parser/RandomParser10.jl")

s = SyntaxTerm("+")
si = SyntaxInstTerm(s, 1)
s = SyntaxChoice([s, s])
si = SyntaxInstChoice(s, 0, si, 1)
s = SyntaxStruct([s,s])
si = SyntaxInstStruct(s, [si, si], 1)
s = SyntaxField("first", TGlob("A"))
si = SyntaxInstReference(TGlob("A"), "a", 1)
si = SyntaxInstSimpleString("iii", 1)
si = SyntaxInstObject(si, 1, TAnno(TGlob("A"), TypeUniverse()))
si = SyntaxInstField(s, si, 1)
# s = SyntaxStrip()
# si = SyntaxInstStrip()

# fs = FinishedsStructure10(3); fs|>trace
# getS(s) = SyntaxInstOwner(SyntaxInstTerm(SyntaxTerm(s), 1))

# fs = FinishedsStructure10([getS("+"), getS("-"), getS(":")]); fs|>trace
# reshape(fs, 0, 1, 1); fs|>trace
# reshape(fs, 0, 0, 1); fs|>trace
# reshape(fs, 0, 1, 0); fs|>trace
# reshape(fs, 0, 2, 3); fs|>trace
# reshape(fs, 0, 2, 2); fs|>trace

# reshape(fs, 3, 3, 1); fs|>trace
# reshape(fs, 2, 3, 3); fs|>trace
# reshape(fs, 2, 3, 0); fs|>trace
# reshape(fs, 3, 3, 2); fs|>trace

# fs = FinishedsStructure10([getS("+"), getS("-"), getS(":")]); fs|>trace
# set(fs, 0,2,[getS("+-")]); fs|>trace
# @assert [s for s in IterableForElementsEndingAt(fs.matrix, 1)] |> length == 1
# @assert [s for s in IterableForElementsEndingAt(fs.matrix, 2)] |> length == 2
# @assert [s for s in IterableForElementsEndingAt(fs.matrix, 3)] |> length == 1
# @assert [s for s in IterableForElementsStartingFrom(fs.matrix, 0)] |> length == 2
# @assert [s for s in IterableForElementsStartingFrom(fs.matrix, 1)] |> length == 1
# @assert [s for s in IterableForElementsStartingFrom(fs.matrix, 2)] |> length == 1


# # OK!^

# get_hc_beg(s::String) = HangingChance10(
#     SyntaxStruct([SyntaxTerm(s),SyntaxTerm("=")]),
#     SyntaxInstTerm(SyntaxTerm(s), 1),
#     0, 1,
#     1, 1)
# get_hc_beg("+")
# get_hc_end(s::String) = HangingChance10(
#     SyntaxStruct([SyntaxTerm("+"),SyntaxTerm(s)]),
#     SyntaxInstTerm(SyntaxTerm(s), 1),
#     1, 1,
#     1, 1)
# get_hc_end("+")

# function get_cs()
#     cs = ChancesStructure10()
#     reshape(cs, 0,0,3)
#     addBeginning(cs, get_hc_beg("+"), 1)
#     addBeginning(cs, get_hc_beg("+"), 1)
#     addEnding(cs, get_hc_end("="), 1)
#     addEnding(cs, get_hc_end("="), 2)
#     println(cs.beginnings.|>length), println(cs.endings.|>length);
#     cs
# end

# cs = get_cs();

# # reshape(cs, 0,1,0); println(cs.beginnings.|>length), println(cs.endings.|>length);# YES
# # reshape(cs, 0,0,1); println(cs.beginnings.|>length), println(cs.endings.|>length);# deleting too much
# # reshape(cs, 0,1,1); println(cs.beginnings.|>length), println(cs.endings.|>length);# YES

# # reshape(cs, 2,3,0); println(cs.beginnings.|>length), println(cs.endings.|>length);# YES
# # reshape(cs, 2,3,2); println(cs.beginnings.|>length), println(cs.endings.|>length);# YES
# # reshape(cs, 3,3,2); println(cs.beginnings.|>length), println(cs.endings.|>length);# YES



# ########## Parsing 1: Parse "+"

# s10 = Structure11()
# addSyntax!(s10.posteriorsStructure, "+", SyntaxTerm("+"))
# initializeMarginals(s10.posteriorsStructure)
# initializeChoices(s10.posteriorsStructure)
# initializePosteriors(s10.posteriorsStructure)
# # initializeStrips(s10.posteriorsStructure)

# insertTerminal(s10, 0,1,SyntaxTerm("+"), 1)
# s10.finisheds|>trace
# doTheBestYouCan(s10)
# s10.finisheds|>trace


# s10 = Structure11()
# rp = RandomParser10("", [], s10)
# parse(rp, "+")
# rp.structure|>trace



# ########## Parsing 2: Parse "->"

# s10 = Structure11()

# SyntaxTerms = Dict{String, SyntaxTerm}()
# SyntaxFields = Dict{String, SyntaxField}()
# SyntaxChoicess = Dict{String, SyntaxChoice}()
# SyntaxStructs = Dict{String, SyntaxStruct}()
# SyntaxStrips = Dict{String, SyntaxStrip}()
# TypeBases = Dict{String, TGlob}()
# TypeFuncs = Dict{String, Term}()
# TypeSums = Dict{String, TSum}()
# TypeProds = Dict{String, TProd}()
# bindings = Dict{Term, SyntaxCore}()

# for i in ["{", "-",">"] SyntaxTerms[i] =SyntaxTerm(i) end
# SyntaxStructs["arrow"] = SyntaxStruct(Array{SyntaxCore}([SyntaxTerms["-"], SyntaxTerms[">"]]))
# SyntaxChoicess["arrow_S"] = SyntaxChoice(Array{SyntaxCore}([SyntaxStructs["arrow"]]))

# for (name, s) in SyntaxTerms  addSyntax!(s10.posteriorsStructure, name, s) end
# for (name, s) in SyntaxChoicess  addSyntax!(s10.posteriorsStructure, name, s) end
# for (name, s) in SyntaxStructs  addSyntax!(s10.posteriorsStructure, name, s) end
# initializeMarginals(s10.posteriorsStructure)
# initializeChoices(s10.posteriorsStructure)
# initializePosteriors(s10.posteriorsStructure)


# text = "->"

# rp = RandomParser10("", [], s10);
# parse(rp, text)
# rp.structure|>trace



########## Parsing 3: Parse some stuff

# buildTypeThatHasSyntInst(s::SyntaxInstStrip, builder_func) = builder_func(collect_strip(s)) # builder_func is REQUIRED to be a (Dict{str, TAnno}) -> TAnno
# buildTypeThatHasSyntInst(s::SyntaxInstStruct, builder_func) = builder_func(collect_fields(s)) # builder_func is REQUIRED to be a (Array{TAnno}) -> TAnno
# buildTypeThatHasSyntInst(s::SyntaxInstChoice, builder_func::Array) = buildTypeThatHasSyntInst(s.choice, builder_func[s.flag+1]) # builder_func is REQUIRED to be a Array{(Dict{str, TAnno}) -> TAnno}


function builder_typearrow(s::SyntaxInstChoice)
    # SyntaxChoicess["typearrow"] = SyntaxChoice(Array{SyntaxCore}([SyntaxStructs["typearrowPar"], SyntaxStrips["typearrowStrip"]]))
    if s.flag == 0 collect_fields(s)["typearrowPar_inpar"]
    else foldr(build_anno_term_TTerm, collect_strip(s))
end

function builder_funcApp(s::SyntaxInstStruct)::TAnno
    # SyntaxStructs["funcApp"] = auto_SyntStruct(AUSS([SyntaxField("funcApp_func", TTerm(TLocInt(1), TLocInt(2))), "(", SyntaxField("funcApp_arg", TLocInt(1)), ")"]))
    fields = collect_fields(s)
    build_anno_term_TApp([fields["funcApp_arg"], fields["funcApp_func"]])
end
function builder_termannotated(s::SyntaxInstStruct)::TAnno
    # SyntaxStructs["termannotated"] = auto_SyntStruct(AUSS([SyntaxField("termannotated_anno_obj", TLocInt(1)), ":", SyntaxField("termannotated_anno_type", TypeUniverse())]))
    fields = collect_fields(s)
    build_anno_term_TAnno(fields["termannotated_anno_obj"], fields["termannotated_anno_type"])
end
function builder_typedef(s::SyntaxInstStruct)::TAnno # For the :Type" syntax
    # SyntaxStructs["typedef"] = auto_SyntStruct(AUSS([SyntaxField("typedef_tname", TypeUniverse()), ":", "Type"]))
    fields = collect_fields(s)
    if fields["typedef_tname"].type.t_out !==TypeUniverse()
        throw(DomainError("Whats going on here ???????? with term $(fields["typedef_tname"]|>pr) written to be : \"Type\", but it didnt come out as a TypeUniverse at all, tho ..."))
    end
    fields["typedef_tname"] # It should ALREADY be a TAnno... ^
end
function builder_product(s::SyntaxInstStrip)::TAnno
    # SyntaxStrips["product"] = auto_SyntStrip(SyntaxTerm("["), SyntaxField("product_fieldS", TLocInt(1)), SyntaxTerm(","), SyntaxTerm("]"))
    build_anno_term_TProd(collect_strip_tannos(s))
end
function builder_productDefFields(s::SyntaxInstStrip)::TAnno
    # SyntaxStrips["productDefFields"] = auto_SyntStrip(SyntaxTerm("["), SyntaxField("productDefFields_fieldS", TLocInt(1)), SyntaxTerm(","), SyntaxTerm("]"))
    dict = Dict{Str, TAnno}(collect_simpleStrings(sstruct)["namedfield_fieldname"] => collect_fields(sstruct)["namedfield_type"] for sstruct in getObjects(s))
    # ^ for EACH VALUE, val.type.t_out should be GUARANTEED to be a TypeUniverse !! (while val.term is the TLocStr)
    build_anno_term_TProd(collect_strip_tannos(s))
end



# function references_handler(d::Array{Dict})



function make_s10()
    s10 = Structure11()

    SyntaxTerms = Dict{String, SyntaxTerm}()
    SyntaxFields = Dict{String, SyntaxField}()
    SyntaxChoicess = Dict{String, SyntaxChoice}()
    SyntaxStructs = Dict{String, SyntaxStruct}()
    SyntaxStrips = Dict{String, SyntaxStrip}()
    TypeBases = Dict{String, TGlob}()
    TypeFuncs = Dict{String, Term}()
    TypeSums = Dict{String, TSum}()
    TypeProds = Dict{String, TProd}()
    bindings = Dict{String, Any}()  # Any is an ARRAY OF FUNCTIONS

    for i in ["{", "-",">",":","=","(",")",";","where","Type","eval","}", "x", "+"] SyntaxTerms[i] =SyntaxTerm(i) end

    function auto_SyntStruct(ss::Array{Union{String, SyntaxCore}})
        for (i, s) in enumerate(ss)
            if s isa SyntaxField
                SyntaxFields[s.name] = s
                ss[i] = SyntaxFields[s.name]  # In Julia this is prob exactly the same, but i want ref equality
            elseif s isa String
                SyntaxTerms[s] = SyntaxTerm(s)
                ss[i] = SyntaxTerms[s]  # In Julia this is prob exactly the same, but i want ref equality
        end end
        SyntaxStruct(ss)
    end
    function auto_SyntStrip(ssb::Union{String, SyntaxCore, Nothing}, sso::Union{String, SyntaxCore}, ssc::Union{String, SyntaxCore}, ssa::Union{String, SyntaxCore, Nothing})
        dd = Dict("ssb"=> ssb,"sso"=> sso,"ssc"=> ssc,"ssa"=> ssa,)
        for (n, s) in dd
            if s isa SyntaxField
            SyntaxFields[s.name] = s
            dd[n] = s  # In Julia this is prob exactly the same, but i want ref equality
        elseif s isa String
            SyntaxTerms[s] = SyntaxTerm(s)
            dd[n] = SyntaxTerms[s]  # In Julia this is prob exactly the same, but i want ref equality
        end end
        SyntaxStrip(dd["ssb"], dd["sso"], dd["ssc"], dd["ssa"])
    end
    AUSS = Array{Union{String, SyntaxCore}}

    # SyntaxStructs["typearrow_nopar"] = auto_SyntStruct(AUSS[SyntaxField("first", TypeUniverse()), SyntaxStructs["arrow"], SyntaxField("second", TypeUniverse())])
    SyntaxStructs["arrow"] = SyntaxStruct(Array{SyntaxCore}([SyntaxTerms["-"], SyntaxTerms[">"]]))
    SyntaxStrips["typearrowStrip"] = auto_SyntStrip(nothing, SyntaxField("typearrowStrip_first", TypeUniverse()), SyntaxStructs["arrow"], nothing)
    SyntaxStructs["typearrowPar"] = auto_SyntStruct(AUSS(["(", SyntaxField("typearrowPar_inpar", TypeUniverse()), ")"]))
    SyntaxChoicess["typearrow"] = SyntaxChoice(Array{SyntaxCore}([SyntaxStructs["typearrowPar"], SyntaxStrips["typearrowStrip"]]))
    bindings["typearrow"] =[builder_typearrow]

    SyntaxStructs["funcApp"] = auto_SyntStruct(AUSS([SyntaxField("funcApp_func", TTerm(TLocInt(1), TLocInt(2))), "(", SyntaxField("funcApp_arg", TLocInt(1)), ")"]))
    bindings["funcApp"] = [builder_funcApp]

    SyntaxStructs["typedef"] = auto_SyntStruct(AUSS([SyntaxField("typedef_tname", TypeUniverse()), ":", "Type"]))
    bindings["typedef"] = [builder_typedef]

    SyntaxStructs["termannotated"] = auto_SyntStruct(AUSS([SyntaxField("termannotated_anno_obj", TLocInt(1)), ":", SyntaxField("termannotated_anno_type", TypeUniverse())]))
    bindings["termannotated"] = [builder_termannotated]

    SyntaxStrips["product"] = auto_SyntStrip(SyntaxTerm("["), SyntaxField("product_fieldS", TLocInt(1)), SyntaxTerm(","), SyntaxTerm("]"))
    bindings["product"] = [builder_product]

    SyntaxStructs["namedfield"] = auto_SyntStruct(AUSS([SyntaxSimpleString("namedfield_fieldname"), ":", SyntaxField("namedfield_type", TypeUniverse())]))
    SyntaxStrips["productDefFields"] = auto_SyntStrip(SyntaxTerm("["), SyntaxStructs["namedfield"], SyntaxTerm("x"), SyntaxTerm("]"))
    bindings["productDefFields"] = [builder_productDefFields]

    SyntaxStrips["funcConc"] = auto_SyntStrip(SyntaxTerm("{"), SyntaxField("field", TLocInt(1)), SyntaxTerm(","), SyntaxTerm("}"))


    s10p = s10.posteriorsStructure
    for (name, s) in SyntaxTerms  addSyntax!(s10p, name, s) end
    for (name, s) in SyntaxChoicess  addSyntax!(s10p, name, s) end
    for (name, s) in SyntaxStructs  addSyntax!(s10p, name, s) end
    for (name, s) in SyntaxStrips  addSyntax!(s10p, name, s) end
    for (name, s) in SyntaxFields  addSyntax!(s10p, name, s) end
    initializeMarginals(s10p)
    initializeChoices(s10p)
    initializePosteriors(s10p)

    for (name, bind) in bindings s10p.bindings[s10p.allSyntaxes[name]] = bind end

    # s10p.bindings[s10p.allSyntaxes["typearrow"]] = [typearrow_builder_strip]

    addGlobal!(s10p, TGlobAutoCtx("b"))
    s10
end


# request = getInferredTerm(SyntaxInstReference(getType(SyntaxField("first", TypeUniverse())),"A", 0.5))
# request.expr |> pr
# request.type |> pr
# got = rp.structure.finisheds.matrix[1][13] |> x->filter(y->y.s isa SyntaxInstObject, x) |> x->x[1].s.inferred_obj
# got.expr |> pr
# got.type |> pr
# robinsonUnify(got.type.t_out, request.type.t_out; mode=imply_)
# can_be_a(got.type.t_out, request.type.t_out)


s10 = make_s10();
text = "A->B"
rp = RandomParser10("", [], s10);
parse(rp, text)
rp.structure|>trace
getBest(rp.structure)[1] |> (x->trace(x; top=true))

s10 = make_s10();
text = "b"
rp = RandomParser10("", [], s10);
parse(rp, text)
rp.structure|>trace
getBest(rp.structure)[1] |> (x->trace(x; top=true))

s10 = make_s10();
text = "(A->B->C)"
rp = RandomParser10("", [], s10);
parse(rp, text)
rp.structure|>trace
getBest(rp.structure)[1] |> (x->trace(x; top=true))

s10 = make_s10();
text = "((A->B)->B)"
rp = RandomParser10("", [], s10);
parse(rp, text)
rp.structure|>trace
getBest(rp.structure)[1] |> (x->trace(x; top=true))

s10 = make_s10();
text = "g(a)"
rp = RandomParser10("", [], s10);
parse(rp, text)
rp.structure|>trace
getBest(rp.structure)[1] |> (x->trace(x; top=true))

s10 = make_s10();
text = "g(a):B"
rp = RandomParser10("", [], s10);
parse(rp, text)
rp.structure|>trace
getBest(rp.structure)[1] |> (x->trace(x; top=true))

s10 = make_s10();
text = "ff:A where ff (  g  )  =  x"
rp = RandomParser10("", [], s10);
parse(rp, text)
rp.structure|>trace
getBest(rp.structure)[1] |> (x->trace(x; top=true))
println("(Btw, length(inputVec) = $(length(rp.inputVec)))")


s10 = make_s10();
text = "ff:A->B where ff (  g  )  =  b"
rp = RandomParser10("", [], s10);
parse(rp, text)
rp.structure|>trace
getBest(rp.structure)[1] |> (x->trace(x; top=true))

s10 = make_s10();
text = "ff:(A->B)-> B  where ff (  g  )  =  g  (  a ) ; eval ff ( h ) "
rp = RandomParser10("", [], s10);
parse(rp, text)
rp.structure|>trace
getBest(rp.structure)[1] |> (x->trace(x; top=true))







# # //randomParser10.getBestTotalFound.? get.{as SyntaxInstStruct->x | as _->None}.? name.display, WHICH IS OF TYPE: Action + 1, WHATEVER THIS MEANS




# # int main3()

# # // this is the text you MEAN to use (you just compile it, not parse it):
# text::String = "a:A; (1.a):A+B"

# # // type expession: T = A + ("T -> T") where A is base type and "T -> T" is the function type
# makeNiceTreeStructure("baseTypeVariable", "SumType", "type", "case1", "case2")



# hChance.chance|>getString
# hChance.object|>trace
# hChance.previouses|>length; hChance.previouses[1].object|>trace

# hChance.previouses[1].previouses|>length
# hChance.previouses[1].previouses[1].object|>trace

# hChance.previouses[1].previouses[1].previouses|>length
# hChance.previouses[1].previouses[1].previouses[1].object|>trace

# hChance.previouses[1].previouses[1].previouses[1].previouses|>length
# hChance.previouses[1].previouses[1].previouses[1].previouses[1].object|>trace

# hChance.previouses[1].previouses[1].previouses[1].previouses[1].previouses|>length
# hChance.previouses[1].previouses[1].previouses[1].previouses[1].previouses[1].object|>trace

# hChance.previouses[1].previouses[1].previouses[1].previouses[1].previouses[1].previouses|>length
# hChance.previouses[1].previouses[1].previouses[1].previouses[1].previouses[1].previouses[1].object|>trace

# hChance.previouses[1].previouses[1].previouses[1].previouses[1].previouses[1].previouses[1].previouses|>length