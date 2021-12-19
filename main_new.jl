

include("TT/unification_3.jl")
include("TT/mylambda1.jl")
include("Parser/RandomParser10.jl")

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

# buildTypeThatHasSyntInst(s::SyntaxInstStrip, builder_func) = builder_func(collect_strip_tannos(s)) # builder_func is REQUIRED to be a (Dict{str, TAnno}) -> TAnno
# buildTypeThatHasSyntInst(s::SyntaxInstStruct, builder_func) = builder_func(collect_fields(s)) # builder_func is REQUIRED to be a (Array{TAnno}) -> TAnno
# buildTypeThatHasSyntInst(s::SyntaxInstChoice, builder_func::Array) = buildTypeThatHasSyntInst(s.choice, builder_func[s.flag+1]) # builder_func is REQUIRED to be a Array{(Dict{str, TAnno}) -> TAnno}


function builder_typearrow(s::SyntaxInstChoice)
    # SyntaxChoicess["typearrow"] = SyntaxChoice(Array{SyntaxCore}([SyntaxStructs["typearrowPar"], SyntaxStrips["typearrowStrip"]]))
    if s.flag == 0 collect_fields(s.choice)["typearrowPar_inpar"]
    else foldr(build_anno_term_TTerm, collect_strip_tannos(s.choice)) end
end

function builder_funcApp(s::SyntaxInstStruct)::TAnno
    # SyntaxStructs["funcApp"] = auto_SyntStruct(AUSS([SyntaxField("funcApp_func", TTerm(TLocInt(1), TLocInt(2))), "(", SyntaxField("funcApp_arg", TLocInt(1)), ")"]))
    fields = collect_fields(s)
    build_anno_term_TApp([fields["funcApp_arg"], fields["funcApp_func"]])
end
function builder_termannotated(s::SyntaxInstStruct)::TAnno
    # SyntaxStructs["termannotated"] = auto_SyntStruct(AUSS([SyntaxField("termannotated_anno_obj", TLocInt(1)), ":", SyntaxField("termannotated_anno_type", TLocInt(1))]))
    fields = collect_fields(s)
    build_anno_term_TAnno(fields["termannotated_anno_obj"], fields["termannotated_anno_type"])
end
function builder_typedef(s::SyntaxInstStruct)::TAnno # For the :Type" syntax
    # SyntaxStructs["typedef"] = auto_SyntStruct(AUSS([SyntaxField("typedef_tname", TLocInt(1)), ":", "Type"]))
    fields = collect_fields(s)
    # if fields["typedef_tname"].type.t_out !==TLocInt(1)
    #     throw(DomainError("Whats going on here ???????? with term $(fields["typedef_tname"]|>pr) written to be : \"Type\", but it didnt come out as a TypeUniverse at all, tho ..."))
    # end
    fields["typedef_tname"] # It should ALREADY be a TAnno... ^
end
function builder_product(s::SyntaxInstStrip)::TAnno
    # SyntaxStrips["product"] = auto_SyntStrip(SyntaxTerm("["), SyntaxField("product_fieldS", TLocInt(1)), SyntaxTerm(","), SyntaxTerm("]"))
    build_anno_term_TProd(collect_strip_tannos(s))
end
function builder_productDefFields(s::SyntaxInstStrip)::TAnno
    # SyntaxStrips["productDefFields"] = auto_SyntStrip(SyntaxTerm("["), SyntaxField("productDefFields_fieldS", TLocInt(1)), SyntaxTerm(","), SyntaxTerm("]"))
    dict = Dict{String, TAnno}(collect_simpleStrings(sstruct)["namedfield_fieldname"] => collect_fields(sstruct)["namedfield_type"] for sstruct in getObjects(s))
    build_anno_term_TProd(Array{TAnno}([]); dict_anno=dict)
end
function builder_funcBodyDef(s::SyntaxInstStruct)::TAnno
    # SyntaxStructs["funcBodyDef"] = auto_SyntStruct(AUSS([SyntaxTerm("{"), SyntaxField("funcBodyDef_body", TLocInt(1)), SyntaxTerm("}")]))
    build_anno_term_TAbs(collect_fields(s)["funcBodyDef_body"])
end
function builder_funcConc(s::SyntaxInstStrip)::TAnno
    # SyntaxStructs["funcConc"] = auto_SyntStruct(AUSS([SyntaxTerm("{"), SyntaxField("funcConc_body", TLocInt(1)), SyntaxTerm("}")]))
    build_anno_term_TConc(collect_strip_tannos(s))
end
function builder_funcAppNamedArgs(s::SyntaxInstStruct)::TAnno
    # SyntaxStructs["funcAppNamedArgs"] = auto_SyntStruct(AUSS([SyntaxField("funcAppNamedArgs_func", TTerm(TLocInt(1), TLocInt(2))), SyntaxStrips["productArgInFunc"]]))
    dict = Dict{String, TAnno}(collect_simpleStrings(sstruct)["namedArg_Argname"] => collect_fields(sstruct)["namedArg_term"]
                               for sstruct in getObjects(s.list[2])) # [2] is productArgInFunc !!!!
    prod_arg = build_anno_term_TProd(Array{TAnno}([]); dict_anno=dict)
    build_anno_term_TApp([prod_arg, collect_fields(s)["funcAppNamedArgs_func"]])
end


function order_list_of_nodes(list_of_nodes::Array{Pair{String, TAnno}})
    parents = list_of_nodes .|> (x->x[1])
    g = SimpleDiGraph(length(parents))
    pos_dict = Dict(word=>i for (i, word) in enumerate(parents))
    @assert length(unique(parents)) == length(parents)
    for node in list_of_nodes
        for child in node[2].t_in.data_tags .|> x->x[1]  #<- these are the REQUIRED fields
            if child in parents
                add_edge!(g, pos_dict[child], pos_dict[node[1]])
            end
        end
    end
    @assert !is_cyclic(g)
    order = topological_sort_by_dfs(g)
    [list_of_nodes[i] for i in order]
end


function builder_programFlowInPars(s::SyntaxInstStrip)::TAnno
    # SyntaxStructs["namedfield"] = auto_SyntStruct(AUSS([SyntaxSimpleString("namedfield_fieldname"), ":", SyntaxField("namedfield_type", TLocInt(1))]))
    # SyntaxStructs["namedTypedObj"] = auto_SyntStruct(AUSS([SyntaxStructs["namedfield"], "=", SyntaxField("namedTypedObj_term", TLocInt(1))]))
    # SyntaxStructs["returnObj"] = auto_SyntStruct(AUSS(["return", SyntaxField("returnObj_term", TLocInt(1))]))
    # SyntaxChoicess["namedTypedObj_or_returnObj"] = SyntaxChoice(Array{SyntaxCore}([SyntaxStructs["namedTypedObj"], SyntaxStructs["returnObj"]]))
    # SyntaxStrips["programFlowInPars"] = auto_SyntStrip(SyntaxTerm("{"), SyntaxStructs["namedTypedObj_or_returnObj"], SyntaxTerm(";"), SyntaxTerm("}"))
    # bindings["programFlowInPars"] = [builder_programFlowInPars]
    strip_objects = getObjects(s)
    thorw(DomainError("BAD"))
    strip_objs_namedTypedObj = [sstruct.choice for sstruct in strip_objects if sstruct.flag == 0] # meaning namedTypedObj
    dict = Array{Pair{String, TAnno}}([collect_simpleStrings(sstruct)["namedfield_fieldname"] => (collect_fields(sstruct)["namedfield_type"], collect_fields(sstruct)["namedTypedObj_term"])
                               for sstruct in strip_objs_namedTypedObj])
    dict = Array{Pair{String, TAnno}}([name=> build_anno_term_TAnno(term, type) for (name, (type, term)) in dict])
    dict = order_list_of_nodes(dict)

    build_anno_term_TProd(Array{TAnno}([]); dict_anno=dict)
    prod_arg = build_anno_term_TProd(Array{TAnno}([]); dict_anno=dict)
    build_anno_term_TApp([prod_arg, collect_fields(s)["funcAppNamedArgs_func"]])
end

# function references_handler(d::Array{Dict})



function make_s10()
    s10 = Structure11()

    SyntaxTerms = Dict{String, SyntaxTerm}()
    SyntaxFields = Dict{String, SyntaxField}()
    SyntaxSimpleStrings = Dict{String, SyntaxSimpleString}()
    SyntaxChoicess = Dict{String, SyntaxChoice}()
    SyntaxStructs = Dict{String, SyntaxStruct}()
    SyntaxStrips = Dict{String, SyntaxStrip}()
    TypeBases = Dict{String, TGlob}()
    TypeFuncs = Dict{String, Term}()
    TypeSums = Dict{String, TSum}()
    TypeProds = Dict{String, TProd}()
    bindings = Dict{String, Any}()  # Any is an ARRAY OF FUNCTIONS

    for i in ["{","[","]","/","\\", "-",">",".",":","=","(",")",";",",","where","Type","eval","}", "x", "+", "return"] SyntaxTerms[i] =SyntaxTerm(i) end

    function auto_SyntStruct(ss::Array{Union{String, SyntaxCore}})
        for (i, s) in enumerate(ss)
            if s isa SyntaxField
                SyntaxFields[s.name] = s
                ss[i] = SyntaxFields[s.name]  # In Julia this is prob exactly the same, but i want ref equality
            elseif s isa SyntaxSimpleString
                SyntaxSimpleStrings[s.name] = s
                ss[i] = SyntaxSimpleStrings[s.name]  # In Julia this is prob exactly the same, but i want ref equality
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
        elseif s isa SyntaxSimpleString
            SyntaxSimpleStrings[s.name] = s
            dd[n] = SyntaxSimpleStrings[s.name]  # In Julia this is prob exactly the same, but i want ref equality
        elseif s isa String
            SyntaxTerms[s] = SyntaxTerm(s)
            dd[n] = SyntaxTerms[s]  # In Julia this is prob exactly the same, but i want ref equality
        end end
        SyntaxStrip(dd["ssb"], dd["sso"], dd["ssc"], dd["ssa"])
    end
    AUSS = Array{Union{String, SyntaxCore}}

    # SyntaxStructs["typearrow_nopar"] = auto_SyntStruct(AUSS[SyntaxField("first", TLocInt(1)), SyntaxStructs["arrow"], SyntaxField("second", TLocInt(1))])
    SyntaxStructs["arrow"] = SyntaxStruct(Array{SyntaxCore}([SyntaxTerms["-"], SyntaxTerms[">"]]))
    SyntaxStrips["typearrowStrip"] = auto_SyntStrip(nothing, SyntaxField("typearrowStrip_first", TLocInt(1)), SyntaxStructs["arrow"], nothing)
    SyntaxStructs["typearrowPar"] = auto_SyntStruct(AUSS(["(", SyntaxField("typearrowPar_inpar", TLocInt(1)), ")"]))
    SyntaxChoicess["typearrow"] = SyntaxChoice(Array{SyntaxCore}([SyntaxStructs["typearrowPar"], SyntaxStrips["typearrowStrip"]]))
    bindings["typearrow"] =[builder_typearrow]

    SyntaxStructs["funcApp"] = auto_SyntStruct(AUSS([SyntaxField("funcApp_func", TTerm(TLocInt(1), TLocInt(2))), "(", SyntaxField("funcApp_arg", TLocInt(1)), ")"]))
    bindings["funcApp"] = [builder_funcApp]

    SyntaxStructs["typedef"] = auto_SyntStruct(AUSS([SyntaxField("typedef_tname", TLocInt(1)), ":", "Type"]))
    bindings["typedef"] = [builder_typedef]

    SyntaxStructs["termannotated"] = auto_SyntStruct(AUSS([SyntaxField("termannotated_anno_obj", TLocInt(1)), ":", SyntaxField("termannotated_anno_type", TLocInt(1))]))
    bindings["termannotated"] = [builder_termannotated]

    SyntaxStrips["product"] = auto_SyntStrip(SyntaxTerm("["), SyntaxField("product_fieldS", TLocInt(1)), SyntaxTerm(","), SyntaxTerm("]"))
    bindings["product"] = [builder_product]

    SyntaxStructs["namedfield"] = auto_SyntStruct(AUSS([SyntaxSimpleString("namedfield_fieldname"), ":", SyntaxField("namedfield_type", TLocInt(1))]))
    SyntaxStrips["productDefFields"] = auto_SyntStrip(SyntaxTerm("["), SyntaxStructs["namedfield"], SyntaxTerm("x"), SyntaxTerm("]"))
    bindings["productDefFields"] = [builder_productDefFields]

    # SyntaxStrips["funcBodyDef"] = auto_SyntStrip(SyntaxTerm("{"), SyntaxField("funcBodyDef_body", TLocInt(1)), SyntaxTerm(","), SyntaxTerm("}"))
    SyntaxStructs["funcBodyDef"] = auto_SyntStruct(AUSS([SyntaxTerm("{"), SyntaxField("funcBodyDef_body", TLocInt(1)), SyntaxTerm("}")]))
    bindings["funcBodyDef"] = [builder_funcBodyDef]

    SyntaxStrips["funcConc"] = auto_SyntStrip(nothing,  SyntaxField("funcConc_func", TLocInt(1)), SyntaxTerm("."), nothing)
    bindings["funcConc"] = [builder_funcConc]

    SyntaxStructs["namedArg"] = auto_SyntStruct(AUSS([SyntaxSimpleString("namedArg_Argname"), "=", SyntaxField("namedArg_term", TLocInt(1))]))
    SyntaxStrips["productArgInFunc"] = auto_SyntStrip(SyntaxTerm("("), SyntaxStructs["namedArg"], SyntaxTerm(","), SyntaxTerm(")"))
    SyntaxStructs["funcAppNamedArgs"] = auto_SyntStruct(AUSS([SyntaxField("funcAppNamedArgs_func", TTerm(TLocInt(1), TLocInt(2))), SyntaxStrips["productArgInFunc"]]))
    bindings["funcAppNamedArgs"] = [builder_funcAppNamedArgs]

    SyntaxStructs["namedTypedObj"] = auto_SyntStruct(AUSS([SyntaxStructs["namedfield"], "=", SyntaxField("namedTypedObj_term", TLocInt(1))]))
    SyntaxStructs["returnObj"] = auto_SyntStruct(AUSS(["return", SyntaxField("returnObj_term", TLocInt(1))]))
    SyntaxChoicess["namedTypedObj_or_returnObj"] = SyntaxChoice(Array{SyntaxCore}([SyntaxStructs["namedTypedObj"], SyntaxStructs["returnObj"]]))
    SyntaxStrips["programFlowInPars"] = auto_SyntStrip(SyntaxTerm("{"), SyntaxChoicess["namedTypedObj_or_returnObj"], SyntaxTerm(";"), SyntaxTerm("}"))
    bindings["programFlowInPars"] = [builder_programFlowInPars]

    s10p = s10.posteriorsStructure
    for (name, s) in SyntaxTerms  addSyntax!(s10p, name, s) end
    for (name, s) in SyntaxChoicess  addSyntax!(s10p, name, s) end
    for (name, s) in SyntaxStructs  addSyntax!(s10p, name, s) end
    for (name, s) in SyntaxStrips  addSyntax!(s10p, name, s) end
    for (name, s) in SyntaxFields  addSyntax!(s10p, name, s) end
    for (name, s) in SyntaxSimpleStrings  addSyntax!(s10p, name, s) end
    initializeMarginals(s10p)
    initializeChoices(s10p)
    initializePosteriors(s10p)

    for (name, bind) in bindings s10p.bindings[s10p.allSyntaxes[name]] = bind end

    # s10p.bindings[s10p.allSyntaxes["typearrow"]] = [typearrow_builder_strip]

    addGlobal!(s10p, TGlobAutoCtx("a"))
    addGlobal!(s10p, TGlobAutoCtx("b"))
    addGlobal!(s10p, TGlobAutoCtx("c"))
    s10
end


s10 = make_s10();
text = "b"
rp = RandomParser10("", [], s10);
parse(rp, text)
rp.structure|>trace
getBest(rp.structure)[1] |> (x->trace(x; top=true))

s10 = make_s10();
text = "A->B"
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
text = "g(e)"
rp = RandomParser10("", [], s10);
parse(rp, text)
rp.structure|>trace
getBest(rp.structure)[1] |> (x->trace(x; top=true))

s10 = make_s10();
text = "g(e):B"
rp = RandomParser10("", [], s10);
parse(rp, text)
rp.structure|>trace
getBest(rp.structure)[1] |> (x->trace(x; top=true))

s10 = make_s10();
text = "[k:A x h:B]"
rp = RandomParser10("", [], s10);
parse(rp, text)
rp.structure|>trace
getBest(rp.structure)[1] |> (x->trace(x; top=true))

s10 = make_s10();
text = "{g(k)}"
rp = RandomParser10("", [], s10);
parse(rp, text)
rp.structure|>trace
getBest(rp.structure)[1] |> (x->trace(x; top=true))

s10 = make_s10();
text = "f(k=h, d=e)"
rp = RandomParser10("", [], s10);
parse(rp, text)
rp.structure|>trace
getBest(rp.structure)[1] |> (x->trace(x; top=true))

s10 = make_s10();
text = "f(z=n)(k=h)"
rp = RandomParser10("", [], s10);
parse(rp, text)
rp.structure|>trace
getBest(rp.structure)[1] |> (x->trace(x; top=true))

s10 = make_s10();
text = "{1(3)(2(3))}"
rp = RandomParser10("", [], s10);
parse(rp, text)
rp.structure|>trace
getBest(rp.structure)[1] |> (x->trace(x; top=true))

s10 = make_s10();
text = "{1(3)(2(3))}(1={1}, 2={b}, 3=a)"
rp = RandomParser10("", [], s10);
parse(rp, text)
rp.structure|>trace
getBest(rp.structure)[1] |> (x->trace(x; top=true))


rp.structure.finisheds.matrix[1][13]





println("addEnding")

request = getInferredTerm(SyntaxInstReference(getType(SyntaxField("first", TLocInt(1))),"A", 0.5))
request.expr |> pr
request.type |> pr
got = rp.structure.finisheds.matrix[0+1][12] |> x->filter(y->y.s isa SyntaxInstObject, x) |> x->x[1].s.inferred_obj
got.expr |> pr
got.type |> pr
robinsonUnify(got.type.t_out, request.type.t_out; mode=imply_)
can_be_a(got.type.t_out, request.type.t_out)

a1 = rp.structure.finisheds.matrix[15+1][18-15] |> x->filter(y->y.s isa SyntaxInstObject, x) |> x->x[1].s.inferred_obj
a1.expr |> pr_E
a1.type |> pr_ctx

a2 = rp.structure.finisheds.matrix[20+1][24-20] |> x->filter(y->y.s isa SyntaxInstObject, x) |> x->x[1].s.inferred_obj
a2.expr |> pr_E
a2.type |> pr_ctx

a3 = rp.structure.finisheds.matrix[27+1][28-27] |> x->filter(y->y.s isa SyntaxInstObject, x) |> x->x[1].s.inferred_obj
a3.expr |> pr_E
a3.type |> pr_ctx

# # //randomParser10.getBestTotalFound.? get.{as SyntaxInstStruct->x | as _->None}.? name.display, WHICH IS OF TYPE: Action + 1, WHATEVER THIS MEANS


build_anno_term_TProd(Array{TAnno}([]); dict_anno=Dict{Id, TAnno}("1"=>a1, "2"=>a2, "3"=>a3))



build_anno_term_TProd(Array{TAnno}([a1, a2, a3]))

infer_type_(TProd(Array{Term}([])), Array{TTerm}([a1.type, a2.type, a3.type]))

a1t = TTermEmpty(TTerm(TProd(Array{Pair{String, Term}}(["1" => TLocInt(1)])), TLocInt(1)))
a1t==a1.type
a2t = TTermEmpty(TTermEmpty(TGlob("B")))
a2t==a2.type
a3t = TTermEmpty(TGlob("A"))
a3t==a3.type

infer_type_(TProd(Array{Term}([])), Array{TTerm}([a2t, a3t])) |>pr_ctx
infer_type_(TProd(Array{Term}([])), Array{TTerm}([a3t, a2t])) |>pr_ctx
infer_type_(TProd(Array{Term}([])), Array{TTerm}([a1t, a3t])) |>pr_ctx
infer_type_(TProd(Array{Term}([])), Array{TTerm}([a1t, a2t])) |>pr_ctx
infer_type_(TProd(Array{Term}([])), Array{TTerm}([a1t, a2t, a3t])) |>pr_ctx
infer_type_(TProd(Array{Term}([])), Array{TTerm}([a2t, a3t, a1t])) |>pr_ctx
infer_type_(TProd(Array{Term}([])), Array{TTerm}([a2t, a1t, a3t])) |>pr_ctx



println(hu)




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