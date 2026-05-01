def trMkEquality(left: Type, right: Type): EqConstr =
    (left, right)


def trMkGivenEquality(left: Type, right: Type): Constr =
    Constr.Eq(left, right)


def trEmptyConstraintEnv(): ConstrEnv =
    ConstrEnv.ConstrEnv(Map.empty(), Map.empty())


// `x, Int32, Gen(0) -> None`
@Test
def reduceTypeOneStepLeavesSimpleTypesUnchanged(): Unit \ Assert = {
    let tyVar = Tyvar.Tyvar("x", Kind.Star);
    let tyCon = Tycon.Tycon("Int32", Kind.Star);

    Assert.assertEq(
        expected = None,
        Type.Var(tyVar) |> reduceTyOne(trEmptyConstraintEnv(), Nil)
    );
    Assert.assertEq(
        expected = None,
        Type.Con(tyCon) |> reduceTyOne(trEmptyConstraintEnv(), Nil)
    );
    Assert.assertEq(
        expected = None,
        Type.Gen(0) |> reduceTyOne(trEmptyConstraintEnv(), Nil)
    )
}


// given: { Elem x = Bool }
// `Elem x -> Some(Bool)`
@Test
def reduceTypeOneStepUsesGivenEqualityForTyassoc(): Unit \ Assert = {
    let arg = Tyvar.Tyvar("x", Kind.Star);
    let assoc = Tyassoc.Tyassoc("Elem", Type.Var(arg), Kind.Star);
    let bool = Type.Con(Tycon.Tycon("Bool", Kind.Star));

    Assert.assertEq(
        expected = Some(bool),
        Type.Assoc(assoc) |> reduceTyOne(
            trEmptyConstraintEnv(),
            trMkGivenEquality(Type.Assoc(assoc), bool) :: Nil
        )
    )
}


// given: { Elem a = a }
// `Elem Int32 -> None`
@Test
def reduceTypeOneStepGivenEqualityRequiresSyntacticLeftHandSideMatch(): Unit \ Assert = {
    let a = Tyvar.Tyvar("a", Kind.Star);
    let int32 = Type.Con(Tycon.Tycon("Int32", Kind.Star));
    let genericAssoc = Tyassoc.Tyassoc("Elem", Type.Var(a), Kind.Star);
    let specificAssoc = Tyassoc.Tyassoc("Elem", int32, Kind.Star);

    Assert.assertEq(
        expected = None,
        Type.Assoc(specificAssoc) |> reduceTyOne(
            trEmptyConstraintEnv(),
            trMkGivenEquality(
                Type.Assoc(genericAssoc),
                Type.Var(a)
            ) :: Nil
        )
    )
}


// constraintEnv: { Elem a = a }
// `Elem Int32 -> Some(Int32)`
@Test
def reduceTypeOneStepInstantiatesConstraintEnvironmentEquality(): Unit \ Assert = {
    let a = Tyvar.Tyvar("a", Kind.Star);
    let int32 = Type.Con(Tycon.Tycon("Int32", Kind.Star));
    let genericAssoc = Tyassoc.Tyassoc("Elem", Type.Var(a), Kind.Star);
    let specificAssoc = Tyassoc.Tyassoc("Elem", int32, Kind.Star);

    let constraintEnv = ConstrEnv.ConstrEnv(
        Map.singleton(
            "Elem",
            trMkEquality(
                Type.Assoc(genericAssoc),
                Type.Var(a)
            ) :: Nil
        ),
        Map.empty()
    );

    Assert.assertEq(
        expected = Some(int32),
        Type.Assoc(specificAssoc) |> reduceTyOne(
            constraintEnv,
            Nil
        )
    )
}


// constraintEnv: { Inner x = Int32, Outer Int32 = Bool }
// `Outer (Inner x) -> Some(Outer Int32)`
@Test
def reduceTypeOneStepReducesTyassocArgumentBeforeOuterLookup(): Unit \ Assert = {
    let x = Tyvar.Tyvar("x", Kind.Star);
    let inner = Tyassoc.Tyassoc("Inner", Type.Var(x), Kind.Star);
    let outer = Tyassoc.Tyassoc(
        "Outer",
        Type.Assoc(inner),
        Kind.Star
    );
    let int32 = Type.Con(Tycon.Tycon("Int32", Kind.Star));
    let bool = Type.Con(Tycon.Tycon("Bool", Kind.Star));
    let outerAfterArgReduction = Tyassoc.Tyassoc("Outer", int32, Kind.Star);

    let constraintEnv = ConstrEnv.ConstrEnv(
        Map.union(
            Map.singleton(
                "Inner",
                trMkEquality(Type.Assoc(inner), int32) :: Nil
            ),
            Map.singleton(
                "Outer",
                trMkEquality(Type.Assoc(outerAfterArgReduction), bool) :: Nil
            )
        ),
        Map.empty()
    );

    Assert.assertEq(
        expected = Some(Type.Assoc(outerAfterArgReduction)),
        Type.Assoc(outer) |> reduceTyOne(constraintEnv, Nil)
    )
}


// constraintEnv: { UnaryCtor Phantom = Unary, Elem Phantom = Int32 }
// `(UnaryCtor Phantom) (Elem Phantom) -> Some(Unary (Elem Phantom))`
@Test
def reduceTypeOneStepApplicationReducesFunctionBeforeArgument(): Unit \ Assert = {
    let unaryKind = Kind.KFun(
        Kind.Star,
        Kind.Star
    );
    let funcAssoc = Tyassoc.Tyassoc(
        "UnaryCtor",
        Type.Con(Tycon.Tycon("Phantom", Kind.Star)),
        unaryKind
    );
    let argAssoc = Tyassoc.Tyassoc(
        "Elem",
        Type.Con(Tycon.Tycon("Phantom", Kind.Star)),
        Kind.Star
    );
    let unary = Type.Con(Tycon.Tycon("Unary", unaryKind));

    let constraintEnv = ConstrEnv.ConstrEnv(
        Map.union(
            Map.singleton(
                "UnaryCtor",
                trMkEquality(Type.Assoc(funcAssoc), unary) :: Nil
            ),
            Map.singleton(
                "Elem",
                trMkEquality(
                    Type.Assoc(argAssoc),
                    Type.Con(Tycon.Tycon("Int32", Kind.Star))
                ) :: Nil
            )
        ),
        Map.empty()
    );

    let ty = Type.Ap(Type.Assoc(funcAssoc), Type.Assoc(argAssoc));

    Assert.assertEq(
        expected = Some(Type.Ap(unary, Type.Assoc(argAssoc))),
        ty |> reduceTyOne(constraintEnv, Nil)
    )
}


// constraintEnv: { Elem Phantom = Int32 }
// `Unary (Elem Phantom) -> Some(Unary Int32)`
@Test
def reduceTypeOneStepApplicationReducesArgumentWhenFunctionIsStable(): Unit \ Assert = {
    let unaryKind = Kind.KFun(
        Kind.Star,
        Kind.Star
    );
    let unary = Type.Con(Tycon.Tycon("Unary", unaryKind));
    let argAssoc = Tyassoc.Tyassoc(
        "Elem",
        Type.Con(Tycon.Tycon("Phantom", Kind.Star)),
        Kind.Star
    );
    let int32 = Type.Con(Tycon.Tycon("Int32", Kind.Star));

    let constraintEnv = ConstrEnv.ConstrEnv(
        Map.singleton(
            "Elem",
            trMkEquality(Type.Assoc(argAssoc), int32) :: Nil
        ),
        Map.empty()
    );

    let ty = Type.Ap(unary, Type.Assoc(argAssoc));

    Assert.assertEq(
        expected = Some(Type.Ap(unary, int32)),
        ty |> reduceTyOne(constraintEnv, Nil)
    )
}


// constraintEnv: { AssocA x = AssocB x, AssocB x = Int32 }
// `AssocA x -> Some(AssocB x)`
@Test
def reduceTypeOneStepReducesChainedTyassocsOneRuleAtATime(): Unit \ Assert = {
    let x = Tyvar.Tyvar("x", Kind.Star);
    let assocA = Tyassoc.Tyassoc("AssocA", Type.Var(x), Kind.Star);
    let assocB = Tyassoc.Tyassoc("AssocB", Type.Var(x), Kind.Star);
    let int32 = Type.Con(Tycon.Tycon("Int32", Kind.Star));

    let constraintEnv = ConstrEnv.ConstrEnv(
        Map.union(
            Map.singleton(
                "AssocA",
                trMkEquality(
                    Type.Assoc(assocA),
                    Type.Assoc(assocB)
                ) :: Nil
            ),
            Map.singleton(
                "AssocB",
                trMkEquality(Type.Assoc(assocB), int32) :: Nil
            )
        ),
        Map.empty()
    );

    Assert.assertEq(
        expected = Some(Type.Assoc(assocB)),
        Type.Assoc(assocA) |> reduceTyOne(constraintEnv, Nil)
    )
}


// constraintEnv: { ReadEff x = Read, WriteEff x = Write }
// `Union (ReadEff x) (Compl (WriteEff x)) -> Some(Union Read (Compl (WriteEff x)))`
@Test
def reduceTypeOneStepTraversesNestedSetFormulaLeftToRight(): Unit \ Assert = {
    let arg = Tyvar.Tyvar("x", Kind.Star);
    let readAssoc = Tyassoc.Tyassoc("ReadEff", Type.Var(arg), Kind.Eff);
    let writeAssoc = Tyassoc.Tyassoc("WriteEff", Type.Var(arg), Kind.Eff);

    let read = Type.efConstant("Read");
    let write = Type.efConstant("Write");

    let constraintEnv = ConstrEnv.ConstrEnv(
        Map.union(
            Map.singleton(
                "ReadEff",
                trMkEquality(
                    Type.Assoc(readAssoc),
                    read
                ) :: Nil
            ),
            Map.singleton(
                "WriteEff",
                trMkEquality(
                    Type.Assoc(writeAssoc),
                    write
                ) :: Nil
            )
        ),
        Map.empty()
    );

    let ty = Type.mkUnion(
        Type.Assoc(readAssoc),
        Type.mkCompl(Type.Assoc(writeAssoc))
    );

    Assert.assertEq(
        expected = Some(Type.mkUnion(
            read,
            Type.mkCompl(Type.Assoc(writeAssoc))
        )),
        ty |> reduceTyOne(constraintEnv, Nil)
    )
}


// constraintEnv: { Assoc x = IO }
// `Compl (Assoc x) -> Some(Compl IO)`
@Test
def reduceTypeOneStepReducesTyassocInsideSetFormula(): Unit \ Assert = {
    let assocId = "Assoc";
    let arg = Tyvar.Tyvar("x", Kind.Star);
    let io = Type.efConstant("IO");
    let assoc = Tyassoc.Tyassoc(
        assocId,
        Type.Var(arg),
        Kind.Eff
    );

    let constraintEnv = ConstrEnv.ConstrEnv(
        Map.singleton(
            assocId,
            (
                Type.Assoc(assoc),
                io
            ) :: Nil
        ),
        Map.empty()
    );

    let ty = Type.mkCompl(Type.Assoc(assoc));

    Assert.assertEq(
        expected = Some(Type.mkCompl(io)),
        ty |> reduceTyOne(constraintEnv, Nil)
    )
}
