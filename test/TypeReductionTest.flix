def trMkEquality(left: Type, right: Type): EqConstr =
    (left, right)


def trMkGivenEquality(left: Type, right: Type): Constr =
    Constr.Eq((left, right))


def trEmptyConstraintEnv(): ConstrEnv =
    emptyConstrEnv()


def trEnvWithGivens(givens: List[Constr]): ConstrEnv =
    addGivens(givens, trEmptyConstraintEnv())


// `x, Int32, Gen(0) -> None`
@Test
def reduceTypeOneStepLeavesSimpleTypesUnchanged(): Unit \ Assert = {
    let tyVar = Tyvar.Tyvar("x", Kind.Star);
    let tyCon = Tycon.Tycon("Int32", Kind.Star);

    Assert.assertEq(
        expected = None,
        Type.Var(tyVar) |> reduce(trEmptyConstraintEnv())
    );
    Assert.assertEq(
        expected = None,
        Type.Con(tyCon) |> reduce(trEmptyConstraintEnv())
    );
    Assert.assertEq(
        expected = None,
        Type.Gen(0) |> reduce(trEmptyConstraintEnv())
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
        Type.Assoc(assoc) |> reduce(
            trEnvWithGivens(
                trMkGivenEquality(Type.Assoc(assoc), bool) :: Nil
            )
        )
    )
}


// given: { Elem a = a }
// `Elem Int32 -> Some(Int32)`
@Test
def reduceTypeOneStepInstantiatesGivenEquality(): Unit \ Assert = {
    let a = Tyvar.Tyvar("a", Kind.Star);
    let int32 = Type.Con(Tycon.Tycon("Int32", Kind.Star));
    let genericAssoc = Tyassoc.Tyassoc("Elem", Type.Var(a), Kind.Star);
    let specificAssoc = Tyassoc.Tyassoc("Elem", int32, Kind.Star);

    Assert.assertEq(
        expected = Some(int32),
        Type.Assoc(specificAssoc) |> reduce(
            trEnvWithGivens(
                trMkGivenEquality(
                    Type.Assoc(genericAssoc),
                    Type.Var(a)
                ) :: Nil
            )
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

    let constraintEnv = addAssocEq(
        "Elem",
        trMkEquality(
            Type.Assoc(genericAssoc),
            Type.Var(a)
        ),
        emptyConstrEnv()
    );

    Assert.assertEq(
        expected = Some(int32),
        Type.Assoc(specificAssoc) |> reduce(
            constraintEnv
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

    let constraintEnv = emptyConstrEnv()
        |> addAssocEq(
            "Inner",
            trMkEquality(Type.Assoc(inner), int32)
        )
        |> addAssocEq(
            "Outer",
            trMkEquality(Type.Assoc(outerAfterArgReduction), bool)
        );

    Assert.assertEq(
        expected = Some(Type.Assoc(outerAfterArgReduction)),
        Type.Assoc(outer) |> reduce(constraintEnv)
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

    let constraintEnv = emptyConstrEnv()
        |> addAssocEq(
            "UnaryCtor",
            trMkEquality(Type.Assoc(funcAssoc), unary)
        )
        |> addAssocEq(
            "Elem",
            trMkEquality(
                Type.Assoc(argAssoc),
                Type.Con(Tycon.Tycon("Int32", Kind.Star))
            )
        );

    let ty = Type.Ap(Type.Assoc(funcAssoc), Type.Assoc(argAssoc));

    Assert.assertEq(
        expected = Some(Type.Ap(unary, Type.Assoc(argAssoc))),
        ty |> reduce(constraintEnv)
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

    let constraintEnv = addAssocEq(
        "Elem",
        trMkEquality(Type.Assoc(argAssoc), int32),
        emptyConstrEnv()
    );

    let ty = Type.Ap(unary, Type.Assoc(argAssoc));

    Assert.assertEq(
        expected = Some(Type.Ap(unary, int32)),
        ty |> reduce(constraintEnv)
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

    let constraintEnv = emptyConstrEnv()
        |> addAssocEq(
            "AssocA",
            trMkEquality(
                Type.Assoc(assocA),
                Type.Assoc(assocB)
            )
        )
        |> addAssocEq(
            "AssocB",
            trMkEquality(Type.Assoc(assocB), int32)
        );

    Assert.assertEq(
        expected = Some(Type.Assoc(assocB)),
        Type.Assoc(assocA) |> reduce(constraintEnv)
    )
}


// constraintEnv: { ReadEff x = Read, WriteEff x = Write }
// `Union (ReadEff x) (Compl (WriteEff x)) -> Some(Union Read (Compl (WriteEff x)))`
@Test
def reduceTypeOneStepTraversesNestedSetFormulaLeftToRight(): Unit \ Assert = {
    let arg = Tyvar.Tyvar("x", Kind.Star);
    let readAssoc = Tyassoc.Tyassoc("ReadEff", Type.Var(arg), Kind.Eff);
    let writeAssoc = Tyassoc.Tyassoc("WriteEff", Type.Var(arg), Kind.Eff);

    let read = efConstant("Read");
    let write = efConstant("Write");

    let constraintEnv = emptyConstrEnv()
        |> addAssocEq(
            "ReadEff",
            trMkEquality(
                Type.Assoc(readAssoc),
                read
            )
        )
        |> addAssocEq(
            "WriteEff",
            trMkEquality(
                Type.Assoc(writeAssoc),
                write
            )
        );

    let ty = mkUnion(
        Type.Assoc(readAssoc),
        mkCompl(Type.Assoc(writeAssoc))
    );

    Assert.assertEq(
        expected = Some(mkUnion(
            read,
            mkCompl(Type.Assoc(writeAssoc))
        )),
        ty |> reduce(constraintEnv)
    )
}


// constraintEnv: { Assoc x = IO }
// `Compl (Assoc x) -> Some(Compl IO)`
@Test
def reduceTypeOneStepReducesTyassocInsideSetFormula(): Unit \ Assert = {
    let assocId = "Assoc";
    let arg = Tyvar.Tyvar("x", Kind.Star);
    let io = efConstant("IO");
    let assoc = Tyassoc.Tyassoc(
        assocId,
        Type.Var(arg),
        Kind.Eff
    );

    let constraintEnv = addAssocEq(
        assocId,
        (Type.Assoc(assoc), io),
        emptyConstrEnv()
    );

    let ty = mkCompl(Type.Assoc(assoc));

    Assert.assertEq(
        expected = Some(mkCompl(io)),
        ty |> reduce(constraintEnv)
    )
}
