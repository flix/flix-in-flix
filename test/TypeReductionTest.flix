def trMkEquality(left: Type, right: Type): EqConstr =
    EqConstr.EqConstr(left, right)


def trMkGivenEquality(left: Type, right: Type): Constr =
    Constr.Eq(trMkEquality(left, right))


def trEmptyConstraintEnv(): ConstraintEnvironment =
    ConstraintEnvironment.ConstraintEnvironment(Map.empty(), Map.empty())


// `x, Int32, Gen(0) -> None`
@Test
def reduceTypeOneStepLeavesSimpleTypesUnchanged(): Unit \ Assert = {
    let tyVar = Type.mkTyvar("x", Kind.Star);
    let tyCon = Type.mkTycon("Int32", Kind.Star);
    let gen = Gen.Gen(0, Kind.Star);

    Assert.assertEq(
        expected = None,
        Type.Var(tyVar) |> reduceTypeOneStep(trEmptyConstraintEnv(), Nil)
    );
    Assert.assertEq(
        expected = None,
        Type.Con(tyCon) |> reduceTypeOneStep(trEmptyConstraintEnv(), Nil)
    );
    Assert.assertEq(
        expected = None,
        Type.Gen(gen) |> reduceTypeOneStep(trEmptyConstraintEnv(), Nil)
    )
}


// given: { Elem x = Bool }
// `Elem x -> Some(Bool)`
@Test
def reduceTypeOneStepUsesGivenEqualityForTyassoc(): Unit \ Assert = {
    let arg = Type.mkTyvar("x", Kind.Star);
    let assoc = Type.mkTyassoc("Elem", Type.Var(arg), Kind.Star);
    let bool = Type.Con(Type.mkTycon("Bool", Kind.Star));

    Assert.assertEq(
        expected = Some(bool),
        Type.Assoc(assoc) |> reduceTypeOneStep(
            trEmptyConstraintEnv(),
            trMkGivenEquality(Type.Assoc(assoc), bool) :: Nil
        )
    )
}


// given: { Elem a = a }
// `Elem Int32 -> None`
@Test
def reduceTypeOneStepGivenEqualityRequiresSyntacticLeftHandSideMatch(): Unit \ Assert = {
    let a = Type.mkTyvar("a", Kind.Star);
    let int32 = Type.Con(Type.mkTycon("Int32", Kind.Star));
    let genericAssoc = Type.mkTyassoc("Elem", Type.Var(a), Kind.Star);
    let specificAssoc = Type.mkTyassoc("Elem", int32, Kind.Star);

    Assert.assertEq(
        expected = None,
        Type.Assoc(specificAssoc) |> reduceTypeOneStep(
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
    let a = Type.mkTyvar("a", Kind.Star);
    let int32 = Type.Con(Type.mkTycon("Int32", Kind.Star));
    let genericAssoc = Type.mkTyassoc("Elem", Type.Var(a), Kind.Star);
    let specificAssoc = Type.mkTyassoc("Elem", int32, Kind.Star);

    let constraintEnv = ConstraintEnvironment.ConstraintEnvironment(
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
        Type.Assoc(specificAssoc) |> reduceTypeOneStep(
            constraintEnv,
            Nil
        )
    )
}


// constraintEnv: { Inner x = Int32, Outer Int32 = Bool }
// `Outer (Inner x) -> Some(Outer Int32)`
@Test
def reduceTypeOneStepReducesTyassocArgumentBeforeOuterLookup(): Unit \ Assert = {
    let x = Type.mkTyvar("x", Kind.Star);
    let inner = Type.mkTyassoc("Inner", Type.Var(x), Kind.Star);
    let outer = Type.mkTyassoc(
        "Outer",
        Type.Assoc(inner),
        Kind.Star
    );
    let int32 = Type.Con(Type.mkTycon("Int32", Kind.Star));
    let bool = Type.Con(Type.mkTycon("Bool", Kind.Star));
    let outerAfterArgReduction = Type.mkTyassoc("Outer", int32, Kind.Star);

    let constraintEnv = ConstraintEnvironment.ConstraintEnvironment(
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
        Type.Assoc(outer) |> reduceTypeOneStep(constraintEnv, Nil)
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
    let funcAssoc = Type.mkTyassoc(
        "UnaryCtor",
        Type.Con(Type.mkTycon("Phantom", Kind.Star)),
        unaryKind
    );
    let argAssoc = Type.mkTyassoc(
        "Elem",
        Type.Con(Type.mkTycon("Phantom", Kind.Star)),
        Kind.Star
    );
    let unary = Type.Con(Type.mkTycon("Unary", unaryKind));

    let constraintEnv = ConstraintEnvironment.ConstraintEnvironment(
        Map.union(
            Map.singleton(
                "UnaryCtor",
                trMkEquality(Type.Assoc(funcAssoc), unary) :: Nil
            ),
            Map.singleton(
                "Elem",
                trMkEquality(
                    Type.Assoc(argAssoc),
                    Type.Con(Type.mkTycon("Int32", Kind.Star))
                ) :: Nil
            )
        ),
        Map.empty()
    );

    let ty = Type.Ap(Type.Assoc(funcAssoc), Type.Assoc(argAssoc));

    Assert.assertEq(
        expected = Some(Type.Ap(unary, Type.Assoc(argAssoc))),
        ty |> reduceTypeOneStep(constraintEnv, Nil)
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
    let unary = Type.Con(Type.mkTycon("Unary", unaryKind));
    let argAssoc = Type.mkTyassoc(
        "Elem",
        Type.Con(Type.mkTycon("Phantom", Kind.Star)),
        Kind.Star
    );
    let int32 = Type.Con(Type.mkTycon("Int32", Kind.Star));

    let constraintEnv = ConstraintEnvironment.ConstraintEnvironment(
        Map.singleton(
            "Elem",
            trMkEquality(Type.Assoc(argAssoc), int32) :: Nil
        ),
        Map.empty()
    );

    let ty = Type.Ap(unary, Type.Assoc(argAssoc));

    Assert.assertEq(
        expected = Some(Type.Ap(unary, int32)),
        ty |> reduceTypeOneStep(constraintEnv, Nil)
    )
}


// constraintEnv: { AssocA x = AssocB x, AssocB x = Int32 }
// `AssocA x -> Some(AssocB x)`
@Test
def reduceTypeOneStepReducesChainedTyassocsOneRuleAtATime(): Unit \ Assert = {
    let x = Type.mkTyvar("x", Kind.Star);
    let assocA = Type.mkTyassoc("AssocA", Type.Var(x), Kind.Star);
    let assocB = Type.mkTyassoc("AssocB", Type.Var(x), Kind.Star);
    let int32 = Type.Con(Type.mkTycon("Int32", Kind.Star));

    let constraintEnv = ConstraintEnvironment.ConstraintEnvironment(
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
        Type.Assoc(assocA) |> reduceTypeOneStep(constraintEnv, Nil)
    )
}


// constraintEnv: { ReadEff x = Read, WriteEff x = Write }
// `Union (ReadEff x) (Compl (WriteEff x)) -> Some(Union Read (Compl (WriteEff x)))`
@Test
def reduceTypeOneStepTraversesNestedSetFormulaLeftToRight(): Unit \ Assert = {
    let arg = Type.mkTyvar("x", Kind.Star);
    let readAssoc = Type.mkTyassoc("ReadEff", Type.Var(arg), Kind.Eff);
    let writeAssoc = Type.mkTyassoc("WriteEff", Type.Var(arg), Kind.Eff);

    let read = Type.efSingleton("Read");
    let write = Type.efSingleton("Write");

    let constraintEnv = ConstraintEnvironment.ConstraintEnvironment(
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

    let ty = Type.efUnion(
        Type.Assoc(readAssoc),
        Type.efCompl(Type.Assoc(writeAssoc))
    );

    Assert.assertEq(
        expected = Some(Type.efUnion(
            read,
            Type.efCompl(Type.Assoc(writeAssoc))
        )),
        ty |> reduceTypeOneStep(constraintEnv, Nil)
    )
}


// constraintEnv: { Assoc x = IO }
// `Compl (Assoc x) -> Some(Compl IO)`
@Test
def reduceTypeOneStepReducesTyassocInsideSetFormula(): Unit \ Assert = {
    let assocId = "Assoc";
    let arg = Tyvar.Tyvar("x", Kind.Star);
    let io = Type.efSingleton("IO");
    let assoc = Tyassoc.Tyassoc(
        assocId,
        Type.Var(arg),
        Kind.Eff
    );

    let constraintEnv = ConstraintEnvironment.ConstraintEnvironment(
        Map.singleton(
            assocId,
            EqConstr.EqConstr(
                Type.Assoc(assoc),
                io
            ) :: Nil
        ),
        Map.empty()
    );

    let ty = Type.efCompl(Type.Assoc(assoc));

    Assert.assertEq(
        expected = Some(Type.efCompl(io)),
        ty |> reduceTypeOneStep(constraintEnv, Nil)
    )
}
