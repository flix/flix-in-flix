def trMkEquality(left: Type, right: Type): EqualityConstraint =
    EqualityConstraint.EqualityConstraint(left, right)


def trMkGivenEquality(left: Type, right: Type): Constraint =
    Constraint.Equality(trMkEquality(left, right))


def trEmptyConstraintEnv(): ConstraintEnvironment =
    ConstraintEnvironment.ConstraintEnvironment(Map.empty(), Map.empty())


// `x, Int32, Gen(0) -> None`
@Test
def reduceTypeOneStepLeavesSimpleTypesUnchanged(): Unit \ Assert = {
    let tyVar = Type.mkTypeVar("x", Kind.Star);
    let tyCon = Type.mkTypeCon("Int32", Kind.Star);
    let gen = Gen.Gen(0, Kind.Star);

    Assert.assertEq(
        expected = None,
        Type.Variable(tyVar) |> reduceTypeOneStep(trEmptyConstraintEnv(), Nil)
    );
    Assert.assertEq(
        expected = None,
        Type.Constructor(tyCon) |> reduceTypeOneStep(trEmptyConstraintEnv(), Nil)
    );
    Assert.assertEq(
        expected = None,
        Type.Gen(gen) |> reduceTypeOneStep(trEmptyConstraintEnv(), Nil)
    )
}


// given: { Elem x = Bool }
// `Elem x -> Some(Bool)`
@Test
def reduceTypeOneStepUsesGivenEqualityForAssociatedMember(): Unit \ Assert = {
    let arg = Type.mkTypeVar("x", Kind.Star);
    let assoc = Type.mkAssoc("Elem", Type.Variable(arg), Kind.Star);
    let bool = Type.Constructor(Type.mkTypeCon("Bool", Kind.Star));

    Assert.assertEq(
        expected = Some(bool),
        Type.AssociatedMember(assoc) |> reduceTypeOneStep(
            trEmptyConstraintEnv(),
            trMkGivenEquality(Type.AssociatedMember(assoc), bool) :: Nil
        )
    )
}


// given: { Elem a = a }
// `Elem Int32 -> None`
@Test
def reduceTypeOneStepGivenEqualityRequiresSyntacticLeftHandSideMatch(): Unit \ Assert = {
    let a = Type.mkTypeVar("a", Kind.Star);
    let int32 = Type.Constructor(Type.mkTypeCon("Int32", Kind.Star));
    let genericAssoc = Type.mkAssoc("Elem", Type.Variable(a), Kind.Star);
    let specificAssoc = Type.mkAssoc("Elem", int32, Kind.Star);

    Assert.assertEq(
        expected = None,
        Type.AssociatedMember(specificAssoc) |> reduceTypeOneStep(
            trEmptyConstraintEnv(),
            trMkGivenEquality(
                Type.AssociatedMember(genericAssoc),
                Type.Variable(a)
            ) :: Nil
        )
    )
}


// constraintEnv: { Elem a = a }
// `Elem Int32 -> Some(Int32)`
@Test
def reduceTypeOneStepInstantiatesConstraintEnvironmentEquality(): Unit \ Assert = {
    let a = Type.mkTypeVar("a", Kind.Star);
    let int32 = Type.Constructor(Type.mkTypeCon("Int32", Kind.Star));
    let genericAssoc = Type.mkAssoc("Elem", Type.Variable(a), Kind.Star);
    let specificAssoc = Type.mkAssoc("Elem", int32, Kind.Star);

    let constraintEnv = ConstraintEnvironment.ConstraintEnvironment(
        Map.singleton(
            Id.Id("Elem"),
            trMkEquality(
                Type.AssociatedMember(genericAssoc),
                Type.Variable(a)
            ) :: Nil
        ),
        Map.empty()
    );

    Assert.assertEq(
        expected = Some(int32),
        Type.AssociatedMember(specificAssoc) |> reduceTypeOneStep(
            constraintEnv,
            Nil
        )
    )
}


// constraintEnv: { Inner x = Int32, Outer Int32 = Bool }
// `Outer (Inner x) -> Some(Outer Int32)`
@Test
def reduceTypeOneStepReducesAssociatedMemberArgumentBeforeOuterLookup(): Unit \ Assert = {
    let x = Type.mkTypeVar("x", Kind.Star);
    let inner = Type.mkAssoc("Inner", Type.Variable(x), Kind.Star);
    let outer = Type.mkAssoc(
        "Outer",
        Type.AssociatedMember(inner),
        Kind.Star
    );
    let int32 = Type.Constructor(Type.mkTypeCon("Int32", Kind.Star));
    let bool = Type.Constructor(Type.mkTypeCon("Bool", Kind.Star));
    let outerAfterArgReduction = Type.mkAssoc("Outer", int32, Kind.Star);

    let constraintEnv = ConstraintEnvironment.ConstraintEnvironment(
        Map.union(
            Map.singleton(
                Id.Id("Inner"),
                trMkEquality(Type.AssociatedMember(inner), int32) :: Nil
            ),
            Map.singleton(
                Id.Id("Outer"),
                trMkEquality(Type.AssociatedMember(outerAfterArgReduction), bool) :: Nil
            )
        ),
        Map.empty()
    );

    Assert.assertEq(
        expected = Some(Type.AssociatedMember(outerAfterArgReduction)),
        Type.AssociatedMember(outer) |> reduceTypeOneStep(constraintEnv, Nil)
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
    let funcAssoc = Type.mkAssoc(
        "UnaryCtor",
        Type.Constructor(Type.mkTypeCon("Phantom", Kind.Star)),
        unaryKind
    );
    let argAssoc = Type.mkAssoc(
        "Elem",
        Type.Constructor(Type.mkTypeCon("Phantom", Kind.Star)),
        Kind.Star
    );
    let unary = Type.Constructor(Type.mkTypeCon("Unary", unaryKind));

    let constraintEnv = ConstraintEnvironment.ConstraintEnvironment(
        Map.union(
            Map.singleton(
                Id.Id("UnaryCtor"),
                trMkEquality(Type.AssociatedMember(funcAssoc), unary) :: Nil
            ),
            Map.singleton(
                Id.Id("Elem"),
                trMkEquality(
                    Type.AssociatedMember(argAssoc),
                    Type.Constructor(Type.mkTypeCon("Int32", Kind.Star))
                ) :: Nil
            )
        ),
        Map.empty()
    );

    let ty = Type.Application(TypeApplication.TypeApplication(
        Type.AssociatedMember(funcAssoc),
        Type.AssociatedMember(argAssoc)
    ));

    Assert.assertEq(
        expected = Some(Type.Application(TypeApplication.TypeApplication(
            unary,
            Type.AssociatedMember(argAssoc)
        ))),
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
    let unary = Type.Constructor(Type.mkTypeCon("Unary", unaryKind));
    let argAssoc = Type.mkAssoc(
        "Elem",
        Type.Constructor(Type.mkTypeCon("Phantom", Kind.Star)),
        Kind.Star
    );
    let int32 = Type.Constructor(Type.mkTypeCon("Int32", Kind.Star));

    let constraintEnv = ConstraintEnvironment.ConstraintEnvironment(
        Map.singleton(
            Id.Id("Elem"),
            trMkEquality(Type.AssociatedMember(argAssoc), int32) :: Nil
        ),
        Map.empty()
    );

    let ty = Type.Application(TypeApplication.TypeApplication(
        unary,
        Type.AssociatedMember(argAssoc)
    ));

    Assert.assertEq(
        expected = Some(Type.Application(TypeApplication.TypeApplication(
            unary,
            int32
        ))),
        ty |> reduceTypeOneStep(constraintEnv, Nil)
    )
}


// constraintEnv: { AssocA x = AssocB x, AssocB x = Int32 }
// `AssocA x -> Some(AssocB x)`
@Test
def reduceTypeOneStepReducesChainedAssociatedMembersOneRuleAtATime(): Unit \ Assert = {
    let x = Type.mkTypeVar("x", Kind.Star);
    let assocA = Type.mkAssoc("AssocA", Type.Variable(x), Kind.Star);
    let assocB = Type.mkAssoc("AssocB", Type.Variable(x), Kind.Star);
    let int32 = Type.Constructor(Type.mkTypeCon("Int32", Kind.Star));

    let constraintEnv = ConstraintEnvironment.ConstraintEnvironment(
        Map.union(
            Map.singleton(
                Id.Id("AssocA"),
                trMkEquality(
                    Type.AssociatedMember(assocA),
                    Type.AssociatedMember(assocB)
                ) :: Nil
            ),
            Map.singleton(
                Id.Id("AssocB"),
                trMkEquality(Type.AssociatedMember(assocB), int32) :: Nil
            )
        ),
        Map.empty()
    );

    Assert.assertEq(
        expected = Some(Type.AssociatedMember(assocB)),
        Type.AssociatedMember(assocA) |> reduceTypeOneStep(constraintEnv, Nil)
    )
}


// constraintEnv: { ReadEff x = Read, WriteEff x = Write }
// `(ReadEff x + ~WriteEff x) -> Some(Read + ~WriteEff x)`
@Test
def reduceTypeOneStepTraversesNestedSetFormulaLeftToRight(): Unit \ Assert = {
    let arg = Type.mkTypeVar("x", Kind.Star);
    let readAssoc = Type.mkAssoc("ReadEff", Type.Variable(arg), Kind.Eff);
    let writeAssoc = Type.mkAssoc("WriteEff", Type.Variable(arg), Kind.Eff);

    let read = SetFormula.Singleton(EffectLabel.EffectLabel(Id.Id("Read")));
    let write = SetFormula.Singleton(EffectLabel.EffectLabel(Id.Id("Write")));

    let constraintEnv = ConstraintEnvironment.ConstraintEnvironment(
        Map.union(
            Map.singleton(
                Id.Id("ReadEff"),
                trMkEquality(
                    Type.AssociatedMember(readAssoc),
                    Type.SetFormula(read)
                ) :: Nil
            ),
            Map.singleton(
                Id.Id("WriteEff"),
                trMkEquality(
                    Type.AssociatedMember(writeAssoc),
                    Type.SetFormula(write)
                ) :: Nil
            )
        ),
        Map.empty()
    );

    let ty = Type.SetFormula(SetFormula.Binary(
        BinarySetFormula.BinarySetFormula(
            SetFormula.AssociatedMember(readAssoc),
            SetBinaryOp.Union,
            SetFormula.Complement(SetFormula.AssociatedMember(writeAssoc))
        )
    ));

    Assert.assertEq(
        expected = Some(Type.SetFormula(SetFormula.Binary(
            BinarySetFormula.BinarySetFormula(
                read,
                SetBinaryOp.Union,
                SetFormula.Complement(SetFormula.AssociatedMember(writeAssoc))
            )
        ))),
        ty |> reduceTypeOneStep(constraintEnv, Nil)
    )
}


// constraintEnv: { Assoc x = IO }
// `~Assoc x -> Some(~IO)`
@Test
def reduceTypeOneStepReducesAssociatedMemberInsideSetFormula(): Unit \ Assert = {
    let assocId = Id.Id("Assoc");
    let arg = TypeVariable.TypeVariable(Id.Id("x"), Kind.Star);
    let io = EffectLabel.EffectLabel(Id.Id("IO"));
    let assoc = AssociatedMember.AssociatedMember(
        assocId,
        Type.Variable(arg),
        Kind.Eff
    );

    let constraintEnv = ConstraintEnvironment.ConstraintEnvironment(
        Map.singleton(
            assocId,
            EqualityConstraint.EqualityConstraint(
                Type.AssociatedMember(assoc),
                Type.SetFormula(SetFormula.Singleton(io))
            ) :: Nil
        ),
        Map.empty()
    );

    let ty = Type.SetFormula(
        SetFormula.Complement(SetFormula.AssociatedMember(assoc))
    );

    Assert.assertEq(
        expected = Some(Type.SetFormula(
            SetFormula.Complement(SetFormula.Singleton(io))
        )),
        ty |> reduceTypeOneStep(constraintEnv, Nil)
    )
}
