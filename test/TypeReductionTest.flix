def trMkEquality(left: Type, right: Type): EqualityConstraint =
    EqualityConstraint.EqualityConstraint(left, right)


def trMkGivenEquality(left: Type, right: Type): Constraint =
    Constraint.Equality(trMkEquality(left, right))


def trEmptyConstraintEnv(): ConstraintEnvironment =
    ConstraintEnvironment.ConstraintEnvironment(Map.empty())


// constraintEnv: { Assoc x = IO }
// `~Assoc x -> ~IO`
@Test
def reduceAssociatedMemberInsideSetFormula(): Unit \ Assert = {
    let assocId = Id.Id("Assoc");
    let arg = TypeVariable.TypeVariable(Id.Id("x"), Kind.TypeStar);
    let io = EffectLabel.EffectLabel(Id.Id("IO"), EffectKind.Regular);
    let assoc = AssociatedMember.AssociatedMember(
        assocId,
        Type.Variable(arg),
        Kind.EffectStar
    );

    let constraintEnv = ConstraintEnvironment.ConstraintEnvironment(
        Map.singleton(
            assocId,
            EqualityConstraint.EqualityConstraint(
                Type.AssociatedMember(assoc),
                Type.SetFormula(SetFormula.Singleton(io))
            ) :: Nil
        )
    );

    let ty = Type.SetFormula(
        SetFormula.Complement(SetFormula.AssociatedMember(assoc))
    );

    Assert.assertEq(
        expected = Type.SetFormula(
            SetFormula.Complement(SetFormula.Singleton(io))
        ),
        ty |> reduceType(constraintEnv, Nil)
    )
}


// `x, Int32, Gen(0) -> unchanged`
@Test
def reduceTypeLeavesSimpleTypesUnchanged(): Unit \ Assert = {
    let tyVar = Type.mkTypeVar("x", Kind.TypeStar);
    let tyCon = Type.mkTypeCon("Int32", Kind.TypeStar);
    let gen = Gen.Gen(0, Kind.TypeStar);

    Assert.assertEq(
        expected = Type.Variable(tyVar),
        Type.Variable(tyVar) |> reduceType(trEmptyConstraintEnv(), Nil)
    );
    Assert.assertEq(
        expected = Type.Constructor(tyCon),
        Type.Constructor(tyCon) |> reduceType(trEmptyConstraintEnv(), Nil)
    );
    Assert.assertEq(
        expected = Type.Gen(gen),
        Type.Gen(gen) |> reduceType(trEmptyConstraintEnv(), Nil)
    )
}


// given: { Elem x = Bool }
// `Elem x -> Bool`
@Test
def reduceTypeUsesGivenEqualityForAssociatedMember(): Unit \ Assert = {
    let arg = Type.mkTypeVar("x", Kind.TypeStar);
    let assoc = Type.mkAssoc("Elem", Type.Variable(arg), Kind.TypeStar);
    let bool = Type.Constructor(Type.mkTypeCon("Bool", Kind.TypeStar));

    Assert.assertEq(
        expected = bool,
        Type.AssociatedMember(assoc) |> reduceType(
            trEmptyConstraintEnv(),
            trMkGivenEquality(Type.AssociatedMember(assoc), bool) :: Nil
        )
    )
}

// constraintEnv: { Inner x = Int32, Outer Int32 = Bool }
// `Outer (Inner x) -> Bool`
@Test
def reduceTypeRecursivelyReducesAssociatedMemberArgumentBeforeLookup(): Unit \ Assert = {
    let x = Type.mkTypeVar("x", Kind.TypeStar);
    let inner = Type.mkAssoc("Inner", Type.Variable(x), Kind.TypeStar);
    let outer = Type.mkAssoc(
        "Outer",
        Type.AssociatedMember(inner),
        Kind.TypeStar
    );
    let int32 = Type.Constructor(Type.mkTypeCon("Int32", Kind.TypeStar));
    let bool = Type.Constructor(Type.mkTypeCon("Bool", Kind.TypeStar));
    let outerAfterArgReduction = Type.mkAssoc("Outer", int32, Kind.TypeStar);

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
        )
    );

    Assert.assertEq(
        expected = bool,
        Type.AssociatedMember(outer) |> reduceType(constraintEnv, Nil)
    )
}


// constraintEnv: { Inner x = Int32 }
// `Outer (Inner x) -> Outer Int32`
@Test
def reduceTypePreservesAssociatedMemberWhenNoEqualityMatches(): Unit \ Assert = {
    let x = Type.mkTypeVar("x", Kind.TypeStar);
    let inner = Type.mkAssoc("Inner", Type.Variable(x), Kind.TypeStar);
    let outer = Type.mkAssoc(
        "Outer",
        Type.AssociatedMember(inner),
        Kind.TypeStar
    );
    let int32 = Type.Constructor(Type.mkTypeCon("Int32", Kind.TypeStar));

    let constraintEnv = ConstraintEnvironment.ConstraintEnvironment(
        Map.singleton(
            Id.Id("Inner"),
            trMkEquality(Type.AssociatedMember(inner), int32) :: Nil
        )
    );

    Assert.assertEq(
        expected = Type.AssociatedMember(
            Type.mkAssoc("Outer", int32, Kind.TypeStar)
        ),
        Type.AssociatedMember(outer) |> reduceType(constraintEnv, Nil)
    )
}


// constraintEnv: { UnaryCtor Phantom = Unary, Elem Phantom = Int32 }
// `(UnaryCtor Phantom) (Elem Phantom) -> Unary Int32`
@Test
def reduceTypeRecursivelyReducesApplicationChildren(): Unit \ Assert = {
    let unaryKind = Kind.Function(FunctionKind.FunctionKind(
        Kind.TypeStar,
        Kind.TypeStar
    ));
    let funcAssoc = Type.mkAssoc(
        "UnaryCtor",
        Type.Constructor(Type.mkTypeCon("Phantom", Kind.TypeStar)),
        unaryKind
    );
    let argAssoc = Type.mkAssoc(
        "Elem",
        Type.Constructor(Type.mkTypeCon("Phantom", Kind.TypeStar)),
        Kind.TypeStar
    );
    let unary = Type.Constructor(Type.mkTypeCon("Unary", unaryKind));
    let int32 = Type.Constructor(Type.mkTypeCon("Int32", Kind.TypeStar));

    let constraintEnv = ConstraintEnvironment.ConstraintEnvironment(
        Map.union(
            Map.singleton(
                Id.Id("UnaryCtor"),
                trMkEquality(Type.AssociatedMember(funcAssoc), unary) :: Nil
            ),
            Map.singleton(
                Id.Id("Elem"),
                trMkEquality(Type.AssociatedMember(argAssoc), int32) :: Nil
            )
        )
    );

    let ty = Type.Application(TypeApplication.TypeApplication(
        Type.AssociatedMember(funcAssoc),
        Type.AssociatedMember(argAssoc)
    ));

    Assert.assertEq(
        expected = Type.Application(TypeApplication.TypeApplication(
            unary,
            int32
        )),
        ty |> reduceType(constraintEnv, Nil)
    )
}


// constraintEnv: { AssocA x = AssocB x, AssocB x = Int32 }
// `AssocA x -> Int32`
@Test
def reduceTypeRecursivelyReducesChainedAssociatedMembers(): Unit \ Assert = {
    let x = Type.mkTypeVar("x", Kind.TypeStar);
    let assocA = Type.mkAssoc("AssocA", Type.Variable(x), Kind.TypeStar);
    let assocB = Type.mkAssoc("AssocB", Type.Variable(x), Kind.TypeStar);
    let int32 = Type.Constructor(Type.mkTypeCon("Int32", Kind.TypeStar));

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
        )
    );

    Assert.assertEq(
        expected = int32,
        Type.AssociatedMember(assocA) |> reduceType(constraintEnv, Nil)
    )
}


// constraintEnv: { ReadEff x = Read, WriteEff x = Write }
// `(ReadEff x + ~WriteEff x) -> (Read + ~Write)`
@Test
def reduceTypeTraversesNestedSetFormula(): Unit \ Assert = {
    let arg = Type.mkTypeVar("x", Kind.TypeStar);
    let readAssoc = Type.mkAssoc("ReadEff", Type.Variable(arg), Kind.EffectStar);
    let writeAssoc = Type.mkAssoc("WriteEff", Type.Variable(arg), Kind.EffectStar);
    let read = SetFormula.Singleton(
        EffectLabel.EffectLabel(Id.Id("Read"), EffectKind.Regular)
    );
    let write = SetFormula.Singleton(
        EffectLabel.EffectLabel(Id.Id("Write"), EffectKind.Regular)
    );

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
        )
    );

    let ty = Type.SetFormula(SetFormula.Binary(
        BinarySetFormula.BinarySetFormula(
            SetFormula.AssociatedMember(readAssoc),
            SetBinaryOp.Union,
            SetFormula.Complement(SetFormula.AssociatedMember(writeAssoc))
        )
    ));

    Assert.assertEq(
        expected = Type.SetFormula(SetFormula.Binary(
            BinarySetFormula.BinarySetFormula(
                read,
                SetBinaryOp.Union,
                SetFormula.Complement(write)
            )
        )),
        ty |> reduceType(constraintEnv, Nil)
    )
}
