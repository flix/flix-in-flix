def unMkEquality(left: Type, right: Type): EqualityConstraint =
    EqualityConstraint.EqualityConstraint(left, right)


def unMkGivenEquality(left: Type, right: Type): Constraint =
    Constraint.Equality(unMkEquality(left, right))


def unEmptyConstraintEnv(): ConstraintEnvironment =
    ConstraintEnvironment.ConstraintEnvironment(Map.empty())


// `x ~ Int32 -> { x -> Int32 }`
@Test
def matchTypesVariableCreatesSubstitution(): Unit \ Assert = {
    let x = Type.mkTypeVar("x", Kind.TypeStar);
    let int32 = Type.Constructor(Type.mkTypeCon("Int32", Kind.TypeStar));

    Assert.assertEq(
        expected = Ok(Substitution.singleton(x, int32)),
        matchTypes(Type.Variable(x), int32)
    )
}


// `x : Type ~ {} -> KindMismatch`
@Test
def matchTypesVariableRejectsKindMismatch(): Unit \ Assert = {
    let x = Type.mkTypeVar("x", Kind.TypeStar);
    let emptySet = Type.SetFormula(SetFormula.Empty);

    Assert.assertEq(
        expected = Err(MatchError.KindMismatch),
        matchTypes(Type.Variable(x), emptySet)
    )
}


// `f x ~ Unary Int32 -> { f -> Unary, x -> Int32 }`
@Test
def matchTypesApplicationMergesSubstitutions(): Unit \ Assert = {
    let t = Kind.TypeStar;
    let tToT = Kind.Function(FunctionKind.FunctionKind(t, t));
    let f = Type.mkTypeVar("f", tToT);
    let x = Type.mkTypeVar("x", t);
    let unary = Type.Constructor(Type.mkTypeCon("Unary", tToT));
    let int32 = Type.Constructor(Type.mkTypeCon("Int32", t));

    let left = Type.Application(
        TypeApplication.TypeApplication(Type.Variable(f), Type.Variable(x))
    );
    let right = Type.Application(
        TypeApplication.TypeApplication(unary, int32)
    );

    match matchTypes(left, right) {
        case Ok(subst) => {
            Assert.assertEq(expected = Some(unary), subst |> Substitution.get(f));
            Assert.assertEq(expected = Some(int32), subst |> Substitution.get(x))
        }

        case Err(err) => bug!("expected successful match, found: ${err}")
    }
}


// `Pair x x ~ Pair Int32 Bool -> DoesNotMatch`
@Test
def matchTypesApplicationRejectsInconsistentSubstitution(): Unit \ Assert = {
    let t = Kind.TypeStar;
    let pair = Type.Constructor(Type.mkTypeCon(
        "Pair",
        Kind.Function(FunctionKind.FunctionKind(
            t,
            Kind.Function(FunctionKind.FunctionKind(t, t))
        ))
    ));
    let x = Type.mkTypeVar("x", t);
    let int32 = Type.Constructor(Type.mkTypeCon("Int32", t));
    let bool = Type.Constructor(Type.mkTypeCon("Bool", t));

    let left = Type.Application(TypeApplication.TypeApplication(
        Type.Application(TypeApplication.TypeApplication(
            pair,
            Type.Variable(x)
        )),
        Type.Variable(x)
    ));
    let right = Type.Application(TypeApplication.TypeApplication(
        Type.Application(TypeApplication.TypeApplication(
            pair,
            int32
        )),
        bool
    ));

    Assert.assertEq(
        expected = Err(MatchError.DoesNotMatch),
        matchTypes(left, right)
    )
}


// `Assoc x ~ Assoc Int32 -> { x -> Int32 }`
@Test
def matchTypesAssociatedMemberMatchesUnderlyingArgument(): Unit \ Assert = {
    let assocId = Id.Id("Assoc");
    let x = Type.mkTypeVar("x", Kind.TypeStar);
    let int32 = Type.Constructor(Type.mkTypeCon("Int32", Kind.TypeStar));

    let left = Type.AssociatedMember(AssociatedMember.AssociatedMember(
        assocId,
        Type.Variable(x),
        Kind.TypeStar
    ));
    let right = Type.AssociatedMember(AssociatedMember.AssociatedMember(
        assocId,
        int32,
        Kind.TypeStar
    ));

    Assert.assertEq(
        expected = Ok(Substitution.singleton(x, int32)),
        matchTypes(left, right)
    )
}


// `Unary x ~ Unary Int32 -> { Unary ~ Unary, x ~ Int32 }`
@Test
def unifyOneStepApplicationCreatesEqualityConstraints(): Unit \ Assert = {
    let t = Kind.TypeStar;
    let tToT = Kind.Function(FunctionKind.FunctionKind(t, t));
    let unary = Type.Constructor(Type.mkTypeCon("Unary", tToT));
    let x = Type.mkTypeVar("x", t);
    let int32 = Type.Constructor(Type.mkTypeCon("Int32", t));

    let left = Type.Application(TypeApplication.TypeApplication(
        unary,
        Type.Variable(x)
    ));
    let right = Type.Application(TypeApplication.TypeApplication(
        unary,
        int32
    ));

    Assert.assertEq(
        expected = Ok((
            unMkEquality(unary, unary)
            :: unMkEquality(Type.Variable(x), int32)
            :: Nil,
            Substitution.empty()
        )),
        unifyOneStep(unEmptyConstraintEnv(), Nil, left, right)
    )
}


// `x ~ Int32 -> { x -> Int32 }`
@Test
def unifyOneStepVariableCreatesSubstitution(): Unit \ Assert = {
    let x = Type.mkTypeVar("x", Kind.TypeStar);
    let int32 = Type.Constructor(Type.mkTypeCon("Int32", Kind.TypeStar));

    Assert.assertEq(
        expected = Ok((Nil, Substitution.singleton(x, int32))),
        unifyOneStep(
            unEmptyConstraintEnv(),
            Nil,
            Type.Variable(x),
            int32
        )
    )
}


// `x ~ Unary x -> OccursCheckFailed`
@Test
def unifyOneStepVariableRejectsOccursCheckFailure(): Unit \ Assert = {
    let t = Kind.TypeStar;
    let tToT = Kind.Function(FunctionKind.FunctionKind(t, t));
    let x = Type.mkTypeVar("x", t);
    let unary = Type.Constructor(Type.mkTypeCon("Unary", tToT));
    let unaryX = Type.Application(TypeApplication.TypeApplication(
        unary,
        Type.Variable(x)
    ));

    Assert.assertEq(
        expected = Err(UnificationError.OccursCheckFailed),
        unifyOneStep(
            unEmptyConstraintEnv(),
            Nil,
            Type.Variable(x),
            unaryX
        )
    )
}


// `Int32 ~ eff -> KindMismatch`
@Test
def unifyOneStepRightVariableRejectsKindMismatch(): Unit \ Assert = {
    let int32 = Type.Constructor(Type.mkTypeCon("Int32", Kind.TypeStar));
    let effectVar = Type.mkTypeVar("eff", Kind.EffectStar);

    Assert.assertEq(
        expected = Err(UnificationError.KindMismatch),
        unifyOneStep(
            unEmptyConstraintEnv(),
            Nil,
            int32,
            Type.Variable(effectVar)
        )
    )
}


// `Int32 ~ Int32 -> no new constraints`
@Test
def unifyOneStepIdenticalTypesShortCircuits(): Unit \ Assert = {
    let int32 = Type.Constructor(Type.mkTypeCon("Int32", Kind.TypeStar));

    Assert.assertEq(
        expected = Ok((Nil, Substitution.empty())),
        unifyOneStep(unEmptyConstraintEnv(), Nil, int32, int32)
    )
}


// `Int32 ~ Bool -> NoApplicableRule`
@Test
def unifyOneStepDifferentConstructorsHaveNoApplicableRule(): Unit \ Assert = {
    let int32 = Type.Constructor(Type.mkTypeCon("Int32", Kind.TypeStar));
    let bool = Type.Constructor(Type.mkTypeCon("Bool", Kind.TypeStar));

    Assert.assertEq(
        expected = Err(UnificationError.NoApplicableRule),
        unifyOneStep(unEmptyConstraintEnv(), Nil, int32, bool)
    )
}


// given: { Elem x = Bool }
// `Elem x ~ Bool -> { Bool ~ Bool }`
@Test
def unifyOneStepAssociatedMemberUsesGivenReductionOneStepAtATime(): Unit \ Assert = {
    let x = Type.mkTypeVar("x", Kind.TypeStar);
    let assoc = Type.mkAssoc("Elem", Type.Variable(x), Kind.TypeStar);
    let bool = Type.Constructor(Type.mkTypeCon("Bool", Kind.TypeStar));

    Assert.assertEq(
        expected = Ok((
            unMkEquality(bool, bool) :: Nil,
            Substitution.empty()
        )),
        unifyOneStep(
            unEmptyConstraintEnv(),
            unMkGivenEquality(Type.AssociatedMember(assoc), bool) :: Nil,
            Type.AssociatedMember(assoc),
            bool
        )
    )
}


// given: { Elem x = Bool }
// `Elem x ~ Int32 -> { Bool ~ Int32 }`
@Test
def unifyOneStepAssociatedMemberProducesResidualEquality(): Unit \ Assert = {
    let x = Type.mkTypeVar("x", Kind.TypeStar);
    let assoc = Type.mkAssoc("Elem", Type.Variable(x), Kind.TypeStar);
    let bool = Type.Constructor(Type.mkTypeCon("Bool", Kind.TypeStar));
    let int32 = Type.Constructor(Type.mkTypeCon("Int32", Kind.TypeStar));

    Assert.assertEq(
        expected = Ok((
            unMkEquality(bool, int32) :: Nil,
            Substitution.empty()
        )),
        unifyOneStep(
            unEmptyConstraintEnv(),
            unMkGivenEquality(Type.AssociatedMember(assoc), bool) :: Nil,
            Type.AssociatedMember(assoc),
            int32
        )
    )
}


// constraintEnv: { ReadEff x = Read }
// `ReadEff x ~ Int32 -> KindMismatch`
@Test
def unifyOneStepAssociatedMemberRejectsKindMismatchAfterReduction(): Unit \ Assert = {
    let x = Type.mkTypeVar("x", Kind.TypeStar);
    let readAssoc = Type.mkAssoc("ReadEff", Type.Variable(x), Kind.EffectStar);
    let read = Type.SetFormula(SetFormula.Singleton(
        EffectLabel.EffectLabel(Id.Id("Read"))
    ));
    let int32 = Type.Constructor(Type.mkTypeCon("Int32", Kind.TypeStar));

    let constraintEnv = ConstraintEnvironment.ConstraintEnvironment(
        Map.singleton(
            Id.Id("ReadEff"),
            unMkEquality(Type.AssociatedMember(readAssoc), read) :: Nil
        )
    );

    Assert.assertEq(
        expected = Err(UnificationError.KindMismatch),
        unifyOneStep(
            constraintEnv,
            Nil,
            Type.AssociatedMember(readAssoc),
            int32
        )
    )
}


// `Elem x ~ Int32 -> NoApplicableRule`
@Test
def unifyOneStepAssociatedMemberWithoutReductionHasNoApplicableRule(): Unit \ Assert = {
    let x = Type.mkTypeVar("x", Kind.TypeStar);
    let assoc = Type.mkAssoc("Elem", Type.Variable(x), Kind.TypeStar);
    let int32 = Type.Constructor(Type.mkTypeCon("Int32", Kind.TypeStar));

    Assert.assertEq(
        expected = Err(UnificationError.NoApplicableRule),
        unifyOneStep(
            unEmptyConstraintEnv(),
            Nil,
            Type.AssociatedMember(assoc),
            int32
        )
    )
}


// `Unary x ~ Unary Int32 -> [], { x -> Int32 }`
@Test
def unifyRepeatApplicationFullyUnifies(): Unit \ Assert = {
    let t = Kind.TypeStar;
    let tToT = Kind.Function(FunctionKind.FunctionKind(t, t));
    let unary = Type.Constructor(Type.mkTypeCon("Unary", tToT));
    let x = Type.mkTypeVar("x", t);
    let int32 = Type.Constructor(Type.mkTypeCon("Int32", t));

    let constraints = unMkEquality(
        Type.Application(TypeApplication.TypeApplication(
            unary,
            Type.Variable(x)
        )),
        Type.Application(TypeApplication.TypeApplication(
            unary,
            int32
        ))
    ) :: Nil;

    let (remaining, subst) = unifyRepeat(unEmptyConstraintEnv(), Nil, constraints);

    Assert.assertEq(expected = Nil, remaining);
    Assert.assertEq(expected = Some(int32), subst |> Substitution.get(x))
}


// `Int32 ~ Bool, x ~ Int32 -> [Int32 ~ Bool], { x -> Int32 }`
@Test
def unifyRepeatPreservesUnsolvedConstraints(): Unit \ Assert = {
    let x = Type.mkTypeVar("x", Kind.TypeStar);
    let int32 = Type.Constructor(Type.mkTypeCon("Int32", Kind.TypeStar));
    let bool = Type.Constructor(Type.mkTypeCon("Bool", Kind.TypeStar));

    let constraints = unMkEquality(int32, bool)
        :: unMkEquality(Type.Variable(x), int32)
        :: Nil;

    let (remaining, subst) = unifyRepeat(unEmptyConstraintEnv(), Nil, constraints);

    Assert.assertEq(expected = unMkEquality(int32, bool) :: Nil, remaining);
    Assert.assertEq(expected = Some(int32), subst |> Substitution.get(x))
}


// given: { Elem x = Bool }
// `Elem x ~ Bool -> [], {}`
@Test
def unifyRepeatConsumesResidualEqualityFromAssociatedMemberReduction(): Unit \ Assert = {
    let x = Type.mkTypeVar("x", Kind.TypeStar);
    let assoc = Type.mkAssoc("Elem", Type.Variable(x), Kind.TypeStar);
    let bool = Type.Constructor(Type.mkTypeCon("Bool", Kind.TypeStar));

    let constraints = unMkEquality(Type.AssociatedMember(assoc), bool) :: Nil;

    let (remaining, subst) = unifyRepeat(
        unEmptyConstraintEnv(),
        unMkGivenEquality(Type.AssociatedMember(assoc), bool) :: Nil,
        constraints
    );

    Assert.assertEq(expected = Nil, remaining);
    Assert.assertEq(expected = Substitution.empty(), subst)
}


// constraintEnv: { AssocA x = AssocB x, AssocB x = Int32 }
// `AssocA x ~ Int32 -> [], {}`
@Test
def unifyRepeatFullyReducesChainedAssociatedMembers(): Unit \ Assert = {
    let x = Type.mkTypeVar("x", Kind.TypeStar);
    let assocA = Type.mkAssoc("AssocA", Type.Variable(x), Kind.TypeStar);
    let assocB = Type.mkAssoc("AssocB", Type.Variable(x), Kind.TypeStar);
    let int32 = Type.Constructor(Type.mkTypeCon("Int32", Kind.TypeStar));

    let constraintEnv = ConstraintEnvironment.ConstraintEnvironment(
        Map.union(
            Map.singleton(
                Id.Id("AssocA"),
                unMkEquality(
                    Type.AssociatedMember(assocA),
                    Type.AssociatedMember(assocB)
                ) :: Nil
            ),
            Map.singleton(
                Id.Id("AssocB"),
                unMkEquality(Type.AssociatedMember(assocB), int32) :: Nil
            )
        )
    );

    let constraints = unMkEquality(Type.AssociatedMember(assocA), int32) :: Nil;

    let (remaining, subst) = unifyRepeat(constraintEnv, Nil, constraints);

    Assert.assertEq(expected = Nil, remaining);
    Assert.assertEq(expected = Substitution.empty(), subst)
}


// `x ~ Int32, y ~ x -> [], { x -> Int32, y -> Int32 }`
@Test
def unifyRepeatComposesSubstitutionsAcrossSteps(): Unit \ Assert = {
    let x = Type.mkTypeVar("x", Kind.TypeStar);
    let y = Type.mkTypeVar("y", Kind.TypeStar);
    let int32 = Type.Constructor(Type.mkTypeCon("Int32", Kind.TypeStar));

    let constraints = unMkEquality(Type.Variable(x), int32)
        :: unMkEquality(Type.Variable(y), Type.Variable(x))
        :: Nil;

    let (remaining, subst) = unifyRepeat(unEmptyConstraintEnv(), Nil, constraints);

    Assert.assertEq(expected = Nil, remaining);
    Assert.assertEq(expected = Some(int32), subst |> Substitution.get(x));
    Assert.assertEq(expected = Some(int32), subst |> Substitution.get(y))
}


// `y ~ x, x ~ Int32 -> [], { x -> Int32, y -> Int32 }`
@Test
def unifyRepeatComposesSubstitutionsAcrossStepsInReverseOrder(): Unit \ Assert = {
    let x = Type.mkTypeVar("x", Kind.TypeStar);
    let y = Type.mkTypeVar("y", Kind.TypeStar);
    let int32 = Type.Constructor(Type.mkTypeCon("Int32", Kind.TypeStar));

    let constraints = unMkEquality(Type.Variable(y), Type.Variable(x))
        :: unMkEquality(Type.Variable(x), int32)
        :: Nil;

    let (remaining, subst) = unifyRepeat(unEmptyConstraintEnv(), Nil, constraints);

    Assert.assertEq(expected = Nil, remaining);
    Assert.assertEq(expected = Some(int32), subst |> Substitution.get(x));
    Assert.assertEq(expected = Some(int32), subst |> Substitution.get(y))
}
