def unMkEquality(left: Type, right: Type): EqualityConstraint =
    EqualityConstraint.EqualityConstraint(left, right)


def unMkGivenEquality(left: Type, right: Type): Constraint =
    Constraint.Equality(unMkEquality(left, right))


def unEmptyConstraintEnv(): ConstraintEnvironment =
    ConstraintEnvironment.ConstraintEnvironment(Map.empty(), Map.empty())


// `x ~ Int32 -> { x -> Int32 }`
@Test
def matchTypesVariableCreatesSubstitution(): Unit \ Assert = {
    let x = Type.mkTyvar("x", Kind.Star);
    let int32 = Type.Con(Type.mkTycon("Int32", Kind.Star));

    Assert.assertEq(
        expected = Ok(Substitution.singleton(x, int32)),
        matchTypes(Type.Var(x), int32)
    )
}


// `x : Type ~ {} -> KindMismatch`
@Test
def matchTypesVariableRejectsKindMismatch(): Unit \ Assert = {
    let x = Type.mkTyvar("x", Kind.Star);
    let emptySet = Type.SetFormula(SetFormula.Empty);

    Assert.assertEq(
        expected = Err(MatchError.KindMismatch),
        matchTypes(Type.Var(x), emptySet)
    )
}


// `f x ~ Unary Int32 -> { f -> Unary, x -> Int32 }`
@Test
def matchTypesApplicationMergesSubstitutions(): Unit \ Assert = {
    let t = Kind.Star;
    let tToT = Kind.KFun(t, t);
    let f = Type.mkTyvar("f", tToT);
    let x = Type.mkTyvar("x", t);
    let unary = Type.Con(Type.mkTycon("Unary", tToT));
    let int32 = Type.Con(Type.mkTycon("Int32", t));

    let left = Type.Ap(Type.Var(f), Type.Var(x));
    let right = Type.Ap(unary, int32);

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
    let t = Kind.Star;
    let pair = Type.Con(Type.mkTycon(
        "Pair",
        Kind.KFun(
            t,
            Kind.KFun(t, t)
        )
    ));
    let x = Type.mkTyvar("x", t);
    let int32 = Type.Con(Type.mkTycon("Int32", t));
    let bool = Type.Con(Type.mkTycon("Bool", t));

    let left = Type.Ap(
        Type.Ap(pair, Type.Var(x)),
        Type.Var(x)
    );
    let right = Type.Ap(
        Type.Ap(pair, int32),
        bool
    );

    Assert.assertEq(
        expected = Err(MatchError.DoesNotMatch),
        matchTypes(left, right)
    )
}


// `Assoc x ~ Assoc Int32 -> { x -> Int32 }`
@Test
def matchTypesTyassocMatchesUnderlyingArgument(): Unit \ Assert = {
    let assocId = Id.Id("Assoc");
    let x = Type.mkTyvar("x", Kind.Star);
    let int32 = Type.Con(Type.mkTycon("Int32", Kind.Star));

    let left = Type.Assoc(Tyassoc.Tyassoc(
        assocId,
        Type.Var(x),
        Kind.Star
    ));
    let right = Type.Assoc(Tyassoc.Tyassoc(
        assocId,
        int32,
        Kind.Star
    ));

    Assert.assertEq(
        expected = Ok(Substitution.singleton(x, int32)),
        matchTypes(left, right)
    )
}


// `Unary x ~ Unary Int32 -> { Unary ~ Unary, x ~ Int32 }`
@Test
def unifyOneStepApplicationCreatesEqualityConstraints(): Unit \ Assert = {
    let t = Kind.Star;
    let tToT = Kind.KFun(t, t);
    let unary = Type.Con(Type.mkTycon("Unary", tToT));
    let x = Type.mkTyvar("x", t);
    let int32 = Type.Con(Type.mkTycon("Int32", t));

    let left = Type.Ap(unary, Type.Var(x));
    let right = Type.Ap(unary, int32);

    Assert.assertEq(
        expected = Ok((
            unMkEquality(unary, unary)
            :: unMkEquality(Type.Var(x), int32)
            :: Nil,
            Substitution.empty()
        )),
        unifyOneStep(unEmptyConstraintEnv(), Nil, left, right)
    )
}


// `x ~ Int32 -> { x -> Int32 }`
@Test
def unifyOneStepVariableCreatesSubstitution(): Unit \ Assert = {
    let x = Type.mkTyvar("x", Kind.Star);
    let int32 = Type.Con(Type.mkTycon("Int32", Kind.Star));

    Assert.assertEq(
        expected = Ok((Nil, Substitution.singleton(x, int32))),
        unifyOneStep(
            unEmptyConstraintEnv(),
            Nil,
            Type.Var(x),
            int32
        )
    )
}


// `x ~ Unary x -> OccursCheckFailed`
@Test
def unifyOneStepVariableRejectsOccursCheckFailure(): Unit \ Assert = {
    let t = Kind.Star;
    let tToT = Kind.KFun(t, t);
    let x = Type.mkTyvar("x", t);
    let unary = Type.Con(Type.mkTycon("Unary", tToT));
    let unaryX = Type.Ap(unary, Type.Var(x));

    Assert.assertEq(
        expected = Err(UnificationError.OccursCheckFailed),
        unifyOneStep(
            unEmptyConstraintEnv(),
            Nil,
            Type.Var(x),
            unaryX
        )
    )
}


// `Int32 ~ eff -> KindMismatch`
@Test
def unifyOneStepRightVariableRejectsKindMismatch(): Unit \ Assert = {
    let int32 = Type.Con(Type.mkTycon("Int32", Kind.Star));
    let effectVar = Type.mkTyvar("eff", Kind.Eff);

    Assert.assertEq(
        expected = Err(UnificationError.KindMismatch),
        unifyOneStep(
            unEmptyConstraintEnv(),
            Nil,
            int32,
            Type.Var(effectVar)
        )
    )
}


// `Int32 ~ Int32 -> no new constraints`
@Test
def unifyOneStepIdenticalTypesShortCircuits(): Unit \ Assert = {
    let int32 = Type.Con(Type.mkTycon("Int32", Kind.Star));

    Assert.assertEq(
        expected = Ok((Nil, Substitution.empty())),
        unifyOneStep(unEmptyConstraintEnv(), Nil, int32, int32)
    )
}


// `Int32 ~ Bool -> NoApplicableRule`
@Test
def unifyOneStepDifferentConstructorsHaveNoApplicableRule(): Unit \ Assert = {
    let int32 = Type.Con(Type.mkTycon("Int32", Kind.Star));
    let bool = Type.Con(Type.mkTycon("Bool", Kind.Star));

    Assert.assertEq(
        expected = Err(UnificationError.NoApplicableRule),
        unifyOneStep(unEmptyConstraintEnv(), Nil, int32, bool)
    )
}


// given: { Elem x = Bool }
// `Elem x ~ Bool -> { Bool ~ Bool }`
@Test
def unifyOneStepTyassocUsesGivenReductionOneStepAtATime(): Unit \ Assert = {
    let x = Type.mkTyvar("x", Kind.Star);
    let assoc = Type.mkTyassoc("Elem", Type.Var(x), Kind.Star);
    let bool = Type.Con(Type.mkTycon("Bool", Kind.Star));

    Assert.assertEq(
        expected = Ok((
            unMkEquality(bool, bool) :: Nil,
            Substitution.empty()
        )),
        unifyOneStep(
            unEmptyConstraintEnv(),
            unMkGivenEquality(Type.Assoc(assoc), bool) :: Nil,
            Type.Assoc(assoc),
            bool
        )
    )
}


// given: { Elem a = a }
// `Elem Int32 ~ Int32 -> NoApplicableRule`
@Test
def unifyOneStepTyassocDoesNotInstantiateGivenEquality(): Unit \ Assert = {
    let a = Type.mkTyvar("a", Kind.Star);
    let int32 = Type.Con(Type.mkTycon("Int32", Kind.Star));
    let genericAssoc = Type.mkTyassoc("Elem", Type.Var(a), Kind.Star);
    let specificAssoc = Type.mkTyassoc("Elem", int32, Kind.Star);

    Assert.assertEq(
        expected = Err(UnificationError.NoApplicableRule),
        unifyOneStep(
            unEmptyConstraintEnv(),
            unMkGivenEquality(
                Type.Assoc(genericAssoc),
                Type.Var(a)
            ) :: Nil,
            Type.Assoc(specificAssoc),
            int32
        )
    )
}


// constraintEnv: { Elem a = a }
// `Elem Int32 ~ Int32 -> { Int32 ~ Int32 }`
@Test
def unifyOneStepTyassocInstantiatesConstraintEnvironmentEquality(): Unit \ Assert = {
    let a = Type.mkTyvar("a", Kind.Star);
    let int32 = Type.Con(Type.mkTycon("Int32", Kind.Star));
    let genericAssoc = Type.mkTyassoc("Elem", Type.Var(a), Kind.Star);
    let specificAssoc = Type.mkTyassoc("Elem", int32, Kind.Star);

    let constraintEnv = ConstraintEnvironment.ConstraintEnvironment(
        Map.singleton(
            Id.Id("Elem"),
            unMkEquality(
                Type.Assoc(genericAssoc),
                Type.Var(a)
            ) :: Nil
        ),
        Map.empty()
    );

    Assert.assertEq(
        expected = Ok((
            unMkEquality(int32, int32) :: Nil,
            Substitution.empty()
        )),
        unifyOneStep(
            constraintEnv,
            Nil,
            Type.Assoc(specificAssoc),
            int32
        )
    )
}


// given: { Elem x = Bool }
// `Elem x ~ Int32 -> { Bool ~ Int32 }`
@Test
def unifyOneStepTyassocProducesResidualEquality(): Unit \ Assert = {
    let x = Type.mkTyvar("x", Kind.Star);
    let assoc = Type.mkTyassoc("Elem", Type.Var(x), Kind.Star);
    let bool = Type.Con(Type.mkTycon("Bool", Kind.Star));
    let int32 = Type.Con(Type.mkTycon("Int32", Kind.Star));

    Assert.assertEq(
        expected = Ok((
            unMkEquality(bool, int32) :: Nil,
            Substitution.empty()
        )),
        unifyOneStep(
            unEmptyConstraintEnv(),
            unMkGivenEquality(Type.Assoc(assoc), bool) :: Nil,
            Type.Assoc(assoc),
            int32
        )
    )
}


// constraintEnv: { ReadEff x = Read }
// `ReadEff x ~ Int32 -> KindMismatch`
@Test
def unifyOneStepTyassocRejectsKindMismatchAfterReduction(): Unit \ Assert = {
    let x = Type.mkTyvar("x", Kind.Star);
    let readAssoc = Type.mkTyassoc("ReadEff", Type.Var(x), Kind.Eff);
    let read = Type.SetFormula(SetFormula.Singleton(
        EffectLabel.EffectLabel(Id.Id("Read"))
    ));
    let int32 = Type.Con(Type.mkTycon("Int32", Kind.Star));

    let constraintEnv = ConstraintEnvironment.ConstraintEnvironment(
        Map.singleton(
            Id.Id("ReadEff"),
            unMkEquality(Type.Assoc(readAssoc), read) :: Nil
        ), 
        Map.empty()
    );

    Assert.assertEq(
        expected = Err(UnificationError.KindMismatch),
        unifyOneStep(
            constraintEnv,
            Nil,
            Type.Assoc(readAssoc),
            int32
        )
    )
}


// `Elem x ~ Int32 -> NoApplicableRule`
@Test
def unifyOneStepTyassocWithoutReductionHasNoApplicableRule(): Unit \ Assert = {
    let x = Type.mkTyvar("x", Kind.Star);
    let assoc = Type.mkTyassoc("Elem", Type.Var(x), Kind.Star);
    let int32 = Type.Con(Type.mkTycon("Int32", Kind.Star));

    Assert.assertEq(
        expected = Err(UnificationError.NoApplicableRule),
        unifyOneStep(
            unEmptyConstraintEnv(),
            Nil,
            Type.Assoc(assoc),
            int32
        )
    )
}


// `Unary x ~ Unary Int32 -> [], { x -> Int32 }`
@Test
def unifyRepeatApplicationFullyUnifies(): Unit \ Assert = {
    let t = Kind.Star;
    let tToT = Kind.KFun(t, t);
    let unary = Type.Con(Type.mkTycon("Unary", tToT));
    let x = Type.mkTyvar("x", t);
    let int32 = Type.Con(Type.mkTycon("Int32", t));

    let constraints = unMkEquality(
        Type.Ap(unary, Type.Var(x)),
        Type.Ap(unary, int32)
    ) :: Nil;

    let (remaining, subst) = unifyRepeat(unEmptyConstraintEnv(), Nil, constraints);

    Assert.assertEq(expected = Nil, remaining);
    Assert.assertEq(expected = Some(int32), subst |> Substitution.get(x))
}


// `Int32 ~ Bool, x ~ Int32 -> [Int32 ~ Bool], { x -> Int32 }`
@Test
def unifyRepeatPreservesUnsolvedConstraints(): Unit \ Assert = {
    let x = Type.mkTyvar("x", Kind.Star);
    let int32 = Type.Con(Type.mkTycon("Int32", Kind.Star));
    let bool = Type.Con(Type.mkTycon("Bool", Kind.Star));

    let constraints = unMkEquality(int32, bool)
        :: unMkEquality(Type.Var(x), int32)
        :: Nil;

    let (remaining, subst) = unifyRepeat(unEmptyConstraintEnv(), Nil, constraints);

    Assert.assertEq(expected = unMkEquality(int32, bool) :: Nil, remaining);
    Assert.assertEq(expected = Some(int32), subst |> Substitution.get(x))
}


// given: { Elem x = Bool }
// `Elem x ~ Bool -> [], {}`
@Test
def unifyRepeatConsumesResidualEqualityFromTyassocReduction(): Unit \ Assert = {
    let x = Type.mkTyvar("x", Kind.Star);
    let assoc = Type.mkTyassoc("Elem", Type.Var(x), Kind.Star);
    let bool = Type.Con(Type.mkTycon("Bool", Kind.Star));

    let constraints = unMkEquality(Type.Assoc(assoc), bool) :: Nil;

    let (remaining, subst) = unifyRepeat(
        unEmptyConstraintEnv(),
        unMkGivenEquality(Type.Assoc(assoc), bool) :: Nil,
        constraints
    );

    Assert.assertEq(expected = Nil, remaining);
    Assert.assertEq(expected = Substitution.empty(), subst)
}


// constraintEnv: { AssocA x = AssocB x, AssocB x = Int32 }
// `AssocA x ~ Int32 -> [], {}`
@Test
def unifyRepeatFullyReducesChainedTyassocs(): Unit \ Assert = {
    let x = Type.mkTyvar("x", Kind.Star);
    let assocA = Type.mkTyassoc("AssocA", Type.Var(x), Kind.Star);
    let assocB = Type.mkTyassoc("AssocB", Type.Var(x), Kind.Star);
    let int32 = Type.Con(Type.mkTycon("Int32", Kind.Star));

    let constraintEnv = ConstraintEnvironment.ConstraintEnvironment(
        Map.union(
            Map.singleton(
                Id.Id("AssocA"),
                unMkEquality(
                    Type.Assoc(assocA),
                    Type.Assoc(assocB)
                ) :: Nil
            ),
            Map.singleton(
                Id.Id("AssocB"),
                unMkEquality(Type.Assoc(assocB), int32) :: Nil
            )
        ),
        Map.empty()
    );

    let constraints = unMkEquality(Type.Assoc(assocA), int32) :: Nil;

    let (remaining, subst) = unifyRepeat(constraintEnv, Nil, constraints);

    Assert.assertEq(expected = Nil, remaining);
    Assert.assertEq(expected = Substitution.empty(), subst)
}


// `x ~ Int32, y ~ x -> [], { x -> Int32, y -> Int32 }`
@Test
def unifyRepeatComposesSubstitutionsAcrossSteps(): Unit \ Assert = {
    let x = Type.mkTyvar("x", Kind.Star);
    let y = Type.mkTyvar("y", Kind.Star);
    let int32 = Type.Con(Type.mkTycon("Int32", Kind.Star));

    let constraints = unMkEquality(Type.Var(x), int32)
        :: unMkEquality(Type.Var(y), Type.Var(x))
        :: Nil;

    let (remaining, subst) = unifyRepeat(unEmptyConstraintEnv(), Nil, constraints);

    Assert.assertEq(expected = Nil, remaining);
    Assert.assertEq(expected = Some(int32), subst |> Substitution.get(x));
    Assert.assertEq(expected = Some(int32), subst |> Substitution.get(y))
}


// `y ~ x, x ~ Int32 -> [], { x -> Int32, y -> Int32 }`
@Test
def unifyRepeatComposesSubstitutionsAcrossStepsInReverseOrder(): Unit \ Assert = {
    let x = Type.mkTyvar("x", Kind.Star);
    let y = Type.mkTyvar("y", Kind.Star);
    let int32 = Type.Con(Type.mkTycon("Int32", Kind.Star));

    let constraints = unMkEquality(Type.Var(y), Type.Var(x))
        :: unMkEquality(Type.Var(x), int32)
        :: Nil;

    let (remaining, subst) = unifyRepeat(unEmptyConstraintEnv(), Nil, constraints);

    Assert.assertEq(expected = Nil, remaining);
    Assert.assertEq(expected = Some(int32), subst |> Substitution.get(x));
    Assert.assertEq(expected = Some(int32), subst |> Substitution.get(y))
}
