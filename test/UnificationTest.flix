use Assert.assertEq
def unMkEquality(left: Type, right: Type): EqConstr =
    EqConstr.EqConstr(left, right)


def unMkGivenEquality(left: Type, right: Type): Constr =
    Constr.Eq(unMkEquality(left, right))


def unEmptyConstraintEnv(): ConstrEnv =
    ConstrEnv.ConstrEnv(Map.empty(), Map.empty())


// `x ~ Int32 -> { x -> Int32 }`
@Test
def matchTypesVariableCreatesSubstitution(): Unit \ Assert = {
    let x = Tyvar.Tyvar("x", Kind.Star);
    let int32 = Type.Con(Tycon.Tycon("Int32", Kind.Star));

    Assert.assertEq(
        expected = Some(Subst.singleton(x, int32)),
        matchTy(Type.Var(x), int32)
    )
}


// `x : Type ~ {} -> KindMismatch`
@Test
def matchTypesVariableRejectsKindMismatch(): Unit \ Assert = {
    let x = Tyvar.Tyvar("x", Kind.Star);
    let emptySet = Type.efEmpty();

    Assert.assertEq(
        expected = None,
        matchTy(Type.Var(x), emptySet)
    )
}


// `f x ~ Unary Int32 -> { f -> Unary, x -> Int32 }`
@Test
def matchTypesApplicationMergesSubstitutions(): Unit \ Assert = {
    let t = Kind.Star;
    let tToT = Kind.KFun(t, t);
    let f = Tyvar.Tyvar("f", tToT);
    let x = Tyvar.Tyvar("x", t);
    let unary = Type.Con(Tycon.Tycon("Unary", tToT));
    let int32 = Type.Con(Tycon.Tycon("Int32", t));

    let left = Type.Ap(Type.Var(f), Type.Var(x));
    let right = Type.Ap(unary, int32);

    match matchTy(left, right) {
        case Some(subst) => {
            Assert.assertEq(expected = Some(unary), subst |> Subst.get(f));
            Assert.assertEq(expected = Some(int32), subst |> Subst.get(x))
        }

        case None => bug!("expected successful match")
    }
}


// `Pair x x ~ Pair Int32 Bool -> DoesNotMatch`
@Test
def matchTypesApplicationRejectsInconsistentSubstitution(): Unit \ Assert = {
    let t = Kind.Star;
    let pair = Type.Con(Tycon.Tycon(
        "Pair",
        Kind.KFun(
            t,
            Kind.KFun(t, t)
        )
    ));
    let x = Tyvar.Tyvar("x", t);
    let int32 = Type.Con(Tycon.Tycon("Int32", t));
    let bool = Type.Con(Tycon.Tycon("Bool", t));

    let left = Type.Ap(
        Type.Ap(pair, Type.Var(x)),
        Type.Var(x)
    );
    let right = Type.Ap(
        Type.Ap(pair, int32),
        bool
    );

    Assert.assertEq(expected = None, matchTy(left, right))
}


// `Assoc x ~ Assoc Int32 -> { x -> Int32 }`
@Test
def matchTypesTyassocMatchesUnderlyingArgument(): Unit \ Assert = {
    let assocId = "Assoc";
    let x = Tyvar.Tyvar("x", Kind.Star);
    let int32 = Type.Con(Tycon.Tycon("Int32", Kind.Star));

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
        expected = Some(Subst.singleton(x, int32)),
        matchTy(left, right)
    )
}


// `Unary x ~ Unary Int32 -> { Unary ~ Unary, x ~ Int32 }`
@Test
def unifyOneStepApplicationCreatesEqualityConstraints(): Unit \ Assert = {
    let t = Kind.Star;
    let tToT = Kind.KFun(t, t);
    let unary = Type.Con(Tycon.Tycon("Unary", tToT));
    let x = Tyvar.Tyvar("x", t);
    let int32 = Type.Con(Tycon.Tycon("Int32", t));

    let left = Type.Ap(unary, Type.Var(x));
    let right = Type.Ap(unary, int32);

    Assert.assertEq(
        expected = Ok((
            unMkEquality(unary, unary)
            :: unMkEquality(Type.Var(x), int32)
            :: Nil,
            Subst.empty()
        )),
        unifyOneStep(unEmptyConstraintEnv(), Nil, left, right)
    )
}


// `x ~ Int32 -> { x -> Int32 }`
@Test
def unifyOneStepVariableCreatesSubstitution(): Unit \ Assert = {
    let x = Tyvar.Tyvar("x", Kind.Star);
    let int32 = Type.Con(Tycon.Tycon("Int32", Kind.Star));

    Assert.assertEq(
        expected = Ok((Nil, Subst.singleton(x, int32))),
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
    let x = Tyvar.Tyvar("x", t);
    let unary = Type.Con(Tycon.Tycon("Unary", tToT));
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
    let int32 = Type.Con(Tycon.Tycon("Int32", Kind.Star));
    let effectVar = Tyvar.Tyvar("eff", Kind.Eff);

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
    let int32 = Type.Con(Tycon.Tycon("Int32", Kind.Star));

    Assert.assertEq(
        expected = Ok((Nil, Subst.empty())),
        unifyOneStep(unEmptyConstraintEnv(), Nil, int32, int32)
    )
}


// `Int32 ~ Bool -> NoApplicableRule`
@Test
def unifyOneStepDifferentConstructorsHaveNoApplicableRule(): Unit \ Assert = {
    let int32 = Type.Con(Tycon.Tycon("Int32", Kind.Star));
    let bool = Type.Con(Tycon.Tycon("Bool", Kind.Star));

    Assert.assertEq(
        expected = Err(UnificationError.NoApplicableRule),
        unifyOneStep(unEmptyConstraintEnv(), Nil, int32, bool)
    )
}


// `IO ~ x + IO -> some boolean substitution for x`
@Test
def unifyOneStepBooleanEffectsCreateSubstitution(): Unit \ Assert = {
    let x = Tyvar.Tyvar("x", Kind.Eff);
    let io = Type.io();
    let right = Type.mkUnion(Type.Var(x), io);

    assertEq(
        expected = true, 
        unifyOneStep(unEmptyConstraintEnv(), Nil, io, right) |> Result.isOk
    )
}


// `IO ~ ~IO -> NoApplicableRule`
@Test
def unifyOneStepUnsatisfiableBooleanEffectsHaveNoApplicableRule(): Unit \ Assert = {
    let io = Type.io();
    let notIo = Type.mkCompl(io);

    Assert.assertEq(
        expected = Err(UnificationError.NoApplicableRule),
        unifyOneStep(unEmptyConstraintEnv(), Nil, io, notIo)
    )
}


// `EffectUniverse ~ EffOf Phantom + ~(EffOf Phantom) -> {}`
@Test
def unifyOneStepBooleanEffectsTreatGroundEffectTyassocAsRigidConstant(): Unit \ Assert = {
    let phantom = Type.Con(Tycon.Tycon("Phantom", Kind.Star));
    let assoc = Type.Assoc(Tyassoc.Tyassoc("EffOf", phantom, Kind.Eff));
    let tautology = Type.mkUnion(assoc, Type.mkCompl(assoc));

    Assert.assertEq(
        expected = Ok((Nil, Subst.empty())),
        unifyOneStep(
            unEmptyConstraintEnv(),
            Nil,
            Type.efUniverse(),
            tautology
        )
    )
}


// `{} ~ EffOf Phantom & ~(EffOf Phantom) -> {}`
@Test
def unifyOneStepBooleanEffectsTreatGroundEffectTyassocAsRigidConstantInContradiction(): Unit \ Assert = {
    let phantom = Type.Con(Tycon.Tycon("Phantom", Kind.Star));
    let assoc = Type.Assoc(Tyassoc.Tyassoc("EffOf", phantom, Kind.Eff));
    let contradiction = Type.mkIntersect(assoc, Type.mkCompl(assoc));

    Assert.assertEq(
        expected = Ok((Nil, Subst.empty())),
        unifyOneStep(
            unEmptyConstraintEnv(),
            Nil,
            Type.efEmpty(),
            contradiction
        )
    )
}


// `{} ~ EffOf Phantom + ~(EffOf Phantom) -> NoApplicableRule`
@Test
def unifyOneStepBooleanEffectsRejectUnsatisfiableGroundEffectTyassocFormula(): Unit \ Assert = {
    let phantom = Type.Con(Tycon.Tycon("Phantom", Kind.Star));
    let assoc = Type.Assoc(Tyassoc.Tyassoc("EffOf", phantom, Kind.Eff));
    let tautology = Type.mkUnion(assoc, Type.mkCompl(assoc));

    Assert.assertEq(
        expected = Err(UnificationError.NoApplicableRule),
        unifyOneStep(
            unEmptyConstraintEnv(),
            Nil,
            Type.efEmpty(),
            tautology
        )
    )
}


// given: { Elem x = Bool }
// `Elem x ~ Bool -> { Bool ~ Bool }`
@Test
def unifyOneStepTyassocUsesGivenReductionOneStepAtATime(): Unit \ Assert = {
    let x = Tyvar.Tyvar("x", Kind.Star);
    let assoc = Tyassoc.Tyassoc("Elem", Type.Var(x), Kind.Star);
    let bool = Type.Con(Tycon.Tycon("Bool", Kind.Star));

    Assert.assertEq(
        expected = Ok((
            unMkEquality(bool, bool) :: Nil,
            Subst.empty()
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
    let a = Tyvar.Tyvar("a", Kind.Star);
    let int32 = Type.Con(Tycon.Tycon("Int32", Kind.Star));
    let genericAssoc = Tyassoc.Tyassoc("Elem", Type.Var(a), Kind.Star);
    let specificAssoc = Tyassoc.Tyassoc("Elem", int32, Kind.Star);

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
    let a = Tyvar.Tyvar("a", Kind.Star);
    let int32 = Type.Con(Tycon.Tycon("Int32", Kind.Star));
    let genericAssoc = Tyassoc.Tyassoc("Elem", Type.Var(a), Kind.Star);
    let specificAssoc = Tyassoc.Tyassoc("Elem", int32, Kind.Star);

    let constraintEnv = ConstrEnv.ConstrEnv(
        Map.singleton(
            "Elem",
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
            Subst.empty()
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
    let x = Tyvar.Tyvar("x", Kind.Star);
    let assoc = Tyassoc.Tyassoc("Elem", Type.Var(x), Kind.Star);
    let bool = Type.Con(Tycon.Tycon("Bool", Kind.Star));
    let int32 = Type.Con(Tycon.Tycon("Int32", Kind.Star));

    Assert.assertEq(
        expected = Ok((
            unMkEquality(bool, int32) :: Nil,
            Subst.empty()
        )),
        unifyOneStep(
            unEmptyConstraintEnv(),
            unMkGivenEquality(Type.Assoc(assoc), bool) :: Nil,
            Type.Assoc(assoc),
            int32
        )
    )
}


// given: { EffOf x = IO }
// `EffOf x ~ eff + IO -> { IO ~ eff + IO }`
@Test
def unifyOneStepEffectTyassocProducesBooleanResidualEquality(): Unit \ Assert = {
    let x = Tyvar.Tyvar("x", Kind.Star);
    let effVar = Tyvar.Tyvar("eff", Kind.Eff);
    let assoc = Tyassoc.Tyassoc("EffOf", Type.Var(x), Kind.Eff);
    let io = Type.io();
    let right = Type.mkUnion(Type.Var(effVar), io);

    Assert.assertEq(
        expected = Ok((
            unMkEquality(io, right) :: Nil,
            Subst.empty()
        )),
        unifyOneStep(
            unEmptyConstraintEnv(),
            unMkGivenEquality(Type.Assoc(assoc), io) :: Nil,
            Type.Assoc(assoc),
            right
        )
    )
}


// constraintEnv: { ReadEff x = Read }
// `ReadEff x ~ Int32 -> KindMismatch`
@Test
def unifyOneStepTyassocRejectsKindMismatchAfterReduction(): Unit \ Assert = {
    let x = Tyvar.Tyvar("x", Kind.Star);
    let readAssoc = Tyassoc.Tyassoc("ReadEff", Type.Var(x), Kind.Eff);
    let read = Type.efConstant("Read");
    let int32 = Type.Con(Tycon.Tycon("Int32", Kind.Star));

    let constraintEnv = ConstrEnv.ConstrEnv(
        Map.singleton(
            "ReadEff",
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
    let x = Tyvar.Tyvar("x", Kind.Star);
    let assoc = Tyassoc.Tyassoc("Elem", Type.Var(x), Kind.Star);
    let int32 = Type.Con(Tycon.Tycon("Int32", Kind.Star));

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
    let unary = Type.Con(Tycon.Tycon("Unary", tToT));
    let x = Tyvar.Tyvar("x", t);
    let int32 = Type.Con(Tycon.Tycon("Int32", t));

    let constraints = unMkEquality(
        Type.Ap(unary, Type.Var(x)),
        Type.Ap(unary, int32)
    ) :: Nil;

    let (remaining, subst) = unifyRepeat(unEmptyConstraintEnv(), Nil, constraints);

    Assert.assertEq(expected = Nil, remaining);
    Assert.assertEq(expected = Some(int32), subst |> Subst.get(x))
}


// `Unary x ~ Unary Int32, IO ~ eff + IO -> [], { x -> Int32, eff -> ... }`
@Test
def unifyRepeatSolvesStarAndBooleanEffectConstraintsTogether(): Unit \ Assert = {
    let t = Kind.Star;
    let tToT = Kind.KFun(t, t);
    let unary = Type.Con(Tycon.Tycon("Unary", tToT));
    let x = Tyvar.Tyvar("x", t);
    let effVar = Tyvar.Tyvar("eff", Kind.Eff);
    let int32 = Type.Con(Tycon.Tycon("Int32", t));
    let io = Type.io();

    let constraints = unMkEquality(
        Type.Ap(unary, Type.Var(x)),
        Type.Ap(unary, int32)
    ) :: unMkEquality(
        io,
        Type.mkUnion(Type.Var(effVar), io)
    ) :: Nil;

    let (remaining, subst) = unifyRepeat(unEmptyConstraintEnv(), Nil, constraints);

    Assert.assertEq(expected = Nil, remaining);
    Assert.assertEq(expected = Some(int32), subst |> Subst.get(x));
    Assert.assertEq(expected = false, subst |> Subst.get(effVar) |> Option.isEmpty)
}


// constraintEnv: { EffOf a = IO }
// `EffOf Int32 ~ eff + IO -> [], { eff -> ... }`
@Test
def unifyRepeatSolvesBooleanResidualFromEffectTyassocReduction(): Unit \ Assert = {
    let a = Tyvar.Tyvar("a", Kind.Star);
    let effVar = Tyvar.Tyvar("eff", Kind.Eff);
    let int32 = Type.Con(Tycon.Tycon("Int32", Kind.Star));
    let genericAssoc = Tyassoc.Tyassoc("EffOf", Type.Var(a), Kind.Eff);
    let specificAssoc = Tyassoc.Tyassoc("EffOf", int32, Kind.Eff);
    let io = Type.io();

    let constraintEnv = ConstrEnv.ConstrEnv(
        Map.singleton(
            "EffOf",
            unMkEquality(Type.Assoc(genericAssoc), io) :: Nil
        ),
        Map.empty()
    );

    let constraints = unMkEquality(
        Type.Assoc(specificAssoc),
        Type.mkUnion(Type.Var(effVar), io)
    ) :: Nil;

    let (remaining, subst) = unifyRepeat(constraintEnv, Nil, constraints);

    Assert.assertEq(expected = Nil, remaining);
    Assert.assertEq(expected = false, subst |> Subst.get(effVar) |> Option.isEmpty)
}


// `Int32 ~ Bool, x ~ Int32 -> [Int32 ~ Bool], { x -> Int32 }`
@Test
def unifyRepeatPreservesUnsolvedConstraints(): Unit \ Assert = {
    let x = Tyvar.Tyvar("x", Kind.Star);
    let int32 = Type.Con(Tycon.Tycon("Int32", Kind.Star));
    let bool = Type.Con(Tycon.Tycon("Bool", Kind.Star));

    let constraints = unMkEquality(int32, bool)
        :: unMkEquality(Type.Var(x), int32)
        :: Nil;

    let (remaining, subst) = unifyRepeat(unEmptyConstraintEnv(), Nil, constraints);

    Assert.assertEq(expected = unMkEquality(int32, bool) :: Nil, remaining);
    Assert.assertEq(expected = Some(int32), subst |> Subst.get(x))
}


// `Int32 ~ Bool, IO ~ eff + IO -> [Int32 ~ Bool], { eff -> ... }`
@Test
def unifyRepeatPreservesUnsolvedStarConstraintsWhileSolvingBooleanEffects(): Unit \ Assert = {
    let effVar = Tyvar.Tyvar("eff", Kind.Eff);
    let int32 = Type.Con(Tycon.Tycon("Int32", Kind.Star));
    let bool = Type.Con(Tycon.Tycon("Bool", Kind.Star));
    let io = Type.io();

    let constraints = unMkEquality(int32, bool)
        :: unMkEquality(io, Type.mkUnion(Type.Var(effVar), io))
        :: Nil;

    let (remaining, subst) = unifyRepeat(unEmptyConstraintEnv(), Nil, constraints);

    Assert.assertEq(expected = unMkEquality(int32, bool) :: Nil, remaining);
    Assert.assertEq(expected = false, subst |> Subst.get(effVar) |> Option.isEmpty)
}


// given: { Elem x = Bool }
// `Elem x ~ Bool -> [], {}`
@Test
def unifyRepeatConsumesResidualEqualityFromTyassocReduction(): Unit \ Assert = {
    let x = Tyvar.Tyvar("x", Kind.Star);
    let assoc = Tyassoc.Tyassoc("Elem", Type.Var(x), Kind.Star);
    let bool = Type.Con(Tycon.Tycon("Bool", Kind.Star));

    let constraints = unMkEquality(Type.Assoc(assoc), bool) :: Nil;

    let (remaining, subst) = unifyRepeat(
        unEmptyConstraintEnv(),
        unMkGivenEquality(Type.Assoc(assoc), bool) :: Nil,
        constraints
    );

    Assert.assertEq(expected = Nil, remaining);
    Assert.assertEq(expected = Subst.empty(), subst)
}


// `x ~ Int32, IO ~ ~IO -> [IO ~ ~IO], { x -> Int32 }`
@Test
def unifyRepeatPreservesUnsolvedBooleanEffectsWhileSolvingStarConstraints(): Unit \ Assert = {
    let x = Tyvar.Tyvar("x", Kind.Star);
    let int32 = Type.Con(Tycon.Tycon("Int32", Kind.Star));
    let io = Type.io();
    let notIo = Type.mkCompl(io);

    let constraints = unMkEquality(Type.Var(x), int32)
        :: unMkEquality(io, notIo)
        :: Nil;

    let (remaining, subst) = unifyRepeat(unEmptyConstraintEnv(), Nil, constraints);

    Assert.assertEq(expected = unMkEquality(io, notIo) :: Nil, remaining);
    Assert.assertEq(expected = Some(int32), subst |> Subst.get(x))
}


// constraintEnv: { EffOf a = ~IO }
// `EffOf Int32 ~ IO -> [~IO ~ IO], {}`
@Test
def unifyRepeatPreservesUnsolvedBooleanResidualFromEffectTyassocReduction(): Unit \ Assert = {
    let a = Tyvar.Tyvar("a", Kind.Star);
    let int32 = Type.Con(Tycon.Tycon("Int32", Kind.Star));
    let genericAssoc = Tyassoc.Tyassoc("EffOf", Type.Var(a), Kind.Eff);
    let specificAssoc = Tyassoc.Tyassoc("EffOf", int32, Kind.Eff);
    let io = Type.io();
    let notIo = Type.mkCompl(io);

    let constraintEnv = ConstrEnv.ConstrEnv(
        Map.singleton(
            "EffOf",
            unMkEquality(Type.Assoc(genericAssoc), notIo) :: Nil
        ),
        Map.empty()
    );

    let constraints = unMkEquality(Type.Assoc(specificAssoc), io) :: Nil;

    let (remaining, subst) = unifyRepeat(constraintEnv, Nil, constraints);

    Assert.assertEq(expected = unMkEquality(notIo, io) :: Nil, remaining);
    Assert.assertEq(expected = Subst.empty(), subst)
}


// constraintEnv: { AssocA x = AssocB x, AssocB x = Int32 }
// `AssocA x ~ Int32 -> [], {}`
@Test
def unifyRepeatFullyReducesChainedTyassocs(): Unit \ Assert = {
    let x = Tyvar.Tyvar("x", Kind.Star);
    let assocA = Tyassoc.Tyassoc("AssocA", Type.Var(x), Kind.Star);
    let assocB = Tyassoc.Tyassoc("AssocB", Type.Var(x), Kind.Star);
    let int32 = Type.Con(Tycon.Tycon("Int32", Kind.Star));

    let constraintEnv = ConstrEnv.ConstrEnv(
        Map.union(
            Map.singleton(
                "AssocA",
                unMkEquality(
                    Type.Assoc(assocA),
                    Type.Assoc(assocB)
                ) :: Nil
            ),
            Map.singleton(
                "AssocB",
                unMkEquality(Type.Assoc(assocB), int32) :: Nil
            )
        ),
        Map.empty()
    );

    let constraints = unMkEquality(Type.Assoc(assocA), int32) :: Nil;

    let (remaining, subst) = unifyRepeat(constraintEnv, Nil, constraints);

    Assert.assertEq(expected = Nil, remaining);
    Assert.assertEq(expected = Subst.empty(), subst)
}


// `x ~ Int32, y ~ x -> [], { x -> Int32, y -> Int32 }`
@Test
def unifyRepeatComposesSubstitutionsAcrossSteps(): Unit \ Assert = {
    let x = Tyvar.Tyvar("x", Kind.Star);
    let y = Tyvar.Tyvar("y", Kind.Star);
    let int32 = Type.Con(Tycon.Tycon("Int32", Kind.Star));

    let constraints = unMkEquality(Type.Var(x), int32)
        :: unMkEquality(Type.Var(y), Type.Var(x))
        :: Nil;

    let (remaining, subst) = unifyRepeat(unEmptyConstraintEnv(), Nil, constraints);

    Assert.assertEq(expected = Nil, remaining);
    Assert.assertEq(expected = Some(int32), subst |> Subst.get(x));
    Assert.assertEq(expected = Some(int32), subst |> Subst.get(y))
}


// `y ~ x, x ~ Int32 -> [], { x -> Int32, y -> Int32 }`
@Test
def unifyRepeatComposesSubstitutionsAcrossStepsInReverseOrder(): Unit \ Assert = {
    let x = Tyvar.Tyvar("x", Kind.Star);
    let y = Tyvar.Tyvar("y", Kind.Star);
    let int32 = Type.Con(Tycon.Tycon("Int32", Kind.Star));

    let constraints = unMkEquality(Type.Var(y), Type.Var(x))
        :: unMkEquality(Type.Var(x), int32)
        :: Nil;

    let (remaining, subst) = unifyRepeat(unEmptyConstraintEnv(), Nil, constraints);

    Assert.assertEq(expected = Nil, remaining);
    Assert.assertEq(expected = Some(int32), subst |> Subst.get(x));
    Assert.assertEq(expected = Some(int32), subst |> Subst.get(y))
}
