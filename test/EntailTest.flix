def enMkEquality(left: Type, right: Type): EqualityConstraint =
    EqualityConstraint.EqualityConstraint(left, right)


def enMkGivenEquality(left: Type, right: Type): Constraint =
    Constraint.Equality(enMkEquality(left, right))


def enMkClassConstraint(name: Id, ty: Type): ClassConstraint =
    ClassConstraint.ClassConstraint(name, ty)


def enMkGivenClass(name: Id, ty: Type): Constraint =
    Constraint.Class(enMkClassConstraint(name, ty))


def enMkInstance(
    className: Id,
    classType: Type,
    context: List[Constraint]
): Instance =
    Instance.Instance(Qualified.Qualified(
        enMkClassConstraint(className, classType),
        context
    ))


def enEmptyConstraintEnv(): ConstraintEnvironment =
    ConstraintEnvironment.ConstraintEnvironment(Map.empty(), Map.empty())


// `x ~ Int32 -> Some([], { x -> Int32 })`
@Test
def entailOneStepDelegatesEqualityGoalsToUnification(): Unit \ Assert = {
    let x = Type.mkTyvar("x", Kind.Star);
    let int32 = Type.Con(Type.mkTycon("Int32", Kind.Star));

    Assert.assertEq(
        expected = Some((Nil, Substitution.singleton(x, int32))),
        entailOneStep(
            enEmptyConstraintEnv(),
            Nil,
            Constraint.Equality(enMkEquality(Type.Var(x), int32))
        )
    )
}


// given: { Elem a = a }
// `Elem Int32 ~ Int32 -> None`
@Test
def entailOneStepDoesNotInstantiateEqualityGiven(): Unit \ Assert = {
    let a = Type.mkTyvar("a", Kind.Star);
    let int32 = Type.Con(Type.mkTycon("Int32", Kind.Star));
    let genericAssoc = Type.mkTyassoc("Elem", Type.Var(a), Kind.Star);
    let specificAssoc = Type.mkTyassoc("Elem", int32, Kind.Star);

    Assert.assertEq(
        expected = None,
        entailOneStep(
            enEmptyConstraintEnv(),
            enMkGivenEquality(
                Type.Assoc(genericAssoc),
                Type.Var(a)
            ) :: Nil,
            Constraint.Equality(enMkEquality(
                Type.Assoc(specificAssoc),
                int32
            ))
        )
    )
}


// constraintEnv: { Elem a = a }
// `Elem Int32 ~ Int32 -> Some([Int32 ~ Int32], {})`
@Test
def entailOneStepInstantiatesEqualityFromConstraintEnvironment(): Unit \ Assert = {
    let a = Type.mkTyvar("a", Kind.Star);
    let int32 = Type.Con(Type.mkTycon("Int32", Kind.Star));
    let genericAssoc = Type.mkTyassoc("Elem", Type.Var(a), Kind.Star);
    let specificAssoc = Type.mkTyassoc("Elem", int32, Kind.Star);

    let constraintEnv = ConstraintEnvironment.ConstraintEnvironment(
        Map.singleton(
            "Elem",
            enMkEquality(
                Type.Assoc(genericAssoc),
                Type.Var(a)
            ) :: Nil
        ),
        Map.empty()
    );

    Assert.assertEq(
        expected = Some((
            Constraint.Equality(enMkEquality(int32, int32)) :: Nil,
            Substitution.empty()
        )),
        entailOneStep(
            constraintEnv,
            Nil,
            Constraint.Equality(enMkEquality(
                Type.Assoc(specificAssoc),
                int32
            ))
        )
    )
}


// given: { Ord Int32 }, classEnv: { Ord : Eq }
// `Eq Int32 -> Some([])`
@Test
def entailOneStepDischargesClassGoalByGivenSuperclass(): Unit \ Assert = {
    let int32 = Type.Con(Type.mkTycon("Int32", Kind.Star));

    let constraintEnv = ConstraintEnvironment.ConstraintEnvironment(
        Map.empty(),
        Map.singleton(
            "Ord",
            Class.Class("Eq" :: Nil, Nil)
        )
    );

    Assert.assertEq(
        expected = Some((Nil, Substitution.empty())),
        entailOneStep(
            constraintEnv,
            enMkGivenClass("Ord", int32) :: Nil,
            Constraint.Class(enMkClassConstraint("Eq", int32))
        )
    )
}


// constraintEnv: { Elem a = a }
// `Show (Elem Int32) -> Some([Show Int32])`
@Test
def entailOneStepReducesClassGoalTypeBeforeOtherEntailmentRules(): Unit \ Assert = {
    let a = Type.mkTyvar("a", Kind.Star);
    let int32 = Type.Con(Type.mkTycon("Int32", Kind.Star));
    let genericAssoc = Type.mkTyassoc("Elem", Type.Var(a), Kind.Star);
    let specificAssoc = Type.mkTyassoc("Elem", int32, Kind.Star);

    let constraintEnv = ConstraintEnvironment.ConstraintEnvironment(
        Map.singleton(
            "Elem",
            enMkEquality(
                Type.Assoc(genericAssoc),
                Type.Var(a)
            ) :: Nil
        ),
        Map.empty()
    );

    Assert.assertEq(
        expected = Some((
            Constraint.Class(enMkClassConstraint("Show", int32)) :: Nil,
            Substitution.empty()
        )),
        entailOneStep(
            constraintEnv,
            Nil,
            Constraint.Class(enMkClassConstraint(
                "Show",
                Type.Assoc(specificAssoc)
            ))
        )
    )
}


// classEnv: { Eq instance Eq a if Show a }
// `Eq Int32 -> Some([Show Int32])`
@Test
def entailOneStepInstantiatesMatchingInstanceContext(): Unit \ Assert = {
    let a = Type.mkTyvar("a", Kind.Star);
    let int32 = Type.Con(Type.mkTycon("Int32", Kind.Star));

    let constraintEnv = ConstraintEnvironment.ConstraintEnvironment(
        Map.empty(),
        Map.singleton(
            "Eq",
            Class.Class(
                Nil,
                enMkInstance(
                    "Eq",
                    Type.Var(a),
                    enMkGivenClass("Show", Type.Var(a)) :: Nil
                ) :: Nil
            )
        )
    );

    Assert.assertEq(
        expected = Some((
            enMkGivenClass("Show", int32) :: Nil,
            Substitution.empty()
        )),
        entailOneStep(
            constraintEnv,
            Nil,
            Constraint.Class(enMkClassConstraint("Eq", int32))
        )
    )
}


// `x ~ Int32, Show x` with given `{ Show Int32 } -> [], { x -> Int32 }`
@Test
def entailRepeatAppliesEqualitySubstitutionToRemainingGoals(): Unit \ Assert = {
    let x = Type.mkTyvar("x", Kind.Star);
    let int32 = Type.Con(Type.mkTycon("Int32", Kind.Star));

    let constraints = Constraint.Equality(
        enMkEquality(Type.Var(x), int32)
    ) :: Constraint.Class(
        enMkClassConstraint("Show", Type.Var(x))
    ) :: Nil;

    let (remaining, subst) = entailRepeat(
        enEmptyConstraintEnv(),
        enMkGivenClass("Show", int32) :: Nil,
        constraints
    );

    Assert.assertEq(expected = Nil, remaining);
    Assert.assertEq(expected = Some(int32), subst |> Substitution.get(x))
}


// given: { Show Int32 }, classEnv: { Eq instance Eq a if Show a, Elem a = a }
// `Eq (Elem Int32) -> [], {}`
@Test
def entailRepeatChainsReductionAndInstanceEntailment(): Unit \ Assert = {
    let a = Type.mkTyvar("a", Kind.Star);
    let int32 = Type.Con(Type.mkTycon("Int32", Kind.Star));
    let genericAssoc = Type.mkTyassoc("Elem", Type.Var(a), Kind.Star);
    let specificAssoc = Type.mkTyassoc("Elem", int32, Kind.Star);

    let constraintEnv = ConstraintEnvironment.ConstraintEnvironment(
        Map.singleton(
            "Elem",
            enMkEquality(
                Type.Assoc(genericAssoc),
                Type.Var(a)
            ) :: Nil
        ),
        Map.singleton(
            "Eq",
            Class.Class(
                Nil,
                enMkInstance(
                    "Eq",
                    Type.Var(a),
                    enMkGivenClass("Show", Type.Var(a)) :: Nil
                ) :: Nil
            )
        )
    );

    let (remaining, subst) = entailRepeat(
        constraintEnv,
        enMkGivenClass("Show", int32) :: Nil,
        Constraint.Class(enMkClassConstraint(
            "Eq",
            Type.Assoc(specificAssoc)
        )) :: Nil
    );

    Assert.assertEq(expected = Nil, remaining);
    Assert.assertEq(expected = Substitution.empty(), subst)
}
