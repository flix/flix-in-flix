def enMkEquality(left: Type, right: Type): EqConstr =
    EqConstr.EqConstr(left, right)


def enMkGivenEquality(left: Type, right: Type): Constr =
    Constr.Eq(enMkEquality(left, right))


def enMkClassConstraint(name: Id, ty: Type): ClassConstr =
    ClassConstr.ClassConstr(name, ty)


def enMkGivenClass(name: Id, ty: Type): Constr =
    Constr.Class(enMkClassConstraint(name, ty))


def enMkInstance(
    className: Id,
    classType: Type,
    context: List[Constr]
): Inst =
    Inst.Inst(Qual.Qual(
        context,
        enMkClassConstraint(className, classType)
    ))


def enEmptyConstraintEnv(): ConstrEnv =
    ConstrEnv.ConstrEnv(Map.empty(), Map.empty())


// `x ~ Int32 -> Some([], { x -> Int32 })`
@Test
def entailOneDelegatesEqualityGoalsToUnification(): Unit \ Assert = {
    let x = Tyvar.Tyvar("x", Kind.Star);
    let int32 = Type.Con(Tycon.Tycon("Int32", Kind.Star));

    Assert.assertEq(
        expected = Some((Nil, Subst.singleton(x, int32))),
        entailOne(
            enEmptyConstraintEnv(),
            Nil,
            Constr.Eq(enMkEquality(Type.Var(x), int32))
        )
    )
}


// given: { Elem a = a }
// `Elem Int32 ~ Int32 -> None`
@Test
def entailOneDoesNotInstantiateEqualityGiven(): Unit \ Assert = {
    let a = Tyvar.Tyvar("a", Kind.Star);
    let int32 = Type.Con(Tycon.Tycon("Int32", Kind.Star));
    let genericAssoc = Tyassoc.Tyassoc("Elem", Type.Var(a), Kind.Star);
    let specificAssoc = Tyassoc.Tyassoc("Elem", int32, Kind.Star);

    Assert.assertEq(
        expected = None,
        entailOne(
            enEmptyConstraintEnv(),
            enMkGivenEquality(
                Type.Assoc(genericAssoc),
                Type.Var(a)
            ) :: Nil,
            Constr.Eq(enMkEquality(
                Type.Assoc(specificAssoc),
                int32
            ))
        )
    )
}


// constraintEnv: { Elem a = a }
// `Elem Int32 ~ Int32 -> Some([Int32 ~ Int32], {})`
@Test
def entailOneInstantiatesEqualityFromConstraintEnvironment(): Unit \ Assert = {
    let a = Tyvar.Tyvar("a", Kind.Star);
    let int32 = Type.Con(Tycon.Tycon("Int32", Kind.Star));
    let genericAssoc = Tyassoc.Tyassoc("Elem", Type.Var(a), Kind.Star);
    let specificAssoc = Tyassoc.Tyassoc("Elem", int32, Kind.Star);

    let constraintEnv = ConstrEnv.ConstrEnv(
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
            Constr.Eq(enMkEquality(int32, int32)) :: Nil,
            Subst.empty()
        )),
        entailOne(
            constraintEnv,
            Nil,
            Constr.Eq(enMkEquality(
                Type.Assoc(specificAssoc),
                int32
            ))
        )
    )
}


// given: { Ord Int32 }, classEnv: { Ord : Eq }
// `Eq Int32 -> Some([])`
@Test
def entailOneDischargesClassGoalByGivenSuperclass(): Unit \ Assert = {
    let int32 = Type.Con(Tycon.Tycon("Int32", Kind.Star));

    let constraintEnv = ConstrEnv.ConstrEnv(
        Map.empty(),
        Map.singleton(
            "Ord",
            Class.Class("Eq" :: Nil, Nil)
        )
    );

    Assert.assertEq(
        expected = Some((Nil, Subst.empty())),
        entailOne(
            constraintEnv,
            enMkGivenClass("Ord", int32) :: Nil,
            Constr.Class(enMkClassConstraint("Eq", int32))
        )
    )
}


// constraintEnv: { Elem a = a }
// `Show (Elem Int32) -> Some([Show Int32])`
@Test
def entailOneReducesClassGoalTypeBeforeOtherEntailmentRules(): Unit \ Assert = {
    let a = Tyvar.Tyvar("a", Kind.Star);
    let int32 = Type.Con(Tycon.Tycon("Int32", Kind.Star));
    let genericAssoc = Tyassoc.Tyassoc("Elem", Type.Var(a), Kind.Star);
    let specificAssoc = Tyassoc.Tyassoc("Elem", int32, Kind.Star);

    let constraintEnv = ConstrEnv.ConstrEnv(
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
            Constr.Class(enMkClassConstraint("Show", int32)) :: Nil,
            Subst.empty()
        )),
        entailOne(
            constraintEnv,
            Nil,
            Constr.Class(enMkClassConstraint(
                "Show",
                Type.Assoc(specificAssoc)
            ))
        )
    )
}


// classEnv: { Eq instance Eq a if Show a }
// `Eq Int32 -> Some([Show Int32])`
@Test
def entailOneInstantiatesMatchingInstanceContext(): Unit \ Assert = {
    let a = Tyvar.Tyvar("a", Kind.Star);
    let int32 = Type.Con(Tycon.Tycon("Int32", Kind.Star));

    let constraintEnv = ConstrEnv.ConstrEnv(
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
            Subst.empty()
        )),
        entailOne(
            constraintEnv,
            Nil,
            Constr.Class(enMkClassConstraint("Eq", int32))
        )
    )
}


// `x ~ Int32, Show x` with given `{ Show Int32 } -> [], { x -> Int32 }`
@Test
def entailRepeatAppliesEqualitySubstitutionToRemainingGoals(): Unit \ Assert = {
    let x = Tyvar.Tyvar("x", Kind.Star);
    let int32 = Type.Con(Tycon.Tycon("Int32", Kind.Star));

    let constraints = Constr.Eq(
        enMkEquality(Type.Var(x), int32)
    ) :: Constr.Class(
        enMkClassConstraint("Show", Type.Var(x))
    ) :: Nil;

    let (remaining, subst) = entailRepeat(
        enEmptyConstraintEnv(),
        enMkGivenClass("Show", int32) :: Nil,
        constraints
    );

    Assert.assertEq(expected = Nil, remaining);
    Assert.assertEq(expected = Some(int32), subst |> Subst.get(x))
}


// given: { Show Int32 }, classEnv: { Eq instance Eq a if Show a, Elem a = a }
// `Eq (Elem Int32) -> [], {}`
@Test
def entailRepeatChainsReductionAndInstanceEntailment(): Unit \ Assert = {
    let a = Tyvar.Tyvar("a", Kind.Star);
    let int32 = Type.Con(Tycon.Tycon("Int32", Kind.Star));
    let genericAssoc = Tyassoc.Tyassoc("Elem", Type.Var(a), Kind.Star);
    let specificAssoc = Tyassoc.Tyassoc("Elem", int32, Kind.Star);

    let constraintEnv = ConstrEnv.ConstrEnv(
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
        Constr.Class(enMkClassConstraint(
            "Eq",
            Type.Assoc(specificAssoc)
        )) :: Nil
    );

    Assert.assertEq(expected = Nil, remaining);
    Assert.assertEq(expected = Subst.empty(), subst)
}
