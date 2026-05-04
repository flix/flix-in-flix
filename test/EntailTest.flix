def enMkEquality(left: Type, right: Type): EqConstr =
    (left, right)


def enMkGivenEquality(left: Type, right: Type): Constr =
    Constr.Eq(left, right)


def enMkClassConstraint(name: Id, ty: Type): ClassConstr =
    (name, ty)


def enMkGivenClass(name: Id, ty: Type): Constr =
    Constr.Class(name, ty)


def enMkInstance(
    className: Id,
    classType: Type,
    context: List[Constr]
): Inst =
    Inst.Inst(Qual.Qual(
        context,
        enMkClassConstraint(className, classType)
    ))


// `x ~ Int32 -> Some([], { x -> Int32 })`
@Test
def entailOneDelegatesEqualityGoalsToUnification(): Unit \ Assert = {
    let x = Tyvar.Tyvar("x", Kind.Star);
    let int32 = Type.Con(Tycon.Tycon("Int32", Kind.Star));

    Assert.assertEq(
        expected = Some((Nil, Subst.singleton(x, int32))),
        entailOne(
            ConstrEnv.empty(),
            Nil,
            Constr.Eq(Type.Var(x), int32)
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
            ConstrEnv.empty(),
            enMkGivenEquality(
                Type.Assoc(genericAssoc),
                Type.Var(a)
            ) :: Nil,
            Constr.Eq(
                Type.Assoc(specificAssoc),
                int32
            )
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

    let constraintEnv = ConstrEnv.addAssocEq(
        "Elem",
        enMkEquality(
            Type.Assoc(genericAssoc),
            Type.Var(a)
        ),
        ConstrEnv.empty()
    );

    Assert.assertEq(
        expected = Some((
            Constr.Eq(int32, int32) :: Nil,
            Subst.empty()
        )),
        entailOne(
            constraintEnv,
            Nil,
            Constr.Eq(
                Type.Assoc(specificAssoc),
                int32
            )
        )
    )
}


// given: { Ord Int32 }, classEnv: { Ord : Eq }
// `Eq Int32 -> Some([])`
@Test
def entailOneDischargesClassGoalByGivenSuperclass(): Unit \ Assert = {
    let int32 = Type.Con(Tycon.Tycon("Int32", Kind.Star));

    let constraintEnv = ConstrEnv.empty()
        |> ConstrEnv.addClass("Ord")
        |> ConstrEnv.addSuper("Ord", "Eq");

    Assert.assertEq(
        expected = Some((Nil, Subst.empty())),
        entailOne(
            constraintEnv,
            enMkGivenClass("Ord", int32) :: Nil,
            Constr.Class("Eq", int32)
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

    let constraintEnv = ConstrEnv.addAssocEq(
        "Elem",
        enMkEquality(
            Type.Assoc(genericAssoc),
            Type.Var(a)
        ),
        ConstrEnv.empty()
    );

    Assert.assertEq(
        expected = Some((
            Constr.Class("Show", int32) :: Nil,
            Subst.empty()
        )),
        entailOne(
            constraintEnv,
            Nil,
            Constr.Class(
                "Show",
                Type.Assoc(specificAssoc)
            )
        )
    )
}


// classEnv: { Eq instance Eq a if Show a }
// `Eq Int32 -> Some([Show Int32])`
@Test
def entailOneInstantiatesMatchingInstanceContext(): Unit \ Assert = {
    let a = Tyvar.Tyvar("a", Kind.Star);
    let int32 = Type.Con(Tycon.Tycon("Int32", Kind.Star));

    let constraintEnv = ConstrEnv.empty()
        |> ConstrEnv.addClass("Eq")
        |> ConstrEnv.addInst(
            "Eq",
            enMkInstance(
                "Eq",
                Type.Var(a),
                enMkGivenClass("Show", Type.Var(a)) :: Nil
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
            Constr.Class("Eq", int32)
        )
    )
}


// `x ~ Int32, Show x` with given `{ Show Int32 } -> [], { x -> Int32 }`
@Test
def entailRepeatAppliesEqualitySubstitutionToRemainingGoals(): Unit \ Assert = {
    let x = Tyvar.Tyvar("x", Kind.Star);
    let int32 = Type.Con(Tycon.Tycon("Int32", Kind.Star));

    let constraints = Constr.Eq(
        Type.Var(x),
        int32
    ) :: Constr.Class(
        "Show",
        Type.Var(x)
    ) :: Nil;

    let (remaining, subst) = entailRepeat(
        ConstrEnv.empty(),
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

    let constraintEnv = ConstrEnv.empty()
        |> ConstrEnv.addAssocEq(
            "Elem",
            enMkEquality(
                Type.Assoc(genericAssoc),
                Type.Var(a)
            )
        )
        |> ConstrEnv.addClass("Eq")
        |> ConstrEnv.addInst(
            "Eq",
            enMkInstance(
                "Eq",
                Type.Var(a),
                enMkGivenClass("Show", Type.Var(a)) :: Nil
            )
        );

    let (remaining, subst) = entailRepeat(
        constraintEnv,
        enMkGivenClass("Show", int32) :: Nil,
        Constr.Class(
            "Eq",
            Type.Assoc(specificAssoc)
        ) :: Nil
    );

    Assert.assertEq(expected = Nil, remaining);
    Assert.assertEq(expected = Subst.empty(), subst)
}
