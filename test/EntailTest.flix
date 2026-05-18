def enMkEquality(left: Type, right: Type): EqConstr =
    (left, right)


def enMkGivenEquality(left: Type, right: Type): Constr =
    Constr.Eq((left, right))


def enMkClassConstraint(name: Id, ty: Type): ClassConstr =
    (name, ty)


def enMkGivenClass(name: Id, ty: Type): Constr =
    Constr.Class((name, ty))


def enEnvWithGivens(givens: List[Constr]): ConstrEnv =
    addGivens(givens, emptyConstrEnv())


def enMkInstance(
    className: Id,
    classType: Type,
    context: List[Constr]
): Inst = Qual.Qual(
    context,
    enMkClassConstraint(className, classType)
)


def enAddInst(inst: Inst, env: ConstrEnv): ConstrEnv =
    match addInst(inst, env) {
        case Ok(nextEnv) => nextEnv
        case Err(err)    => bug!(err)
    }


// `x ~ Int32 -> Some([], { x -> Int32 })`
@Test
def entailDelegatesEqualityGoalsToUnification(): Unit \ Assert = {
    let x = Tyvar.Tyvar("x", Kind.Star);
    let int32 = Type.Con(Tycon.Tycon("Int32", Kind.Star));

    Assert.assertEq(
        expected = Some((Nil, Subst.singleton(x, int32))),
        entail(
            emptyConstrEnv(),
            Constr.Eq((Type.Var(x), int32))
        )
    )
}


// given: { Elem a = a }
// `Elem Int32 ~ Int32 -> Some([Int32 ~ Int32], {})`
@Test
def entailInstantiatesEqualityGiven(): Unit \ Assert = {
    let a = Tyvar.Tyvar("a", Kind.Star);
    let int32 = Type.Con(Tycon.Tycon("Int32", Kind.Star));
    let genericAssoc = Tyassoc.Tyassoc("Elem", Type.Var(a), Kind.Star);
    let specificAssoc = Tyassoc.Tyassoc("Elem", int32, Kind.Star);

    Assert.assertEq(
        expected = Some((
            Constr.Eq((int32, int32)) :: Nil,
            Subst.empty()
        )),
        entail(
            enEnvWithGivens(
                enMkGivenEquality(
                    Type.Assoc(genericAssoc),
                    Type.Var(a)
                ) :: Nil
            ),
            Constr.Eq((
                Type.Assoc(specificAssoc),
                int32
            ))
        )
    )
}


// constraintEnv: { Elem a = a }
// `Elem Int32 ~ Int32 -> Some([Int32 ~ Int32], {})`
@Test
def entailInstantiatesEqualityFromConstraintEnvironment(): Unit \ Assert = {
    let a = Tyvar.Tyvar("a", Kind.Star);
    let int32 = Type.Con(Tycon.Tycon("Int32", Kind.Star));
    let genericAssoc = Tyassoc.Tyassoc("Elem", Type.Var(a), Kind.Star);
    let specificAssoc = Tyassoc.Tyassoc("Elem", int32, Kind.Star);

    let constraintEnv = addAssocEq(
        "Elem",
        enMkEquality(
            Type.Assoc(genericAssoc),
            Type.Var(a)
        ),
        emptyConstrEnv()
    );

    Assert.assertEq(
        expected = Some((
            Constr.Eq((int32, int32)) :: Nil,
            Subst.empty()
        )),
        entail(
            constraintEnv,
            Constr.Eq((
                Type.Assoc(specificAssoc),
                int32
            ))
        )
    )
}


// given: { Ord Int32 }, classEnv: { Ord : Eq }
// `Eq Int32 -> Some([])`
@Test
def entailDischargesClassGoalByGivenSuperclass(): Unit \ Assert = {
    let int32 = Type.Con(Tycon.Tycon("Int32", Kind.Star));

    let constraintEnv = emptyConstrEnv()
        |> addClass("Ord")
        |> addSuper("Ord", "Eq")
        |> addGivens(enMkGivenClass("Ord", int32) :: Nil);

    Assert.assertEq(
        expected = Some((Nil, Subst.empty())),
        entail(
            constraintEnv,
            Constr.Class(("Eq", int32))
        )
    )
}


// constraintEnv: { Elem a = a }
// `Show (Elem Int32) -> Some([Show Int32])`
@Test
def entailReducesClassGoalTypeBeforeOtherEntailmentRules(): Unit \ Assert = {
    let a = Tyvar.Tyvar("a", Kind.Star);
    let int32 = Type.Con(Tycon.Tycon("Int32", Kind.Star));
    let genericAssoc = Tyassoc.Tyassoc("Elem", Type.Var(a), Kind.Star);
    let specificAssoc = Tyassoc.Tyassoc("Elem", int32, Kind.Star);

    let constraintEnv = addAssocEq(
        "Elem",
        enMkEquality(
            Type.Assoc(genericAssoc),
            Type.Var(a)
        ),
        emptyConstrEnv()
    );

    Assert.assertEq(
        expected = Some((
            Constr.Class(("Show", int32)) :: Nil,
            Subst.empty()
        )),
        entail(
            constraintEnv,
            Constr.Class((
                "Show",
                Type.Assoc(specificAssoc)
            ))
        )
    )
}


// classEnv: { Eq instance Eq (List a) if Show a }
// `Eq (List Int32) -> Some([Show Int32])`
@Test
def entailInstantiatesMatchingInstanceContext(): Unit \ Assert = {
    let a = Tyvar.Tyvar("a", Kind.Star);
    let int32 = Type.Con(Tycon.Tycon("Int32", Kind.Star));
    let listA = mkAp(tList(), Type.Var(a));
    let listInt32 = mkAp(tList(), int32);

    let constraintEnv = emptyConstrEnv()
        |> addClass("Eq")
        |> enAddInst(
            enMkInstance(
                "Eq",
                listA,
                enMkGivenClass("Show", Type.Var(a)) :: Nil
            )
        );

    Assert.assertEq(
        expected = Some((
            enMkGivenClass("Show", int32) :: Nil,
            Subst.empty()
        )),
        entail(
            constraintEnv,
            Constr.Class(("Eq", listInt32))
        )
    )
}


// `x ~ Int32, Show x` with given `{ Show Int32 } -> [], { x -> Int32 }`
@Test
def entailRepeatAppliesEqualitySubstitutionToRemainingGoals(): Unit \ Assert = {
    let x = Tyvar.Tyvar("x", Kind.Star);
    let int32 = Type.Con(Tycon.Tycon("Int32", Kind.Star));

    let constraints = Constr.Eq((
        Type.Var(x),
        int32
    )) :: Constr.Class((
        "Show",
        Type.Var(x)
    )) :: Nil;

    let constraintEnv = enEnvWithGivens(enMkGivenClass("Show", int32) :: Nil);

    let (remaining, subst) = solveAll(
        constraintEnv,
        constraints
    );

    Assert.assertEq(expected = Nil, remaining);
    Assert.assertEq(expected = Some(int32), subst |> Subst.get(x))
}


// given: { Show Int32 }, classEnv: { Eq instance Eq (List a) if Show a, Elem a = List a }
// `Eq (Elem Int32) -> [], {}`
@Test
def entailRepeatChainsReductionAndInstanceEntailment(): Unit \ Assert = {
    let a = Tyvar.Tyvar("a", Kind.Star);
    let int32 = Type.Con(Tycon.Tycon("Int32", Kind.Star));
    let genericAssoc = Tyassoc.Tyassoc("Elem", Type.Var(a), Kind.Star);
    let specificAssoc = Tyassoc.Tyassoc("Elem", int32, Kind.Star);

    let constraintEnv = emptyConstrEnv()
        |> addAssocEq(
            "Elem",
            enMkEquality(
                Type.Assoc(genericAssoc),
                mkAp(tList(), Type.Var(a))
            )
        )
        |> addClass("Eq")
        |> enAddInst(
            enMkInstance(
                "Eq",
                mkAp(tList(), Type.Var(a)),
                enMkGivenClass("Show", Type.Var(a)) :: Nil
            )
        )
        |> addGivens(enMkGivenClass("Show", int32) :: Nil);

    let (remaining, subst) = solveAll(
        constraintEnv,
        Constr.Class((
            "Eq",
            Type.Assoc(specificAssoc)
        )) :: Nil
    );

    Assert.assertEq(expected = Nil, remaining);
    Assert.assertEq(expected = Subst.empty(), subst)
}
