def suMkClassConstraint(name: Id, ty: Type): ClassConstr =
    ClassConstr.ClassConstr(name, ty)


def suMkGivenClass(name: Id, ty: Type): Constr =
    Constr.Class(suMkClassConstraint(name, ty))


def suMkScheme(
    kinds: List[Kind],
    context: List[Constr],
    ty: Type
): Scheme[Type] =
    Scheme.Scheme(kinds, Qual.Qual(context, ty))


def suEmptyConstraintEnv(): ConstrEnv =
    ConstrEnv.ConstrEnv(Map.empty(), Map.empty())


def suRunSubsume(env: ConstrEnv, l: Scheme[Type], r: Scheme[Type]): Bool =
    Fresh.withFresh(_ -> subsume(env, l, r))


// `Int32 ≤ Int32`
@Test
def subsumeAcceptsIdenticalMonotypes(): Unit \ Assert = {
    let int32 = Type.int32();
    let scheme = Scheme.newUnqual(int32);

    Assert.assertEq(
        expected = true,
        suRunSubsume(suEmptyConstraintEnv(), scheme, scheme)
    )
}


// `forall a. a ≤ Int32`
@Test
def subsumeLetsLeftPolymorphicSchemeMatchMonotype(): Unit \ Assert = {
    let poly = suMkScheme(Kind.Star :: Nil, Nil, Type.Gen(0));
    let mono = Scheme.newUnqual(Type.int32());

    Assert.assertEq(
        expected = true,
        suRunSubsume(suEmptyConstraintEnv(), poly, mono)
    )
}


// `Int32 ≤ forall a. a -> false`
@Test
def subsumeTreatsRightQuantifiedVariablesAsRigid(): Unit \ Assert = {
    let mono = Scheme.newUnqual(Type.int32());
    let poly = suMkScheme(Kind.Star :: Nil, Nil, Type.Gen(0));

    Assert.assertEq(
        expected = false,
        suRunSubsume(suEmptyConstraintEnv(), mono, poly)
    )
}


// `forall a. Show a => a ≤ forall b. b -> false`
@Test
def subsumeRejectsLeftContextNotEntailedByRightScheme(): Unit \ Assert = {
    let left = suMkScheme(
        Kind.Star :: Nil,
        suMkGivenClass("Show", Type.Gen(0)) :: Nil,
        Type.Gen(0)
    );
    let right = suMkScheme(Kind.Star :: Nil, Nil, Type.Gen(0));

    Assert.assertEq(
        expected = false,
        suRunSubsume(suEmptyConstraintEnv(), left, right)
    )
}


// classEnv: { Ord : Eq }
// `forall a. Eq a => a ≤ forall b. Ord b => b`
@Test
def subsumeUsesRightContextAndSuperclassEntailment(): Unit \ Assert = {
    let constraintEnv = ConstrEnv.ConstrEnv(
        Map.empty(),
        Map.singleton(
            "Ord",
            Class.Class("Eq" :: Nil, Nil)
        )
    );

    let left = suMkScheme(
        Kind.Star :: Nil,
        suMkGivenClass("Eq", Type.Gen(0)) :: Nil,
        Type.Gen(0)
    );
    let right = suMkScheme(
        Kind.Star :: Nil,
        suMkGivenClass("Ord", Type.Gen(0)) :: Nil,
        Type.Gen(0)
    );

    Assert.assertEq(
        expected = true,
        suRunSubsume(constraintEnv, left, right)
    )
}


// constraintEnv: { Elem a = a }
// `Elem Int32 ≤ Int32`
@Test
def subsumeReducesAssociatedTypesWhileCheckingTypeEquality(): Unit \ Assert = {
    let a = Tyvar.Tyvar("a", Kind.Star);
    let int32 = Type.int32();
    let genericAssoc = Tyassoc.Tyassoc("Elem", Type.Var(a), Kind.Star);
    let specificAssoc = Tyassoc.Tyassoc("Elem", int32, Kind.Star);

    let constraintEnv = ConstrEnv.ConstrEnv(
        Map.singleton(
            "Elem",
            EqConstr.EqConstr(Type.Assoc(genericAssoc), Type.Var(a)) :: Nil
        ),
        Map.empty()
    );

    let left = Scheme.newUnqual(Type.Assoc(specificAssoc));
    let right = Scheme.newUnqual(int32);

    Assert.assertEq(
        expected = true,
        suRunSubsume(constraintEnv, left, right)
    )
}
