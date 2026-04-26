def mkTypeVar(name: String, kind: Kind): TypeVariable =
    TypeVariable.TypeVariable(Id.Id(name), kind)


def mkTypeCon(name: String, kind: Kind): TypeConstructor =
    TypeConstructor.TypeConstructor(Id.Id(name), kind)


@Test
def matchTypesVariableCreatesSubstitution(): Unit \ Assert = {
    let x = mkTypeVar("x", Kind.TypeStar);
    let int32 = Type.Constructor(mkTypeCon("Int32", Kind.TypeStar));

    Assert.assertEq(
        expected = Ok(Substitution.singleton(x, int32)),
        matchTypes(Type.Variable(x), int32)
    )
}


@Test
def matchTypesVariableRejectsKindMismatch(): Unit \ Assert = {
    let x = mkTypeVar("x", Kind.TypeStar);
    let emptySet = Type.SetFormula(SetFormula.Empty);

    Assert.assertEq(
        expected = Err(MatchError.KindMismatch),
        matchTypes(Type.Variable(x), emptySet)
    )
}


@Test
def matchTypesApplicationMergesSubstitutions(): Unit \ Assert = {
    let t = Kind.TypeStar;
    let tToT = Kind.Function(FunctionKind.FunctionKind(t, t));
    let f = mkTypeVar("f", tToT);
    let x = mkTypeVar("x", t);
    let unary = Type.Constructor(mkTypeCon("Unary", tToT));
    let int32 = Type.Constructor(mkTypeCon("Int32", t));

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


@Test
def matchTypesApplicationRejectsInconsistentSubstitution(): Unit \ Assert = {
    let t = Kind.TypeStar;
    let pair = Type.Constructor(mkTypeCon(
        "Pair",
        Kind.Function(FunctionKind.FunctionKind(
            t,
            Kind.Function(FunctionKind.FunctionKind(t, t))
        ))
    ));
    let x = mkTypeVar("x", t);
    let int32 = Type.Constructor(mkTypeCon("Int32", t));
    let bool = Type.Constructor(mkTypeCon("Bool", t));

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
        expected = Err(MatchError.KindMismatch),
        matchTypes(left, right)
    )
}


@Test
def matchTypesAssociatedMemberMatchesUnderlyingArgument(): Unit \ Assert = {
    let assocId = Id.Id("Assoc");
    let x = mkTypeVar("x", Kind.TypeStar);
    let int32 = Type.Constructor(mkTypeCon("Int32", Kind.TypeStar));

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
