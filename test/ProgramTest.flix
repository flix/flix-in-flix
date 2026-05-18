use Assert.assertEq

def prEmptyConstraintEnv(): ConstrEnv =
    emptyConstrEnv()


def prDecl(id: Id, sch: Scheme, expr: Expr): TopLevelDecl =
    (id, sch, expr)


def prMkHandlerBody(effectId: Id, kId: Id): Expr =
    Expr.Semi(
        Expr.Do(effectId),
        Expr.Ap(
            Expr.Var(kId),
            Expr.Lit(tUnit())
        )
    )


// `[] -> []`
@Test
def typeCheckProgramLeavesEmptyProgramEmpty(): Unit \ Assert = {
    Assert.assertEq(
        expected = Nil,
        Fresh.withFresh(_ -> typeCheckProgram(prEmptyConstraintEnv(), Nil))
    )
}


// `x: Int32 = Int32 -> []`
@Test
def typeCheckProgramAcceptsPureMatchingLiteral(): Unit \ Assert = {
    let decls = prDecl(
        "x",
        mkScheme(tInt32()),
        Expr.Lit(tInt32())
    ) :: Nil;

    Assert.assertEq(
        expected = ("x", Nil) :: Nil,
        Fresh.withFresh(_ -> typeCheckProgram(prEmptyConstraintEnv(), decls))
    )
}


// `x: Int32 = x -> []`
@Test
def typeCheckProgramUsesSelfAssumptionDuringInference(): Unit \ Assert = {
    let decls = prDecl(
        "x",
        mkScheme(tInt32()),
        Expr.Var("x")
    ) :: Nil;

    Assert.assertEq(
        expected = ("x", Nil) :: Nil,
        Fresh.withFresh(_ -> typeCheckProgram(prEmptyConstraintEnv(), decls))
    )
}


// `useLater: Int32 = provider, provider: Int32 = Bool -> [[], [Bool ~ Int32]]`
@Test
def typeCheckProgramBuildsInitialAssumptionsFromAllDeclarations(): Unit \ Assert = {
    let decls = prDecl(
        "useLater",
        mkScheme(tInt32()),
        Expr.Var("provider")
    ) :: prDecl(
        "provider",
        mkScheme(tInt32()),
        Expr.Lit(tBool())
    ) :: Nil;

    Assert.assertEq(
        expected = ("useLater", Nil)
            :: ("provider", Constr.Eq((tBool(), tInt32())) :: Nil)
            :: Nil,
        Fresh.withFresh(_ -> typeCheckProgram(prEmptyConstraintEnv(), decls))
    )
}


// `main: Unit = do IO -> [IO ~ {}]`
@Test
def typeCheckProgramReturnsResidualEffectConstraintForImpureDeclaration(): Unit \ Assert = {
    let decls = prDecl(
        "main",
        mkScheme(tUnit()),
        Expr.Do("IO")
    ) :: Nil;

    Assert.assertEq(
        expected = ("main", Constr.Eq((efIo(), efEmpty())) :: Nil) :: Nil,
        Fresh.withFresh(_ -> typeCheckProgram(prEmptyConstraintEnv(), decls))
    )
}


// `test: forall a. a -> Unit \ {B + C} = \x -> run do A with handlers [k1 => do B; k1(()), k2 => do C; k2(())] -> []`
@Test
def typeCheckProgramAcceptsHandledProgramFromTestCase(): Unit \ Assert = {
    let scheme = Scheme.Scheme(
        Kind.Star :: Nil,
        Qual.Qual(
            Nil,
            mkArrow(
                Type.Gen(0),
                mkUnion(efConstant("B"), efConstant("C")),
                tUnit()
            )
        )
    );

    let handlers = Nel.Nel(
        ("k1", prMkHandlerBody("B", "k1")),
        ("k2", prMkHandlerBody("C", "k2")) :: Nil
    );

    let decls = prDecl(
        "test",
        scheme,
        Expr.Lam(
            "x",
            Expr.RunWith(
                Expr.Do("A"),
                "A",
                handlers
            )
        )
    ) :: Nil;

    Assert.assertEq(
        expected = ("test", Nil) :: Nil,
        Fresh.withFresh(_ -> typeCheckProgram(prEmptyConstraintEnv(), decls))
    )
}
