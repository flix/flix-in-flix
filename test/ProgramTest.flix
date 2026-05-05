use Assert.assertEq

def prEmptyConstraintEnv(): ConstrEnv =
    ConstrEnv.empty()


def prDecl(id: Id, sch: Scheme, expr: Expr): TopLevelDecl =
    (id, sch, expr)


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
            :: ("provider", Constr.Eq(tBool(), tInt32()) :: Nil)
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
        expected = ("main", Constr.Eq(efIo(), efEmpty()) :: Nil) :: Nil,
        Fresh.withFresh(_ -> typeCheckProgram(prEmptyConstraintEnv(), decls))
    )
}
