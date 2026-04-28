// `x -> [x]`
@Test
def freeTypeVariablesOfVariable(): Unit \ Assert = {
    let x = Tyvar.Tyvar(Id.Id("x"), Kind.Star);
    let ty = Type.Var(x);

    Assert.assertEq(expected = x :: Nil, ty |> FreeTypeVariable.freeTypeVariables)
}

// `x y -> [x, y]`
@Test
def freeTypeVariablesOfTypeApplication(): Unit \ Assert = {
    let x = Tyvar.Tyvar(Id.Id("x"), Kind.Star);
    let y = Tyvar.Tyvar(Id.Id("y"), Kind.Star);
    let ty = Type.Ap(Type.Var(x), Type.Var(y));

    Assert.assertEq(expected = x :: y :: Nil, ty |> FreeTypeVariable.freeTypeVariables)
}

// `(x + ~y) -> [x, y]`
@Test
def freeTypeVariablesOfSetFormula(): Unit \ Assert = {
    let x = Tyvar.Tyvar(Id.Id("x"), Kind.Eff);
    let y = Tyvar.Tyvar(Id.Id("y"), Kind.Eff);
    let setFormula = SetFormula.Binary(
        BinarySetFormula.BinarySetFormula(
            SetFormula.Variable(x),
            SetBinaryOp.Union,
            SetFormula.Complement(SetFormula.Variable(y))
        )
    );
    let ty = Type.SetFormula(setFormula);

    Assert.assertEq(expected = x :: y :: Nil, ty |> FreeTypeVariable.freeTypeVariables)
}
