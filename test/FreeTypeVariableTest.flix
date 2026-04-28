// `x -> [x]`
@Test
def freeTypeVariablesOfVariable(): Unit \ Assert = {
    let x = TypeVariable.TypeVariable(Id.Id("x"), Kind.Star);
    let ty = Type.Variable(x);

    Assert.assertEq(expected = x :: Nil, ty |> FreeTypeVariable.freeTypeVariables)
}

// `x y -> [x, y]`
@Test
def freeTypeVariablesOfTypeApplication(): Unit \ Assert = {
    let x = TypeVariable.TypeVariable(Id.Id("x"), Kind.Star);
    let y = TypeVariable.TypeVariable(Id.Id("y"), Kind.Star);
    let ty = Type.Application(
        TypeApplication.TypeApplication(
            Type.Variable(x),
            Type.Variable(y)
        )
    );

    Assert.assertEq(expected = x :: y :: Nil, ty |> FreeTypeVariable.freeTypeVariables)
}

// `(x + ~y) -> [x, y]`
@Test
def freeTypeVariablesOfSetFormula(): Unit \ Assert = {
    let x = TypeVariable.TypeVariable(Id.Id("x"), Kind.Eff);
    let y = TypeVariable.TypeVariable(Id.Id("y"), Kind.Eff);
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
