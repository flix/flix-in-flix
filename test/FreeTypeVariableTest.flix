@Test
def freeTypeVariablesOfVariable(): Unit \ Assert = {
    let x = TypeVariable.TypeVariable(Id.Id("x"), Kind.TypeStar);
    let ty = Type.Variable(x);

    Assert.assertEq(expected = x :: Nil, ty |> FreeTypeVariable.freeTypeVariables)
}

@Test
def freeTypeVariablesOfTypeApplication(): Unit \ Assert = {
    let x = TypeVariable.TypeVariable(Id.Id("x"), Kind.TypeStar);
    let y = TypeVariable.TypeVariable(Id.Id("y"), Kind.TypeStar);
    let ty = Type.Application(
        TypeApplication.TypeApplication(
            Type.Variable(x),
            Type.Variable(y)
        )
    );

    Assert.assertEq(expected = x :: y :: Nil, ty |> FreeTypeVariable.freeTypeVariables)
}

@Test
def freeTypeVariablesOfSetFormula(): Unit \ Assert = {
    let x = TypeVariable.TypeVariable(Id.Id("x"), Kind.EffectStar);
    let y = TypeVariable.TypeVariable(Id.Id("y"), Kind.EffectStar);
    let setFormula = SetFormula.Binary(
        BinarySetFormula.BinarySetFormula(
            SetFormula.TypeVariable(x),
            SetBinaryOp.Union,
            SetFormula.Complement(SetFormula.TypeVariable(y))
        )
    );
    let ty = Type.SetFormula(setFormula);

    Assert.assertEq(expected = x :: y :: Nil, ty |> FreeTypeVariable.freeTypeVariables)
}
