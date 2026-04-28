// `x -> [x]`
@Test
def freeTypeVariablesOfVariable(): Unit \ Assert = {
    let x = Tyvar.Tyvar("x", Kind.Star);
    let ty = Type.Var(x);

    Assert.assertEq(expected = x :: Nil, ty |> FreeVars.fvs)
}

// `x y -> [x, y]`
@Test
def freeTypeVariablesOfTypeApplication(): Unit \ Assert = {
    let x = Tyvar.Tyvar("x", Kind.Star);
    let y = Tyvar.Tyvar("y", Kind.Star);
    let ty = Type.Ap(Type.Var(x), Type.Var(y));

    Assert.assertEq(expected = x :: y :: Nil, ty |> FreeVars.fvs)
}

// `Union x (Compl y) -> [x, y]`
@Test
def freeTypeVariablesOfSetFormula(): Unit \ Assert = {
    let x = Tyvar.Tyvar("x", Kind.Eff);
    let y = Tyvar.Tyvar("y", Kind.Eff);
    let ty = Type.efUnion(Type.Var(x), Type.efCompl(Type.Var(y)));

    Assert.assertEq(expected = x :: y :: Nil, ty |> FreeVars.fvs)
}
