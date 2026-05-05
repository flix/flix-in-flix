// x & y unifies T
@Test
pub def booleanXandYUnifyWithTrue(): Unit \ Assert = {
    let x = Type.Var(Tyvar.Tyvar("x", Kind.Eff));
    let y = Type.Var(Tyvar.Tyvar("y", Kind.Eff));
    let f = mkIntersect(x, y);

    Assert.assertEq(
        expected = false,
        boolUnify(f, efUni()) |> Option.isEmpty
    )
}

// x & y unifies F
@Test
pub def booleanXandYUnifyWithFalse(): Unit \ Assert = {
    let x = Type.Var(Tyvar.Tyvar("x", Kind.Eff));
    let y = Type.Var(Tyvar.Tyvar("y", Kind.Eff));
    let f = mkIntersect(x, y);

    Assert.assertEq(
        expected = false,
        boolUnify(f, efEmpty()) |> Option.isEmpty
    )
}

// T does not unify F
@Test
pub def trueDoesNotUnifyWithFalse(): Unit \ Assert = {
    Assert.assertEq(
        expected = true,
        boolUnify(efUni(), efEmpty()) |> Option.isEmpty
    )
}

// x does not unify ~x
@Test
pub def complementDoesNotUnifyWithOriginal(): Unit \ Assert = {
    let x = Type.Var(Tyvar.Tyvar("x", Kind.Eff));
    let f = mkCompl(x);

    Assert.assertEq(
        expected = true,
        boolUnify(f, x) |> Option.isEmpty
    )
}

// y + ~(x & z) does not unify with x & (~y & z)
@Test
pub def threeVariablesDoesNotUnify(): Unit \ Assert = {
    let x = Type.Var(Tyvar.Tyvar("x", Kind.Eff));
    let y = Type.Var(Tyvar.Tyvar("y", Kind.Eff));
    let z = Type.Var(Tyvar.Tyvar("z", Kind.Eff));

    let f1 = mkUnion(y, mkCompl(mkIntersect(x, z)));
    let f2 = mkIntersect(x, mkIntersect(mkCompl(y), z));

    Assert.assertEq(
        expected = true,
        boolUnify(f1, f2) |> Option.isEmpty
    )
}

// a & b unify c & d
pub def fourVariablesUnify(): Unit \ Assert = {
    let a = Type.Var(Tyvar.Tyvar("a", Kind.Eff));
    let b = Type.Var(Tyvar.Tyvar("b", Kind.Eff));
    let c = Type.Var(Tyvar.Tyvar("c", Kind.Eff));
    let d = Type.Var(Tyvar.Tyvar("d", Kind.Eff));

    let f1 = mkIntersect(a, b);
    let f2 = mkIntersect(c, d);

    Assert.assertEq(
        expected = false,
        boolUnify(f1, f2) |> Option.isEmpty
    )
}
