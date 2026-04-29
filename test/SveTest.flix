// x & y unifies T
pub def booleanXandYUnifyWithTrue(): Unit \ Assert = {
    let x = Type.Var(Tyvar.Tyvar("x", Kind.Eff));
    let y = Type.Var(Tyvar.Tyvar("y", Kind.Eff));
    let f = Type.mkIntersect(x, y);

    Assert.assertEq(
        expected = false,
        boolUnify(f, Type.efUniverse()) |> Option.isEmpty
    )
}

// x & y unifies F
pub def booleanXandYUnifyWithFalse(): Unit \ Assert = {
    let x = Type.Var(Tyvar.Tyvar("x", Kind.Eff));
    let y = Type.Var(Tyvar.Tyvar("y", Kind.Eff));
    let f = Type.mkIntersect(x, y);

    Assert.assertEq(
        expected = false,
        boolUnify(f, Type.efEmpty()) |> Option.isEmpty
    )
}