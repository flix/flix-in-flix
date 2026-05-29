pub type alias Handler = (Id, Expr)

pub enum Expr {
    case Var(Id, Type)
    case Lit(Type)
    case Ap(Expr, Expr, Type, Type) // Type.error?
    case Lam(Id, Type, Expr)
    case Do(Id)
    case IfElse(Expr, Expr, Expr)
    case Semi(Expr, Expr)
    case RunWith(Expr, Id, Nel[Handler])
}

pub def zonk(expr: Expr, subst: Subst): Expr = match expr {
    case Expr.Var(id, ty) => Expr.Var(id, Substable.apply(subst, ty))
    case Expr.Lit(ty) => Expr.Lit(ty)
    case Expr.Ap(fun, arg, apTy, apEf) => Expr.Ap(
        zonk(fun, subst),
        zonk(arg, subst),
        Substable.apply(subst, apTy),
        Substable.apply(subst, apEf)
    )

    case Expr.Lam(id, paramTy, body) =>
        Expr.Lam(id, Substable.apply(subst, paramTy), zonk(body, subst))
    case Expr.Do(ef) => Expr.Do(ef)
    case Expr.IfElse(c, t, f) =>
        Expr.IfElse(zonk(c, subst), zonk(t, subst), zonk(f, subst))
    case Expr.Semi(e1, e2) => Expr.Semi(zonk(e1, subst), zonk(e2, subst))
    case Expr.RunWith(e, ef, hs) => Expr.RunWith(
        zonk(e, subst),
        ef,
        Nel.map(h -> (fst(h), zonk(snd(h), subst)), hs)
    )
}

pub def typeOf(expr: Expr): (Type, Type) = match expr {
    case Expr.Var(_, ty) => (ty, efEmpty())
    case Expr.Lit(ty) => (ty, efEmpty())
    case Expr.Do(ef) => (tUnit(), efConstant(ef))
    case Expr.Ap(_, _, apTy, apEf) => (apTy, apEf)
    case Expr.Lam(_, paramTy, body) =>
        let (bodyTy, bodyEf) = typeOf(body);
        (mkArrow(paramTy, bodyEf, bodyTy), efEmpty())
    case Expr.Semi(e1, e2) => {
        let (_, e1Ef) = typeOf(e1);
        let (e2Ty, e2Ef) = typeOf(e2);
        (e2Ty, mkUnion(e1Ef, e2Ef))
    }
    case Expr.IfElse(c, t, f) => {
        let (_, cEf) = typeOf(c);
        let (tTy, tEf) = typeOf(t);
        let (_, fEf) = typeOf(f);
        (tTy, mkUnion(cEf, mkUnion(tEf, fEf)))
    }
    case Expr.RunWith(e, ef, hs) => {
        let (eTy, eEf) = typeOf(e);
        let excluded = mkExclusion(eEf, efConstant(ef));
        let finalEf = Nel.foldLeft(
            (acc, h) -> mkUnion(acc, snd(typeOf(snd(h)))),
            excluded,
            hs
        );

        (eTy, finalEf)
    }
}

pub def infer(assumps: Assumps, expr: Expr): (Type, Type) \ Fresh + Collect + Report = match expr {
    case Expr.Var(x, iVarTy)           => inferVar(assumps, x, iVarTy)
    case Expr.Lit(x)                   => (x, efEmpty())
    case Expr.Ap(fun, arg, apTy, apEf) => inferAp(assumps, fun, arg, apTy, apEf)
    case Expr.Do(ef)                   => inferDo(ef)
    case Expr.Lam(x, paramT, e)        => inferLam(assumps, x, paramT, e)
    case Expr.IfElse(c, t, f)          => inferIfElse(assumps, c, t, f)
    case Expr.Semi(e1, e2)             => inferSemi(assumps, e1, e2)
    case Expr.RunWith(e, ef, hs)       => inferRunWith(assumps, e, ef, hs)
}

def inferVar(assumps: Assumps, x: Id, varT: Type): (Type, Type) \ Fresh + Collect + Report =
    match Map.get(x, assumps) {
        case Some(sch) => {
            let Qual.Qual(context, ty) = freshInst(sch);
            foreach (c <- context)
                Collect.collect(c);
            Collect.collect(Constr.Eq((ty, varT)));
            (ty, efEmpty())
        }
        case None =>
            Report.report("Unbound variable: " + x);
            (
                Type.Var(Fresh.freshVar(Kind.Star)),
                Type.Var(Fresh.freshVar(Kind.Eff))
            )
    }

def inferAp(assums: Assumps, f: Expr, a: Expr, apTy: Type, apEf: Type): (Type, Type) \ Fresh + Collect + Report =
    let (funTy, funE) = infer(assums, f);
    let (argTy, argE) = infer(assums, a);

    let freshE = Type.Var(Fresh.freshVar(Kind.Eff));

    Collect.collect(Constr.Eq((funTy, mkArrow(argTy, freshE, apTy))));
    Collect.collect(Constr.Eq((apEf, mkUnion(mkUnion(freshE, funE), argE))));

    (apTy, mkUnion(mkUnion(freshE, funE), argE))

def inferLam(assums: Assumps, x: Id, paramT: Type, e: Expr): (Type, Type) \ Fresh + Collect + Report =
    let freshVarScheme = mkScheme(paramT);
    let newAssumps = Map.insert(x, freshVarScheme, assums);
    let (bodyTy, bodyEff) = infer(newAssumps, e);

    (mkArrow(paramT, bodyEff, bodyTy), efEmpty())

def inferIfElse(
    assums: Assumps,
    c: Expr,
    t: Expr,
    f: Expr
): (Type, Type) \ Fresh + Collect + Report =
    let (cTy, cEff) = infer(assums, c);
    let (tTy, tEff) = infer(assums, t);
    let (fTy, fEff) = infer(assums, f);

    Collect.collect(Constr.Eq((cTy, tBool())));
    Collect.collect(Constr.Eq((tTy, fTy)));

    (tTy, mkUnion(cEff, mkUnion(tEff, fEff)))

def inferSemi(
    assums: Assumps,
    e1: Expr,
    e2: Expr
): (Type, Type) \ Fresh + Collect + Report =
    let (e1Ty, e1Eff) = infer(assums, e1);
    let (e2Ty, e2Eff) = infer(assums, e2);

    Collect.collect(Constr.Eq((e1Ty, tUnit())));

    (e2Ty, mkUnion(e1Eff, e2Eff))

def inferHandlers(
    assums: Assumps,
    hs: Nel[Handler],
    kTy: Type,
    eTy: Type
): Nel[Type] \ Fresh + Collect + Report = {
    Nel.map(
        x -> {
            let (kId, h) = x;
            let (ht, he) = infer(Map.insert(kId, mkScheme(kTy), assums), h);
            Collect.collect(Constr.Eq((ht, eTy)));
            he
        },
        hs
    )
}

def inferRunWith(
    assums: Assumps,
    e: Expr,
    ef: Id,
    hs: Nel[Handler]
): (Type, Type) \ Fresh + Collect + Report = {
    let (eTy, eEff) = infer(assums, e);
    let inferRwEff = Type.Var(Fresh.freshVar(Kind.Eff));
    let kTy = mkArrow(tUnit(), inferRwEff, eTy);
    let hEffs = inferHandlers(assums, hs, kTy, eTy);
    let excluded = mkExclusion(eEff, efConstant(ef));
    let runWithEff = Nel.foldLeft(
        (acc, hEff) -> mkUnion(acc, hEff),
        excluded,
        hEffs
    );

    Collect.collect(Constr.Eq((inferRwEff, runWithEff)));

    (eTy, runWithEff)
}

def inferDo(ef: Id): (Type, Type) = (tUnit(), efConstant(ef))
