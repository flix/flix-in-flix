pub enum Expr {
    case Var(Id),
    case Lit(Type),
    case Ap(Expr, Expr),
    case Lam(Id, Expr),
    case Do(Id),
    case IfElse(Expr, Expr, Expr),
    case RunWith(Expr, Id)
}

mod Expr {
    pub def infer(assumps: Assumps, expr: Expr): (Type, Type) \ Fresh + Collect 
    = match expr {
        case Expr.Var(x) => inferVar(assumps, x)
        case Expr.Lit(x) => (x, Type.efEmpty())
        case Expr.Ap(fun, arg) => inferAp(assumps, fun, arg) 
        case Do(ef) => inferDo(ef)
        case Expr.Lam(x, e) => inferLam(assumps, x, e)
        case IfElse(c, t, f) => inferIfElse(assumps, c, t, f)
        case RunWith(e, ef) => inferRunWith(assumps, e, ef)
    }

    def inferVar(assumps: Assumps, x: Id): (Type, Type) \ Fresh + Collect = 
        match Map.get(x, assumps) {
            case Some(sch) => {
                let qual = Fresh.freshInst(sch);
                foreach (c <- Qual.context(qual)) Collect.collect(c);
                (Qual.head(qual), Type.efEmpty())
            }
            case None => (
                Type.Var(Fresh.freshVar(Kind.Star)),
                Type.Var(Fresh.freshVar(Kind.Eff))
            )
        }

    def inferAp(
        assumps: Assumps, fun: Expr, arg: Expr
    ): (Type, Type) \ Fresh + Collect = 
        let (funTy, funE) = infer(assumps, fun);
        let (argTy, argE) = infer(assumps, arg);

        let freshE = Type.Var(Fresh.freshVar(Kind.Eff));
        let freshR = Type.Var(Fresh.freshVar(Kind.Star));

        Collect.collect(Constr.Eq(funTy, Type.mkArrow(argTy, freshE, freshR)));

        (freshR, Type.mkUnion(argE, Type.mkUnion(funE, freshE)))

    def inferLam(
        assumps: Assumps, x: Id, e: Expr
    ): (Type, Type) \ Fresh + Collect =  {
        let newVar = Fresh.freshVar(Kind.Star);
        let freshVarScheme = Scheme.newUnqual(Type.Var(newVar));
        let newAssumps = Map.insert(x, freshVarScheme, assumps);
        let (bodyTy, bodyEff) = infer(newAssumps, e);

        (Type.mkArrow(Type.Var(newVar), bodyEff, bodyTy), Type.efEmpty())
    }

    def inferIfElse(
        assums: Assumps, c: Expr, t: Expr, f: Expr
    ): (Type, Type) \ Fresh + Collect = {
        let (cTy, cEff) = infer(assums, c);
        let (tTy, tEff) = infer(assums, t);
        let (fTy, fEff) = infer(assums, f);

        Collect.collect(Constr.Eq(cTy, Type.bool()));
        Collect.collect(Constr.Eq(tTy, fTy));

        (tTy, Type.mkUnion(cEff, Type.mkUnion(tEff, fEff)))
    }

    def inferRunWith(
        assums: Assumps, e: Expr, ef: Id
    ): (Type, Type) \ Fresh + Collect = {
        let (eTy, eEff) = infer(assums, e);
        (eTy, Type.mkExclusion(eEff, Type.efConstant(ef)))
    }

    def inferDo(ef: Id): (Type, Type) = (Type.unit(), Type.efConstant(ef))
}

def genWithVars(gv: Set[Tyvar], qual: Qual[Type]): Scheme[Type] =
    let gvl = Set.toList(gv);
    let kinds = List.map(Kinded.kind, gvl);
    let subst = List.toMap(List.map(
        x -> (snd(x), Type.Gen(fst(x))), 
        List.zipWithIndex(gvl)
    ));
    let schQual = Substable.apply(subst, qual);

    Scheme.Scheme(kinds, schQual)
