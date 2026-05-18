pub type alias Handler = (Id, Expr)

pub enum Expr {
    case Var(Id),
    case Lit(Type),
    case Ap(Expr, Expr),
    case Lam(Id, Expr),
    case Do(Id),
    case IfElse(Expr, Expr, Expr),
    case Semi(Expr, Expr),
    
    // represent the `run <e> with <e>` constructor
    // where
    // - Expr is the body of the `run` with effectful computation
    // - Id is the effect being handled
    // - Nel[Handler] is the list of handlers for each operation of the effect
    case RunWith(Expr, Id, Nel[Handler])
}

pub def infer(assumps: Assumps, expr: Expr): (Type, Type) \ Fresh + Collect 
    = match expr {
        case Expr.Var(x) => inferVar(assumps, x)
        case Expr.Lit(x) => (x, efEmpty())
        case Expr.Ap(fun, arg) => inferAp(assumps, fun, arg) 
        case Expr.Do(ef) => inferDo(ef)
        case Expr.Lam(x, e) => inferLam(assumps, x, e)
        case Expr.IfElse(c, t, f) => inferIfElse(assumps, c, t, f)
        case Expr.Semi(e1, e2) => inferSemi(assumps, e1, e2)
        case Expr.RunWith(e, ef, hs) => inferRunWith(assumps, e, ef, hs)
    }

def inferVar(assumps: Assumps, x: Id): (Type, Type) \ Fresh + Collect = 
    // In case of variable not found, should we:
    // - Panic? since we don't want to concern with error handling, it will
    // be easier to just panic and we don't need to clutter the code with 
    // error handling logic?
    // - Leave it like this
    // - Build an error handling mechanism.
    match Map.get(x, assumps) {
        case Some(sch) => {
            let Qual.Qual(context, ty) = freshInst(sch);
            foreach (c <- context) Collect.collect(c);
            (ty, efEmpty())
        }
        case None => (
            Type.Var(Fresh.freshVar(Kind.Star)),
            Type.Var(Fresh.freshVar(Kind.Eff))
        )
    }

def inferAp(assums: Assumps, f: Expr, a: Expr): (Type, Type) \ Fresh + Collect = 
    let (funTy, funE) = infer(assums, f);
    let (argTy, argE) = infer(assums, a);

    let freshE = Type.Var(Fresh.freshVar(Kind.Eff));
    let freshR = Type.Var(Fresh.freshVar(Kind.Star));

    Collect.collect(Constr.Eq((funTy, mkArrow(argTy, freshE, freshR))));

    (freshR, mkUnion(argE, mkUnion(funE, freshE)))

def inferLam(assums: Assumps, x: Id, e: Expr): (Type, Type) \ Fresh + Collect = 
    let newVar = Fresh.freshVar(Kind.Star);
    let freshVarScheme = mkScheme(Type.Var(newVar));
    let newAssumps = Map.insert(x, freshVarScheme, assums);
    let (bodyTy, bodyEff) = infer(newAssumps, e);

    (mkArrow(Type.Var(newVar), bodyEff, bodyTy), efEmpty())


def inferIfElse(
    assums: Assumps, c: Expr, t: Expr, f: Expr
): (Type, Type) \ Fresh + Collect = 
    let (cTy, cEff) = infer(assums, c);
    let (tTy, tEff) = infer(assums, t);
    let (fTy, fEff) = infer(assums, f);

    Collect.collect(Constr.Eq((cTy, tBool())));
    Collect.collect(Constr.Eq((tTy, fTy)));

    (tTy, mkUnion(cEff, mkUnion(tEff, fEff)))

def inferSemi(
    assums: Assumps, e1: Expr, e2: Expr
): (Type, Type) \ Fresh + Collect =
    let (e1Ty, e1Eff) = infer(assums, e1);
    let (e2Ty, e2Eff) = infer(assums, e2);

    Collect.collect(Constr.Eq((e1Ty, tUnit())));

    (e2Ty, mkUnion(e1Eff, e2Eff))

def inferHandlers(
    assums: Assumps, hs: Nel[Handler], kTy: Type, eTy: Type
): Nel[Type] \ Fresh + Collect =  {
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
    assums: Assumps, e: Expr, ef: Id, hs: Nel[Handler]
): (Type, Type) \ Fresh + Collect = {
    let (eTy, eEff) = infer(assums, e);
    let kEf = Type.Var(Fresh.freshVar(Kind.Eff));
    let kTy = mkArrow(tUnit(), kEf, eTy);
    let hEffs = inferHandlers(assums, hs, kTy, eTy);
    let excluded = mkExclusion(eEff, efConstant(ef));
    let runWithEff = Nel.foldLeft(
        (acc, hEff) -> mkUnion(acc, hEff),
        excluded,
        hEffs
    );
    Collect.collect(Constr.Eq((kEf, runWithEff)));
    (eTy, runWithEff)
}

def inferDo(ef: Id): (Type, Type) = (tUnit(), efConstant(ef))
