def sve(f: Type, vars: List[Tyvar]): Option[Subst] = 
    if (not isSat(f)) Some(Subst.empty()) else match vars {
        case Nil => None case x :: xs => {
            let l = Substable.apply(Subst.singleton(x, efEmpty()), f);
            let r = Substable.apply(Subst.singleton(x, efUni()), f);
            let lr = mkIntersect(l, r);

            forM (sub <- sve(lr, xs)) yield {
                let newH = mkUnion(
                    Substable.apply(sub, l),
                    mkIntersect(
                        Type.Var(x), 
                        mkCompl(Substable.apply(sub, r))
                    )
                );

                Map.union(sub, Subst.singleton(x, newH))
            }
        }
    }

def isSat(f: Type): Bool = {
    evaluteAll(f, Set.toList(boolVars(f)), Set.empty())
}

def evaluteAll(f: Type, vars: List[Type], trueVars: Set[Type]): Bool = {
    match vars {
        case Nil => evaluate(f, trueVars)
        case x :: xs => 
            evaluteAll(f, xs, Set.union(trueVars, Set.singleton(x))) 
            or evaluteAll(f, xs, trueVars)
    }
}

def evaluate(f: Type, trueVars: Set[Type]): Bool =  {
    if (f == efEmpty()) false
    else if (f == efUni()) true
    else if (Set.memberOf(f, trueVars)) true
    else match f {
        case Type.Ap(f1, f2) => {
            // we handle two cases: complement and binary ops
            if (f1 == efCompl()) not evaluate(f2, trueVars)
            else match f1 {
                // must be in the form of `ap(ap(binOp arg1) arg2)`
                case Type.Ap(binOp, arg1) => {
                    let lBool = evaluate(arg1, trueVars);
                    let rBool = evaluate(f2, trueVars);

                    if (binOp == efUnion()) lBool or rBool
                    else if (binOp == efIntersect()) lBool and rBool
                    else if (binOp == efXor()) lBool != rBool
                    else bug!("Expected a binary operator, but found: ${binOp}")
                }
                case _ => bug!("Expected a binary operator, but found: ${f1}")
            }
        }
        case _ => false
    }
}

def boolVars(t: Type): Set[Type] = match t {
    case Type.Ap(f, x) => Set.union(boolVars(f), boolVars(x))
    case Type.Con(_) if (t == efEmpty() or t == efUni()) 
        => Set.empty()
    case Type.Gen(_) => bug!("Gen shouldn't be present in boolUnify")
    case _ => Set.singleton(t)
}

pub def boolMatch(t1: Type, t2: Type): Option[Subst] = 
    sve(mkXor(t1, t2), Set.toList(FreeVars.fvs(t1)))

pub def boolUnify(f1: Type, f2: Type): Option[Subst] = {
    let eqType = mkXor(f1 ,f2);
    sve(eqType, Set.toList(FreeVars.fvs(eqType)))
}

def boolFormEq(f1: Type, f2: Type): Bool = not (isSat(mkXor(f1 ,f2)))

// REMARK: Is this necessary?
pub def equiv(t1: Type, t2: Type): Bool = match (t1, t2) {
    case (Type.Var(v1), Type.Var(v2)) if v1 == v2 => true
    case (Type.Ap(f1, x1), Type.Ap(f2, x2)) if equiv(f1, f2) and equiv(x1, x2) 
        => true
    case (Type.Con(c1), Type.Con(c2)) if c1 == c2 => true
    case (
        Type.Assoc(Tyassoc.Tyassoc(lid, larg, _)), 
        Type.Assoc(Tyassoc.Tyassoc(rid, rarg, _))
    ) if lid == rid => equiv(larg, rarg)
    case (Type.Gen(a), Type.Gen(b)) if a == b => true
    case _ if kindOf(t1) == Kind.Eff and kindOf(t2) == Kind.Eff 
        => boolFormEq(t1, t2)
    case _ => false
}
