def sve(f: Type, vars: List[Tyvar]): Option[Subst] = {
    if (not isSat(f)) Some(Subst.empty())

    else match vars {
        case Nil => None
        case x :: xs => {
            let l = Substable.apply(Subst.singleton(x, Type.efEmpty()), f);
            let r = Substable.apply(Subst.singleton(x, Type.efUniverse()), f);
            let lr = Type.mkIntersect(l, r);

            forM (
                sub <- sve(lr, xs)
            ) yield {
                let newH = Type.mkUnion(
                    Substable.apply(sub, l),
                    Type.mkIntersect(
                        Type.Var(x), 
                        Type.mkCompl(Substable.apply(sub, r))
                    )
                );

                Map.union(sub, Subst.singleton(x, newH))
            }
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
    if (f == Type.efEmpty()) false
    else if (f == Type.efUniverse()) true
    else if (Set.memberOf(f, trueVars)) true
    else match f {
        case Type.Ap(f1, f2) => {
            // we handle two cases: complement and binary ops

            if (f1 == Type.efComplement()) not evaluate(f2, trueVars)

            else match f1 {
                // must be in the form of `ap(ap(binOp arg1) arg2)`
                case Type.Ap(binOp, arg1) => {
                    let lBool = evaluate(arg1, trueVars);
                    let rBool = evaluate(f2, trueVars);

                    if (binOp == Type.efUnion()) lBool or rBool
                    else if (binOp == Type.efIntersect()) lBool and rBool
                    else if (binOp == Type.efXor()) lBool != rBool
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
    case Type.Con(_) => 
        if (t == Type.efEmpty() or t == Type.efUniverse()) Set.empty()
        else Set.singleton(t)
    
    // treat it as an uninterpreted constant
    case Type.Assoc(_) => Set.singleton(t),

    case Type.Gen(_) => bug!("Gen shouldn't be present in boolUnify")
    case Type.Var(_) => Set.singleton(t)
}

pub def boolUnify(f1: Type, f2: Type): Option[Subst] = {
    let eqType = Type.mkXor(f1 ,f2);
    let fvs = Set.toList(FreeVars.fvs(eqType));

    sve(eqType, fvs)
}
