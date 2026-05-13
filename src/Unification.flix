pub def unify(e: ConstrEnv, l: Type, r: Type): Option[(List[EqConstr], Subst)] =
    if (equiv(l, r)) Some((Nil, Subst.empty()))
    else unifyNoEq(e, l, r)
def unifyNoEq(e: ConstrEnv, l: Type, r: Type): Option[(List[EqConstr], Subst)] = 
    match (l, r) {
        case (Type.Assoc(a), _) => Option.map(
            s -> (s, Subst.empty()), 
            reduceUnifyAssoc(e, a, r)
        )
        case (_, Type.Assoc(a)) => Option.map(
            eqs -> (eqs, Subst.empty()), 
            reduceUnifyAssoc(e, a, l)
        )
        case (Type.Var(v), x) if not Set.memberOf(v, FreeVars.fvs(x)) 
            => Option.map(sub -> (Nil, sub), bindVar(v, r))
        case (x, Type.Var(v)) if not Set.memberOf(v, FreeVars.fvs(x)) 
            => Option.map(sub -> (Nil, sub), bindVar(v, l))
        case _ if kindOf(l) == Kind.Eff and kindOf(r) == Kind.Eff => 
            Option.map(s -> (Nil, s), boolUnify(l, r))
        case (Type.Ap(lF, lA), Type.Ap(rF, rA)) => Some((
            (lF, rF) :: (lA, rA) :: Nil, Subst.empty()
        ))
        case _ => None
    }
def reduceUnifyAssoc(e: ConstrEnv, a: Tyassoc, t: Type): Option[List[EqConstr]] 
    = forM(redAm <- reduce(e, Type.Assoc(a))) yield (redAm, t) :: Nil
def bindVar(tvar: Tyvar, ty: Type): Option[Subst] = 
    if (kindOf(Type.Var(tvar)) != kindOf(ty)) None
    else Some(Subst.singleton(tvar, ty))
