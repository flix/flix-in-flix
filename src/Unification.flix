pub def unify(e: ConstrEnv, l: Type, r: Type): Option[(List[EqConstr], Subst)] =
    if (equiv(l, r))
        Some((Nil, Map.empty()))
    else
        unifyNoEq(e, l, r)
def unifyNoEq(e: ConstrEnv, l: Type, r: Type): Option[(List[EqConstr], Subst)] =
    match (l, r) {
        case (Type.Assoc(a), _) => Option.map(
            s -> (s, Map.empty()),
            reduceUnifyAssoc(e, a, r)
        )
        case (_, Type.Assoc(a)) => Option.map(
            eqs -> (eqs, Map.empty()),
            reduceUnifyAssoc(e, a, l)
        )
        case (Type.Var(v), x) if not Set.memberOf(v, FreeVars.fvs(x)) => Option.map(sub -> (Nil, sub), bindVar(v, r))
        case (x, Type.Var(v)) if not Set.memberOf(v, FreeVars.fvs(x)) => Option.map(sub -> (Nil, sub), bindVar(v, l))
        case _ if kindOf(l) == Kind.Eff and kindOf(r) == Kind.Eff =>
            Option.map(s -> (Nil, s), boolUnify(l, r))
        case (Type.Ap(lF, lA), Type.Ap(rF, rA)) => Some(
            (
                (lF, rF) :: (lA, rA) :: Nil,
                Map.empty()
            )
        )
        case _ => None
    }
def reduceUnifyAssoc(e: ConstrEnv, a: Tyassoc, t: Type): Option[List[EqConstr]] =
    forM (redAm <- reduce(e, Type.Assoc(a)))
        yield (redAm, t) :: Nil
def bindVar(tvar: Tyvar, ty: Type): Option[Subst] =
    if (kindOf(Type.Var(tvar)) != kindOf(ty))
        None
    else
        Some(Map.singleton(tvar, ty))
// used in overlapping instance checking.
def mgu(l: Type, r: Type): Option[Subst] = match (l, r) {
    case (Type.Var(v), t) => bindVar(v, t)
    case (t, Type.Var(v)) => bindVar(v, t)
    case (Type.Ap(lF, lA), Type.Ap(rF, rA)) =>
        forM (
            fSub <- mgu(lF, rF);
            aSub <- mgu(Substable.apply(fSub, lA), Substable.apply(fSub, rA))
        ) yield compose(aSub, fSub)
    case (Type.Con(lc), Type.Con(rc)) if lc == rc => Some(Map.empty())
    case _ => None
}
