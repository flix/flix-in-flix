pub def matchTy(l: Type, r: Type): Option[Subst] = match (l, r) {
    case (Type.Ap(lhsFn, lhsArg), Type.Ap(rhsFn, rhsArg)) =>
        forM (
            fnSub <- matchTy(lhsFn, rhsFn);
            argSub <- matchTy(lhsArg, rhsArg);
            sub <- merge(fnSub, argSub)
        ) yield sub
    case (Type.Var(tvar), _) => {
        if (kindOf(Type.Var(tvar)) != kindOf(r))
            None
        else
            Some(Map.singleton(tvar, r))
    }
    case (Type.Con(lc), Type.Con(rc)) if lc == rc => Some(Map.empty())
    case (
        Type.Assoc(Tyassoc.Tyassoc(lid, larg, _)),
        Type.Assoc(Tyassoc.Tyassoc(rid, rarg, _))
    ) if rid == lid => matchTy(larg, rarg)
    case _ if kindOf(l) == Kind.Eff and kindOf(r) == Kind.Eff => boolMatch(l, r),
    case _ => None
}
