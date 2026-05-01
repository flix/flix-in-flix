pub def matchTy(l: Type, r: Type): Option[Subst] = match (l, r) {
    case (Type.Ap(lhsFn, lhsArg), Type.Ap(rhsFn, rhsArg)) => forM(
        fnSub <- matchTy(lhsFn, rhsFn);
        argSub <- matchTy(lhsArg, rhsArg);
        sub <- Subst.merge(fnSub, argSub)
    ) yield sub
    case (Type.Var(tvar), _) => {
        if (Kinded.kind(tvar) != Kinded.kind(r)) None 
        else Some(Subst.singleton(tvar, r))
    }
    case (Type.Con(lc), Type.Con(rc)) if lc == rc  => Some(Subst.empty())
    case (Type.Assoc(la), Type.Assoc(ra)) if Tyassoc.id(la) == Tyassoc.id(ra) 
        => matchTy(Tyassoc.ty(la), Tyassoc.ty(ra))
    case _ if Kinded.kind(l) == Kind.Eff and Kinded.kind(r) == Kind.Eff 
        // REMARK: is boolMatch necessary here?
        => boolMatch(l, r),
    case _ => None
}