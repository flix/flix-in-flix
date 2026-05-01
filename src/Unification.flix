pub def unifyOneStep(env: ConstrEnv, giv: List[Constr], lhs: Type, rhs: Type): 
    Option[(List[EqConstr], Subst)] =
        if (boolEq(lhs, rhs)) Some((Nil, Subst.empty()))
        else unifyNoEq(env, giv, lhs, rhs)

def unifyNoEq(env: ConstrEnv, giv: List[Constr], lhs: Type, rhs: Type): 
    Option[(List[EqConstr], Subst)] = match (lhs, rhs) {
        case (Type.Ap(lhsFn, lhsArg), Type.Ap(rhsFn, rhsArg)) => Some((
            EqConstr.EqConstr(lhsFn, rhsFn) 
                :: EqConstr.EqConstr(lhsArg, rhsArg) 
                :: Nil,
            Subst.empty()
        ))
        case (Type.Var(tvar), _) 
            => Option.map(sub -> (Nil, sub), bindVar(tvar, rhs))
        case (_, Type.Var(tvar)) 
            => Option.map(sub -> (Nil, sub), bindVar(tvar, lhs))
        case (Type.Assoc(am), _) => Option.map(
            eqs -> (eqs, Subst.empty()), 
            bindAssoc(env, giv, am, rhs)
        )
        case (_, Type.Assoc(am)) => Option.map(
            eqs -> (eqs, Subst.empty()), 
            bindAssoc(env, giv, am, lhs)
        )
        case _ 
            if Kinded.kind(lhs) == Kind.Eff and Kinded.kind(rhs) == Kind.Eff => 
            match boolUnify(lhs, rhs) {
                case Some(sub) => Some((Nil, sub))
                case None => None
            }
        case _ => None
    }

def bindAssoc(env: ConstrEnv, giv: List[Constr], am: Tyassoc, ty: Type): 
    Option[List[EqConstr]] = forM (
        redAm <- reduceTyOne(env, giv, Type.Assoc(am));
        _ <- if (Kinded.kind(redAm) != Kinded.kind(ty)) None
            else Some(())
    ) yield EqConstr.EqConstr(redAm, ty) :: Nil

def bindVar(tvar: Tyvar, ty: Type): Option[Subst] = {
    if (Set.memberOf(tvar, FreeVars.fvs(ty)) 
        or Kinded.kind(tvar) != Kinded.kind(ty)) None
    else Some(Subst.singleton(tvar, ty))
}

def unifyRepeatHelper(
    env: ConstrEnv,
    giv: List[Constr],
    eqs: List[EqConstr],
    curSub: Subst
): (List[EqConstr], Subst) = {
    def findStep(done: List[EqConstr], rest: List[EqConstr]): 
        Option[(List[EqConstr], Subst)] = match rest {
            case Nil => None

            case head :: tail => match unifyOneStep(
                env, giv, EqConstr.left(head), EqConstr.right(head)
            ) {
                case Some((newEqs, sub)) => {
                    let nextEqs = List.map(Substable.apply(sub), done ++ tail);
                    Some((nextEqs ++ newEqs, sub))
                }

                case None => findStep(head :: done, tail)
            }
    };

    match findStep(Nil, eqs) {
        case Some((nextEqs, sub)) 
            => unifyRepeatHelper(env, giv, nextEqs, Subst.compose(sub, curSub))
        case None => (eqs, curSub)
    }
}

pub def unifyRepeat(
    env: ConstrEnv,
    giv: List[Constr],
    eqs: List[EqConstr]
): (List[EqConstr], Subst) = unifyRepeatHelper(env, giv, eqs, Subst.empty())
