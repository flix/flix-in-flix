pub enum MatchError with Eq, ToString, Hash, Order {
    case DoesNotMatch,
    case KindMismatch
}

pub def matchTy(lhs: Type, rhs: Type): Result[MatchError, Subst] 
    = match (lhs, rhs) {
        case (Type.Ap(lhsFn, lhsArg), Type.Ap(rhsFn, rhsArg)) => {
            forM (
                fnSub <- matchTy(lhsFn, rhsFn);
                argSub <- matchTy(lhsArg, rhsArg);
                sub <- Option.getWithDefault(
                    Err(MatchError.DoesNotMatch),
                    Option.map(Ok, Subst.merge(fnSub, argSub))
                )
            ) yield sub
        }

        case (Type.Var(tvar), _) => {
            let lhsKind = Kinded.kind(tvar);
            let rhsKind = Kinded.kind(rhs);
            if (lhsKind != rhsKind) Err(MatchError.KindMismatch)
            else Ok(Subst.singleton(tvar, rhs))
        }

        case (Type.Con(lhsCon), Type.Con(rhsCon)) if lhsCon == rhsCon 
            => Ok(Subst.empty())

        case (Type.Assoc(lhsAm), Type.Assoc(rhsAm)) 
            if Tyassoc.id(lhsAm) == Tyassoc.id(rhsAm) 
            => matchTy(Tyassoc.ty(lhsAm), Tyassoc.ty(rhsAm))

        case _ => Err(MatchError.DoesNotMatch)
    }

pub enum UnificationError with Eq, ToString, Hash, Order {
    case OccursCheckFailed
    case KindMismatch
    case NoApplicableRule
}

pub def unifyOneStep(env: ConstrEnv, giv: List[Constr], lhs: Type, rhs: Type): 
    Result[UnificationError, (List[EqConstr], Subst)] =
        if (lhs == rhs) Ok((Nil, Subst.empty()))
        else unifyNoEq(env, giv, lhs, rhs)

def unifyNoEq(env: ConstrEnv, giv: List[Constr], lhs: Type, rhs: Type): 
    Result[UnificationError, (List[EqConstr], Subst)] = match (lhs, rhs) {
        case (Type.Ap(lhsFn, lhsArg), Type.Ap(rhsFn, rhsArg)) => Ok((
            EqConstr.EqConstr(lhsFn, rhsFn) 
                :: EqConstr.EqConstr(lhsArg, rhsArg) 
                :: Nil,
            Subst.empty()
        ))

        case (Type.Var(tvar), _) 
            => Result.map(sub -> (Nil, sub), bindVar(tvar, rhs))
        case (_, Type.Var(tvar)) 
            => Result.map(sub -> (Nil, sub), bindVar(tvar, lhs))
        case (Type.Assoc(am), _) => Result.map(
            eqs -> (eqs, Subst.empty()), 
            bindAssoc(env, giv, am, rhs)
        )
        case (_, Type.Assoc(am)) => Result.map(
            eqs -> (eqs, Subst.empty()), 
            bindAssoc(env, giv, am, lhs)
        )

        case _ => Err(UnificationError.NoApplicableRule)
    }

def bindAssoc(env: ConstrEnv, giv: List[Constr], am: Tyassoc, ty: Type): 
    Result[UnificationError, List[EqConstr]] = forM (
        redAm <- Option.toOk(
            UnificationError.NoApplicableRule,
            reduceTyOne(env, giv, Type.Assoc(am))
        );
        _ <- if (Kinded.kind(redAm) != Kinded.kind(ty))
                Err(UnificationError.KindMismatch)
            else Ok(())
    ) yield EqConstr.EqConstr(redAm, ty) :: Nil

def bindVar(tvar: Tyvar, ty: Type): Result[UnificationError, Subst] = {
    if (List.memberOf(tvar, FreeVars.fvs(ty)))
        Err(UnificationError.OccursCheckFailed)
    else if (Kinded.kind(tvar) != Kinded.kind(ty))
        Err(UnificationError.KindMismatch)
    else
        Ok(Subst.singleton(tvar, ty))
}

def unifyRepeatHelper(
    env: ConstrEnv,
    giv: List[Constr],
    eqs: List[EqConstr],
    curSub: Subst
): (List[EqConstr], Subst) = {
    def findStep(
        done: List[EqConstr],
        rest: List[EqConstr]
    ): Option[(List[EqConstr], Subst)] = match rest {
        case Nil => None

        case head :: tail => {
            match unifyOneStep(
                env, 
                giv,
                EqConstr.left(head), 
                EqConstr.right(head)
            ) {
                case Ok((newEqs, sub)) => {
                    let nextEqs = List.map(
                        eq -> Substable.apply(sub, eq), 
                        done ++ tail
                    );

                    Some((nextEqs ++ newEqs, sub))
                }

                case Err(_) => findStep(head :: done, tail)
            }
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
