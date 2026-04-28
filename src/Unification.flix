pub enum MatchError with Eq, ToString, Hash, Order {
    case DoesNotMatch,
    case KindMismatch
}


pub def matchTypes(
    left: Type, 
    right: Type
): Result[MatchError, Subst] = match (left, right) {
    case ( 
        Type.Ap(leftFunc, leftArg),
        Type.Ap(rightFunc, rightArg)
    ) => {
        forM (
            funcSubst <- matchTypes(
                leftFunc,
                rightFunc
            );
            argSubst <- matchTypes(
                leftArg,
                rightArg
            );
            mergedSubst <- Subst.merge(funcSubst, argSubst)
                |> Option.map(Ok)
                |> Option.getWithDefault(
                    Err(MatchError.DoesNotMatch)
                )
        ) yield mergedSubst
    }

    case (Type.Var(leftVar), _) => {
        let varKind = leftVar |> Kinded.kind;
        let rightKind = right |> Kinded.kind;

        if (varKind != rightKind) 
            Err(MatchError.KindMismatch)
        else
            Ok(Subst.singleton(leftVar, right))
    }

    case (Type.Con(leftCon), Type.Con(rightCon)) 
        if leftCon == rightCon => Ok(Subst.empty())

    case (Type.Assoc(leftAM), Type.Assoc(rightAM)) 
        if leftAM |> Tyassoc.id == rightAM |> Tyassoc.id => {
            matchTypes(
                leftAM |> Tyassoc.ty, rightAM |> Tyassoc.ty
            )
        }

    case _ => Err(MatchError.DoesNotMatch)
}


pub enum UnificationError with Eq, ToString, Hash, Order {
    case OccursCheckFailed
    case KindMismatch
    case NoApplicableRule
}


pub def unifyOneStep(
    constraintEnv: ConstrEnv,
    given: List[Constr],
    left: Type,
    right: Type
): Result[UnificationError, (List[EqConstr], Subst)] =
    if (left == right) Ok((Nil, Subst.empty()))
    else unifyOneStepWithoutEq(constraintEnv, given, left, right)


def unifyOneStepWithoutEq(
    constraintEnv: ConstrEnv,
    given: List[Constr],
    left: Type,
    right: Type
): Result[UnificationError, (List[EqConstr], Subst)] =
    match (left, right) {
        case (
            Type.Ap(leftFunc, leftArg),
            Type.Ap(rightFunc, rightArg)
        ) => {
            Ok((
                EqConstr.EqConstr(leftFunc, rightFunc)
                :: EqConstr.EqConstr(leftArg, rightArg)
                :: Nil,
                Subst.empty()
            ))
        }

        case (Type.Var(leftVar),  _) => bindVar(leftVar, right)
            |> Result.map(x -> (Nil, x)),

        case (_, Type.Var(rightVar)) => bindVar(rightVar, left)
            |> Result.map(x -> (Nil, x)),

        case (Type.Assoc(leftAM), _) => 
            bindAM(constraintEnv, given, leftAM, right)
            |> Result.map(x -> (x, Subst.empty()))

        case (_, Type.Assoc(rightAM)) => 
            bindAM(constraintEnv, given, rightAM, left)
            |> Result.map(x -> (x, Subst.empty()))

        case _ => Err(UnificationError.NoApplicableRule)
    }


def bindAM(
    constraintEnv: ConstrEnv,
    given: List[Constr],
    am: Tyassoc, 
    ty: Type
): Result[UnificationError, List[EqConstr]] = {
    forM (
        reducedAm <- reduceTyOne(constraintEnv, given, Type.Assoc(am)) 
            |> Option.toOk(UnificationError.NoApplicableRule);

        _ <- if (reducedAm |> Kinded.kind != ty |> Kinded.kind) 
                Err(UnificationError.KindMismatch)
            else Ok(())
    )  yield EqConstr.EqConstr(reducedAm, ty) :: Nil
}


def bindVar(
    var: Tyvar, 
    ty: Type
): Result[UnificationError, Subst] = {
    if (ty == Type.Var(var)) 
        Ok(Subst.empty())
    else if (ty 
        |> FreeVars.fvs 
        |> List.memberOf(var)
    )
        Err(UnificationError.OccursCheckFailed)
    else if (var |> Kinded.kind != ty |> Kinded.kind) 
        Err(UnificationError.KindMismatch)
    else
        Ok(Subst.singleton(var, ty))
}


def repeatUnificationHelper(
    constraintEnv: ConstrEnv,
    given: List[Constr],
    constraints: List[EqConstr],
    currentSubst: Subst
): (List[EqConstr], Subst) = {
    def findApplicable(
        processed: List[EqConstr],
        pending: List[EqConstr]
    ): Option[(List[EqConstr], Subst)] = match pending {
        case Nil => None

        case head :: tail => {
            // if we can apply some rule to head, then we have made progress
            match unifyOneStep(
                constraintEnv,
                given, 
                head |> EqConstr.left, 
                head |> EqConstr.right
            ) {
                case Ok((unifyEqConstr, subst)) => {
                    // apply substitution to the remaining constraints
                    let nextConstraints = 
                        (processed ++ tail)
                            |> List.map(c -> c |> Substable.apply(subst))
                        ++ unifyEqConstr;

                    Some((nextConstraints, subst))
                }

                case Err(_) => findApplicable(head :: processed, tail)
            }
        }
    };

    match findApplicable(Nil, constraints) {
        case Some((nextConstraints, subst)) => 
            repeatUnificationHelper(
                constraintEnv,
                given,
                nextConstraints,
                Subst.compose(subst, currentSubst)
            )

        case None => (constraints, currentSubst)
    }
}


pub def unifyRepeat(
    constraintEnv: ConstrEnv,
    given: List[Constr],
    constraints: List[EqConstr]
): (List[EqConstr], Subst) = 
    repeatUnificationHelper(
        constraintEnv, 
        given, 
        constraints, 
        Subst.empty()
    )
