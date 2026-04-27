pub enum MatchError with Eq, ToString, Hash, Order {
    case DoesNotMatch,
    case KindMismatch
}


pub def matchTypes(
    left: Type, 
    right: Type
): Result[MatchError, Substitution] = match (left, right) {
    case ( 
        Type.Application(leftApp),
        Type.Application(rightApp)
    ) => {
        forM (
            funcSubst <- matchTypes(
                leftApp |> TypeApplication.function,
                rightApp |> TypeApplication.function
            );
            argSubst <- matchTypes(
                leftApp |> TypeApplication.argument,
                rightApp |> TypeApplication.argument
            );
            mergedSubst <- Substitution.merge(funcSubst, argSubst)
                |> Option.map(Ok)
                |> Option.getWithDefault(
                    Err(MatchError.DoesNotMatch)
                )
        ) yield mergedSubst
    }

    case (Type.Variable(leftVar), _) => {
        let varKind = leftVar |> Kinded.kind;
        let rightKind = right |> Kinded.kind;

        if (varKind != rightKind) 
            Err(MatchError.KindMismatch)
        else
            Ok(Substitution.singleton(leftVar, right))
    }

    case (Type.Constructor(leftCon), Type.Constructor(rightCon)) 
        if leftCon == rightCon => Ok(Substitution.empty())

    // TODO: one-way boolean unification for set formulas
    case (Type.SetFormula(leftSet), Type.SetFormula(rightSet)) => ???

    case (Type.AssociatedMember(leftAM), Type.AssociatedMember(rightAM)) 
        if leftAM |> AssociatedMember.id == rightAM |> AssociatedMember.id => {
            matchTypes(
                leftAM |> AssociatedMember.ty, rightAM |> AssociatedMember.ty
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
    constraintEnv: ConstraintEnvironment,
    given: List[Constraint],
    left: Type,
    right: Type
): Result[UnificationError, (List[EqualityConstraint], Substitution)] =
    if (left == right) Ok((Nil, Substitution.empty()))
    else unifyOneStepWithoutEq(constraintEnv, given, left, right)


def unifyOneStepWithoutEq(
    constraintEnv: ConstraintEnvironment,
    given: List[Constraint],
    left: Type,
    right: Type
): Result[UnificationError, (List[EqualityConstraint], Substitution)] =
    match (left, right) {
        case (
            Type.Application(leftApp),
            Type.Application(rightApp)
        ) => {
            let leftFunc = leftApp |> TypeApplication.function;
            let leftArg = leftApp |> TypeApplication.argument;

            let rightFunc = rightApp |> TypeApplication.function;
            let rightArg = rightApp |> TypeApplication.argument;

            Ok((
                EqualityConstraint.EqualityConstraint(leftFunc, rightFunc)
                :: EqualityConstraint.EqualityConstraint(leftArg, rightArg)
                :: Nil,
                Substitution.empty()
            ))
        }

        case (Type.Variable(leftVar),  _) => bindVar(leftVar, right)
            |> Result.map(x -> (Nil, x)),

        case (_, Type.Variable(rightVar)) => bindVar(rightVar, left)
            |> Result.map(x -> (Nil, x)),

        case (Type.AssociatedMember(leftAM), _) => 
            bindAM(constraintEnv, given, leftAM, right)
            |> Result.map(x -> (x, Substitution.empty()))

        case (_, Type.AssociatedMember(rightAM)) => 
            bindAM(constraintEnv, given, rightAM, left)
            |> Result.map(x -> (x, Substitution.empty()))

        // TODO: Boolean unification for set formulas
        case (Type.SetFormula(leftSet), Type.SetFormula(rightSet)) => ???

        case _ => Err(UnificationError.NoApplicableRule)
    }


def bindAM(
    constraintEnv: ConstraintEnvironment,
    given: List[Constraint],
    am: AssociatedMember, 
    ty: Type
): Result[UnificationError, List[EqualityConstraint]] = {
    forM (
        reducedAm <- reduceTypeOneStep(constraintEnv, given, Type.AssociatedMember(am)) 
            |> Option.toOk(UnificationError.NoApplicableRule);

        _ <- if (reducedAm |> Kinded.kind != ty |> Kinded.kind) 
                Err(UnificationError.KindMismatch)
            else Ok(())
    )  yield EqualityConstraint.EqualityConstraint(reducedAm, ty) :: Nil
}


def bindVar(
    var: TypeVariable, 
    ty: Type
): Result[UnificationError, Substitution] = {
    if (ty == Type.Variable(var)) 
        Ok(Substitution.empty())
    else if (ty 
        |> FreeTypeVariable.freeTypeVariables 
        |> List.memberOf(var)
    )
        Err(UnificationError.OccursCheckFailed)
    else if (var |> Kinded.kind != ty |> Kinded.kind) 
        Err(UnificationError.KindMismatch)
    else
        Ok(Substitution.singleton(var, ty))
}


def repeatUnificationHelper(
    constraintEnv: ConstraintEnvironment,
    given: List[Constraint],
    constraints: List[EqualityConstraint],
    currentSubst: Substitution
): (List[EqualityConstraint], Substitution) = {
    def findApplicable(
        processed: List[EqualityConstraint],
        pending: List[EqualityConstraint]
    ): Option[(List[EqualityConstraint], Substitution)] = match pending {
        case Nil => None

        case head :: tail => {
            // if we can apply some rule to head, then we have made progress
            match unifyOneStep(
                constraintEnv,
                given, 
                head |> EqualityConstraint.left, 
                head |> EqualityConstraint.right
            ) {
                case Ok((unifyEqConstr, subst)) => {
                    // apply substitution to the remaining constraints
                    let nextConstraints = 
                        (processed ++ tail)
                            |> List.map(c -> c |> Substitutable.apply(subst))
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
                Substitution.compose(subst, currentSubst)
            )

        case None => (constraints, currentSubst)
    }
}


pub def unifyRepeat(
    constraintEnv: ConstraintEnvironment,
    given: List[Constraint],
    constraints: List[EqualityConstraint]
): (List[EqualityConstraint], Substitution) = 
    repeatUnificationHelper(
        constraintEnv, 
        given, 
        constraints, 
        Substitution.empty()
    )

