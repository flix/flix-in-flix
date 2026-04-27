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
    case OccursCheckFailed,
    case KindMismatch
    case DoesNotUnify
}


pub def unifyOneStep(
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

        case (Type.Constructor(leftCon), Type.Constructor(rightCon)) 
            if leftCon == rightCon => Ok((Nil, Substitution.empty()))

        case (Type.AssociatedMember(leftAM), _) => 
            bindAM(constraintEnv, given, leftAM, right)
            |> Result.map(x -> (x, Substitution.empty()))

        case (_, Type.AssociatedMember(rightAM)) => 
            bindAM(constraintEnv, given, rightAM, left)
            |> Result.map(x -> (x, Substitution.empty()))

        // TODO: Boolean unification for set formulas
        case (Type.SetFormula(leftSet), Type.SetFormula(rightSet)) => ???

        case _ => Err(UnificationError.DoesNotUnify)
    }


def bindAM(
    constraintEnv: ConstraintEnvironment,
    given: List[Constraint],
    am: AssociatedMember, 
    ty: Type
): Result[UnificationError, List[EqualityConstraint]] = {
    let amReduced = reduceType(constraintEnv, given, Type.AssociatedMember(am));

    if (amReduced == ty) 
        Ok(Nil)
    else if (amReduced |> Kinded.kind != ty |> Kinded.kind) 
        Err(UnificationError.KindMismatch)
    else
        Ok(EqualityConstraint.EqualityConstraint(amReduced, ty) :: Nil)
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