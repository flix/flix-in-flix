pub enum MatchError with Eq, ToString, Hash, Order {
    case DoesNotMatch,
    case KindMismatch
}


pub def matchTypes(
    left: Type, 
    right: Type
): Result[MatchError, Substitution] = match (left, right) {
    case ( Type.Application(leftApp),
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
                leftAM |> AssociatedMember.ty,
                rightAM |> AssociatedMember.ty
            )
        }

    case _ => Err(MatchError.DoesNotMatch)
}


