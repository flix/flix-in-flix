def reduceInnerTyassocOneStep(
    constraintEnv: ConstraintEnvironment,
    given: List[Constr],
    assoc: Tyassoc
): Option[Type] = {
    assoc 
        |> Tyassoc.ty 
        |> reduceTypeOneStep(constraintEnv, given)
        |> Option.map(ty -> Type.Assoc(
            Tyassoc.Tyassoc(
                assoc |> Tyassoc.id,
                ty,
                assoc |> Tyassoc.kind
            )
        ))
}


def reduceTyassocFromGiven(
    given: List[Constr],
    assoc: Tyassoc
): Option[Type] = {
    given
        |> List.filterMap(c -> c |> Constr.asEq)
        |> List.findMap(c -> {
            let leftAM = c |> EqConstr.left;
            if (leftAM == Type.Assoc(assoc)) {
                Some(c |> EqConstr.right)
            } else None
        })
}


def reduceTyassocFromEnv(
    constraintEnv: ConstraintEnvironment,
    assoc: Tyassoc
): Option[Type] = {
    constraintEnv
        |> ConstraintEnvironment.lookupTyassocEquality(
            assoc |> Tyassoc.id
        )
        |> List.findMap(c -> {
            let leftAM = c |> EqConstr.left;

            matchTypes(leftAM, Type.Assoc(assoc))
                |> Result.toOption
                |> Option.map(s -> c 
                    |> EqConstr.right 
                    |> Substable.apply(s))
        })
}


def reduceTyassocOneStep(
    constraintEnv: ConstraintEnvironment,
    given: List[Constr],
    assoc: Tyassoc
): Option[Type] = {
    let reducedInner = reduceInnerTyassocOneStep(
        constraintEnv,
        given,
        assoc
    );


    if (not (reducedInner |> Option.isEmpty)) {
        reducedInner
    } else {
        let fromGiven = reduceTyassocFromGiven(given, assoc);

        if (not (fromGiven |> Option.isEmpty)) {
            fromGiven
        } else {
            reduceTyassocFromEnv(constraintEnv, assoc)
        }
    }
}


def reduceTypeOneStep(
    constraintEnv: ConstraintEnvironment,
    given: List[Constr],
    ty: Type
): Option[Type] = { 
    match ty {
        case Type.Var(_) => None,
        case Type.Con(_) => None,
        case Type.Gen(_) => None

        case Type.Assoc(assoc) => 
            reduceTyassocOneStep(constraintEnv, given, assoc)

        case Type.Ap(function, argument) => {
            let reducedFn = function
                |> reduceTypeOneStep(constraintEnv, given)
                |> Option.map(redFn -> Type.Ap(
                    redFn,
                    argument
                ));

            if (reducedFn |> Option.isEmpty)
                argument
                    |> reduceTypeOneStep(constraintEnv, given)
                    |> Option.map(redArg -> Type.Ap(
                        function,
                        redArg
                ))
            else
                reducedFn
        }
    }
}
