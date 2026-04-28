def reduceInnerTyassocOneStep(
    constraintEnv: ConstraintEnvironment,
    given: List[Constraint],
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
    given: List[Constraint],
    assoc: Tyassoc
): Option[Type] = {
    given
        |> List.filterMap(c -> c |> Constraint.asEqualityConstraint)
        |> List.findMap(c -> {
            let leftAM = c |> EqualityConstraint.left;
            if (leftAM == Type.Assoc(assoc)) {
                Some(c |> EqualityConstraint.right)
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
            let leftAM = c |> EqualityConstraint.left;

            matchTypes(leftAM, Type.Assoc(assoc))
                |> Result.toOption
                |> Option.map(s -> c 
                    |> EqualityConstraint.right 
                    |> Substitutable.apply(s))
        })
}


def reduceTyassocOneStep(
    constraintEnv: ConstraintEnvironment,
    given: List[Constraint],
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


def reduceSetFormulaOneStep(
    constraintEnv: ConstraintEnvironment,
    given: List[Constraint],
    setFormula: SetFormula
): Option[SetFormula] = {
    match setFormula {
        case SetFormula.Singleton(_) => None,

        case SetFormula.Variable(_) => None,

        case SetFormula.Gen(_) => None,

        case SetFormula.Empty => None,

        case SetFormula.Binary(binarySetFormula) => {
            let reducedLeft = binarySetFormula 
                |> BinarySetFormula.left
                |> reduceSetFormulaOneStep(constraintEnv, given)
                |> Option.map(s -> SetFormula.Binary(
                    BinarySetFormula.BinarySetFormula(
                        s,
                        binarySetFormula |> BinarySetFormula.op,
                        binarySetFormula |> BinarySetFormula.right
                    )
                ));

            if (reducedLeft |> Option.isEmpty)
                binarySetFormula 
                    |> BinarySetFormula.right
                    |> reduceSetFormulaOneStep(constraintEnv, given)
                    |> Option.map(s -> SetFormula.Binary(
                        BinarySetFormula.BinarySetFormula(
                            binarySetFormula |> BinarySetFormula.left,
                            binarySetFormula |> BinarySetFormula.op,
                            s
                        )
                    ))
            else reducedLeft
        }

        case SetFormula.Complement(inner) => 
            inner |> reduceSetFormulaOneStep(constraintEnv, given)
                |> Option.map(s -> SetFormula.Complement(s))

        case SetFormula.Tyassoc(assoc) => 
            reduceTyassocOneStep(constraintEnv, given, assoc)
                |> Option.map(ty -> match ty {
                    case Type.SetFormula(sf) => sf,
                    case Type.Assoc(s) => 
                        SetFormula.Tyassoc(s),

                    case _ => bug!("Expected a set formula")
                })
    }
}


def reduceTypeOneStep(
    constraintEnv: ConstraintEnvironment,
    given: List[Constraint],
    ty: Type
): Option[Type] = { 
    match ty {
        case Type.Var(_) => None,
        case Type.Con(_) => None,
        case Type.Gen(_) => None

        case Type.Assoc(assoc) => 
            reduceTyassocOneStep(constraintEnv, given, assoc)

        case Type.Ap(app) => {
            let reducedFn = app 
                |> TypeApplication.function
                |> reduceTypeOneStep(constraintEnv, given)
                |> Option.map(redFn -> Type.Ap(
                    TypeApplication.TypeApplication(
                        redFn,
                        app |> TypeApplication.argument
                    )
                ));

            if (reducedFn |> Option.isEmpty)
                app
                    |> TypeApplication.argument
                    |> reduceTypeOneStep(constraintEnv, given)
                    |> Option.map(redArg -> Type.Ap(
                        TypeApplication.TypeApplication(
                            app |> TypeApplication.function,
                            redArg
                        )
                    ))
            else
                reducedFn
        }

        case Type.SetFormula(setFormula) => 
            reduceSetFormulaOneStep(constraintEnv, given, setFormula)
                |> Option.map(Type.SetFormula)  
    }
}
