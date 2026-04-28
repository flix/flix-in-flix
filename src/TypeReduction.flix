def reduceInnerAssociatedMemberOneStep(
    constraintEnv: ConstraintEnvironment,
    given: List[Constraint],
    assoc: AssociatedMember
): Option[Type] = {
    assoc 
        |> AssociatedMember.ty 
        |> reduceTypeOneStep(constraintEnv, given)
        |> Option.map(ty -> Type.AssociatedMember(
            AssociatedMember.AssociatedMember(
                assoc |> AssociatedMember.id,
                ty,
                assoc |> AssociatedMember.kind
            )
        ))
}


def reduceAssociatedMemberFromGiven(
    given: List[Constraint],
    assoc: AssociatedMember
): Option[Type] = {
    given
        |> List.filterMap(c -> c |> Constraint.asEqualityConstraint)
        |> List.findMap(c -> {
            let leftAM = c |> EqualityConstraint.left;
            if (leftAM == Type.AssociatedMember(assoc)) {
                Some(c |> EqualityConstraint.right)
            } else None
        })
}


def reduceAssociatedMemberFromEnv(
    constraintEnv: ConstraintEnvironment,
    assoc: AssociatedMember
): Option[Type] = {
    constraintEnv
        |> ConstraintEnvironment.lookupAssociatedMemberEquality(
            assoc |> AssociatedMember.id
        )
        |> List.findMap(c -> {
            let leftAM = c |> EqualityConstraint.left;

            matchTypes(leftAM, Type.AssociatedMember(assoc))
                |> Result.toOption
                |> Option.map(s -> c 
                    |> EqualityConstraint.right 
                    |> Substitutable.apply(s))
        })
}


def reduceAssociatedMemberOneStep(
    constraintEnv: ConstraintEnvironment,
    given: List[Constraint],
    assoc: AssociatedMember
): Option[Type] = {
    let reducedInner = reduceInnerAssociatedMemberOneStep(
        constraintEnv,
        given,
        assoc
    );


    if (not (reducedInner |> Option.isEmpty)) {
        reducedInner
    } else {
        let fromGiven = reduceAssociatedMemberFromGiven(given, assoc);

        if (not (fromGiven |> Option.isEmpty)) {
            fromGiven
        } else {
            reduceAssociatedMemberFromEnv(constraintEnv, assoc)
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

        case SetFormula.AssociatedMember(assoc) => 
            reduceAssociatedMemberOneStep(constraintEnv, given, assoc)
                |> Option.map(ty -> match ty {
                    case Type.SetFormula(sf) => sf,
                    case Type.AssociatedMember(s) => 
                        SetFormula.AssociatedMember(s),

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
        case Type.Variable(_) => None,
        case Type.Constructor(_) => None,
        case Type.Gen(_) => None

        case Type.AssociatedMember(assoc) => 
            reduceAssociatedMemberOneStep(constraintEnv, given, assoc)

        case Type.Application(app) => {
            let reducedFn = app 
                |> TypeApplication.function
                |> reduceTypeOneStep(constraintEnv, given)
                |> Option.map(redFn -> Type.Application(
                    TypeApplication.TypeApplication(
                        redFn,
                        app |> TypeApplication.argument
                    )
                ));

            if (reducedFn |> Option.isEmpty)
                app
                    |> TypeApplication.argument
                    |> reduceTypeOneStep(constraintEnv, given)
                    |> Option.map(redArg -> Type.Application(
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
