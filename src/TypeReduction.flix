def reduceAssociatedMemberOneStep(
    constraintEnv: ConstraintEnvironment,
    given: List[Constraint],
    assoc: AssociatedMember
): Type = {
    let argument = assoc 
        |> AssociatedMember.ty 
        |> reduceTypeOneStep(constraintEnv, given);

    let reducedAM = Type.AssociatedMember(
        AssociatedMember.AssociatedMember(
            assoc |> AssociatedMember.id,
            argument,
            assoc |> AssociatedMember.kind
        )
    );

    let constraintFromGiven = given
        |> List.filterMap(c -> c |> Constraint.asEqualityConstraint);
    let constraintFromEnv = constraintEnv
        |> ConstraintEnvironment.lookupAssociatedMemberEquality(
            assoc |> AssociatedMember.id
        );

    let allConstraints = constraintFromGiven ++ constraintFromEnv;

    allConstraints
        |> List.findMap(c -> {
            let leftAM = c |> EqualityConstraint.left;

            forM (
                subst <- matchTypes(leftAM, reducedAM) 
                    |> Result.toOption
            ) yield c 
                |> EqualityConstraint.right 
                |> Substitutable.apply(subst)
        })
        |> Option.getWithDefault(reducedAM)
}


def reduceSetFormulaOneStep(
    constraintEnv: ConstraintEnvironment,
    given: List[Constraint],
    setFormula: SetFormula
): SetFormula = {
    match setFormula {
        case SetFormula.Singleton(_) => setFormula

        case SetFormula.Binary(binarySetFormula) => {
            let left = binarySetFormula
                |> BinarySetFormula.left
                |> reduceSetFormulaOneStep(constraintEnv, given);
            let right = binarySetFormula
                |> BinarySetFormula.right
                |> reduceSetFormulaOneStep(constraintEnv, given);

            SetFormula.Binary(BinarySetFormula.BinarySetFormula(
                left,
                binarySetFormula |> BinarySetFormula.op,
                right
            ))
        }

        case SetFormula.Complement(inner) =>
            SetFormula.Complement(
                inner |> reduceSetFormulaOneStep(constraintEnv, given)
            )

        case SetFormula.TypeVariable(_) => setFormula

        case SetFormula.Gen(_) => setFormula

        case SetFormula.AssociatedMember(assoc) =>
            match reduceAssociatedMemberOneStep(constraintEnv, given, assoc) {
                case Type.AssociatedMember(reducedAssoc) =>
                    SetFormula.AssociatedMember(reducedAssoc)

                case Type.SetFormula(reducedSetFormula) =>
                    reducedSetFormula

                case unexpected => bug!(
                    "Expected associated member reduction to yield an effect, but found: ${unexpected}"
                )
            }

        case SetFormula.Empty => setFormula
    }
}


def reduceTypeOneStep(
    constraintEnv: ConstraintEnvironment,
    given: List[Constraint],
    ty: Type
): Type = { 
    match ty {
        case Type.Variable(_) => ty,
        case Type.Constructor(_) => ty,
        case Type.AssociatedMember(assoc) =>
            reduceAssociatedMemberOneStep(constraintEnv, given, assoc)

        case Type.Application(app) => {
            let func = app
                |> TypeApplication.function
                |> reduceTypeOneStep(constraintEnv, given);
            let arg = app
                |> TypeApplication.argument
                |> reduceTypeOneStep(constraintEnv, given);

            Type.Application(TypeApplication.TypeApplication(
                func, arg
            ))
        }

        case Type.SetFormula(setFormula) =>
            Type.SetFormula(
                setFormula |> reduceSetFormulaOneStep(constraintEnv, given)
            )

        case Type.Gen(_) => ty
    }
}


@Tailrec
pub def reduceType(
    constraintEnv: ConstraintEnvironment,
    given: List[Constraint],
    ty: Type
): Type = {
    let reducedTy = reduceTypeOneStep(constraintEnv, given, ty);

    if (reducedTy == ty) reducedTy
    else reduceType(constraintEnv, given, reducedTy)
}
