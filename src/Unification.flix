pub enum UnificationFailure {
    case OccursCheckFailed(TypeVariable, Type),
    case UnificationMismatch(Type, Type)
}



pub def mgu(left: Type, right: Type): 
    Result[UnificationFailure, (Substitution, List[Constraint])] =
    
    match (left, right) {
        case (Type.Application(leftA), Type.Application(rightA)) =>  {
            forM (
                (leftSubst, leftConstraints) <- mgu(
                    leftA |> TypeApplication.function, 
                    rightA |> TypeApplication.function
                );
                (rightSubst, rightConstraints) <- mgu(
                    leftA |> TypeApplication.argument, 
                    rightA |> TypeApplication.argument
                )
            ) yield {
                let constraints = leftConstraints ++ rightConstraints;

                ???
            }
        }

        case (a, b) => Err(UnificationFailure.UnificationMismatch(a, b))
    }
