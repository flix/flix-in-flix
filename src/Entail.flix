pub def entailOneStep(
    constraintEnv: ConstraintEnvironment,
    given: List[Constraint],
    goal: Constraint
): Option[(List[Constraint], Substitution)] = {
    match goal {
        case Constraint.Class(clsConstraint) => 
            entailClassConstraintOneStep(constraintEnv, given, clsConstraint)
                |> Option.map((newConstraints) -> 
                    (newConstraints, Substitution.empty())
                ),
        
        // delegate to the unification procedure
        case Constraint.Equality(eqConstraint) => {
            unifyOneStep(
                constraintEnv,
                given, 
                eqConstraint |> EqualityConstraint.left,
                eqConstraint |> EqualityConstraint.right
            ) 
                |> Result.toOption
                |> Option.map(res -> (
                    res |> fst |> List.map(Constraint.Equality),
                    res |> snd
                ))
        }
    }
}


def tryInstance(
    inst: Instance,
    classType: Type
): Option[List[Constraint]] = {
    let instHead = inst |> Instance.head |> ClassConstraint.classType;

    matchTypes(instHead, classType)
        |> Result.toOption
        |> Option.map(s -> {
            inst |> Instance.context
                |> Substitutable.apply(s)
        })
}


def reduceClassConstraint(
    constraintEnv: ConstraintEnvironment,
    givens: List[Constraint],
    classConstraint: ClassConstraint
): Option[ClassConstraint] = {
    classConstraint
        |> ClassConstraint.classType
        |> reduceTypeOneStep(constraintEnv, givens)
        |> Option.map(ty -> ClassConstraint.ClassConstraint(
            classConstraint |> ClassConstraint.classId,
            ty
        ))
}


def entailClassConstraintOneStep(
    constraintEnv: ConstraintEnvironment,
    given: List[Constraint],
    goal: ClassConstraint
): Option[List[Constraint]] = {
    let bySuper = given |> List.exists(x -> {
        match x {
            case Constraint.Class(givenClsConstraint) => {
                let givenClassType = givenClsConstraint 
                    |> ClassConstraint.classType;
                
                let goalClassType = goal 
                    |> ClassConstraint.classType;
        
                // doesn't have the same type, so can't be used to 
                // entail
                if (givenClassType != goalClassType) false
                else {        
                    constraintEnv 
                        |> ConstraintEnvironment.getTransitiveParentClasses(
                            givenClsConstraint |> ClassConstraint.classId
                        )
                        |> Set.memberOf(goal |> ClassConstraint.classId)
                }
            }

            case Constraint.Equality(_) => false
        }
    });

    if (bySuper) Some(Nil)
    else {
        match goal |> reduceClassConstraint(constraintEnv, given) {
            case Some(reduced) => Some(Constraint.Class(reduced) :: Nil)
            case None => {
                forM (        
                    classDecl <- constraintEnv 
                        |> ConstraintEnvironment.lookupClass(
                            goal |> ClassConstraint.classId
                        );

                    chain <- classDecl       
                        |> Class.instances
                        |> List.findMap(s -> tryInstance(
                            s, 
                            goal |> ClassConstraint.classType
                        ))     
                ) yield chain
            }
        }
    }  
}