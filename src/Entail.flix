pub def entailOneStep(
    constraintEnv: ConstrEnv,
    given: List[Constr],
    goal: Constr
): Option[(List[Constr], Subst)] = {
    match goal {
        case Constr.Class(clsConstraint) => 
            entailClassConstraintOneStep(constraintEnv, given, clsConstraint)
                |> Option.map((newConstraints) -> 
                    (newConstraints, Subst.empty())
                ),
        
        // delegate to the unification procedure
        case Constr.Eq(eqConstraint) => {
            unifyOneStep(
                constraintEnv,
                given, 
                eqConstraint |> EqConstr.left,
                eqConstraint |> EqConstr.right
            ) 
                |> Result.toOption
                |> Option.map(res -> (
                    res |> fst |> List.map(Constr.Eq),
                    res |> snd
                ))
        }
    }
}


def repeatEntailmentHelper(
    constraintEnv: ConstrEnv,
    given: List[Constr],
    constraints: List[Constr],
    currentSubst: Subst
): (List[Constr], Subst) = {
    def findApplicable(
        processed: List[Constr],
        pending: List[Constr]
    ): Option[(List[Constr], Subst)] = match pending {
        case Nil => None

        case head :: tail => {
            match entailOneStep(constraintEnv, given, head) {
                case Some((newConstraints, subst)) => {
                    let nextConstraints =
                        (processed ++ tail)
                            |> List.map(c -> c |> Substable.apply(subst))
                        ++ newConstraints;

                    Some((nextConstraints, subst))
                }

                case None => findApplicable(head :: processed, tail)
            }
        }
    };

    match findApplicable(Nil, constraints) {
        case Some((nextConstraints, subst)) =>
            repeatEntailmentHelper(
                constraintEnv,
                given,
                nextConstraints,
                Subst.compose(subst, currentSubst)
            )

        case None => (constraints, currentSubst)
    }
}


pub def entailRepeat(
    constraintEnv: ConstrEnv,
    given: List[Constr],
    constraints: List[Constr]
): (List[Constr], Subst) =
    repeatEntailmentHelper(
        constraintEnv,
        given,
        constraints,
        Subst.empty()
    )


def tryInstance(
    inst: Inst,
    classType: Type
): Option[List[Constr]] = {
    let instHead = inst |> Inst.head |> ClassConstr.classType;

    matchTypes(instHead, classType)
        |> Result.toOption
        |> Option.map(s -> {
            inst |> Inst.context
                |> Substable.apply(s)
        })
}


def reduceClassConstraint(
    constraintEnv: ConstrEnv,
    givens: List[Constr],
    classConstraint: ClassConstr
): Option[ClassConstr] = {
    classConstraint
        |> ClassConstr.classType
        |> reduceTyOne(constraintEnv, givens)
        |> Option.map(ty -> ClassConstr.ClassConstr(
            classConstraint |> ClassConstr.classId,
            ty
        ))
}


def entailClassConstraintOneStep(
    constraintEnv: ConstrEnv,
    given: List[Constr],
    goal: ClassConstr
): Option[List[Constr]] = {
    let bySuper = given |> List.exists(x -> {
        match x {
            case Constr.Class(givenClsConstraint) => {
                let givenClassType = givenClsConstraint 
                    |> ClassConstr.classType;
                
                let goalClassType = goal 
                    |> ClassConstr.classType;
        
                // doesn't have the same type, so can't be used to 
                // entail
                if (givenClassType != goalClassType) false
                else {        
                    constraintEnv 
                        |> ConstrEnv.parentClasses(
                            givenClsConstraint |> ClassConstr.classId
                        )
                        |> Set.memberOf(goal |> ClassConstr.classId)
                }
            }

            case Constr.Eq(_) => false
        }
    });

    if (bySuper) Some(Nil)
    else {
        match goal |> reduceClassConstraint(constraintEnv, given) {
            case Some(reduced) => Some(Constr.Class(reduced) :: Nil)
            case None => {
                forM (        
                    classDecl <- constraintEnv 
                        |> ConstrEnv.lookupClass(
                            goal |> ClassConstr.classId
                        );

                    chain <- classDecl       
                        |> Class.insts
                        |> List.findMap(s -> tryInstance(
                            s, 
                            goal |> ClassConstr.classType
                        ))     
                ) yield chain
            }
        }
    }  
}
