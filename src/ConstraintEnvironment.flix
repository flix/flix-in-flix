pub enum Instance(Qualified[Constraint])


mod Instance {
    pub def head(inst: Instance): Constraint = match inst {
        case Instance(qualified) => qualified |> Qualified.head
    }


    pub def context(inst: Instance): List[Constraint] = match inst {
        case Instance(qualified) => qualified |> Qualified.context
    }
}


pub enum Class(List[Id], List[Instance])

 
mod Class {
    pub def superClasses(cls: Class): List[Id] = match cls {
        case Class(superClasses, _) =>  superClasses
    }
 

    pub def instances(cls: Class): List[Instance] = match cls {
        case Class(_, instances) => instances
    }
}


pub enum ConstraintEnvironment(
    // Map from associated member id to the equality constraints
    Map[Id, List[EqualityConstraint]]
)


mod ConstraintEnvironment {
    def associatedMemberEqualities(
        constraintEnv: ConstraintEnvironment 
    ): Map[Id, List[EqualityConstraint]] = match constraintEnv {
        case ConstraintEnvironment(map) => map
    }

    pub def lookupAssociatedMemberEquality(
        id: Id,
        constraintEnv: ConstraintEnvironment
    ): List[EqualityConstraint] = {
        let map = constraintEnv 
            |> ConstraintEnvironment.associatedMemberEqualities;

        map |> Map.get(id) |> Option.getWithDefault(Nil)
    }
}