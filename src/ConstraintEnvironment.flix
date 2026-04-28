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
    Map[Id, List[EqualityConstraint]],
    Map[Id, Class]
)


mod ConstraintEnvironment {
    use ConstraintEnvironment.getSuperClassesOfClass
    def associatedMemberEqualities(
        constraintEnv: ConstraintEnvironment 
    ): Map[Id, List[EqualityConstraint]] = match constraintEnv {
        case ConstraintEnvironment(map, _) => map
    }


    def classMap(constraintEnv: ConstraintEnvironment): Map[Id, Class] = match constraintEnv {
        case ConstraintEnvironment(_, classMap) => classMap
    }


    pub def lookupAssociatedMemberEquality(
        id: Id,
        constraintEnv: ConstraintEnvironment
    ): List[EqualityConstraint] = {
        let map = constraintEnv 
            |> ConstraintEnvironment.associatedMemberEqualities;

        map |> Map.get(id) |> Option.getWithDefault(Nil)
    }


    pub def getSuperClassesOfClass(
        id: Id,
        constraintEnv: ConstraintEnvironment
    ): List[Id] = {
        let classMap = constraintEnv |> classMap;

        classMap
            |> Map.get(id)
            |> Option.map(cls -> cls |> Class.superClasses)
            |> Option.getWithDefault(Nil)
    }


    pub def getSuperClassFact(clsEnv: ConstraintEnvironment): 
        #{ StrictSuper(Id, Id) | r } = {
        let classMap = clsEnv |> classMap;

        inject classMap
            |> Map.keysOf
            |> Set.flatMap(x -> {
                clsEnv 
                    |> getSuperClassesOfClass(x) 
                    |> List.map(y -> (y, x))
                    |> List.toSet
            }) into StrictSuper/2
    }


    pub def getTransitiveParentClasses(
        id: Id,
        constraintEnv: ConstraintEnvironment
    ): Set[Id] = {
        let superClassFact = constraintEnv |> getSuperClassFact;

        let rules: #{ Super(Id, Id), StrictSuper(Id, Id) } = #{
            Super(x, y) :- StrictSuper(x, y).
            Super(x, y) :- StrictSuper(x, z), Super(z, y).
        };

        query superClassFact, rules, #{ Super(id, id). } 
            select x from Super(x, id)
            |> Vector.toSet
    }
}