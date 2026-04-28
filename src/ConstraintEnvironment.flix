pub enum Instance(Qualified[ClassConstr])


mod Instance {
    pub def head(inst: Instance): ClassConstr = match inst {
        case Instance(qualified) => qualified |> Qualified.head
    }


    pub def context(inst: Instance): List[Constr] = match inst {
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
    Map[Id, List[EqConstr]],
    Map[Id, Class]
)


mod ConstraintEnvironment {
    def associatedMemberEqualities(
        constraintEnv: ConstraintEnvironment 
    ): Map[Id, List[EqConstr]] = match constraintEnv {
        case ConstraintEnvironment(map, _) => map
    }


    def classMap(constraintEnv: ConstraintEnvironment): Map[Id, Class] = match constraintEnv {
        case ConstraintEnvironment(_, classMap) => classMap
    }


    pub def lookupClass(
        id: Id, 
        constraintEnv: ConstraintEnvironment
    ): Option[Class] = {
        let map = constraintEnv |> classMap;

        map |> Map.get(id)
    }


    pub def lookupTyassocEquality(
        id: Id,
        constraintEnv: ConstraintEnvironment
    ): List[EqConstr] = {
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
