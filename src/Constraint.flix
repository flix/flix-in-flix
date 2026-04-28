pub enum ClassConstraint(Id, Type) with Eq, ToString, Hash, Order


mod ClassConstraint {
    pub def classId(constraint: ClassConstraint): Id = match constraint {
        case ClassConstraint(id, _) => id
    }


    pub def classType(constraint: ClassConstraint): Type = match constraint {
        case ClassConstraint(_, ty) => ty
    }
}


instance Substable[ClassConstraint] {
    pub def apply(
        substitution: Subst, 
        a: ClassConstraint
    ): ClassConstraint =  {
        let id = a 
            |> ClassConstraint.classId;
        
        let ty = a
            |> ClassConstraint.classType
            |> Substable.apply(substitution);

        ClassConstraint.ClassConstraint(id, ty)
    }
}


pub enum EqualityConstraint(Type, Type) with Eq, ToString, Hash, Order


instance Substable[EqualityConstraint] {
    pub def apply(
        substitution: Subst, 
        a: EqualityConstraint
    ): EqualityConstraint =  {
        let left = a 
            |> EqualityConstraint.left 
            |> Substable.apply(substitution);
        
        let right = a
            |> EqualityConstraint.right
            |> Substable.apply(substitution);

        EqualityConstraint.EqualityConstraint(left, right)
    }
}



mod EqualityConstraint {
    pub def left(constraint: EqualityConstraint): Type = match constraint {
        case EqualityConstraint(left, _) => left
    }


    pub def right(constraint: EqualityConstraint): Type = match constraint {
        case EqualityConstraint(_, right) => right
    }
}


pub enum Constraint with Eq, ToString, Hash, Order {
    case Class(ClassConstraint),
    case Equality(EqualityConstraint)
}


instance Substable[Constraint] {
    pub def apply(substitution: Subst, a: Constraint): Constraint = 
        match a {
            case Constraint.Class(clsConstraint) => 
                Constraint.Class(
                    clsConstraint |> Substable.apply(substitution)
                ),
            case Constraint.Equality(eqConstraint) => 
                Constraint.Equality(
                    eqConstraint |> Substable.apply(substitution)
                )
        }
}


mod Constraint {
    pub def asEqualityConstraint(constraint: Constraint): 
        Option[EqualityConstraint] = match constraint {
            case Constraint.Equality(eqConstraint) => Some(eqConstraint),
            case _ => None
        }
}


pub enum Qualified[a](a, List[Constraint]) with Eq, ToString, Hash, Order
 

mod Qualified {
    pub def head(qualified: Qualified[q]): q = match qualified {
        case Qualified(q, _) => q
    }


    pub def context(qualified: Qualified[q]): List[Constraint] 
        = match qualified {
            case Qualified(_, constraints) => constraints
        }   
}  


pub enum Scheme[a](Qualified[a]) with Eq, ToString, Hash, Order
 
  
mod Scheme {  
    pub def head(scheme: Scheme[a]): a = match scheme {
        case Scheme(qualified) => qualified |> Qualified.head
    }


    pub def context(scheme: Scheme[a]): List[Constraint] 
        = match scheme {
            case Scheme(qualified) => qualified |> Qualified.context
        }
}