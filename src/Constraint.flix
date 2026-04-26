pub enum ClassConstraint(Id, Type) with Eq, ToString, Hash, Order


pub enum EqualityConstraint(Type, Type) with Eq, ToString, Hash, Order


pub enum Constraint with Eq, ToString, Hash, Order {
    case Class(ClassConstraint),
    case Equality(EqualityConstraint)
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