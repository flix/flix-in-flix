pub enum ClassConstr(Id, Type) with Eq, ToString, Hash, Order

mod ClassConstr {
    pub def id(con: ClassConstr): Id = match con { 
        case ClassConstr(id, _) => id 
    }
    pub def ty(con: ClassConstr): Type = match con { 
        case ClassConstr(_, ty) => ty 
    }
}

instance Substable[ClassConstr] {
    pub def apply(subst: Subst, con: ClassConstr): ClassConstr = {
        let id = ClassConstr.id(con);
        let ty = Substable.apply(subst, ClassConstr.ty(con));
        ClassConstr.ClassConstr(id, ty)
    }
}

pub enum EqConstr(Type, Type) with Eq, ToString, Hash, Order

instance Substable[EqConstr] {
    pub def apply(subst: Subst, con: EqConstr): EqConstr = {
        let lhs = Substable.apply(subst, EqConstr.left(con));
        let rhs = Substable.apply(subst, EqConstr.right(con));
        EqConstr.EqConstr(lhs, rhs)
    }
}

mod EqConstr {
    pub def left(con: EqConstr): Type = match con { 
        case EqConstr(lhs, _) => lhs
    }
    pub def right(con: EqConstr): Type = match con { 
        case EqConstr(_, rhs) => rhs 
    }
}

pub enum Constr with Eq, ToString, Hash, Order {
    case Class(ClassConstr),
    case Eq(EqConstr)
}

instance Substable[Constr] {
    pub def apply(subst: Subst, con: Constr): Constr = match con {
        case Constr.Class(cls) => Constr.Class(Substable.apply(subst, cls))
        case Constr.Eq(eq) => Constr.Eq(Substable.apply(subst, eq))
    }
}

mod Constr {
    pub def asEq(con: Constr): Option[EqConstr] = match con {
        case Constr.Eq(eq) => Some(eq)
        case _ => None
    }
}

pub enum Qual[a](a, List[Constr]) with Eq, ToString, Hash, Order

mod Qual {
    pub def head(qua: Qual[q]): q = match qua { case Qual(q, _) => q }
    pub def context(qua: Qual[q]): List[Constr] = match qua {
        case Qual(_, ctx) => ctx 
    }
}

    }
}
