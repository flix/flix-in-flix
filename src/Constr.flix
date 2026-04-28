pub enum ClassConstr(Id, Type) with Eq, ToString, Hash, Order

mod ClassConstr {
    pub def classId(con: ClassConstr): Id = match con { 
        case ClassConstr(id, _) => id 
    }
    pub def classType(con: ClassConstr): Type = match con { 
        case ClassConstr(_, ty) => ty 
    }
}

instance Substable[ClassConstr] {
    pub def apply(subst: Subst, con: ClassConstr): ClassConstr = {
        let id = ClassConstr.classId(con);
        let ty = Substable.apply(subst, ClassConstr.classType(con));
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

pub enum Qualified[a](a, List[Constr]) with Eq, ToString, Hash, Order

mod Qualified {
    pub def head(qua: Qualified[q]): q = match qua { 
        case Qualified(q, _) => q
    }
    pub def context(qua: Qualified[q]): List[Constr] = match qua {
        case Qualified(_, ctx) => ctx 
    }
}

pub enum Scheme[a](Qualified[a]) with Eq, ToString, Hash, Order

mod Scheme {
    pub def head(sch: Scheme[a]): a = match sch {
        case Scheme(qua) => Qualified.head(qua)
    }

    pub def context(sch: Scheme[a]): List[Constr] = match sch {
        case Scheme(qua) => Qualified.context(qua)
    }
}
