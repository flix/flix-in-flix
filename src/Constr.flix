pub enum ClassConstr(Id, Type) with Eq, ToString, Hash, Order

instance Instantiate[ClassConstr] {
    pub def inst(tys: List[Type], sch: ClassConstr): ClassConstr = match sch {
        case ClassConstr.ClassConstr(id, ty) => 
            ClassConstr.ClassConstr(id, Instantiate.inst(tys, ty))
    }
}

instance FreeVars[ClassConstr] {
    pub def fvs(a: ClassConstr): Set[Tyvar] = match a {
        case ClassConstr.ClassConstr(_, ty) => FreeVars.fvs(ty)
    }
}

mod ClassConstr {
    pub def id(c: ClassConstr): Id = match c { case ClassConstr(id, _) => id }
    pub def ty(c: ClassConstr): Type = match c { case ClassConstr(_, ty) => ty }
}

instance Substable[ClassConstr] {
    pub def apply(subst: Subst, con: ClassConstr): ClassConstr = {
        let id = ClassConstr.id(con);
        let ty = Substable.apply(subst, ClassConstr.ty(con));
        ClassConstr.ClassConstr(id, ty)
    }
}

pub enum EqConstr(Type, Type) with Eq, ToString, Hash, Order

instance FreeVars[EqConstr] {
    pub def fvs(a: EqConstr): Set[Tyvar] = match a {
        case EqConstr.EqConstr(l, r) => FreeVars.fvs(l) ++ FreeVars.fvs(r)
    }
}

instance Instantiate[EqConstr] {
    pub def inst(tys: List[Type], sch: EqConstr): EqConstr = match sch {
        case EqConstr.EqConstr(lhs, rhs) => EqConstr.EqConstr(
            Instantiate.inst(tys, lhs),
            Instantiate.inst(tys, rhs)
        )
    }
}

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

instance FreeVars[Constr] {
    pub def fvs(con: Constr): Set[Tyvar] = match con {
        case Constr.Class(cls) => FreeVars.fvs(cls)
        case Constr.Eq(eq) => FreeVars.fvs(eq)
    }
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

instance Instantiate[Constr] {
    pub def inst(tys: List[Type], sch: Constr): Constr = match sch {
        case Constr.Class(cls) => Constr.Class(Instantiate.inst(tys, cls))
        case Constr.Eq(eq) => Constr.Eq(Instantiate.inst(tys, eq))
    }
}


pub enum Qual[a](List[Constr], a) with Eq, ToString, Hash, Order

instance FreeVars[Qual[a]] with FreeVars[a] {
    pub def fvs(a: Qual[a]): Set[Tyvar] = match a {
        case Qual.Qual(q, ctx) => FreeVars.fvs(q) ++ FreeVars.fvs(ctx)
    }
}

instance Substable[Qual[a]] with Substable[a] {
    pub def apply(subst: Subst, a: Qual[a]): Qual[a] = match a {
        case Qual.Qual(q, ctx) => Qual.Qual(
            Substable.apply(subst, q),
            Substable.apply(subst, ctx)
        )
    }
}

mod Qual {
    pub def head(qua: Qual[q]): q = match qua { case Qual(_, q) => q }
    pub def context(qua: Qual[q]): List[Constr] = match qua {
        case Qual(ctx, _) => ctx 
    }
    pub def newUnqual(q: q): Qual[q] = Qual(Nil, q)
}

instance Instantiate[Qual[a]] with Instantiate[a] {
    pub def inst(tys: List[Type], sch: Qual[a]): Qual[a] = match sch {
        case Qual.Qual(q, ctx) => Qual.Qual(
            Instantiate.inst(tys, q),
            Instantiate.inst(tys, ctx)
        )
    }
}

