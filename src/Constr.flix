pub type alias ClassConstr = (Id, Type)
pub type alias EqConstr = (Type, Type)

instance Substable[(a, b)] with Substable[a], Substable[b] {
    pub def apply(subst: Subst, a: (a, b)): (a, b) = match a {
        case (x, y) => (
            Substable.apply(subst, x), Substable.apply(subst, y)
        )
    }
}

pub enum Constr with Eq, ToString, Order {
    case Class(ClassConstr),
    case Eq(EqConstr)
}

instance FreeVars[Constr] {
    pub def fvs(con: Constr): Set[Tyvar] = match con {
        case Constr.Class((_, ty)) => FreeVars.fvs(ty)
        case Constr.Eq((lhs, rhs)) => FreeVars.fvs(lhs) ++ FreeVars.fvs(rhs)
    }
}

instance Substable[Constr] {
    pub def apply(sub: Subst, con: Constr): Constr = match con {
        case Constr.Class((i, t)) => Constr.Class((i, Substable.apply(sub, t)))
        case Constr.Eq((l, r)) => Constr.Eq((
            Substable.apply(sub, l), Substable.apply(sub, r)
        ))
    }
}

instance Instantiate[Constr] {
    pub def inst(tys: List[Type], sch: Constr): Constr = match sch {
        case Constr.Class((i, t)) => Constr.Class((i, Instantiate.inst(tys, t)))
        case Constr.Eq((l, r)) => Constr.Eq((
            Instantiate.inst(tys, l), Instantiate.inst(tys, r)
        ))
    }
}

pub enum Qual[a](List[Constr], a)

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

instance Instantiate[Qual[a]] with Instantiate[a] {
    pub def inst(tys: List[Type], sch: Qual[a]): Qual[a] = match sch {
        case Qual.Qual(q, ctx) => Qual.Qual(
            Instantiate.inst(tys, q),
            Instantiate.inst(tys, ctx)
        )
    }
}

