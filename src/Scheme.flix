pub enum Scheme[a](List[Kind], Qual[a]) with ToString

instance Substable[Scheme[a]] with Substable[a] {
    pub def apply(subst: Subst, a: Scheme[a]): Scheme[a] = match a {
        case Scheme.Scheme(kinds, qua) => Scheme.Scheme(
            kinds, Substable.apply(subst, qua)
        )
    }
}

instance FreeVars[Scheme[a]] with FreeVars[a] {
    pub def fvs(a: Scheme[a]): Set[Tyvar] = match a {
        case Scheme.Scheme(_, qua) => FreeVars.fvs(qua)
    }
}


mod Scheme {
    pub def head(sch: Scheme[a]): a = match sch {
        case Scheme(_, qua) => Qual.head(qua)
    }
    pub def qual(sch: Scheme[a]): Qual[a] = match sch {
        case Scheme(_, qua) => qua
    }
    pub def varKinds(sch: Scheme[a]): List[Kind] = match sch {
        case Scheme(kinds, _) => kinds
    }   
    pub def newUnqual(a: a): Scheme[a] = Scheme(Nil, Qual.newUnqual(a))
}

pub trait Instantiate[a] {
    pub def inst(tys: List[Type], sch: a): a
}

instance Instantiate[List[a]] with Instantiate[a] {
    pub def inst(tys: List[Type], sch: List[a]): List[a] = 
        List.map(s -> Instantiate.inst(tys, s), sch)
}
