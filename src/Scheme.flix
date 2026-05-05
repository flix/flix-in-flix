pub enum Scheme(List[Kind], Qual[Type]) with ToString

instance Substable[Scheme] {
    pub def apply(subst: Subst, a: Scheme): Scheme = match a {
        case Scheme.Scheme(kinds, qua) => Scheme.Scheme(
            kinds, Substable.apply(subst, qua)
        )
    }
}

instance FreeVars[Scheme] {
    pub def fvs(a: Scheme): Set[Tyvar] = match a {
        case Scheme.Scheme(_, qua) => FreeVars.fvs(qua)
    }
}


mod Scheme {
    pub def head(sch: Scheme): Type = match sch {
        case Scheme(_, qua) => Qual.head(qua)
    }
    pub def qual(sch: Scheme): Qual[Type] = match sch {
        case Scheme(_, qua) => qua
    }
    pub def varKinds(sch: Scheme): List[Kind] = match sch {
        case Scheme(kinds, _) => kinds
    }   
    pub def newUnqual(t: Type): Scheme = Scheme(Nil, Qual.newUnqual(t))
}

pub trait Instantiate[a] {
    pub def inst(tys: List[Type], sch: a): a
}

instance Instantiate[List[a]] with Instantiate[a] {
    pub def inst(tys: List[Type], sch: List[a]): List[a] = 
        List.map(s -> Instantiate.inst(tys, s), sch)
}
