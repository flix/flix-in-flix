pub enum Scheme[a](List[Kind], Qual[a]) with ToString

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
}

pub trait Instantiate[a] {
    pub def inst(tys: List[Type], sch: a): a
}

instance Instantiate[List[a]] with Instantiate[a] {
    pub def inst(tys: List[Type], sch: List[a]): List[a] = 
        List.map(s -> Instantiate.inst(tys, s), sch)
}
