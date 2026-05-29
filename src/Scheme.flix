pub enum Scheme(List[Kind], Qual[Type])

instance Substable[Scheme] {
    pub def apply(subst: Subst, a: Scheme): Scheme = match a {
        case Scheme.Scheme(kinds, qua) => Scheme.Scheme(
            kinds,
            Substable.apply(subst, qua)
        )
    }
}

pub trait Instantiate[a] {
    pub def inst(tys: List[Type], sch: a): a
}

instance Instantiate[List[a]] with Instantiate[a] {
    pub def inst(tys: List[Type], sch: List[a]): List[a] =
        List.map(s -> Instantiate.inst(tys, s), sch)
}

pub def mkScheme(t: Type): Scheme = Scheme.Scheme(Nil, Qual.Qual(Nil, t))
