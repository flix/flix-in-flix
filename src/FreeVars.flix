pub trait FreeVars[a] {
    pub def fvs(a: a): Set[Tyvar]
}


instance FreeVars[List[a]] with FreeVars[a] {
    pub def fvs(a: List[a]): Set[Tyvar] =
        List.foldLeft(
            (acc, x) -> Set.union(acc, FreeVars.fvs(x)),
            Set.empty(),
            a
        )
}

instance FreeVars[Map[k, v]] with FreeVars[v] {
    pub def fvs(m: Map[k, v]): Set[Tyvar] =
        Map.foldLeft((s, v) -> Set.union(FreeVars.fvs(v), s), Set.empty(), m)
}