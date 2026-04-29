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
