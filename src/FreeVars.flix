pub trait FreeVars[a] {
    pub def fvs(a: a): List[Tyvar]
}


instance FreeVars[List[a]] with FreeVars[a] {
    pub def fvs(a: List[a]): List[Tyvar] =
        a |> List.flatMap(FreeVars.fvs)
}
