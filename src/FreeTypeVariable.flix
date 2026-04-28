pub trait FreeTypeVariable[a] {
    pub def freeTypeVariables(a: a): List[Tyvar]
}


instance FreeTypeVariable[List[a]] with FreeTypeVariable[a] {
    pub def freeTypeVariables(a: List[a]): List[Tyvar] = 
        a |> List.flatMap(FreeTypeVariable.freeTypeVariables)
}
