pub trait FreeTypeVariable[a] {
    pub def freeTypeVariables(a: a): List[TypeVariable]
}


instance FreeTypeVariable[List[a]] with FreeTypeVariable[a] {
    pub def freeTypeVariables(a: List[a]): List[TypeVariable] = 
        a |> List.flatMap(FreeTypeVariable.freeTypeVariables)
}
