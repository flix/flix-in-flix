pub type alias Assumps = Map[Id, Scheme]

instance Substable[Map[k, v]] with Substable[v] {
    pub def apply(subst: Subst, a: Map[k, v]): Map[k, v] = 
        Map.map(v -> Substable.apply(subst, v), a)
}
