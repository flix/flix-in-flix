pub enum Substitution(Map[TypeVariable, Type]) with Eq, ToString, Hash, Order


pub trait Substitutable[a] {
    pub def apply(a: a, substitution: Substitution): a
}


instance Substitutable[List[a]] with Substitutable[a] {
    pub def apply(a: List[a], substitution: Substitution): List[a] = 
        a |> List.map(x -> substitution |> Substitutable.apply(x))
}


mod Substitution {
    pub def empty(): Substitution = Substitution(Map.empty())


    pub def get(tyVar: TypeVariable, subst: Substitution): Option[Type] 
        = match subst {
            case Substitution(map) => map |> Map.get(tyVar)
        }
}