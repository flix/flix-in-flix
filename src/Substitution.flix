pub enum Substitution(Map[TypeVariable, Type]) with Eq, ToString, Hash, Order


pub trait Substitutable[a] {
    pub def apply(a: a, substitution: Substitution): a
}


instance Substitutable[List[a]] with Substitutable[a] {
    pub def apply(a: List[a], substitution: Substitution): List[a] = 
        a |> List.map(x -> substitution |> Substitutable.apply(x))
}


mod Substitution {
    def map(s: Substitution): Map[TypeVariable, Type] 
        = match s {
            case Substitution.Substitution(m) => m
        }


    pub def empty(): Substitution = Substitution(Map.empty())


    pub def get(tyVar: TypeVariable, subst: Substitution): Option[Type] 
        = match subst {
            case Substitution(map) => map |> Map.get(tyVar)
        }

    
    pub def compose(s1: Substitution, s2: Substitution): Substitution = {
        let s2Map = s2 |> map;

        let composedMap = s2Map 
            |> Map.map(v -> s1 |> Substitutable.apply(v));

        Substitution.Substitution(Map.union(composedMap, s2Map))
    }
}