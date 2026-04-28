pub enum Substitution(Map[TypeVariable, Type]) with Eq, ToString, Hash, Order


pub trait Substitutable[a] {
    pub def apply(substitution: Substitution, a: a): a
}


instance Substitutable[List[a]] with Substitutable[a] {
    pub def apply(substitution: Substitution, a: List[a]): List[a] = 
        a |> List.map(x -> x |> Substitutable.apply(substitution))
}


mod Substitution {
    def map(s: Substitution): Map[TypeVariable, Type] 
        = match s {
            case Substitution.Substitution(m) => m
        }

    
    pub def singleton(tyVar: TypeVariable, ty: Type): Substitution = 
        Substitution.Substitution(Map.singleton(tyVar, ty))


    pub def empty(): Substitution = Substitution(Map.empty())


    pub def get(tyVar: TypeVariable, subst: Substitution): Option[Type] 
        = match subst {
            case Substitution(map) => map |> Map.get(tyVar)
        }

    
    pub def compose(s1: Substitution, s2: Substitution): Substitution = {
        let s2Map = s2 |> map;

        let composedMap = s2Map 
            |> Map.map(v -> v |> Substitutable.apply(s1));

        Substitution.Substitution(Map.union(composedMap, s1 |> map))
    }


    pub def merge(s1: Substitution, s2: Substitution): Option[Substitution] = {
        // check overlapping keys and ensure they are equal
        let overlappingKeys = (s1 |> map) 
            |> Map.keysOf
            |> Set.filter(k -> (s2 |> map) |> Map.memberOf(k));

        let isConsistent = overlappingKeys
            |> Set.forAll(k -> 
                (s1 |> map) |> Map.get(k) == 
                (s2 |> map) |> Map.get(k)
            );

        if (isConsistent) {
            Some(Substitution.Substitution(
                (s1 |> map) |> Map.union(s2 |> map)
            ))
        } else {
            None
        }
    }
}
