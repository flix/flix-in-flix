pub enum Subst(Map[Tyvar, Type]) with Eq, ToString, Hash, Order


pub trait Substable[a] {
    pub def apply(substitution: Subst, a: a): a
}


instance Substable[List[a]] with Substable[a] {
    pub def apply(substitution: Subst, a: List[a]): List[a] = 
        a |> List.map(x -> x |> Substable.apply(substitution))
}


mod Subst {
    def map(s: Subst): Map[Tyvar, Type] 
        = match s {
            case Subst.Subst(m) => m
        }

    
    pub def singleton(tyVar: Tyvar, ty: Type): Subst = 
        Subst.Subst(Map.singleton(tyVar, ty))


    pub def empty(): Subst = Subst(Map.empty())


    pub def get(tyVar: Tyvar, subst: Subst): Option[Type] 
        = match subst {
            case Subst(map) => map |> Map.get(tyVar)
        }

    
    pub def compose(s1: Subst, s2: Subst): Subst = {
        let s2Map = s2 |> map;

        let composedMap = s2Map 
            |> Map.map(v -> v |> Substable.apply(s1));

        Subst.Subst(Map.union(composedMap, s1 |> map))
    }


    pub def merge(s1: Subst, s2: Subst): Option[Subst] = {
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
            Some(Subst.Subst(
                (s1 |> map) |> Map.union(s2 |> map)
            ))
        } else {
            None
        }
    }
}
