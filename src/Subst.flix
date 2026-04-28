pub enum Subst(Map[Tyvar, Type]) with Eq, ToString, Hash, Order

pub trait Substable[a] {
    pub def apply(subst: Subst, a: a): a
}

instance Substable[List[a]] with Substable[a] {
    pub def apply(subst: Subst, list: List[a]): List[a] =
        List.map(x -> Substable.apply(subst, x), list)
}

mod Subst {
    def map(subst: Subst): Map[Tyvar, Type] = match subst {
        case Subst.Subst(smap) => smap
    }

    pub def singleton(tvar: Tyvar, ty: Type): Subst = Subst.Subst(Map.singleton(tvar, ty))

    pub def empty(): Subst = Subst(Map.empty())

    pub def get(tvar: Tyvar, subst: Subst): Option[Type] = match subst {
        case Subst(smap) => Map.get(tvar, smap)
    }

    pub def compose(sub1: Subst, sub2: Subst): Subst = {
        let smap = map(sub2);
        let cmap = Map.map(ty -> Substable.apply(sub1, ty), smap);
        Subst.Subst(Map.union(cmap, map(sub1)))
    }

    pub def merge(sub1: Subst, sub2: Subst): Option[Subst] = {
        let map1 = map(sub1);
        let map2 = map(sub2);
        let keys = Set.filter(k -> Map.memberOf(k, map2), Map.keysOf(map1));
        let same = Set.forAll(k -> Map.get(k, map1) == Map.get(k, map2), keys);
        if (same) Some(Subst.Subst(Map.union(map1, map2))) else None
    }
}
