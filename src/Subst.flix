pub type alias Subst = Map[Tyvar, Type]

pub trait Substable[a] {
    pub def apply(subst: Subst, a: a): a
}

instance Substable[List[a]] with Substable[a] {
    pub def apply(subst: Subst, list: List[a]): List[a] =
        List.map(x -> Substable.apply(subst, x), list)
}

pub def compose(sub1: Subst, sub2: Subst): Subst = {
    let cmap = Map.map(ty -> Substable.apply(sub1, ty), sub2);
    Map.union(cmap, sub1)
}

pub def merge(sub1: Subst, sub2: Subst): Option[Subst] = {
    let keys = Set.filter(k -> Map.memberOf(k, sub2), Map.keysOf(sub1));
    let same = Set.forAll(k -> Map.get(k, sub1) == Map.get(k, sub2), keys);
    if (same) Some(Map.union(sub1, sub2)) else None
}
