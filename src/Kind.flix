pub enum Kind with Eq, ToString, Hash, Order {
    case Eff,
    case Star,
    case KFun(Kind, Kind)
}

mod Kind {
    pub def arrow(): Kind = Kind.KFun(
        Kind.Star, 
        Kind.KFun(Kind.Eff, Kind.KFun(Kind.Star, Kind.Star))
    )

    pub def efUnary(): Kind = Kind.KFun(Kind.Eff, Kind.Eff)

    pub def efBinary(): Kind 
        = Kind.KFun(Kind.Eff, Kind.KFun(Kind.Eff, Kind.Eff))
}

pub trait Kinded[a] {
    pub def kind(a: a): Kind
}
