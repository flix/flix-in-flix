pub enum Kind with Eq, ToString, Order {
    case Eff,
    case Star,
    case KFun(Kind, Kind)
}

pub def kArrow(): Kind = Kind.KFun(
    Kind.Star, 
    Kind.KFun(Kind.Eff, Kind.KFun(Kind.Star, Kind.Star))
)

pub def kEfUnary(): Kind = Kind.KFun(Kind.Eff, Kind.Eff)

pub def kEfBinary(): Kind
    = Kind.KFun(Kind.Eff, Kind.KFun(Kind.Eff, Kind.Eff))