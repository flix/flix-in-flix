pub enum Kind with Eq, ToString, Hash, Order {
    case Eff,
    case Star,
    case KFun(Kind, Kind)
}


pub trait Kinded[a] {
    pub def kind(a: a): Kind
}
