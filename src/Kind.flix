pub enum FunctionKind(Kind, Kind) with Eq, ToString, Hash, Order


mod FunctionKind {
    pub def parameter(functionKind: FunctionKind): Kind = match functionKind {
        case FunctionKind(left, _) => left
    }


    pub def result(functionKind: FunctionKind): Kind = match functionKind {
        case FunctionKind(_, right) => right
    }
}


pub enum Kind with Eq, ToString, Hash, Order {
    case EffectStar,
    case TypeStar,
    case Function(FunctionKind)
}


pub trait Kinded[a] {
    pub def kind(a: a): Kind
}
