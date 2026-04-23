pub enum TypeVariable(Id, Kind) with Eq, ToString, Hash, Order


mod TypeVariable {
    pub def kind(typevariable: TypeVariable): Kind = match typevariable {
        case TypeVariable(_, kind) => kind
    }
}


instance Kinded[TypeVariable] {
    pub def kind(a: TypeVariable): Kind = a |> TypeVariable.kind
}


pub enum TypeConstructor(Id, Kind) with Eq, ToString, Hash, Order


mod TypeConstructor {
    pub def kind(typeconstructor: TypeConstructor): Kind = match typeconstructor {
        case TypeConstructor(_, kind) => kind
    }
}


instance Kinded[TypeConstructor] {
    pub def kind(a: TypeConstructor): Kind = a |> TypeConstructor.kind
}


pub enum AssociatedMember(Id, Kind) with Eq, ToString, Hash, Order


mod AssociatedMember {
    pub def kind(associatedMember: AssociatedMember): Kind = match associatedMember {
        case AssociatedMember(_, kind) => kind
    }
}


instance Kinded[AssociatedMember] {
    pub def kind(a: AssociatedMember): Kind = a |> AssociatedMember.kind
}


pub enum TypeApplication(Type, Type) with Eq, ToString, Hash, Order


mod TypeApplication {
    pub def function(typeapplication: TypeApplication): Type 
        = match typeapplication {
            case TypeApplication(function, _) => function
        }

    
    pub def argument(typeapplication: TypeApplication): Type
        = match typeapplication {
            case TypeApplication(_, argument) => argument
        }
}


instance Kinded[TypeApplication] {
    pub def kind(a: TypeApplication): Kind = {
        let functionKind = a |> TypeApplication.function |> Kinded.kind;

        match functionKind {
            case Kind.Function(kind) => kind |> FunctionKind.result
            case _ => bug!(
                "Expected a function kind, but found: ${functionKind}"
            )
        }
    }
}


pub enum Gen(Int32, Kind) with Eq, ToString, Hash, Order


mod Gen {
    pub def kind(gen: Gen): Kind = match gen {
        case Gen(_, kind) => kind
    }
}


instance Kinded[Gen] {
    pub def kind(a: Gen): Kind = a |> Gen.kind
}


pub enum SetBinaryOp with Eq, ToString, Hash, Order {
    case Union,
    case Intersection,
    case Xor
}


pub enum BinarySetFormula(SetFormula, SetBinaryOp, SetFormula) 
    with Eq, ToString, Hash, Order


mod BinarySetFormula {
    pub def left(binarySetFormula: BinarySetFormula): SetFormula = 
        match binarySetFormula {
            case BinarySetFormula(l, _, _) => l
        }

    
    pub def op(binarySetFormula: BinarySetFormula): SetBinaryOp =
        match binarySetFormula {
            case BinarySetFormula(_, op, _) => op
        }


    pub def right(binarySetFormula: BinarySetFormula): SetFormula =
        match binarySetFormula {    
            case BinarySetFormula(_, _, r) => r
        }
}


pub enum EffectKind with Eq, ToString, Hash, Order {
    case Regular,
    case Region
}


pub enum EffectLabel(Id, EffectKind) with Eq, ToString, Hash, Order


pub enum SetFormula with Eq, ToString, Hash, Order {
    case Singleton(EffectLabel),
    case Binary(BinarySetFormula)
    case Complement(SetFormula)
    case TypeVariable(TypeVariable)
    case AssociatedMember(AssociatedMember)
    case Empty
}


instance Kinded[SetFormula] {
    pub def kind(_a: SetFormula): Kind = Kind.EffectStar
}


pub enum Type with Eq, ToString, Hash, Order {
    case Variable(TypeVariable)
    case TypeConstructor(TypeConstructor)
    case AssociatedMember(AssociatedMember)
    case TypeApplication(TypeApplication)
    case Gen(Gen)
} 


instance Kinded[Type] {
   pub def kind(a: Type): Kind = match a {
        case Type.Variable(variable) => 
            variable |> Kinded.kind

        case Type.TypeConstructor(typeconstructor) => 
            typeconstructor |> Kinded.kind

        case Type.AssociatedMember(associatedMember) =>
            associatedMember |> Kinded.kind

        case Type.TypeApplication(typeApplication) =>
            typeApplication |> Kinded.kind

        case Type.Gen(gen) => 
            gen |> Kinded.kind
    }
}
