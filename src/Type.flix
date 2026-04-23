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


pub enum AssociatedMember(Id, Type, Kind) with Eq, ToString, Hash, Order


mod AssociatedMember {
    pub def kind(associatedMember: AssociatedMember): Kind = match associatedMember {
        case AssociatedMember(_, _, kind) => kind
    }


    pub def ty(associatedMember: AssociatedMember): Type = match associatedMember {
        case AssociatedMember(_, ty, _) => ty
    }
}


instance Substitutable[AssociatedMember] {
    pub def apply(a: AssociatedMember, substitution: Substitution): AssociatedMember = 
        match a {
            case AssociatedMember.AssociatedMember(id, ty, kind) => 
                AssociatedMember.AssociatedMember(
                    id,
                    substitution |> Substitutable.apply(ty),
                    kind
                )
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

instance Substitutable[TypeApplication] {
    pub def apply(a: TypeApplication, substitution: Substitution): TypeApplication = 
        match a {
            case TypeApplication.TypeApplication(function, argument) => 
                TypeApplication.TypeApplication(
                    substitution |> Substitutable.apply(function),
                    substitution |> Substitutable.apply(argument)
                )
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


instance Substitutable[BinarySetFormula] {
    pub def apply(a: BinarySetFormula, substitution: Substitution): BinarySetFormula = 
        match a {
            case BinarySetFormula.BinarySetFormula(left, op, right) => 
                BinarySetFormula.BinarySetFormula(
                    substitution |> Substitutable.apply(left),
                    op,
                    substitution |> Substitutable.apply(right)
                )
        }
}


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
    case Gen(Gen)
    case AssociatedMember(AssociatedMember)
    case Empty
}


instance Substitutable[SetFormula] {
    pub def apply(a: SetFormula, substitution: Substitution): SetFormula  
        = match a {
            case SetFormula.Singleton(_) => a

            case SetFormula.Binary(binarySetFormula) => 
                SetFormula.Binary(substitution |> Substitutable.apply(binarySetFormula))

            case SetFormula.Complement(setFormula) => 
                SetFormula.Complement(substitution |> Substitutable.apply(setFormula))

            case SetFormula.TypeVariable(typeVariable) => 
                substitution 
                    |> Substitution.get(typeVariable)
                    |> Option.map(Type.unwrapSetFormula)
                    |> Option.getWithDefault(a)

            case SetFormula.Gen(_) => a

            case SetFormula.AssociatedMember(associatedMember) =>
                SetFormula.AssociatedMember(associatedMember)

            case SetFormula.Empty =>
                SetFormula.Empty
        }
}



instance Kinded[SetFormula] {
    pub def kind(_a: SetFormula): Kind = Kind.EffectStar
}


pub enum Type with Eq, ToString, Hash, Order {
    case Variable(TypeVariable)
    case TypeConstructor(TypeConstructor)
    case AssociatedMember(AssociatedMember)
    case TypeApplication(TypeApplication)
    case SetFormula(SetFormula)
    case Gen(Gen)
} 


mod Type {
    pub def unwrapSetFormula(ty: Type): SetFormula = match ty {
        case Type.SetFormula(setFormula) => setFormula
        case _ => bug!("Expected a SetFormula type, but found: ${ty}")
    }
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

        case Type.SetFormula(setFormula) =>
            setFormula |> Kinded.kind
    }
}


instance Substitutable[Type] {
    pub def apply(a: Type, substitution: Substitution): Type = match a {
        case Type.Variable(variable) => 
            substitution 
                |> Substitution.get(variable)
                |> Option.getWithDefault(a)

        case Type.TypeApplication(typeApplication) => Type.TypeApplication(
            substitution |> Substitutable.apply(typeApplication)
        )

        case Type.SetFormula(setFormula) =>
            Type.SetFormula(substitution |> Substitutable.apply(setFormula))

        case Type.Gen(_) => a

        case Type.TypeConstructor(_) =>  a

        case Type.AssociatedMember(_) => a
    }
}
