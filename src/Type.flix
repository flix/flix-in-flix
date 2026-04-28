pub enum TypeVariable(Id, Kind) with Eq, ToString, Hash, Order


mod TypeVariable {
    pub def kind(typevariable: TypeVariable): Kind = match typevariable {
        case TypeVariable(_, kind) => kind
    }
}


instance Kinded[TypeVariable] {
    pub def kind(a: TypeVariable): Kind = a |> TypeVariable.kind
}


instance FreeTypeVariable[TypeVariable] {
    pub def freeTypeVariables(a: TypeVariable): List[TypeVariable] = a :: Nil
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


    pub def id(associatedMember: AssociatedMember): Id = match associatedMember {
        case AssociatedMember(id, _, _) => id
    }
}


instance Substitutable[AssociatedMember] {
    pub def apply(substitution: Substitution, a: AssociatedMember): AssociatedMember = 
        match a {
            case AssociatedMember.AssociatedMember(id, ty, kind) => 
                AssociatedMember.AssociatedMember(
                    id,
                    ty |> Substitutable.apply(substitution),
                    kind
                )
        }
}


instance Kinded[AssociatedMember] {
    pub def kind(a: AssociatedMember): Kind = a |> AssociatedMember.kind
}


instance FreeTypeVariable[AssociatedMember] {
    pub def freeTypeVariables(a: AssociatedMember): List[TypeVariable] =
        a |> AssociatedMember.ty |> FreeTypeVariable.freeTypeVariables
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
    pub def apply(substitution: Substitution, a: TypeApplication): TypeApplication = 
        match a {
            case TypeApplication.TypeApplication(function, argument) => 
                TypeApplication.TypeApplication(
                    function |> Substitutable.apply(substitution),
                    argument |> Substitutable.apply(substitution)
                )
        }
}


instance Kinded[TypeApplication] {
    pub def kind(a: TypeApplication): Kind = {
        let functionKind = a |> TypeApplication.function |> Kinded.kind;

        match functionKind {
            case Kind.KFun(_, result) => result
            case _ => bug!(
                "Expected a function kind, but found: ${functionKind}"
            )
        }
    }
}


instance FreeTypeVariable[TypeApplication] {
    pub def freeTypeVariables(a: TypeApplication): List[TypeVariable] =
        (a |> TypeApplication.function |> FreeTypeVariable.freeTypeVariables) :::
        (a |> TypeApplication.argument |> FreeTypeVariable.freeTypeVariables)
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


instance FreeTypeVariable[BinarySetFormula] {
    pub def freeTypeVariables(a: BinarySetFormula): List[TypeVariable] = 
        (a |> BinarySetFormula.left |> FreeTypeVariable.freeTypeVariables) :::
        (a |> BinarySetFormula.right |> FreeTypeVariable.freeTypeVariables)
}


instance Substitutable[BinarySetFormula] {
    pub def apply(substitution: Substitution, a: BinarySetFormula): BinarySetFormula = 
        match a {
            case BinarySetFormula.BinarySetFormula(left, op, right) => 
                BinarySetFormula.BinarySetFormula(
                    left |> Substitutable.apply(substitution),
                    op,
                    right |> Substitutable.apply(substitution)
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


pub enum EffectLabel(Id) with Eq, ToString, Hash, Order


pub enum SetFormula with Eq, ToString, Hash, Order {
    case Singleton(EffectLabel),
    case Binary(BinarySetFormula)
    case Complement(SetFormula)
    case Variable(TypeVariable)
    case Gen(Gen)
    case AssociatedMember(AssociatedMember)
    case Empty
}


instance Substitutable[SetFormula] {
    pub def apply(substitution: Substitution, a: SetFormula): SetFormula  
        = match a {
            case SetFormula.Singleton(_) => a

            case SetFormula.Binary(binarySetFormula) => 
                SetFormula.Binary(binarySetFormula |> Substitutable.apply(substitution))

            case SetFormula.Complement(setFormula) => 
                SetFormula.Complement(setFormula |> Substitutable.apply(substitution))

            case SetFormula.Variable(typeVariable) => 
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
    pub def kind(_a: SetFormula): Kind = Kind.Eff
}


instance FreeTypeVariable[SetFormula] {
    pub def freeTypeVariables(a: SetFormula): List[TypeVariable] =
        match a {
            case SetFormula.Singleton(_) => Nil

            case SetFormula.Binary(binarySetFormula) =>
                (binarySetFormula |> BinarySetFormula.left |> FreeTypeVariable.freeTypeVariables) :::
                (binarySetFormula |> BinarySetFormula.right |> FreeTypeVariable.freeTypeVariables)

            case SetFormula.Complement(setFormula) =>
                setFormula |> FreeTypeVariable.freeTypeVariables

            case SetFormula.Variable(typeVariable) =>
                typeVariable |> FreeTypeVariable.freeTypeVariables

            case SetFormula.Gen(_) => Nil

            case SetFormula.AssociatedMember(associatedMember) =>
                associatedMember |> FreeTypeVariable.freeTypeVariables

            case SetFormula.Empty => Nil
        }
}


pub enum Type with Eq, ToString, Hash, Order {
    case Variable(TypeVariable)
    case Constructor(TypeConstructor)
    case AssociatedMember(AssociatedMember)
    case Application(TypeApplication)
    case SetFormula(SetFormula)
    case Gen(Gen)
} 


mod Type {
    pub def mkTypeVar(name: String, kind: Kind): TypeVariable =
        TypeVariable.TypeVariable(Id.Id(name), kind)


    pub def mkTypeCon(name: String, kind: Kind): TypeConstructor =
        TypeConstructor.TypeConstructor(Id.Id(name), kind)


    pub def mkAssoc(name: String, ty: Type, kind: Kind): AssociatedMember =
        AssociatedMember.AssociatedMember(Id.Id(name), ty, kind)


    pub def unwrapSetFormula(ty: Type): SetFormula = match ty {
        case Type.SetFormula(setFormula) => setFormula
        case _ => bug!("Expected a SetFormula type, but found: ${ty}")
    }
}


instance Kinded[Type] {
   pub def kind(a: Type): Kind = match a {
        case Type.Variable(variable) => 
            variable |> Kinded.kind

        case Type.Constructor(constructor) => 
            constructor |> Kinded.kind

        case Type.AssociatedMember(associatedMember) =>
            associatedMember |> Kinded.kind

        case Type.Application(application) =>
            application |> Kinded.kind

        case Type.Gen(gen) => 
            gen |> Kinded.kind

        case Type.SetFormula(setFormula) =>
            setFormula |> Kinded.kind
    }
}


instance Substitutable[Type] {
    pub def apply(substitution: Substitution, a: Type): Type = match a {
        case Type.Variable(variable) => 
            substitution 
                |> Substitution.get(variable)
                |> Option.getWithDefault(a)

        case Type.Application(typeApplication) => Type.Application(
            typeApplication |> Substitutable.apply(substitution)
        )

        case Type.SetFormula(setFormula) =>
            Type.SetFormula(setFormula |> Substitutable.apply(substitution))

        case Type.Gen(_) => a

        case Type.Constructor(_) =>  a

        case Type.AssociatedMember(_) => a
    }
}


instance FreeTypeVariable[Type] {
    pub def freeTypeVariables(a: Type): List[TypeVariable] = match a {
        case Type.Variable(variable) =>
            variable |> FreeTypeVariable.freeTypeVariables

        case Type.Constructor(_) =>
            Nil

        case Type.AssociatedMember(associatedMember) =>
            associatedMember |> FreeTypeVariable.freeTypeVariables

        case Type.Application(application) =>
            application |> FreeTypeVariable.freeTypeVariables

        case Type.SetFormula(setFormula) =>
            setFormula |> FreeTypeVariable.freeTypeVariables

        case Type.Gen(_) =>
            Nil
    }
}
