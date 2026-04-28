pub enum Tyvar(Id, Kind) with Eq, ToString, Hash, Order


mod Tyvar {
    pub def kind(typevariable: Tyvar): Kind = match typevariable {
        case Tyvar(_, kind) => kind
    }
}


instance Kinded[Tyvar] {
    pub def kind(a: Tyvar): Kind = a |> Tyvar.kind
}


instance FreeTypeVariable[Tyvar] {
    pub def freeTypeVariables(a: Tyvar): List[Tyvar] = a :: Nil
}


pub enum Tycon(Id, Kind) with Eq, ToString, Hash, Order


mod Tycon {
    pub def kind(typeconstructor: Tycon): Kind = match typeconstructor {
        case Tycon(_, kind) => kind
    }
}


instance Kinded[Tycon] {
    pub def kind(a: Tycon): Kind = a |> Tycon.kind
}


pub enum Tyassoc(Id, Type, Kind) with Eq, ToString, Hash, Order


mod Tyassoc {
    pub def kind(associatedMember: Tyassoc): Kind = match associatedMember {
        case Tyassoc(_, _, kind) => kind
    }


    pub def ty(associatedMember: Tyassoc): Type = match associatedMember {
        case Tyassoc(_, ty, _) => ty
    }


    pub def id(associatedMember: Tyassoc): Id = match associatedMember {
        case Tyassoc(id, _, _) => id
    }
}


instance Substitutable[Tyassoc] {
    pub def apply(substitution: Substitution, a: Tyassoc): Tyassoc = 
        match a {
            case Tyassoc.Tyassoc(id, ty, kind) => 
                Tyassoc.Tyassoc(
                    id,
                    ty |> Substitutable.apply(substitution),
                    kind
                )
        }
}


instance Kinded[Tyassoc] {
    pub def kind(a: Tyassoc): Kind = a |> Tyassoc.kind
}


instance FreeTypeVariable[Tyassoc] {
    pub def freeTypeVariables(a: Tyassoc): List[Tyvar] =
        a |> Tyassoc.ty |> FreeTypeVariable.freeTypeVariables
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
    pub def freeTypeVariables(a: BinarySetFormula): List[Tyvar] = 
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
    case Variable(Tyvar)
    case Gen(Gen)
    case Tyassoc(Tyassoc)
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

            case SetFormula.Tyassoc(associatedMember) =>
                SetFormula.Tyassoc(associatedMember)

            case SetFormula.Empty =>
                SetFormula.Empty
        }
}


instance Kinded[SetFormula] {
    pub def kind(_a: SetFormula): Kind = Kind.Eff
}


instance FreeTypeVariable[SetFormula] {
    pub def freeTypeVariables(a: SetFormula): List[Tyvar] =
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

            case SetFormula.Tyassoc(associatedMember) =>
                associatedMember |> FreeTypeVariable.freeTypeVariables

            case SetFormula.Empty => Nil
        }
}


pub enum Type with Eq, ToString, Hash, Order {
    case Var(Tyvar)
    case Con(Tycon)
    case Assoc(Tyassoc)
    case Ap(Type, Type)
    case SetFormula(SetFormula)
    case Gen(Gen)
} 


mod Type {
    pub def mkTyvar(name: String, kind: Kind): Tyvar =
        Tyvar.Tyvar(Id.Id(name), kind)


    pub def mkTycon(name: String, kind: Kind): Tycon =
        Tycon.Tycon(Id.Id(name), kind)


    pub def mkTyassoc(name: String, ty: Type, kind: Kind): Tyassoc =
        Tyassoc.Tyassoc(Id.Id(name), ty, kind)


    pub def unwrapSetFormula(ty: Type): SetFormula = match ty {
        case Type.SetFormula(setFormula) => setFormula
        case _ => bug!("Expected a SetFormula type, but found: ${ty}")
    }
}


instance Kinded[Type] {
   pub def kind(a: Type): Kind = match a {
        case Type.Var(variable) => 
            variable |> Kinded.kind

        case Type.Con(constructor) => 
            constructor |> Kinded.kind

        case Type.Assoc(associatedMember) =>
            associatedMember |> Kinded.kind

        case Type.Ap(function, _) => {
            let functionKind = function |> Kinded.kind;

            match functionKind {
                case Kind.KFun(_, result) => result
                case _ => bug!(
                    "Expected a function kind, but found: ${functionKind}"
                )
            }
        }

        case Type.Gen(gen) => 
            gen |> Kinded.kind

        case Type.SetFormula(setFormula) =>
            setFormula |> Kinded.kind
    }
}


instance Substitutable[Type] {
    pub def apply(substitution: Substitution, a: Type): Type = match a {
        case Type.Var(variable) => 
            substitution 
                |> Substitution.get(variable)
                |> Option.getWithDefault(a)

        case Type.Ap(function, argument) => Type.Ap(
            function |> Substitutable.apply(substitution),
            argument |> Substitutable.apply(substitution)
        )

        case Type.SetFormula(setFormula) =>
            Type.SetFormula(setFormula |> Substitutable.apply(substitution))

        case Type.Gen(_) => a

        case Type.Con(_) =>  a

        case Type.Assoc(_) => a
    }
}


instance FreeTypeVariable[Type] {
    pub def freeTypeVariables(a: Type): List[Tyvar] = match a {
        case Type.Var(variable) =>
            variable |> FreeTypeVariable.freeTypeVariables

        case Type.Con(_) =>
            Nil

        case Type.Assoc(associatedMember) =>
            associatedMember |> FreeTypeVariable.freeTypeVariables

        case Type.Ap(function, argument) =>
            (function |> FreeTypeVariable.freeTypeVariables) :::
            (argument |> FreeTypeVariable.freeTypeVariables)

        case Type.SetFormula(setFormula) =>
            setFormula |> FreeTypeVariable.freeTypeVariables

        case Type.Gen(_) =>
            Nil
    }
}
