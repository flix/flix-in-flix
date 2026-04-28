pub enum Tyvar(Id, Kind) with Eq, ToString, Hash, Order


mod Tyvar {
    pub def kind(typevariable: Tyvar): Kind = match typevariable {
        case Tyvar(_, kind) => kind
    }
}


instance Kinded[Tyvar] {
    pub def kind(a: Tyvar): Kind = a |> Tyvar.kind
}


instance FreeVars[Tyvar] {
    pub def fvs(a: Tyvar): List[Tyvar] = a :: Nil
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


instance FreeVars[Tyassoc] {
    pub def fvs(a: Tyassoc): List[Tyvar] =
        a |> Tyassoc.ty |> FreeVars.fvs
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


pub enum Type with Eq, ToString, Hash, Order {
    case Var(Tyvar)
    case Con(Tycon)
    case Assoc(Tyassoc)
    case Ap(Type, Type)
    case Gen(Gen)
} 


mod Type {
    pub def mkTyvar(name: Id, kind: Kind): Tyvar =
        Tyvar.Tyvar(name, kind)


    pub def mkTycon(name: Id, kind: Kind): Tycon =
        Tycon.Tycon(name, kind)


    pub def mkTyassoc(name: Id, ty: Type, kind: Kind): Tyassoc =
        Tyassoc.Tyassoc(name, ty, kind)


    def efUnaryKind(): Kind = Kind.KFun(Kind.Eff, Kind.Eff)


    def efBinaryKind(): Kind = Kind.KFun(
        Kind.Eff,
        Kind.KFun(Kind.Eff, Kind.Eff)
    )


    pub def efUnion(left: Type, right: Type): Type =
        Type.Ap(
            Type.Ap(
                Type.Con(Type.mkTycon("+", efBinaryKind())),
                left
            ),
            right
        )


    pub def efIntersect(left: Type, right: Type): Type =
        Type.Ap(
            Type.Ap(
                Type.Con(Type.mkTycon("&", efBinaryKind())),
                left
            ),
            right
        )


    pub def efXor(left: Type, right: Type): Type =
        Type.Ap(
            Type.Ap(
                Type.Con(Type.mkTycon("^", efBinaryKind())),
                left
            ),
            right
        )


    pub def efCompl(ty: Type): Type =
        Type.Ap(Type.Con(Type.mkTycon("~", efUnaryKind())), ty)


    pub def efEmpty(): Type =
        Type.Con(Type.mkTycon("{}", Kind.Eff))


    pub def efSingleton(name: Id): Type =
        Type.Con(Type.mkTycon(name, Kind.Eff))
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

        case Type.Gen(_) => a

        case Type.Con(_) =>  a

        case Type.Assoc(_) => a
    }
}


instance FreeVars[Type] {
    pub def fvs(a: Type): List[Tyvar] = match a {
        case Type.Var(variable) =>
            variable |> FreeVars.fvs

        case Type.Con(_) =>
            Nil

        case Type.Assoc(associatedMember) =>
            associatedMember |> FreeVars.fvs

        case Type.Ap(function, argument) =>
            (function |> FreeVars.fvs) :::
            (argument |> FreeVars.fvs)

        case Type.Gen(_) =>
            Nil
    }
}
