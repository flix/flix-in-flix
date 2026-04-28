pub enum Tyvar(Id, Kind) with Eq, ToString, Hash, Order


mod Tyvar {
    pub def kind(typevariable: Tyvar): Kind = match typevariable {
        case Tyvar(_, kind) => kind
    }
}


instance Kinded[Tyvar] {
    pub def kind(a: Tyvar): Kind = Tyvar.kind(a)
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
    pub def kind(a: Tycon): Kind = Tycon.kind(a)
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
                    Substitutable.apply(substitution, ty),
                    kind
                )
        }
}


instance Kinded[Tyassoc] {
    pub def kind(a: Tyassoc): Kind = Tyassoc.kind(a)
}


instance FreeVars[Tyassoc] {
    pub def fvs(a: Tyassoc): List[Tyvar] =
        FreeVars.fvs(Tyassoc.ty(a))
}


pub enum Gen(Int32, Kind) with Eq, ToString, Hash, Order


mod Gen {
    pub def kind(gen: Gen): Kind = match gen {
        case Gen(_, kind) => kind
    }
}


instance Kinded[Gen] {
    pub def kind(a: Gen): Kind = Gen.kind(a)
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
            Kinded.kind(variable)

        case Type.Con(constructor) => 
            Kinded.kind(constructor)

        case Type.Assoc(associatedMember) =>
            Kinded.kind(associatedMember)

        case Type.Ap(function, _) => {
            let functionKind = Kinded.kind(function);

            match functionKind {
                case Kind.KFun(_, result) => result
                case _ => bug!(
                    "Expected a function kind, but found: ${functionKind}"
                )
            }
        }

        case Type.Gen(gen) => 
            Kinded.kind(gen)
    }
}


instance Substitutable[Type] {
    pub def apply(substitution: Substitution, a: Type): Type = match a {
        case Type.Var(variable) => 
            Option.getWithDefault(
                a,
                Substitution.get(variable, substitution)
            )

        case Type.Ap(function, argument) => Type.Ap(
            Substitutable.apply(substitution, function),
            Substitutable.apply(substitution, argument)
        )

        case Type.Gen(_) => a

        case Type.Con(_) =>  a

        case Type.Assoc(_) => a
    }
}


instance FreeVars[Type] {
    pub def fvs(a: Type): List[Tyvar] = match a {
        case Type.Var(variable) =>
            FreeVars.fvs(variable)

        case Type.Con(_) =>
            Nil

        case Type.Assoc(associatedMember) =>
            FreeVars.fvs(associatedMember)

        case Type.Ap(function, argument) =>
            FreeVars.fvs(function) :::
            FreeVars.fvs(argument)

        case Type.Gen(_) =>
            Nil
    }
}
