pub enum Tyvar(Id, Kind) with Eq, ToString, Hash, Order

mod Tyvar {
    pub def kind(v: Tyvar): Kind = match v { case Tyvar(_, k) => k }
}

instance Kinded[Tyvar] {
    pub def kind(v: Tyvar): Kind = Tyvar.kind(v)
}

instance FreeVars[Tyvar] {
    pub def fvs(v: Tyvar): List[Tyvar] = v :: Nil
}

pub enum Tycon(Id, Kind) with Eq, ToString, Hash, Order

mod Tycon {
    pub def kind(c: Tycon): Kind = match c { case Tycon(_, k) => k }
}

instance Kinded[Tycon] {
    pub def kind(c: Tycon): Kind = Tycon.kind(c)
}

pub enum Tyassoc(Id, Type, Kind) with Eq, ToString, Hash, Order

mod Tyassoc {
    pub def kind(a: Tyassoc): Kind = match a { case Tyassoc(_, _, k) => k }
    pub def ty(a: Tyassoc): Type = match a { case Tyassoc(_, t, _) => t }
    pub def id(a: Tyassoc): Id = match a { case Tyassoc(id, _, _) => id }
}

instance Substable[Tyassoc] {
    pub def apply(s: Subst, a: Tyassoc): Tyassoc = match a {
        case Tyassoc.Tyassoc(id, t, k) 
            => Tyassoc.Tyassoc(id, Substable.apply(s, t), k)
    }
}

instance Kinded[Tyassoc] {
    pub def kind(a: Tyassoc): Kind = Tyassoc.kind(a)
}

instance FreeVars[Tyassoc] {
    pub def fvs(a: Tyassoc): List[Tyvar] = FreeVars.fvs(Tyassoc.ty(a))
}

pub enum Gen(Int32, Kind) with Eq, ToString, Hash, Order

mod Gen {
    pub def kind(g: Gen): Kind = match g { case Gen(_, k) => k }
}

instance Kinded[Gen] {
    pub def kind(g: Gen): Kind = Gen.kind(g)
}

pub enum Type with Eq, ToString, Hash, Order {
    case Var(Tyvar)
    case Con(Tycon)
    case Assoc(Tyassoc)
    case Ap(Type, Type)
    case Gen(Gen)
}

mod Type {
    pub def mkTyvar(name: Id, k: Kind): Tyvar = Tyvar.Tyvar(name, k)
    pub def mkTycon(name: Id, k: Kind): Tycon = Tycon.Tycon(name, k)
    pub def mkTyassoc(name: Id, t: Type, k: Kind): Tyassoc
        = Tyassoc.Tyassoc(name, t, k)

    def efUnaryKind(): Kind = Kind.KFun(Kind.Eff, Kind.Eff)
    def efBinaryKind(): Kind 
        = Kind.KFun(Kind.Eff, Kind.KFun(Kind.Eff, Kind.Eff))
    def ef1(sym: Id, t: Type): Type 
        = Type.Ap(Type.Con(Type.mkTycon(sym, efUnaryKind())), t)
    def ef2(sym: Id, l: Type, r: Type): Type 
        = Type.Ap(Type.Ap(Type.Con(Type.mkTycon(sym, efBinaryKind())), l), r)

    pub def efUnion(l: Type, r: Type): Type = ef2("+", l, r)
    pub def efIntersect(l: Type, r: Type): Type = ef2("&", l, r)
    pub def efXor(l: Type, r: Type): Type = ef2("^", l, r)
    pub def efCompl(t: Type): Type = ef1("~", t)

    pub def efEmpty(): Type = Type.Con(Type.mkTycon("{}", Kind.Eff))
    pub def efSingleton(name: Id): Type = Type.Con(Type.mkTycon(name, Kind.Eff))
}

instance Kinded[Type] {
    pub def kind(t: Type): Kind = match t {
        case Type.Var(v) => Kinded.kind(v)
        case Type.Con(c) => Kinded.kind(c)
        case Type.Assoc(a) => Kinded.kind(a)
        case Type.Ap(f, _) => let fk = Kinded.kind(f); match fk {
            case Kind.KFun(_, k) => k
            case _ => bug!("Expected a function kind, but found: ${fk}")
        }
        case Type.Gen(g) => Kinded.kind(g)
    }
}

instance Substable[Type] {
    pub def apply(s: Subst, t: Type): Type = match t {
        case Type.Var(v) => Option.getWithDefault(t, Subst.get(v, s))
        case Type.Ap(f, x) 
            => Type.Ap(Substable.apply(s, f), Substable.apply(s, x))
        case Type.Gen(_) => t
        case Type.Con(_) => t
        case Type.Assoc(_) => t
    }
}

instance FreeVars[Type] {
    pub def fvs(t: Type): List[Tyvar] = match t {
        case Type.Var(v) => FreeVars.fvs(v)
        case Type.Con(_) => Nil
        case Type.Assoc(a) => FreeVars.fvs(a)
        case Type.Ap(f, x) => FreeVars.fvs(f) ::: FreeVars.fvs(x)
        case Type.Gen(_) => Nil
    }
}
