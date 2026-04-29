pub enum Tyvar(Id, Kind) with Eq, ToString, Hash, Order

mod Tyvar {
    pub def kind(v: Tyvar): Kind = match v { case Tyvar(_, k) => k }
}

instance Kinded[Tyvar] {
    pub def kind(v: Tyvar): Kind = Tyvar.kind(v)
}

instance FreeVars[Tyvar] {
    pub def fvs(v: Tyvar): Set[Tyvar] = Set.singleton(v)
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
    pub def kind(a: Tyassoc): Kind = match a {
        case Tyassoc.Tyassoc(_, _, k) => k
    }
}

instance FreeVars[Tyassoc] {
    pub def fvs(a: Tyassoc): Set[Tyvar] = FreeVars.fvs(Tyassoc.ty(a))
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
    pub def unit(): Type = Type.Con(Tycon.Tycon("Unit", Kind.Star))
    pub def int32(): Type = Type.Con(Tycon.Tycon("Int32", Kind.Star))
    pub def char(): Type = Type.Con(Tycon.Tycon("Char", Kind.Star))
    pub def bool(): Type = Type.Con(Tycon.Tycon("Bool", Kind.Star))
    pub def list(): Type 
        = Type.Con(Tycon.Tycon("List", Kind.KFun(Kind.Star, Kind.Star)))
    pub def arrow(): Type = Type.Con(Tycon.Tycon("->",  Kind.arrow()))
    pub def mkAp(fn: Type, arg: Type): Type = Type.Ap(fn, arg)
}

mod Type {
    pub def efUnion(): Type = Type.Con(Tycon.Tycon("+", Kind.efBinary()))
    pub def efIntersect(): Type = Type.Con(Tycon.Tycon("&", Kind.efBinary()))
    pub def efXor(): Type = Type.Con(Tycon.Tycon("^", Kind.efBinary()))
    pub def efComplement(): Type = Type.Con(Tycon.Tycon("~", Kind.efUnary()))


    pub def efEmpty(): Type = Type.Con(Tycon.Tycon("{}", Kind.Eff))
    pub def efConstant(name: Id): Type = Type.Con(Tycon.Tycon(name, Kind.Eff))

    pub def io(): Type = efConstant("IO")
    pub def random(): Type = efConstant("Random")
    pub def http(): Type = efConstant("Http")
    pub def efUniverse(): Type = efConstant("EffectUniverse")
}



mod Type {
    def innerCompl(t: Type) : Option[Type] = match t {
        case Type.Ap(com, inner) if com == Type.efComplement() => Some(inner)
        case _ => None
    }

    pub def mkUnion(left: Type, right: Type): Type = {
        if (left == right) left

        else if (
            innerCompl(left) == Some(right) 
            or innerCompl(right) == Some(left)
        ) Type.efUniverse()

        else if (
            left == Type.efUniverse()
            or right == Type.efUniverse()
        ) Type.efUniverse()

        else if (left == Type.efEmpty()) right
        else if (right == Type.efEmpty()) left

        else Type.mkAp(Type.mkAp(Type.efUnion(), left), right)
    }

    pub def mkIntersect(left: Type, right: Type): Type = {
        if (left == right) left

        else if (
            innerCompl(left) == Some(right) 
            or innerCompl(right) == Some(left)
        ) Type.efEmpty()

        else if (
            left == Type.efEmpty()
            or right == Type.efEmpty()
        ) Type.efEmpty()

        else if (left == Type.efUniverse()) right
        else if (right == Type.efUniverse()) left

        else Type.mkAp(Type.mkAp(Type.efIntersect(), left), right)
    }

    pub def mkXor(left: Type, right: Type): Type = {
        if (left == right) Type.efEmpty()

        else if (
            innerCompl(left) == Some(right) 
            or innerCompl(right) == Some(left)
        ) Type.efUniverse()

        else if (left == Type.efEmpty()) right
        else if (right == Type.efEmpty()) left

        else if (left == Type.efUniverse()) Type.mkCompl(right)
        else if (right == Type.efUniverse()) Type.mkCompl(left)

        else Type.mkAp(Type.mkAp(Type.efXor(), left), right)
    }

    pub def mkCompl(inner: Type): Type = {
        if (inner == Type.efEmpty()) Type.efUniverse()
        else if (inner == Type.efUniverse()) Type.efEmpty()
        else match innerCompl(inner) {
            case Some(t) 
                => if (t == Type.efEmpty()) Type.efUniverse() 
                else if (t == Type.efUniverse()) Type.efEmpty() 
                else t
            case None => Type.mkAp(Type.efComplement(), inner)
        }
    }
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
    pub def fvs(t: Type): Set[Tyvar] = match t {
        case Type.Var(v) => FreeVars.fvs(v)
        case Type.Con(_) => Set.empty()
        case Type.Assoc(a) => FreeVars.fvs(a)
        case Type.Ap(f, x) => FreeVars.fvs(f) ++ FreeVars.fvs(x)
        case Type.Gen(_) => Set.empty()
    }
}
