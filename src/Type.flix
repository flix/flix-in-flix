pub enum Tyvar(Id, Kind) with Eq, ToString, Hash, Order

instance FreeVars[Tyvar] {
    pub def fvs(v: Tyvar): Set[Tyvar] = Set.singleton(v)
}

pub enum Tycon(Id, Kind) with Eq, ToString, Hash, Order

pub enum Tyassoc(Id, Type, Kind) with Eq, ToString, Hash, Order

instance Instantiate[Tyassoc] {
    pub def inst(tys: List[Type], s: Tyassoc): Tyassoc = match s {
        case Tyassoc.Tyassoc(id, t, k) 
            => Tyassoc.Tyassoc(id, Instantiate.inst(tys, t), k)
    }
}

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

instance FreeVars[Tyassoc] {
    pub def fvs(a: Tyassoc): Set[Tyvar] = FreeVars.fvs(Tyassoc.ty(a))
}

pub enum Type with Eq, ToString, Hash, Order {
    case Var(Tyvar)
    case Con(Tycon)
    case Assoc(Tyassoc)
    case Ap(Type, Type)
    case Gen(Int32)
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
    pub def efUnion(): Type = Type.Con(Tycon.Tycon("+", Kind.efBinary()))
    pub def efIntersect(): Type = Type.Con(Tycon.Tycon("&", Kind.efBinary()))
    pub def efXor(): Type = Type.Con(Tycon.Tycon("^", Kind.efBinary()))
    pub def efCompl(): Type = Type.Con(Tycon.Tycon("~", Kind.efUnary()))

    pub def efEmpty(): Type = Type.Con(Tycon.Tycon("{}", Kind.Eff))
    pub def efConstant(name: Id): Type = Type.Con(Tycon.Tycon(name, Kind.Eff))

    pub def io(): Type = efConstant("IO")
    pub def random(): Type = efConstant("Random")
    pub def http(): Type = efConstant("Http")
    pub def efUni(): Type = efConstant("EffectUniverse")

    pub def mkArrow(arg: Type, ef: Type, res: Type): Type = {
        Type.mkAp(Type.mkAp(Type.arrow(), arg), Type.mkAp(ef, res))
    }

    def tryComl(t: Type) : Option[Type] = match t {
        case Type.Ap(com, inner) if com == Type.efCompl() => Some(inner)
        case _ => None
    }

    pub def mkUnion(l: Type, r: Type): Type = {
        if (l == r) l
        else if (tryComl(l) == Some(r) or tryComl(r) == Some(l)) Type.efUni()
        else if (l == Type.efUni() or r == Type.efUni()) Type.efUni()
        else if (l == Type.efEmpty()) r else if (r == Type.efEmpty()) l
        else Type.mkAp(Type.mkAp(Type.efUnion(), l), r)
    }

    pub def mkIntersect(l: Type, r: Type): Type = {
        if (l == r) l
        else if (tryComl(l) == Some(r) or tryComl(r) == Some(l)) Type.efEmpty()
        else if (l == Type.efEmpty() or r == Type.efEmpty()) Type.efEmpty()
        else if (l == Type.efUni()) r else if (r == Type.efUni()) l
        else Type.mkAp(Type.mkAp(Type.efIntersect(), l), r)
    }

    pub def mkXor(l: Type, r: Type): Type = {
        if (l == r) Type.efEmpty()
        else if (tryComl(l) == Some(r) or tryComl(r) == Some(l)) Type.efUni()
        else if (l == Type.efEmpty()) r else if (r == Type.efEmpty()) l
        else if (l == Type.efUni()) Type.mkCompl(r)
        else if (r == Type.efUni()) Type.mkCompl(l)
        else Type.mkAp(Type.mkAp(Type.efXor(), l), r)
    }

    pub def mkCompl(i: Type): Type = {
        if (i == Type.efEmpty()) Type.efUni()
        else if (i == Type.efUni()) Type.efEmpty()
        else match tryComl(i) {
            case Some(t) => 
                if (t == Type.efEmpty()) Type.efUni() 
                else if (t == Type.efUni()) Type.efEmpty() 
                else t
            case None => Type.mkAp(Type.efCompl(), i)
        }
    }

    pub def mkExclusion(l: Type, r: Type): Type = {
        mkIntersect(l, mkCompl(r))
    }
}

pub def kindOf(t: Type): Kind = match t {
    case Type.Var(Tyvar.Tyvar(_, k)) => k,
    case Type.Con(Tycon.Tycon(_, k)) => k,
    case Type.Assoc(Tyassoc.Tyassoc(_, _, k)) => k
    case Type.Ap(f, _) => let fk = kindOf(f); match fk {
        case Kind.KFun(_, k) => k
        case _ => bug!("Expected a function kind, but found: ${fk}")
    }
    case Type.Gen(_) => bug!("Gen should'be asked for its kind directly")
}

instance Substable[Type] {
    pub def apply(s: Subst, t: Type): Type = match t {
        case Type.Var(v) => Option.getWithDefault(t, Subst.get(v, s))
        case Type.Ap(f, x) 
            => Type.Ap(Substable.apply(s, f), Substable.apply(s, x))
        case Type.Assoc(a) => Type.Assoc(Substable.apply(s, a))
        case Type.Gen(_) => t
        case Type.Con(_) => t
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

instance Instantiate[Type] {
    pub def inst(tys: List[Type], sch: Type): Type = match sch {
        case Type.Gen(i) => List.get(i, tys)
        case Type.Ap(f, x) => Type.Ap(
            Instantiate.inst(tys, f), 
            Instantiate.inst(tys, x)
        )
        case Type.Assoc(a) => Type.Assoc(Instantiate.inst(tys, a))
        case _ => sch
    }
}
