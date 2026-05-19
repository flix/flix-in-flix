pub enum Tyvar(Id, Kind) with Eq, ToString, Order

pub enum Tycon(Id, Kind) with Eq, ToString, Order

pub enum Tyassoc(Id, Type, Kind) with Eq, ToString, Order

pub enum Type with Eq, ToString, Order {
    case Var(Tyvar)
    case Con(Tycon)
    case Assoc(Tyassoc)
    case Ap(Type, Type)
    case Gen(Int32)
}

pub def tUnit(): Type = Type.Con(Tycon.Tycon("Unit", Kind.Star))
pub def tInt32(): Type = Type.Con(Tycon.Tycon("Int32", Kind.Star))
pub def tChar(): Type = Type.Con(Tycon.Tycon("Char", Kind.Star))
pub def tBool(): Type = Type.Con(Tycon.Tycon("Bool", Kind.Star))
pub def tList(): Type =
    Type.Con(Tycon.Tycon("List", Kind.KFun(Kind.Star, Kind.Star)))
pub def tArrow(): Type = Type.Con(Tycon.Tycon("->", kArrow()))
pub def mkAp(fn: Type, arg: Type): Type = Type.Ap(fn, arg)
pub def efUnion(): Type = Type.Con(Tycon.Tycon("+", kEfBinary()))
pub def efIntersect(): Type = Type.Con(Tycon.Tycon("&", kEfBinary()))
pub def efXor(): Type = Type.Con(Tycon.Tycon("^", kEfBinary()))
pub def efCompl(): Type = Type.Con(Tycon.Tycon("~", kEfUnary()))

pub def efEmpty(): Type = Type.Con(Tycon.Tycon("{}", Kind.Eff))
pub def efConstant(name: Id): Type = Type.Con(Tycon.Tycon(name, Kind.Eff))

pub def efIo(): Type = efConstant("IO")
pub def efRandom(): Type = efConstant("Random")
pub def efHttp(): Type = efConstant("Http")
pub def efUni(): Type = efConstant("EffectUniverse")

pub def mkArrow(arg: Type, ef: Type, res: Type): Type = {
    mkAp(mkAp(mkAp(tArrow(), arg), ef), res)
}

def tryComl(t: Type): Option[Type] = match t {
    case Type.Ap(com, inner) if com == efCompl() => Some(inner)
    case _                                       => None
}

pub def mkUnion(l: Type, r: Type): Type = {
    if (l == r)
        l
    else if (tryComl(l) == Some(r) or tryComl(r) == Some(l))
        efUni()
    else if (l == efUni() or r == efUni())
        efUni()
    else if (l == efEmpty())
        r
    else if (r == efEmpty())
        l
    else
        mkAp(mkAp(efUnion(), l), r)
}

pub def mkIntersect(l: Type, r: Type): Type = {
    if (l == r)
        l
    else if (tryComl(l) == Some(r) or tryComl(r) == Some(l))
        efEmpty()
    else if (l == efEmpty() or r == efEmpty())
        efEmpty()
    else if (l == efUni())
        r
    else if (r == efUni())
        l
    else
        mkAp(mkAp(efIntersect(), l), r)
}

pub def mkXor(l: Type, r: Type): Type = {
    if (l == r)
        efEmpty()
    else if (tryComl(l) == Some(r) or tryComl(r) == Some(l))
        efUni()
    else if (l == efEmpty())
        r
    else if (r == efEmpty())
        l
    else if (l == efUni())
        mkCompl(r)
    else if (r == efUni())
        mkCompl(l)
    else
        mkAp(mkAp(efXor(), l), r)
}

pub def mkCompl(i: Type): Type = {
    if (i == efEmpty())
        efUni()
    else if (i == efUni())
        efEmpty()
    else
        match tryComl(i) {
            case Some(t) =>
                if (t == efEmpty())
                    efUni()
                else if (t == efUni())
                    efEmpty()
                else
                    t
            case None => mkAp(efCompl(), i)
        }
}

pub def mkExclusion(l: Type, r: Type): Type = {
    mkIntersect(l, mkCompl(r))
}

pub def kindOf(t: Type): Kind = match t {
    case Type.Var(Tyvar.Tyvar(_, k)) => k,
    case Type.Con(Tycon.Tycon(_, k)) => k,
    case Type.Assoc(Tyassoc.Tyassoc(_, _, k)) => k
    case Type.Ap(f, _) => match kindOf(f) {
        case Kind.KFun(_, k) => k
        case _               => unreachable!()
    }
    case Type.Gen(_) => unreachable!()
}

instance Substable[Type] {
    pub def apply(s: Subst, t: Type): Type = match t {
        case Type.Var(v) => Option.getWithDefault(t, Subst.get(v, s))
        case Type.Ap(f, x) => Type.Ap(Substable.apply(s, f), Substable.apply(s, x))
        case Type.Assoc(Tyassoc.Tyassoc(i, a, k)) => Type.Assoc(
            Tyassoc.Tyassoc(
                i,
                Substable.apply(s, a),
                k
            )
        )
        case Type.Gen(_) => t
        case Type.Con(_) => t
    }
}

instance FreeVars[Type] {
    pub def fvs(t: Type): Set[Tyvar] = match t {
        case Type.Var(v)                          => Set.singleton(v)
        case Type.Con(_)                          => Set.empty()
        case Type.Assoc(Tyassoc.Tyassoc(_, a, _)) => FreeVars.fvs(a)
        case Type.Ap(f, x)                        => FreeVars.fvs(f) ++ FreeVars.fvs(x)
        case Type.Gen(_)                          => Set.empty()
    }
}

instance Instantiate[Type] {
    pub def inst(tys: List[Type], sch: Type): Type = match sch {
        case Type.Gen(i) => List.get(i, tys)
        case Type.Ap(f, x) => Type.Ap(
            Instantiate.inst(tys, f),
            Instantiate.inst(tys, x)
        )
        case Type.Assoc(Tyassoc.Tyassoc(i, t, k)) => Type.Assoc(
            Tyassoc.Tyassoc(
                i,
                Instantiate.inst(tys, t),
                k
            )
        )
        case _ => sch
    }
}
