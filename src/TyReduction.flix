def redArgAssoc(env: ConstrEnv, giv: List[Constr], am: Tyassoc): Option[Type] = 
    let Tyassoc.Tyassoc(i, a, k) = am;
    Option.map(ty -> Type.Assoc(Tyassoc.Tyassoc(i, ty, k)), reduce(env, giv, a))

def reduceAssocGiven(giv: List[Constr], am: Tyassoc): Option[Type] 
    = List.findMap(
        c -> match c {
            case Constr.Eq(lhs, rhs) if equiv(lhs, Type.Assoc(am))
                => Some(rhs)
            case _ => None
        },
        giv
    )

def reduceAssocEnv(env: ConstrEnv, am: Tyassoc): Option[Type] = 
    let Tyassoc.Tyassoc(id, _, _) = am;
    List.findMap(
        eq -> 
            let (lhs, rhs) = eq;
            Option.map(
                sub -> Substable.apply(sub, rhs),
                matchTy(lhs, Type.Assoc(am))
            ),

        ConstrEnv.lookupTyassoc(id, env)
    )

def reduceAssoc(env: ConstrEnv, giv: List[Constr], am: Tyassoc): Option[Type] 
    = match redArgAssoc(env, giv, am) {
        case Some(ty) => Some(ty)
        case None => match reduceAssocGiven(giv, am) {
            case Some(ty) => Some(ty)
            case None => reduceAssocEnv(env, am)
        }
    }

pub def reduce(env: ConstrEnv, giv: List[Constr], ty: Type): 
    Option[Type] = match ty {
        case Type.Assoc(am) => reduceAssoc(env, giv, am)
        case Type.Ap(fn, arg) => match reduce(env, giv, fn) {
            case Some(redFn) => Some(Type.Ap(redFn, arg))
            case None => Option.map(
                redArg -> Type.Ap(fn, redArg), 
                reduce(env, giv, arg)
            )
        }
        case _ => None
    }
