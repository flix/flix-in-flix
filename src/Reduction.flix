def redArgAssoc(env: ConstrEnv, am: Tyassoc): Option[Type] = 
    let Tyassoc.Tyassoc(i, a, k) = am; Option.map(
        ty -> Type.Assoc(Tyassoc.Tyassoc(i, ty, k)), reduce(env, a)
    )
def reduceAssocEnv(env: ConstrEnv, am: Tyassoc): Option[Type] = 
    let Tyassoc.Tyassoc(id, _, _) = am; List.findMap(
        eq -> let (lhs, rhs) = eq; Option.map(
            sub -> Substable.apply(sub, rhs),
            matchTy(lhs, Type.Assoc(am))
        ),
        Map.getWithDefault(id, Nil, env#tyAssocEqs)
    )
def reduceAssoc(env: ConstrEnv, am: Tyassoc): Option[Type] =
    match reduceAssocEnv(env, am) {
        case Some(ty) => Some(ty)
        case None => redArgAssoc(env, am)
    }
pub def reduce(env: ConstrEnv, ty: Type): 
    Option[Type] = match ty {
        case Type.Assoc(am) => reduceAssoc(env, am)
        case Type.Ap(fn, arg) => match reduce(env, fn) {
            case Some(redFn) => Some(Type.Ap(redFn, arg))
            case None => Option.map(
                redArg -> Type.Ap(fn, redArg), 
                reduce(env, arg)
            )
        }
        case _ => None
    }
