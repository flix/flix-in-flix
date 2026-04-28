def reduceInnerAssoc(env: ConstrEnv, giv: List[Constr], am: Tyassoc): 
    Option[Type] = Option.map(
        ty -> Type.Assoc(Tyassoc.Tyassoc(Tyassoc.id(am), ty, Tyassoc.kind(am))),
        reduceTyOne(env, giv, Tyassoc.ty(am))
    )

def reduceAssocGiven(giv: List[Constr], am: Tyassoc): Option[Type] 
    = List.findMap(
        eq -> {
            let lhs = EqConstr.left(eq);
            if (lhs == Type.Assoc(am)) Some(EqConstr.right(eq)) else None
        }, 
        List.filterMap(c -> Constr.asEq(c), giv)
    )

def reduceAssocEnv(env: ConstrEnv, am: Tyassoc): Option[Type] 
    = List.findMap(
        eq -> {
            let lhs = EqConstr.left(eq);
            Option.map(
                sub -> Substable.apply(sub, EqConstr.right(eq)),
                Result.toOption(matchTypes(lhs, Type.Assoc(am)))
            )
        }, 
        ConstrEnv.lookupTyassoc(Tyassoc.id(am), env)
    )


def reduceAssoc(env: ConstrEnv, giv: List[Constr], am: Tyassoc): Option[Type] 
    = match reduceInnerAssoc(env, giv, am) {
        case Some(ty) => Some(ty)
        case None => match reduceAssocGiven(giv, am) {
            case Some(ty) => Some(ty)
            case None => reduceAssocEnv(env, am)
        }
    }

pub def reduceTyOne(env: ConstrEnv, giv: List[Constr], ty: Type): 
    Option[Type] = match ty {
        case Type.Var(_) => None
        case Type.Con(_) => None
        case Type.Gen(_) => None

        case Type.Assoc(am) => reduceAssoc(env, giv, am)

        case Type.Ap(fn, arg) => match reduceTyOne(env, giv, fn) {
            case Some(redFn) => Some(Type.Ap(redFn, arg))
            case None => Option.map(
                redArg -> Type.Ap(fn, redArg), 
                reduceTyOne(env, giv, arg)
            )
        }
    }
