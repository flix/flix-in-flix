def reduceInnerAssoc(env: ConstrEnv, giv: List[Constr], am: Tyassoc): 
    Option[Type] = Option.map(
        ty -> Type.Assoc(Tyassoc.Tyassoc(Tyassoc.id(am), ty, kindOf(Type.Assoc(am)))),
        reduceTyOne(env, giv, Tyassoc.ty(am))
    )

def reduceAssocGiven(giv: List[Constr], am: Tyassoc): Option[Type] 
    = List.findMap(
        c -> match c {
            // REMARK: is boolEq necessary here?
            case Constr.Eq(lhs, rhs) if boolEq(lhs, Type.Assoc(am))
                => Some(rhs)
            case _ => None
        },
        giv
    )

def reduceAssocEnv(env: ConstrEnv, am: Tyassoc): Option[Type] 
    = List.findMap(
        eq -> Option.map(
            sub -> Substable.apply(sub, snd(eq)),
            matchTy(fst(eq), Type.Assoc(am))
        ),
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
        case Type.Assoc(am) => reduceAssoc(env, giv, am)
        case Type.Ap(fn, arg) => match reduceTyOne(env, giv, fn) {
            case Some(redFn) => Some(Type.Ap(redFn, arg))
            case None => Option.map(
                redArg -> Type.Ap(fn, redArg), 
                reduceTyOne(env, giv, arg)
            )
        }
        case _ => None
    }
