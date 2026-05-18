pub def entail(env: ConstrEnv, goal: Constr): Option[(List[Constr], Subst)] = 
    match goal {
        case Constr.Class((id, ty)) =>
            Option.map(cs -> (cs, Subst.empty()), entailClass(env, id, ty))
        case Constr.Eq((lhs, rhs)) => Option.map(
            res -> let (eqs, sub) = res; (List.map(Constr.Eq, eqs), sub),
            unify(env, lhs, rhs)
        )
    }

def bySuper(env: ConstrEnv, id: Id, ty: Type): Bool 
    = List.exists(
        gc -> let (gid, gty) = gc; equiv(gty, ty) 
            and Set.memberOf(id, parentClasses(gid, env)),
        givenClasses(env)
    )

def entailClass(env: ConstrEnv, clsId: Id, clsTy: Type): 
    Option[List[Constr]] = 
        if (bySuper(env, clsId, clsTy)) Some(Nil) 
        else match reduceClass(env, clsId, clsTy) {
            case Some(redCls) => Some(Constr.Class(redCls) :: Nil)
            case None => byInst(env, clsId, clsTy)
        }

def byInst(env: ConstrEnv, clsId: Id, clsTy: Type): Option[List[Constr]] =
    List.findMap(
        i -> let Qual.Qual(ctx, (_, ty)) = i;
            Option.map(sub -> Substable.apply(sub, ctx), matchTy(ty, clsTy)),
        Map.getWithDefault(clsId, Nil, env#classInsts)
    )

def reduceClass(env: ConstrEnv, clsId: Id, clsTy: Type): Option[ClassConstr] = 
    Option.map(ty -> (clsId, ty), reduce(env, clsTy))

def findStep(e: ConstrEnv, done: List[Constr], rest: List[Constr]): 
    Option[(List[Constr], Subst)] = match rest {
        case Nil => None, case head :: tail => {
            match entail(e, head) {
                case Some((newCs, sub)) => {
                    let doneS = List.map(c -> Substable.apply(sub, c), done);
                    let tailS = List.map(c -> Substable.apply(sub, c), tail);

                    Some((doneS ++ newCs ++ tailS, sub))
                }

                case None => findStep(e, head :: done, tail)
            }
        }
    }

def iterate(e: ConstrEnv, cs: List[Constr], s: Subst): (List[Constr], Subst) = 
    match findStep(e, Nil, cs) {
        case Some((nextCs, sub)) => iterate(e, nextCs, Subst.compose(sub, s))
        case None => (cs, s)
    }

pub def entailRepeat(env: ConstrEnv, cs: List[Constr]): (List[Constr], Subst) =
    iterate(env, cs, Subst.empty())
