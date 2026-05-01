pub def entailOne(env: ConstrEnv, giv: List[Constr], goal: Constr): 
    Option[(List[Constr], Subst)] = match goal {
        case Constr.Class(id, ty) =>
            Option.map(
                cs -> (cs, Subst.empty()),
                entailClassOne(env, giv, id, ty)
            )
        case Constr.Eq(lhs, rhs) => Option.map(
            res -> (List.map(eq -> Constr.Eq(fst(eq), snd(eq)), fst(res)), snd(res)),
            unifyOne(env, giv, lhs, rhs)
        )
    }

def bySuper(env: ConstrEnv, giv: List[Constr], clsId: Id, clsTy: Type): Bool 
    = List.exists(
        gc -> match gc {
            case Constr.Class(id, ty) if (ty == clsTy) =>
                Set.memberOf(clsId, ConstrEnv.parentClasses(id, env))
            case _ => false
        }, 
        giv
    )

def entailClassOne(env: ConstrEnv, giv: List[Constr], clsId: Id, clsTy: Type): 
    Option[List[Constr]] = 
        if (bySuper(env, giv, clsId, clsTy)) Some(Nil) 
        else match reduceClass(env, giv, clsId, clsTy) {
            case Some(redCls) => Some(Constr.Class(fst(redCls), snd(redCls)) :: Nil)
            case None => byInst(env, clsId, clsTy)
        }

def tryInst(inst: Inst, clsTy: Type): Option[List[Constr]] = Option.map(
    sub -> Substable.apply(sub, Inst.context(inst)),
    matchTy(snd(Inst.head(inst)), clsTy)
)

def byInst(env: ConstrEnv, clsId: Id, clsTy: Type): Option[List[Constr]] = {
    forM (
        cls <- ConstrEnv.lookupClass(clsId, env);
        ctx <- List.findMap(i -> tryInst(i, clsTy), Class.insts(cls))
    ) yield ctx
}

def reduceClass(env: ConstrEnv, giv: List[Constr], clsId: Id, clsTy: Type): 
    Option[ClassConstr] = Option.map(
        ty -> (clsId, ty),
        reduceTyOne(env, giv, clsTy)
    )

def entailRepeatHelper(
    env: ConstrEnv,
    giv: List[Constr],
    cs: List[Constr],
    curSub: Subst
): (List[Constr], Subst) = {
    def findStep(
        done: List[Constr],
        rest: List[Constr]
    ): Option[(List[Constr], Subst)] = match rest {
        case Nil => None

        case head :: tail => {
            match entailOne(env, giv, head) {
                case Some((newCs, sub)) => {
                    let nextCs = List.map(
                        c -> Substable.apply(sub, c), 
                        done ++ tail
                    );

                    Some((nextCs ++ newCs, sub))
                }

                case None => findStep(head :: done, tail)
            }
        }
    };

    match findStep(Nil, cs) {
        case Some((nextCs, sub)) => entailRepeatHelper(
            env, 
            giv, 
            nextCs, 
            Subst.compose(sub, curSub)
        )
        case None => (cs, curSub)
    }
}


pub def entailRepeat(
    env: ConstrEnv,
    giv: List[Constr],
    cs: List[Constr]
): (List[Constr], Subst) =
    entailRepeatHelper(env, giv, cs, Subst.empty())
