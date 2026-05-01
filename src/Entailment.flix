pub def entailOne(env: ConstrEnv, giv: List[Constr], goal: Constr): 
    Option[(List[Constr], Subst)] = match goal {
        case Constr.Class(cls) =>
            Option.map(cs -> (cs, Subst.empty()), entailClassOne(env, giv, cls))
        case Constr.Eq(eq) => Option.map(
            res -> (List.map(Constr.Eq, fst(res)), snd(res)),
            unifyOne(env, giv, EqConstr.left(eq), EqConstr.right(eq))
        )
    }

def bySuper(env: ConstrEnv, giv: List[Constr], g: ClassConstr): Bool 
    = List.exists(
        gc -> match gc {
            case Constr.Class(cls) =>
                if (ClassConstr.ty(cls) != ClassConstr.ty(g)) false
                else Set.memberOf(ClassConstr.id(g), 
                    ConstrEnv.parentClasses(ClassConstr.id(cls), env)
                )
            case Constr.Eq(_) => false
        }, 
        giv
    )

def entailClassOne(env: ConstrEnv, giv: List[Constr], g: ClassConstr): 
    Option[List[Constr]] = 
        if (bySuper(env, giv, g)) Some(Nil) 
        else match reduceClass(env, giv, g) {
            case Some(redCls) => Some(Constr.Class(redCls) :: Nil)
            case None => byInst(env, g)
        }

def tryInst(inst: Inst, clsTy: Type): Option[List[Constr]] = Option.map(
    sub -> Substable.apply(sub, Inst.context(inst)),
    matchTy(ClassConstr.ty(Inst.head(inst)), clsTy)
)

def byInst(env: ConstrEnv, g: ClassConstr): Option[List[Constr]] = {
    let gid = ClassConstr.id(g);
    let gt = ClassConstr.ty(g);

    forM (
        cls <- ConstrEnv.lookupClass(gid, env);
        ctx <- List.findMap(i -> tryInst(i, gt), Class.insts(cls))
    ) yield ctx
}

def reduceClass(env: ConstrEnv, giv: List[Constr], cls: ClassConstr): 
    Option[ClassConstr] = Option.map(
        ty -> ClassConstr.ClassConstr(ClassConstr.id(cls), ty),
        reduceTyOne(env, giv, ClassConstr.ty(cls))
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

