pub enum Inst(Qual[ClassConstr])

mod Inst {
    pub def head(inst: Inst): ClassConstr = match inst {
        case Inst(qua) => Qual.head(qua)
    }

    pub def context(inst: Inst): List[Constr] = match inst {
        case Inst(qua) => Qual.context(qua)
    }
}

pub enum ConstrEnv(
    // Map from associated member id to the equality constraints
    Map[Id, List[EqConstr]],
    Map[Id, List[Inst]],
    Set[(Id, Id)]
)

mod ConstrEnv {
    pub def empty(): ConstrEnv = ConstrEnv(
        Map.empty(), Map.empty(), Set.empty()
    )

    def tyassocs(env: ConstrEnv): Map[Id, List[EqConstr]] = match env {
        case ConstrEnv(amap, _, _) => amap
    }

    pub def addAssocEq(
        id: Id, 
        eq: EqConstr, 
        env: ConstrEnv
    ): ConstrEnv = match env {
        case ConstrEnv(amap, cmap, sups) => ConstrEnv(
            Map.insertWith(List.append, id, eq :: Nil, amap),
            cmap,
            sups
        )
    }

    pub def addClass(id: Id, env: ConstrEnv): ConstrEnv = match env {
        case ConstrEnv(amap, cmap, sups) => ConstrEnv(
            amap, 
            Map.insert(id, Nil, cmap),
            sups
        )
    }

    pub def addInst(id: Id, inst: Inst, env: ConstrEnv): ConstrEnv = match env {
        case ConstrEnv(amap, cmap, sups) => ConstrEnv(
            amap,
            Map.insertWith(List.append, id, inst :: Nil, cmap),
            sups
        )
    }

    pub def addSuper(sub: Id, sup: Id, env: ConstrEnv): ConstrEnv = match env {
        case ConstrEnv(amap, cmap, sups) => ConstrEnv(
            amap,
            cmap,
            Set.insert((sub, sup), sups)
        )
    }

    pub def getClassInsts(id: Id, env: ConstrEnv): List[Inst] = {
        Option.getWithDefault(Nil, Map.get(id, match env {
            case ConstrEnv(_, cmap, _) => cmap
        }))
    }

    pub def lookupTyassoc(id: Id, env: ConstrEnv): List[EqConstr] = {
        Option.getWithDefault(Nil, Map.get(id, tyassocs(env)))
    }

    pub def superFact(e: ConstrEnv): #{ StrictSuper(Id, Id) | r } = match e {
        case ConstrEnv(_, _, sups) =>  inject sups into StrictSuper/2
    }

    pub def parentClasses(id: Id, env: ConstrEnv): Set[Id] = {
        let rules: #{ Super(Id, Id), StrictSuper(Id, Id) } = #{
            Super(x, y) :- StrictSuper(x, y).
            Super(x, y) :- StrictSuper(x, z), Super(z, y).
        };

        Vector.toSet(query superFact(env), rules, #{ Super(id, id). }
            select x from Super(id, x)
        )
    }
}
