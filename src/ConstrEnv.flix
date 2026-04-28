pub enum Inst(Qual[ClassConstr])

mod Inst {
    pub def head(inst: Inst): ClassConstr = match inst {
        case Inst(qua) => Qual.head(qua)
    }

    pub def context(inst: Inst): List[Constr] = match inst {
        case Inst(qua) => Qual.context(qua)
    }
}

pub enum Class(List[Id], List[Inst])

mod Class {
    pub def supers(cls: Class): List[Id] = match cls { 
        case Class(sups, _) => sups 
    }
    pub def insts(cls: Class): List[Inst] = match cls { 
        case Class(_, insts) => insts
    }
}

pub enum ConstrEnv(
    // Map from associated member id to the equality constraints
    Map[Id, List[EqConstr]],
    Map[Id, Class]
)

mod ConstrEnv {
    def tyassocs(env: ConstrEnv): Map[Id, List[EqConstr]] = match env {
        case ConstrEnv(amap, _) => amap
    }

    def classes(env: ConstrEnv): Map[Id, Class] = match env {
        case ConstrEnv(_, cmap) => cmap
    }

    pub def lookupClass(id: Id, env: ConstrEnv): Option[Class] = {
        Map.get(id, classes(env))
    }

    pub def lookupTyassoc(id: Id, env: ConstrEnv): List[EqConstr] = {
        Option.getWithDefault(Nil, Map.get(id, tyassocs(env)))
    }

    pub def supersOf(id: Id, env: ConstrEnv): List[Id] = {
        Option.getWithDefault(
            Nil,
            Option.map(cls -> Class.supers(cls), Map.get(id, classes(env)))
        )
    }

    pub def superFact(env: ConstrEnv): #{ StrictSuper(Id, Id) | r } = {
        inject Set.flatMap(
            x -> List.toSet(List.map(y -> (y, x), supersOf(x, env))),
            Map.keysOf(classes(env))
        ) into StrictSuper/2
    }

    pub def parentClasses(id: Id, env: ConstrEnv): Set[Id] = {
        let rules: #{ Super(Id, Id), StrictSuper(Id, Id) } = #{
            Super(x, y) :- StrictSuper(x, y).
            Super(x, y) :- StrictSuper(x, z), Super(z, y).
        };

        Vector.toSet(query superFact(env), rules, #{ Super(id, id). }
            select x from Super(x, id)
        )
    }
}
