pub type alias Inst = Qual[ClassConstr]

pub enum ConstrEnv(
    // Map from associated member id to the equality constraints
    Map[Id, List[EqConstr]],
    Map[Id, List[Qual[ClassConstr]]],
    Map[Id, Id],
    Set[(Id, Id)]
)

mod ConstrEnv {
    pub def empty(): ConstrEnv = ConstrEnv(
        Map.empty(), Map.empty(), Map.empty(), Set.empty()
    )

    def tyassocs(env: ConstrEnv): Map[Id, List[EqConstr]] = match env {
        case ConstrEnv(amap, _, _, _) => amap
    }

    pub def addAssocEq(
        id: Id, 
        eq: EqConstr, 
        env: ConstrEnv
    ): ConstrEnv = match env {
        case ConstrEnv(amap, cmap, assocs, sups) => ConstrEnv(
            Map.insertWith(List.append, id, eq :: Nil, amap),
            cmap,
            assocs,
            sups
        )
    }

    pub def addClass(id: Id, env: ConstrEnv): ConstrEnv = match env {
        case ConstrEnv(amap, cmap, assocs, sups) => ConstrEnv(
            amap, 
            Map.insert(id, Nil, cmap),
            assocs, 
            sups
        )
    }

    pub def addInst(id: Id, inst: Qual[ClassConstr], env: ConstrEnv): ConstrEnv = match env {
        case ConstrEnv(amap, cmap, assocs, sups) => ConstrEnv(
            amap,
            Map.insertWith(List.append, id, inst :: Nil, cmap),
            assocs,
            sups
        )
    }

    pub def addSuper(sub: Id, sup: Id, env: ConstrEnv): ConstrEnv = match env {
        case ConstrEnv(amap, cmap, assocs, sups) => ConstrEnv(
            amap,
            cmap,
            assocs,
            Set.insert((sub, sup), sups)
        )
    }

    pub def getTraitOfAssoc(id: Id, env: ConstrEnv): Id = match env {
        case ConstrEnv(_, _, assocs, _) => match Map.get(id, assocs){
            case Some(traitId) => traitId
            case None => bug!("Unknown associated member: " + id)
        }
        
    }

    pub def addAssocTo(assocId: Id, classId: Id, env: ConstrEnv): ConstrEnv = 
        match env {
            case ConstrEnv(amap, cmap, assocs, sups) => ConstrEnv(
                amap,
                cmap,
                Map.insert(assocId, classId, assocs),
                sups
            )
        }

    pub def getClassInsts(id: Id, env: ConstrEnv): List[Qual[ClassConstr]] = {
        Option.getWithDefault(Nil, Map.get(id, match env {
            case ConstrEnv(_, cmap, _, _) => cmap
        }))
    }

    pub def lookupTyassoc(id: Id, env: ConstrEnv): List[EqConstr] = {
        Option.getWithDefault(Nil, Map.get(id, tyassocs(env)))
    }

    pub def superFact(e: ConstrEnv): #{ StrictSuper(Id, Id) | r } = match e {
        case ConstrEnv(_, _, _, sups) =>  inject sups into StrictSuper/2
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
