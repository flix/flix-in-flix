pub type alias Inst = Qual[ClassConstr]

pub enum ConstrEnv(
    Map[Id, List[EqConstr]], // map from associated member to its equality
    Map[Id, List[Qual[ClassConstr]]], // map from class to its instances
    Map[Id, Id], // map from associated member to its trait
    List[ClassConstr], // list of given classes
    Set[(Id, Id)] // set of (sub, sup) where sub is a subclass of sup
)
// ConstrEnv is getting pretty ungly :(

mod ConstrEnv {
    pub def empty(): ConstrEnv = ConstrEnv(
        Map.empty(), Map.empty(), Map.empty(), Nil, Set.empty()
    )

    def exAssocEq(m: Map[Id, List[EqConstr]], eq: List[Constr]): 
        Map[Id, List[EqConstr]] = match eq {
            case Nil => m,
            case Constr.Eq((l, r)) :: t => {
                let id = match l {
                    case Type.Assoc(Tyassoc.Tyassoc(id, _, _)) => id
                    case _ => bug!("Expected an associated type")
                };

                exAssocEq(Map.insertWith(List.append, id, (l, r) :: Nil, m), t)
            }

            case _ :: t => exAssocEq(m, t)
        }

    pub def addGivens(givens: List[Constr], env: ConstrEnv): ConstrEnv = 
        match env {
            case ConstrEnv(amap, cmap, assocs, gcs, sups) => ConstrEnv(
                exAssocEq(amap, givens),
                cmap,
                assocs,
                gcs ++ List.filterMap(
                    c -> match c {
                        case Constr.Class(id) => Some(id)
                        case _ => None
                    }, 
                    givens
                ),
                sups
            )
        }


    pub def givenClasses(env: ConstrEnv): List[ClassConstr] = match env {
        case ConstrEnv(_, _, _, gcs, _) => gcs
    }

    def tyassocs(env: ConstrEnv): Map[Id, List[EqConstr]] = match env {
        case ConstrEnv(amap, _, _, _, _) => amap
    }

    pub def addAssocEq(
        id: Id, 
        eq: EqConstr, 
        env: ConstrEnv
    ): ConstrEnv = match env {
        case ConstrEnv(amap, cmap, assocs, gcs, sups) => ConstrEnv(
            Map.insertWith(List.append, id, eq :: Nil, amap),
            cmap,
            assocs,
            gcs,
            sups
        )
    }

    pub def addClass(id: Id, env: ConstrEnv): ConstrEnv = match env {
        case ConstrEnv(amap, cmap, assocs, gcs, sups) => ConstrEnv(
            amap, 
            Map.insert(id, Nil, cmap),
            assocs, 
            gcs,
            sups
        )
    }

    pub def addInst(id: Id, inst: Qual[ClassConstr], env: ConstrEnv): ConstrEnv = match env {
        case ConstrEnv(amap, cmap, assocs, gcs, sups) => ConstrEnv(
            amap,
            Map.insertWith(List.append, id, inst :: Nil, cmap),
            assocs,
            gcs,
            sups
        )
    }

    pub def addSuper(sub: Id, sup: Id, env: ConstrEnv): ConstrEnv = match env {
        case ConstrEnv(amap, cmap, assocs, gcs, sups) => ConstrEnv(
            amap,
            cmap,
            assocs,
            gcs,
            Set.insert((sub, sup), sups)
        )
    }

    pub def getTraitOfAssoc(id: Id, env: ConstrEnv): Id = match env {
        case ConstrEnv(_, _, assocs, _, _) => match Map.get(id, assocs){
            case Some(traitId) => traitId
            case None => bug!("Unknown associated member: " + id)
        }
        
    }

    pub def addAssocTo(assocId: Id, classId: Id, env: ConstrEnv): ConstrEnv = 
        match env {
            case ConstrEnv(amap, cmap, assocs, gcs, sups) => ConstrEnv(
                amap,
                cmap,
                Map.insert(assocId, classId, assocs),
                gcs,
                sups
            )
        }

    pub def getClassInsts(id: Id, env: ConstrEnv): List[Qual[ClassConstr]] = {
        Option.getWithDefault(Nil, Map.get(id, match env {
            case ConstrEnv(_, cmap, _, _, _) => cmap
        }))
    }

    pub def lookupTyassoc(id: Id, env: ConstrEnv): List[EqConstr] = {
        Option.getWithDefault(Nil, Map.get(id, tyassocs(env)))
    }

    pub def superFact(e: ConstrEnv): #{ StrictSuper(Id, Id) | r } = match e {
        case ConstrEnv(_, _, _, _, sups) =>  inject sups into StrictSuper/2
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
