pub type alias Inst = Qual[ClassConstr]


pub type alias ConstrEnv = {
    tyAssocEqs = Map[Id, List[EqConstr]], 
    classInsts = Map[Id, List[Qual[ClassConstr]]],
    assocToClass = Map[Id, Id],
    givenClasses = List[ClassConstr],
    sups = Set[(Id, Id)]
}

pub def emptyConstrEnv(): ConstrEnv = {
    tyAssocEqs = Map.empty(),
    classInsts = Map.empty(),
    assocToClass = Map.empty(),
    givenClasses = Nil,
    sups = Set.empty()
}

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

pub def addGivens(givens: List[Constr], env: ConstrEnv): ConstrEnv = {
    tyAssocEqs = exAssocEq(env#tyAssocEqs, givens),
    givenClasses = env#givenClasses ++ List.filterMap(
        c -> match c {
            case Constr.Class(id) => Some(id)
            case _ => None
        },
        givens
    ) 
    | env
}

pub def addAssocEq(id: Id, eq: EqConstr, env: ConstrEnv): ConstrEnv = {
    tyAssocEqs = Map.insertWith(List.append, id, eq :: Nil, env#tyAssocEqs) | env
}

pub def addClass(id: Id, env: ConstrEnv): ConstrEnv = {
    classInsts = Map.insert(id, Nil, env#classInsts) | env
}

pub def addInst(id: Id, inst: Qual[ClassConstr], env: ConstrEnv): ConstrEnv = {
    classInsts = Map.insertWith(List.append, id, inst :: Nil, env#classInsts) | env
}

pub def addSuper(sub: Id, sup: Id, env: ConstrEnv): ConstrEnv = {
    sups = Set.insert((sub, sup), env#sups) | env
}

pub def addAssocTo(assocId: Id, classId: Id, env: ConstrEnv): ConstrEnv = {
    assocToClass = Map.insert(assocId, classId, env#assocToClass) | env
}

pub def parentClasses(id: Id, env: ConstrEnv): Set[Id] =
    let rules: #{ Super(Id, Id), StrictSuper(Id, Id) } = #{
        Super(x, y) :- StrictSuper(x, y).
        Super(x, y) :- StrictSuper(x, z), Super(z, y).
    };

    Vector.toSet(
        query (inject env#sups into StrictSuper/2), rules, #{ Super(id, id). }
        select x from Super(id, x)
    )

pub def givenClasses(env: ConstrEnv): List[ClassConstr] = env#givenClasses