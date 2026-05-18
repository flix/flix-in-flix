/// Represents name, its type ascribed by the programmer, and its body.
pub type alias TopLevelDecl = (Id, Scheme, Expr)

/// Represents a typical diagnostic result of type checking of a program: 
/// contains the Id of the Expr declared, and a list of unsatisfied constraints.
pub type alias Check = (Id, List[Constr])

pub def typeCheckProgram(env: ConstrEnv, decls: List[TopLevelDecl]): List[Check] \ Fresh = {
    let initialAssums = List.map(x -> let (id, sch, _) = x; (id, sch), decls) 
        |> List.toMap;

    List.map(
        x -> region r {
            let (id, sch, expr) = x;
            let constrs = Ref.fresh(r, Nil);

            let (ty, ef) = run infer(initialAssums, expr)
                with handler Collect {
                    def collect(c, res) = {
                        Ref.put(c :: Ref.get(constrs), constrs);
                        res(())
                    }
                };

            (id, subsume(env, ty, Ref.get(constrs), ef, sch))
        }, 
        decls
    )
}

def collectAssoc(ty: Type): Set[Tyassoc] = match ty {
    case Type.Assoc(Tyassoc.Tyassoc(id, a, k)) => 
        Set.singleton(Tyassoc.Tyassoc(id, a, k)) ++ collectAssoc(a)
    case Type.Ap(l, r) => collectAssoc(l) ++ collectAssoc(r)
    case _ => Set.empty()
}

def collectAssocInCtx(cs: List[Constr]): Set[Tyassoc] = List.foldLeft(
    (set, c) -> match c {
        case Constr.Class((_, t)) => set ++ collectAssoc(t)
        case Constr.Eq((l, r)) => set ++ collectAssoc(l) ++ collectAssoc(r)
    }, 
    Set.empty(), 
    cs
)

def collectAssocInQual(q: Qual[Type]): Set[Tyassoc] = 
    let Qual.Qual(ctx, head) = q; collectAssocInCtx(ctx) ++ collectAssoc(head)

def assocWfConstrs(q: Qual[Type], env: ConstrEnv): List[Constr] 
    = Set.toList(Set.map(
        x -> {
            let Tyassoc.Tyassoc(id, arg, _) = x;
            let traitId = getTraitOfAssoc(id, env);
            Constr.Class((traitId, arg))
        },
        collectAssocInQual(q)
    ))

def skolemize(sch: Scheme): Qual[Type] \ Fresh = {
    let Scheme.Scheme(varKinds, qual) = sch;
    let skolems = List.map(Fresh.freshCon >> Type.Con, varKinds);
    Instantiate.inst(skolems, qual)
}

def subsume(
    env: ConstrEnv, eTy: Type, eConstrs: List[Constr], eEff: Type, ann: Scheme
): List[Constr] \ Fresh = 
    let skolemizedQual = skolemize(ann);
    let Qual.Qual(givs, annTy) = skolemizedQual;
    fst(entailRepeat(
        addGivens(fst(entailRepeat(env, givs)), env), 
        Constr.Eq((eTy, annTy)) :: Constr.Eq((eEff, efEmpty())) 
            :: eConstrs ++ assocWfConstrs(skolemizedQual, env)
    ))
