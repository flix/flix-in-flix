/// Represents name, its type ascribed by the programmer, and its body.
pub type alias TopLevelDecl = (Id, Scheme, Expr)

/// Represents a typical diagnostic result of type checking of a program: 
/// contains the Id of the Expr declared, and a list of unsatisfied constraints.
pub type alias Check = (Id, List[Constr])

pub def typeCheckProgram(env: ConstrEnv, decls: List[TopLevelDecl]): List[Check] \ Fresh = {
    let initialAssums = List.map(x -> let (id, sch, _) = x; (id, sch), decls) 
        |> List.toMap;

    List.map(
        x -> {
            let (id, sch, expr) = x;
            let ((ty, ef), constrs) = 
                Collect.withCollect(() -> infer(initialAssums, expr));

            (id, subsume(env, Qual.Qual(constrs, ty), ef, sch))
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

/// ΘP , [T / a2] π2 |= entail {π1, τ1 = [T /a2]τ2} ->! •; R
/// where T are fresh type constructors
/// --------------------------------------------------
/// ΘP |- subsume (∀a1.π1 ⇒τ1) ≤ (∀a2.π2 ⇒τ2)
///
/// But the `l` is already instantiated with fresh inference variables and the 
/// eff must be pure.
def subsume(
    e: ConstrEnv, 
    l: Qual[Type], 
    le: Type, 
    r: Scheme
): List[Constr] \ Fresh = 
    let Scheme.Scheme(varKinds, qual) = r;
    let rcon = List.map(Fresh.freshCon >> Type.Con, varKinds);
    let rinst = Instantiate.inst(rcon, qual);

    let requiredClsConstrs = Set.toList(Set.map(
        x ->  {
            let Tyassoc.Tyassoc(id, arg, _) = x;
            let traitId = ConstrEnv.getTraitOfAssoc(id, e);
            Constr.Class((traitId, arg))
        },
        collectAssocInQual(rinst)
    ));

    // the substitution should be empty.
    let Qual.Qual(rGivs, rTy) = rinst;
    let Qual.Qual(lWanteds, lTy) = l;

    let (reducedGivs, _) = entailRepeat(e, rGivs);
    
    let tyEq = Constr.Eq((lTy, rTy));
    let efPure = Constr.Eq((le, efEmpty()));
    let wanteds = tyEq :: efPure :: lWanteds ++ requiredClsConstrs;
    let eWithGivs = ConstrEnv.addGivens(reducedGivs, e);

    fst(entailRepeat(eWithGivs, wanteds))
