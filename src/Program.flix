/// Represents name, its type ascribed by the programmer, and its body.
pub type alias TopLevelDecl = (Id, Scheme[Type], Expr)

/// Represents a typical diagnostic result of type checking of a program: 
/// contains the Id of the Expr declared, and a list of unsatisfied constraints.
pub type alias Check = (Id, List[Constr])

pub def typeCheckProgram(
    env: ConstrEnv, 
    decls: List[TopLevelDecl]
): List[Check] \ Fresh = {
    let initialAssums = List.map(x -> {
        let (id, sch, _) = x;
        (id, sch)
    }, decls) |> List.toMap;

    List.map(
        x -> {
            let (id, sch, expr) = x;
            let ((ty, ef), constrs) = 
                Collect.withCollect(() -> Expr.infer(initialAssums, expr));

            (id, subsume(env, Qual.Qual(constrs, ty), ef, sch))
        }, 
        decls
    )
}

def collectAssoc(ty: Type): Set[Tyassoc] = match ty {
    case Type.Assoc(a) => Set.singleton(a) ++ collectAssoc(Tyassoc.ty(a))
    case Type.Ap(l, r) => collectAssoc(l) ++ collectAssoc(r)
    case _ => Set.empty()
}

def collectAssocInContext(cs: List[Constr]): Set[Tyassoc] = List.foldLeft(
    (set, c) -> match c {
        case Constr.Class(_, t) => set ++ collectAssoc(t)
        case Constr.Eq(l, r) => set ++ collectAssoc(l) ++ collectAssoc(r)
    }, 
    Set.empty(), 
    cs
)

def collectAssocInQual(q: Qual[Type]): Set[Tyassoc] = 
    collectAssocInContext(Qual.context(q)) ++ collectAssoc(Qual.head(q))

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
    r: Scheme[Type]
): List[Constr] \ Fresh = 
    let rcon = List.map(Fresh.freshCon >> Type.Con, Scheme.varKinds(r));
    let rinst = Instantiate.inst(rcon, Scheme.qual(r));

    let requiredClsConstrs = Set.toList(Set.map(
        x -> Constr.Class(
            ConstrEnv.getTraitOfAssoc(Tyassoc.id(x), e), Tyassoc.ty(x)
        ),
        collectAssocInQual(rinst)
    ));

    // the substitution should be empty.
    let (reducedGivs, _) = entailRepeat(e, Nil, Qual.context(rinst));
    
    let tyEq = Constr.Eq(Qual.head(l), Qual.head(rinst));
    let efPure = Constr.Eq(le, Type.efEmpty());
    let wanteds = tyEq :: efPure :: Qual.context(l) ++ requiredClsConstrs;

    fst(entailRepeat(e, reducedGivs, wanteds))