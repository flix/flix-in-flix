use Expr.infer

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
                Collect.withCollect(() -> infer(initialAssums, expr));

            (id, subsume(env, Qual.Qual(constrs, ty), ef, sch))
        }, 
        decls
    )
}

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

    let tyEq = Constr.Eq(Qual.head(l), Qual.head(rinst));
    let efPure = Constr.Eq(le, Type.efEmpty());

    let wanteds = tyEq :: efPure :: Qual.context(l);

    fst(entailRepeat(e, Qual.context(rinst), wanteds))
