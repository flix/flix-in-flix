/// ΘP , [T / a2] π2 |= entail {π1, τ1 = [T /a2]τ2} ->! •; R
/// where T are fresh type constructors
/// --------------------------------------------------
/// ΘP |- subsume (∀a1.π1 ⇒τ1) ≤ (∀a2.π2 ⇒τ2)
pub def subsume(e: ConstrEnv, l: Scheme[Type], r: Scheme[Type]): Bool \ Fresh = 
    let lvar = List.map(Fresh.freshVar >> Type.Var, Scheme.varKinds(l));
    let rcon = List.map(Fresh.freshCon >> Type.Con, Scheme.varKinds(r));

    let linst = Instantiate.inst(lvar, Scheme.qual(l));
    let rinst = Instantiate.inst(rcon, Scheme.qual(r));

    let tyEq = Constr.Eq(EqConstr.EqConstr(Qual.head(linst), Qual.head(rinst)));
    let wanteds = tyEq :: Qual.context(linst);

    let (constr, _) = entailRepeat(e, Qual.context(rinst), wanteds);

    constr == Nil
