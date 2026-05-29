pub eff Fresh {
    def freshCon(k: Kind): Tycon
    def freshVar(k: Kind): Tyvar
}

mod Fresh {
    pub def withFresh(f: Unit -> a \ e): a \ e - Fresh = region r {
        let conRef = Ref.fresh(r, 0);
        let varRef = Ref.fresh(r, 0);

        run f() with handler Fresh {
            def freshCon(k, res) =
                let curr = Ref.get(conRef);
                Ref.put(curr + 1, conRef);
                res(Tycon.Tycon("!c${curr}", k))

            def freshVar(k, res) =
                let curr = Ref.get(varRef);
                Ref.put(curr + 1, varRef);
                res(Tyvar.Tyvar("!v${curr}", k))
        }
    }
}

pub def freshInst(s: Scheme): Qual[Type] \ Fresh = {
    let Scheme.Scheme(varKinds, qual) = s;
    let ts = List.map(k -> Type.Var(Fresh.freshVar(k)), varKinds);
    Instantiate.inst(ts, qual)
}
