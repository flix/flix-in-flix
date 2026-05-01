pub eff Collect {
    def collect(cns: Constr): Unit
}

mod Collect {
    pub def withCollect(f: Unit -> a \ e): (a, List[Constr]) \ e - Collect = region r {
        let constrs = Ref.fresh(r, Nil);

        let res = run f() with handler Collect {
            def collect(c, res) = {
                Ref.put(c :: Ref.get(constrs), constrs);
                res(())
            }
        };

        (res, Ref.get(constrs))
    }
}

