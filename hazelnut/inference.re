open Hazelnut;
open Printer;

type canonical_constramnot =
  | Con(Prov.t, Htyp.t);

// precondition: recieves a consistent constramnot
// postondition: returns an equivalent list of canonical (left side is hole) constriants
let rec unfold_constramnot: constramnot => list(canonical_constramnot) =
  fun
  | Con(Hole(p), t) => [Con(p, t)]
  | Con(t, Hole(p)) => [Con(p, t)]
  | Con(EHole, _) => []
  | Con(_, EHole) => []
  | Con(Num, Num) => []
  | Con(Arrow(t1, t2), Arrow(t3, t4)) =>
    unfold_constramnot(Con(t1, t3): constramnot)
    @ unfold_constramnot(Con(t2, t4))
  | Con(Num, Arrow(_))
  | Con(Arrow(_), Num) => failwith("impossible");

let unfold_constramnots: list(constramnot) => list(canonical_constramnot) =
  List.concat_map(unfold_constramnot);

let rec provs_in_typ: Htyp.t => list(Prov.t) =
  fun
  | Hole(p) => [p]
  | EHole => []
  | Num => []
  | Arrow(t1, t2) => provs_in_typ(t1) @ provs_in_typ(t2);

// let rec provs_in_constramnots: list(canonical_constramnot) => list(Prov.t) =
//   fun
//   | [] => []
//   | [(p, t), ...tl] => [p] @ provs_in_typ(t) @ provs_in_constramnots(tl);

// let uniq_provs: list(Prov.t) => list(Prov.t) =
//   List.sort_uniq((p1, p2) =>
//     String.compare(string_of_prov(p1), string_of_prov(p2))
//   );

module StringMap = Map.Make(String);
type data = (Prov.t, list(Prov.t), list(Htyp.t));
type data_elem = UnionFind.elem(data);
type prov_map = StringMap.t(data_elem);
let lookup = (p: Prov.t, m: prov_map): data_elem =>
  StringMap.find(string_of_prov(p), m);
let lookup_get = (p: Prov.t, m: prov_map): data =>
  UnionFind.get(lookup(p, m));

let merge_data = ((p, l1, l2): data, (_, l3, l4): data): data => (
  p,
  l1 @ l3,
  l2 @ l4,
);

let update_data = (p: Prov.t, d: data, m: prov_map): unit => {
  let elem_p = lookup(p, m);
  UnionFind.set(elem_p, merge_data(UnionFind.get(elem_p), d));
};

let add_if_absent = (p: Prov.t, m: prov_map): prov_map =>
  if (!StringMap.mem(string_of_prov(p), m)) {
    StringMap.add(string_of_prov(p), UnionFind.make((p, [], [])), m);
  } else {
    m;
  };

let update_prov_map_of_constramnot =
    (c: canonical_constramnot, m: prov_map): prov_map => {
  switch (c) {
  | Con(p, Hole(q)) =>
    let m = add_if_absent(p, m);
    let m = add_if_absent(q, m);
    let _ = UnionFind.merge(merge_data, lookup(p, m), lookup(q, m));
    m;
  | Con(p, t) =>
    let m = add_if_absent(p, m);
    let qs = provs_in_typ(t);
    let m = List.fold_left((m, q) => add_if_absent(q, m), m, qs);
    List.iter(q => update_data(q, (Syn(0), [p], []), m), qs);
    update_data(p, (Syn(0), [], [t]), m);
    m;
  };
};

let prov_map_of_constramnots = (cs: list(canonical_constramnot)): prov_map => {
  List.fold_left(
    (m, c) => update_prov_map_of_constramnot(c, m),
    StringMap.empty,
    cs,
  );
};

let find_dominant_provs = (m: prov_map): list(Prov.t) => {
  List.filter_map(
    ((_, d)) => {
      let (p, qs, _) = UnionFind.get(d);
      if (List.length(qs) == 0) {
        Some(p);
      } else {
        None;
      };
    },
    StringMap.bindings(m),
  );
};

type solution =
  | Hole
  | Num
  | Arrow(solution, solution)
  | Multi(list(solution)) // Nums before arrows
  | Cyclic;

let rec refine_solution = (s: solution, t: Htyp.t): solution => {
  switch (s, t) {
  | (s, Hole(_)) => s
  | (s, EHole) => s
  | (Hole, Num) => Num
  | (Hole, Arrow(t1, t2)) =>
    Arrow(refine_solution(Hole, t1), refine_solution(Hole, t2))
  | (Num, Num) => Num
  | (Num, Arrow(t1, t2)) =>
    Multi([
      Num,
      Arrow(refine_solution(Hole, t1), refine_solution(Hole, t2)),
    ])
  | (Arrow(s1, s2), Num) => Multi([Num, Arrow(s1, s2)])
  | (Arrow(s1, s2), Arrow(t1, t2)) =>
    Arrow(refine_solution(s1, t1), refine_solution(s2, t2))
  | (Multi(ss), t) => Multi(ss @ [refine_solution(Hole, t)]) // TODO: compress possibilities
  // | (Multi([]), _)
  // | (Multi([Hole, ..._]), _)
  // | (Multi([Multi(_), ..._]), _)
  // | (Multi([Cyclic, ..._]), _) => failwith("impossible")
  // | (Multi([Num, ...ss]), Num) => Multi([Num, ...ss])
  // | (Multi([Arrow(s1, s2), ...ss]), Num) =>
  //   Multi([Num, Arrow(s1, s2), ...ss])
  // | (Multi([Num, ...ss]), Arrow(t1, t2)) => Multi(todo)
  // | (Multi(ss), Arrow(t1, t2)) => Multi(todo)
  | (Cyclic, _) => Cyclic
  };
};

let solve_prov = (p: Prov.t, m: prov_map): solution => {
  let (_, _, ts) = UnionFind.get(StringMap.find(string_of_prov(p), m));
  print_endline(
    string_of_prov(p)
    ++ "  constrained to "
    ++ String.concat(",", List.map(string_of_htyp, ts)),
  );
  List.fold_left(refine_solution, Hole, ts);
};

let rec solution_typ_rec = (p: Prov.t, s: solution): Htyp.t => {
  switch (s) {
  | Hole => Hole(p)
  | Num => Num
  | Arrow(s1, s2) =>
    Arrow(
      solution_typ_rec(LArrow(p), s1),
      solution_typ_rec(RArrow(p), s2),
    )
  | Multi(_) => EHole
  | Cyclic => EHole
  };
};

let solution_typ = (p: Prov.t, s: solution): Htyp.t => {
  switch (s) {
  | Hole => EHole
  | Multi(_) => EHole
  | Cyclic => EHole
  | Num
  | Arrow(_) => solution_typ_rec(p, s)
  };
};

// let rec alter_hole_once_solved = (p : Prov.t, q: Prov.t, st: Htyp.t, m : prov_map) : Htyp.t => {
//   let eq(p', q') = UnionFind.eq(lookup(p', m), lookup(q', m));
//   if (eq(p,q)) { st } else {
//     switch(q, st) {
//       | (LArrow(q), Arrow(s1, s2)) => {
//         switch(alter_hole_once_solved(p))
//       }
//       | _ => failwith("un")
//     }
//   }
// }

let rec solution_typ_replace_typ =
        (p: Prov.t, t: Htyp.t, st: Htyp.t, m: prov_map): Htyp.t => {
  switch (t) {
  // | Hole(q) when UnionFind.eq(lookup(p, m), lookup(q, m)) => st
  | Hole(q) when p == q => st
  | Hole(q) => Hole(q)
  // | Hole(Surface(u)) => Hole(Surface(u))
  // | Hole(Syn(u)) => Hole(Syn(u))
  // | Hole(LArrow(q)) =>
  //   switch (solution_typ_replace_typ(p, Hole(q), st, m)) {
  //   | EHole => EHole
  //   | Num => EHole
  //   | Hole(q') => Hole(LArrow(q'))
  //   | Arrow(t1, _) => t1
  //   }
  // | Hole(RArrow(q)) =>
  //   switch (solution_typ_replace_typ(p, Hole(q), st, m)) {
  //   | EHole => EHole
  //   | Num => EHole
  //   | Hole(q') => Hole(RArrow(q'))
  //   | Arrow(_, t2) => t2
  //   }
  | EHole => EHole
  | Num => Num
  | Arrow(t1, t2) =>
    Arrow(
      solution_typ_replace_typ(p, t1, st, m),
      solution_typ_replace_typ(p, t2, st, m),
    )
  };
};

let solution_typ_replace_con =
    (p: Prov.t, Con(t1, t2): constramnot, st: Htyp.t, m: prov_map)
    : constramnot => {
  Con(
    solution_typ_replace_typ(p, t1, st, m),
    solution_typ_replace_typ(p, t2, st, m),
  );
};

let solution_typ_replace_cons =
    (p: Prov.t, cs: list(constramnot), st: Htyp.t, m: prov_map)
    : list(constramnot) =>
  List.map(c => solution_typ_replace_con(p, c, st, m), cs);

type sol_map = StringMap.t(solution);

let extend_sol_map =
    (cs: list(constramnot), sm: sol_map)
    : option((list(constramnot), sol_map)) => {
  let canonical_cs = unfold_constramnots(cs); // make constraints canonical
  let m = prov_map_of_constramnots(canonical_cs); // compute provenance map
  switch (find_dominant_provs(m)) {
  // if you find a dominant provenance...
  | [] => None
  | [p, ..._] =>
    Some(
      {
        let s = solve_prov(p, m); // solve it
        print_endline("solved " ++ string_of_prov(p));
        let st = solution_typ(p, s); // turn it into a type
        let ps =
          List.filter_map(
            ((p', p_elem)) =>
              if (UnionFind.eq(lookup(p, m), StringMap.find(p', m))) {
                let (canonical_p, _, _) = UnionFind.get(p_elem);
                Some(canonical_p);
              } else {
                None;
              },
            StringMap.bindings(m),
          );
        let cs' =
          List.fold_left(
            (cs_acc, pss) => solution_typ_replace_cons(pss, cs_acc, st, m),
            cs,
            ps,
          ); // replace it with the solution type in constraints
        // let sm' = solution_typ_replace_sol_map(...)
        let sm' =
          List.fold_left(
            (sm_acc, pss) => StringMap.add(string_of_prov(pss), s, sm_acc),
            sm,
            ps,
          ); // and update the solution map
        (cs', sm');
      },
    )
  };
};

let string_of_constramnot = (Con(t1, t2): constramnot): string => {
  string_of_htyp(t1) ++ "~" ++ string_of_htyp(t2);
};

let string_of_constramnots = (cs: list(constramnot)): string => {
  "{" ++ String.concat("\n", List.map(string_of_constramnot, cs)) ++ "}";
};

let string_of_data = ((_, ps, ts): data): string =>
  "["
  ++ String.concat(", ", List.map(string_of_prov, ps))
  ++ "] | ["
  ++ String.concat(", ", List.map(string_of_htyp, ts))
  ++ "]";

let string_of_prov_map = (m: prov_map): string => {
  let f: ((string, data_elem)) => string =
    ((p, d)) => p ++ ": " ++ string_of_data(UnionFind.get(d));
  let l: list((string, data_elem)) = StringMap.bindings(m);
  "{" ++ String.concat("\n", List.map(f, l)) ++ "}";
};

let rec string_of_solution =
  fun
  | Hole => "?"
  | Num => "Num"
  | Arrow(s1, s2) =>
    "(" ++ string_of_solution(s1) ++ "->" ++ string_of_solution(s2) ++ ")"
  | Multi(ss) =>
    "{" ++ String.concat("|", List.map(string_of_solution, ss)) ++ "}"
  | Cyclic => "{Cyclic}";

let string_of_sol_map = (m: sol_map): string => {
  let f: ((string, solution)) => string =
    ((p, d)) => p ++ ": " ++ string_of_solution(d);
  let l: list((string, solution)) = StringMap.bindings(m);
  "{" ++ String.concat("\n", List.map(f, l)) ++ "}";
};

// Note: when removing a provenance p after solving it:
// If it was solved as inconsistent, remove all provs that end in p, recursively

let rec solve_rec = (cs: list(constramnot), sm: sol_map): sol_map => {
  switch (extend_sol_map(cs, sm)) {
  | None =>
    print_endline(string_of_constramnots(cs));
    sm;
  | Some((cs', sm')) => solve_rec(cs', sm')
  };
};

let solve = (cs: list(constramnot)): sol_map =>
  solve_rec(cs, StringMap.empty);

let go = (cs: list(constramnot)): unit => {
  print_endline("-----GO-----");
  print_endline(string_of_constramnots(cs));
  let sm = solve(cs);
  print_endline(string_of_sol_map(sm));
  // let cs = unfold_constramnots(cs);
  // let m = prov_map_of_constramnots(cs);
  // print_endline("go2");
  // print_endline(string_of_int(List.length(StringMap.to_list(m))));
  // print_endline(string_of_prov_map(m));
};

// module ProvGraph = Map.Make(Prov.t);
// type prov_graph = ProvGraph.t(list(Htyp.t));

// Actually the keys are provenances
// module ProvGraph = Map.Make(String);
// type prov_graph = ProvGraph.t(list(Htyp.t));
// module ProvEquiv = UnionFind.Make(A);
// type prov_equiv = UnionFind.Make(string);

// let canonize = (e: prov_equiv, p: Prov.t): option(Prov.t) => {
//   ProvGraph.find_opt(Hazelnut.string_of_prov(p), e)
// };

// g maps canonical provenances to a list of concrete types
// e maps non-canonical provenances to the canonical provenance
// let extend_inclusion_graph = (c : canonical_constramnot, g : prov_graph, e : prov_equiv) : prov_graph => {
//   switch(c) {
//     | (p, Hole(q)) => let _ = UnionFind.union(make(p), make(q)); g
//     | (p, t) =>
//   }
// }

// let construct_inclusion_graph : list(canonical_constramnot) => prov_graph
