open Hazelnut;
open Printer;

type canonical_constramnot = (Prov.t, Htyp.t);

// precondition: recieves a consistent constramnot
// postondition: returns an equivalent list of canonical (left side is hole) constriants
let rec unfold_constramnot: constramnot => list(canonical_constramnot) =
  fun
  | (Hole(p), t) => [(p, t)]
  | (t, Hole(p)) => [(p, t)]
  | (Num, Num) => []
  | (Arrow(t1, t2), Arrow(t3, t4)) =>
    unfold_constramnot((t1, t3)) @ unfold_constramnot((t2, t4))
  | (Num, Arrow(_))
  | (Arrow(_), Num) => failwith("impossible");

let unfold_constramnots: list(constramnot) => list(canonical_constramnot) =
  List.concat_map(unfold_constramnot);

let rec provs_in_typ: Htyp.t => list(Prov.t) =
  fun
  | Hole(p) => [p]
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
type data = (list(Prov.t), list(Htyp.t));
type data_elem = UnionFind.elem(data);
type prov_map = StringMap.t(data_elem);
let lookup = (p: Prov.t, m: prov_map): data_elem =>
  StringMap.find(string_of_prov(p), m);

let merge_data = ((l1, l2): data, (l3, l4): data): data => (
  l1 @ l3,
  l2 @ l4,
);

let update_data = (p: Prov.t, d: data, m: prov_map): unit => {
  let elem_p = lookup(p, m);
  UnionFind.set(elem_p, merge_data(UnionFind.get(elem_p), d));
};

let add_if_absent = (p: Prov.t, m: prov_map): prov_map =>
  if (!StringMap.mem(string_of_prov(p), m)) {
    StringMap.add(string_of_prov(p), UnionFind.make(([], [])), m);
  } else {
    m;
  };

let update_prov_map_of_constramnot =
    (c: canonical_constramnot, m: prov_map): prov_map => {
  switch (c) {
  | (p, Hole(q)) =>
    let m = add_if_absent(p, m);
    let m = add_if_absent(q, m);
    let _ = UnionFind.merge(merge_data, lookup(p, m), lookup(q, m));
    m;
  | (p, t) =>
    let m = add_if_absent(p, m);
    let qs = provs_in_typ(t);
    let m = List.fold_left((m, q) => add_if_absent(q, m), m, qs);
    List.iter(q => update_data(q, ([p], []), m), qs);
    update_data(p, ([], [t]), m);
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

let string_of_constramnot = ((t1, t2): constramnot): string => {
  string_of_htyp(t1) ++ "~" ++ string_of_htyp(t2);
};

let string_of_constramnots = (cs: list(constramnot)): string => {
  "{" ++ String.concat("\n", List.map(string_of_constramnot, cs)) ++ "}";
};

let string_of_data = ((ps, _): data): string =>
  String.concat(" | ", List.map(string_of_prov, ps));

let string_of_map = (m: prov_map): string => {
  let f: ((string, data_elem)) => string =
    ((p, d)) => p ++ ": " ++ string_of_data(UnionFind.get(d));
  let l: list((string, data_elem)) = StringMap.bindings(m);
  "{" ++ String.concat("\n", List.map(f, l)) ++ "}";
};

let go = (cs: list(constramnot)): unit => {
  print_endline("-----GO-----");
  print_endline(string_of_constramnots(cs));
  let cs = unfold_constramnots(cs);
  let m = prov_map_of_constramnots(cs);
  // print_endline("go2");
  // print_endline(string_of_int(List.length(StringMap.to_list(m))));
  print_endline(string_of_map(m));
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
