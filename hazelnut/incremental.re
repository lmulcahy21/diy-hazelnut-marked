open Sexplib.Std;
// open Monad_lib.Monad; // Uncomment this line to use the maybe monad

let compare_string = String.compare;
let compare_int = Int.compare;
let compare_bool = Bool.compare;

module Ityp = {
  [@deriving sexp]
  type lower_typ = {
    skip_up: ref(upper_typ),
    child: ref(upper_typ),
  }

  and middle_typ =
    | Arrow(lower_typ, lower_typ)
    | Num
    | Hole

  and upper_typ = {
    parent: ref(option(lower_typ)),
    is_new: bool,
    middle: middle_typ,
  };
  // type t =
  //   | Arrow(edge, edge)
  //   | Num
  //   | Hole
  // and edge = {
  //   is_new: bool,
  //   exp: ref(t),
  //   parent,
  // }
  // and parent =
  //   | None
  //   | Parent(ref(t));
};

[@deriving (sexp, compare)]
type newness = bool;

module Iexp = {
  [@deriving sexp]
  type lower_exp = {
    skip_up: ref(upper_exp),
    ana: option(Ityp.upper_typ),
    marked: bool,
    child: ref(upper_exp),
  }

  and middle_exp =
    | Var(string, bool)
    | NumLit(int)
    | Plus(lower_exp, lower_exp)
    | Lam(string, Ityp.upper_typ, bool, lower_exp)
    | Ap(lower_exp, bool, lower_exp)
    | Asc(lower_exp, Ityp.upper_typ)
    | EHole

  and upper_exp = {
    parent: ref(option(lower_exp)),
    syn: option(Ityp.upper_typ),
    middle: middle_exp,
  };
  // type t =
  //   | Var(string, bool)
  //   | NumLit(int)
  //   | Plus(edge, edge)
  //   | Lam(string, Ityp.t, bool, edge)
  //   | Ap(edge, bool, edge)
  //   | Asc(edge, Ityp.t)
  //   | EHole
  // and edge = {
  //   syn: etyp,
  //   marked: bool,
  //   ana: etyp,
  //   t,
  //   parent,
  // }
  // and parent =
  //   | None
  //   | Parent(ref(t), int);
};

type program =
  | Root(Iexp.upper_exp);

let typ_hole_upper: Ityp.upper_typ = {
  parent: ref(None),
  is_new: false,
  middle: Hole,
};

let exp_hole_upper: Iexp.upper_exp = {
  parent: ref(None),
  syn: Some(typ_hole_upper),
  middle: EHole,
};

let initial_program: program = Root(exp_hole_upper);

let dummy_upper_ref = ref(exp_hole_upper);

type iaction =
  | WrapPlus;

let apply_action = (e: Iexp.upper_exp, a: iaction): unit => {
  switch (a) {
  | WrapPlus =>
    let parent = e.parent;
    let e1 = e;
    let e2: Iexp.upper_exp = exp_hole_upper;
    let new_lower_left: Iexp.lower_exp = {
      skip_up: dummy_upper_ref,
      ana: Some({parent: ref(None), is_new: true, middle: Num}),
      marked: false,
      child: ref(e1),
    };
    let new_lower_right: Iexp.lower_exp = {
      skip_up: dummy_upper_ref,
      ana: Some({parent: ref(None), is_new: false, middle: Num}),
      marked: false,
      child: ref(e2),
    };
    let new_mid: Iexp.middle_exp = Plus(new_lower_left, new_lower_right);
    let new_upper: Iexp.upper_exp = {
      parent,
      syn: Some({parent: ref(None), is_new: true, middle: Num}),
      middle: new_mid,
    };
    new_lower_left.skip_up := new_upper;
    new_lower_right.skip_up := new_upper;
    e1.parent := Some(new_lower_left);
    e2.parent := Some(new_lower_right);
    switch (parent^) {
    | None => ()
    | Some(parent_lower) => parent_lower.child := new_upper
    };
  };
};
