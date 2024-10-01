open Sexplib.Std;
// open Monad_lib.Monad; // Uncomment this line to use the maybe monad

let compare_string = String.compare;
let compare_int = Int.compare;
let compare_bool = Bool.compare;

module Ityp = {
  [@deriving sexp]
  type lower = {
    skip_up: ref(upper),
    child: ref(upper),
  }

  and middle =
    | Arrow(lower, lower)
    | Num
    | Hole

  and upper = {
    parent: ref(option(lower)),
    is_new: bool,
    middle,
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
  type lower = {
    skip_up: ref(upper),
    ana: option(Ityp.upper),
    marked: bool,
    child: ref(upper),
  }

  and middle =
    | Var(string, bool)
    | NumLit(int)
    | Plus(lower, lower)
    | Lam(string, Ityp.upper, bool, lower)
    | Ap(lower, bool, lower)
    | Asc(lower, Ityp.upper)
    | EHole

  and upper = {
    parent: ref(option(lower)),
    syn: option(Ityp.upper),
    middle,
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
  | Root(Iexp.upper);

let typ_hole_upper: Ityp.upper = {
  parent: ref(None),
  is_new: false,
  middle: Hole,
};

let exp_hole_upper: Iexp.upper = {
  parent: ref(None),
  syn: Some(typ_hole_upper),
  middle: EHole,
};

let initial_program: program = Root(exp_hole_upper);

let dummy_upper_ref = ref(exp_hole_upper);

type iaction =
  | WrapPlus;

let apply_action = (e: Iexp.upper, a: iaction): unit => {
  switch (a) {
  | WrapPlus =>
    // The target of the action becomes the left child
    let e1 = e;
    // An empty hole becomes the right child
    let e2: Iexp.upper = exp_hole_upper;
    // We need to save the parent of the target for later
    let old_parent = e1.parent^;

    // Create the new lower expressions with the correct children and new syn
    // But we can't instantiate the skip-up pointers yet
    let new_lower_left: Iexp.lower = {
      skip_up: dummy_upper_ref,
      ana: Some({parent: ref(None), is_new: true, middle: Num}),
      marked: false,
      child: ref(e1),
    };
    // In this case, we don't need to mark the syn of the hole as new, since
    // We can take the shortcut of computing consistency (trivially true)
    let new_lower_right: Iexp.lower = {
      skip_up: dummy_upper_ref,
      ana: Some({parent: ref(None), is_new: false, middle: Num}),
      marked: false,
      child: ref(e2),
    };
    // Continue to form the middle and upper expressions with the right
    // "children" (not pointers to children), and using the remembered parent
    let new_mid: Iexp.middle = Plus(new_lower_left, new_lower_right);
    let new_upper: Iexp.upper = {
      parent: ref(old_parent),
      syn: Some({parent: ref(None), is_new: true, middle: Num}),
      middle: new_mid,
    };

    // Now the parents of the children and the child of the parent must be
    // updated, as well as the skip-up pointers.
    new_lower_left.skip_up := new_upper;
    new_lower_right.skip_up := new_upper;
    e1.parent := Some(new_lower_left);
    e2.parent := Some(new_lower_right);
    switch (old_parent) {
    | None => ()
    | Some(parent_lower) => parent_lower.child := new_upper
    };
  };
};
