open Sexplib.Std;
// open Monad_lib.Monad; // Uncomment this line to use the maybe monad

let compare_string = String.compare;
let compare_int = Int.compare;
let compare_bool = Bool.compare;

module Ityp = {
  [@deriving sexp]
  type lower = {
    mutable skip_up: upper,
    mutable child: upper,
  }

  and middle =
    | Arrow(lower, lower)
    | Num
    | Hole

  and upper = {
    mutable parent: option(lower),
    mutable is_new: bool,
    middle,
  };
};

[@deriving (sexp, compare)]
type newness = bool;

module Iexp = {
  [@deriving sexp]
  type lower = {
    mutable skip_up: upper,
    ana: option(Ityp.upper),
    marked: bool,
    mutable child: upper,
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
    mutable parent: option(lower),
    syn: option(Ityp.upper),
    middle,
  };
};

type program =
  | Root(ref(Iexp.upper));

let typ_hole_upper: bool => Ityp.upper =
  is_new => {parent: None, is_new, middle: Hole};

let typ_num_upper: bool => Ityp.upper =
  is_new => {parent: None, is_new, middle: Num};

let exp_hole_upper: bool => Iexp.upper =
  is_new => {
    parent: None,
    syn: Some(typ_hole_upper(is_new)),
    middle: EHole,
  };

let initial_program: program = Root(ref(exp_hole_upper(false)));

let dummy_upper = exp_hole_upper(false);

type iaction =
  | Delete
  | InsertNumLit(int)
  | WrapPlus1;

let freshen_typ = (t: option(Ityp.upper)): unit => {
  switch (t) {
  | None => ()
  | Some(upper) => upper.is_new = true
  };
};

let freshen_ana_in_parent = (p: option(Iexp.lower)): unit => {
  switch (p) {
  | None => ()
  | Some(lower) => freshen_typ(lower.ana)
  };
};

let set_child_in_parent = (p: option(Iexp.lower), c: Iexp.upper): unit => {
  switch (p) {
  | None => ()
  | Some(lower) => lower.child = c
  };
};

let apply_action = (e: Iexp.upper, a: iaction): unit => {
  switch (a) {
  | Delete =>
    let e': Iexp.upper = exp_hole_upper(true);
    e'.parent = e.parent;
    set_child_in_parent(e.parent, e');
    freshen_ana_in_parent(e.parent);
  | InsertNumLit(x) =>
    let e': Iexp.upper = {
      parent: None,
      syn: Some(typ_num_upper(true)),
      middle: NumLit(x),
    };
    e'.parent = e.parent;
    set_child_in_parent(e.parent, e');
    freshen_ana_in_parent(e.parent);
  | WrapPlus1 =>
    // The target of the action becomes the left child
    let e1 = e;
    // An empty hole becomes the right child
    let e2: Iexp.upper = exp_hole_upper(false);
    // We need to save the parent of the target for later
    let old_parent = e1.parent;

    // Create the new lower expressions with the correct children and new syn
    // But we can't instantiate the skip-up pointers yet
    let new_lower_left: Iexp.lower = {
      skip_up: dummy_upper,
      ana: Some({parent: None, is_new: true, middle: Num}),
      marked: false,
      child: e1,
    };
    // In this case, we don't need to mark the syn of the hole as new, since
    // We can take the shortcut of computing consistency (trivially true)
    let new_lower_right: Iexp.lower = {
      skip_up: dummy_upper,
      ana: Some({parent: None, is_new: false, middle: Num}),
      marked: false,
      child: e2,
    };
    // Continue to form the middle and upper expressions with the right
    // "children" (not pointers to children), and using the remembered parent
    let new_mid: Iexp.middle = Plus(new_lower_left, new_lower_right);
    let new_upper: Iexp.upper = {
      parent: old_parent,
      syn: Some({parent: None, is_new: true, middle: Num}),
      middle: new_mid,
    };

    // Now the parents of the children and the child of the parent must be
    // updated, as well as the skip-up pointers.
    new_lower_left.skip_up = new_upper;
    new_lower_right.skip_up = new_upper;
    e1.parent = Some(new_lower_left);
    e2.parent = Some(new_lower_right);
    set_child_in_parent(old_parent, new_upper);
  };
};
