open Sexplib.Std;
open Hazelnut;
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

let rec htyp_of_ityp: Ityp.upper => Htyp.t =
  upper => htyp_of_ityp_middle(upper.middle)

and htyp_of_ityp_middle: Ityp.middle => Htyp.t =
  middle =>
    switch (middle) {
    | Arrow(t1, t2) =>
      Arrow(htyp_of_ityp_lower(t1), htyp_of_ityp_lower(t2))
    | Num => Num
    | Hole => Hole
    }
and htyp_of_ityp_lower: Ityp.lower => Htyp.t =
  lower => htyp_of_ityp(lower.child);

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
    mutable parent,
    syn: option(Ityp.upper),
    middle,
  }

  and parent =
    | Deleted // root of a subtree that has been deleted
    | Root({mutable child: upper}) // root of the main program
    | Lower(lower); // child location of a constuctor
};

let markif = (b: bool, m: Mark.t, exp: Hexp.t): Hexp.t =>
  if (b) {
    Mark(exp, m);
  } else {
    exp;
  };

let rec hexp_of_iexp: Iexp.upper => Hexp.t =
  upper => hexp_of_iexp_middle(upper.middle)

and hexp_of_iexp_middle: Iexp.middle => Hexp.t =
  middle =>
    switch (middle) {
    | Var(x, m) => markif(m, Free, Var(x))
    | NumLit(x) => NumLit(x)
    | Plus(e1, e2) => Plus(hexp_of_iexp_lower(e1), hexp_of_iexp_lower(e2))
    | Lam(x, t, m, e) =>
      markif(
        m,
        LamAscIncon,
        Lam(x, htyp_of_ityp(t), hexp_of_iexp_lower(e)),
      )
    | Ap(e1, m, e2) =>
      markif(
        m,
        NonArrowAp,
        Ap(hexp_of_iexp_lower(e1), hexp_of_iexp_lower(e2)),
      )
    | Asc(e, t) => Asc(hexp_of_iexp_lower(e), htyp_of_ityp(t))
    | EHole => EHole
    }
and hexp_of_iexp_lower: Iexp.lower => Hexp.t =
  lower => markif(lower.marked, Inconsistent, hexp_of_iexp(lower.child));

let typ_hole_upper: bool => Ityp.upper =
  is_new => {parent: None, is_new, middle: Hole};

let typ_num_upper: bool => Ityp.upper =
  is_new => {parent: None, is_new, middle: Num};

let exp_hole_upper: bool => Iexp.upper =
  is_new => {
    parent: Deleted,
    syn: Some(typ_hole_upper(is_new)),
    middle: EHole,
  };

let dummy_upper = exp_hole_upper(false);

let freshen_typ = (t: option(Ityp.upper)): unit => {
  switch (t) {
  | None => ()
  | Some(upper) => upper.is_new = true
  };
};

let freshen_ana_in_parent = (p: Iexp.parent): unit => {
  switch (p) {
  | Deleted
  | Root(_) => ()
  | Lower(r) => freshen_typ(r.ana)
  };
};

let set_child_in_parent = (p: Iexp.parent, c: Iexp.upper): unit => {
  switch (p) {
  | Deleted => ()
  | Root(r) => r.child = c
  | Lower(r) => r.child = c
  };
};

type iaction =
  | Delete
  | InsertNumLit(int)
  | WrapPlus1
  | WrapAp1;

let apply_action = (e: Iexp.upper, a: iaction): Iexp.upper => {
  switch (a) {
  | Delete =>
    let e': Iexp.upper = {
      parent: e.parent,
      syn: Some(typ_hole_upper(true)),
      middle: EHole,
    };
    set_child_in_parent(e.parent, e');
    freshen_ana_in_parent(e.parent);
    e.parent = Deleted;
    e';

  | InsertNumLit(x) =>
    let e': Iexp.upper = {
      parent: e.parent,
      syn: Some(typ_num_upper(true)),
      middle: NumLit(x),
    };
    set_child_in_parent(e.parent, e');
    freshen_ana_in_parent(e.parent);
    e.parent = Deleted;
    e';

  | WrapPlus1 =>
    // The target of the action becomes the left child
    let e1 = e;
    // An empty hole becomes the right child
    let e2: Iexp.upper = exp_hole_upper(false);

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
      parent: e1.parent,
      syn: Some({parent: None, is_new: true, middle: Num}),
      middle: new_mid,
    };

    // Now the parents of the children and the child of the parent must be
    // updated, as well as the skip-up pointers.
    new_lower_left.skip_up = new_upper;
    new_lower_right.skip_up = new_upper;
    set_child_in_parent(e1.parent, new_upper);
    e1.parent = Lower(new_lower_left);
    e2.parent = Lower(new_lower_right);
    new_upper;

  | WrapAp1 =>
    let e1 = e;
    freshen_typ(e1.syn); // TODO this will need to return a worker list
    let e2 = exp_hole_upper(true);
    let new_lower_left: Iexp.lower = {
      skip_up: dummy_upper,
      ana: None,
      marked: false,
      child: e1,
    };
    let new_lower_right: Iexp.lower = {
      skip_up: dummy_upper,
      ana: None,
      marked: false,
      child: e2,
    };
    let new_mid: Iexp.middle = Ap(new_lower_left, false, new_lower_right);
    let new_upper: Iexp.upper = {
      parent: e1.parent,
      syn: None,
      middle: new_mid,
    };
    new_lower_left.skip_up = new_upper;
    new_lower_right.skip_up = new_upper;
    let old_parent = e1.parent;
    e1.parent = Lower(new_lower_left);
    e2.parent = Lower(new_lower_right);
    set_child_in_parent(old_parent, new_upper);
    new_upper;
  };
};
