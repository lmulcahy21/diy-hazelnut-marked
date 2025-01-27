open Sexplib.Std;
open Hazelnut;
// open Monad_lib.Monad; // Uncomment this line to use the maybe monad

// To use structure sharing, we can't use mutable types
// module Ityp = {
//   [@deriving sexp]
//   type lower = {
//     mutable upper,
//     mutable child: upper,
//   }

//   and middle =
//     | Arrow(lower, lower)
//     | Num
//     | Hole

//   and upper = {
//     mutable parent: option(lower),
//     mutable is_new: bool,
//     middle,
//   };
// };

// let rec htyp_of_ityp: Ityp.upper => Htyp.t =
//   upper => htyp_of_ityp_middle(upper.middle)

// and htyp_of_ityp_middle: Ityp.middle => Htyp.t =
//   middle =>
//     switch (middle) {
//     | Arrow(t1, t2) =>
//       Arrow(htyp_of_ityp_lower(t1), htyp_of_ityp_lower(t2))
//     | Num => Num
//     | Hole => Hole
//     }
// and htyp_of_ityp_lower: Ityp.lower => Htyp.t =
//   lower => htyp_of_ityp(lower.child);

module Iexp = {
  [@deriving sexp]
  type lower = {
    mutable upper,
    ana: option(Htyp.t),
    marked: bool,
    mutable child: upper,
  }

  and middle =
    | Var(string, bool)
    | NumLit(int)
    | Plus(lower, lower)
    | Lam(string, Htyp.t, bool, lower)
    | Ap(lower, bool, lower)
    | Asc(lower, Htyp.t)
    | EHole

  and upper = {
    mutable parent,
    syn: option(Htyp.t),
    middle,
  }

  and child_ref = {mutable root_child: upper}

  and parent =
    | Deleted // root of a subtree that has been deleted
    | Root(child_ref) // root of the main program
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
      markif(m, LamAscIncon, Lam(x, t, hexp_of_iexp_lower(e)))
    | Ap(e1, m, e2) =>
      markif(
        m,
        NonArrowAp,
        Ap(hexp_of_iexp_lower(e1), hexp_of_iexp_lower(e2)),
      )
    | Asc(e, t) => Asc(hexp_of_iexp_lower(e), t)
    | EHole => EHole
    }
and hexp_of_iexp_lower: Iexp.lower => Hexp.t =
  lower => markif(lower.marked, Inconsistent, hexp_of_iexp(lower.child));

let _print_iexp_upper: Iexp.upper => unit =
  upper =>
    print_endline(
      "iexp print: " ++ string_of_sexp(Iexp.sexp_of_upper(upper)),
    );

// let typ_hole_upper: bool => Ityp.upper =
//   is_new => {
//     parent: None,
//     is_new,
//     middle: Hole,
//   };

// let typ_num_upper: bool => Ityp.upper =
//   is_new => {
//     parent: None,
//     is_new,
//     middle: Num,
//   };

let exp_hole_upper: Iexp.upper = {
  parent: Deleted,
  syn: Some(Hole),
  middle: EHole,
};

let initial_cursor: Iexp.upper = exp_hole_upper;
let initial_program: Iexp.parent = {
  let r: Iexp.child_ref = {root_child: initial_cursor};
  initial_cursor.parent = Root(r);
  Root(r);
};

let dummy_upper = exp_hole_upper;

// let freshen_typ = (t: option(Ityp.upper)): unit => {
//   switch (t) {
//   | None => ()
//   | Some(upper) => upper.is_new = true
//   };
// };

// let freshen_ana_in_parent = (p: Iexp.parent): unit => {
//   switch (p) {
//   | Deleted
//   | Root(_) => ()
//   | Lower(r) => freshen_typ(r.ana)
//   };
// };

let set_child_in_parent = (p: Iexp.parent, c: Iexp.upper): unit => {
  switch (p) {
  | Deleted => ()
  | Root(r) => r.root_child = c
  | Lower(r) => r.child = c
  };
};

let upper_of_parent = (p: Iexp.parent): option(Iexp.upper) => {
  switch (p) {
  | Deleted
  | Root(_) => None
  | Lower(r) => Some(r.upper)
  };
};

module Child = {
  [@deriving (sexp, compare)]
  type t =
    | One
    | Two
    | Three;
};

module Iaction = {
  [@deriving sexp]
  type t =
    | MoveUp
    | MoveDown(Child.t)
    | Delete
    | InsertNumLit(int)
    | WrapPlus(Child.t)
    | WrapAp(Child.t);
};

let apply_action = (e: Iexp.upper, a: Iaction.t): Iexp.upper => {
  let e_parent = e.parent;
  switch (a) {
  | MoveUp =>
    switch (upper_of_parent(e.parent)) {
    | None => e
    | Some(e') => e'
    }

  | MoveDown(child) =>
    switch (e.middle) {
    | Var(_, _)
    | NumLit(_)
    | EHole => e
    | Plus(e1, e2) =>
      switch (child) {
      | One => e1.child
      | Two => e2.child
      | Three => e
      }
    | Lam(_, _, _, e1) =>
      switch (child) {
      | One => e1.child
      | Two
      | Three => e
      }
    | Ap(e1, _, e2) =>
      switch (child) {
      | One => e1.child
      | Two => e2.child
      | Three => e
      }
    | Asc(e1, _) =>
      switch (child) {
      | One => e1.child
      | Two
      | Three => e
      }
    }

  | Delete =>
    let e': Iexp.upper = {
      parent: e.parent,
      syn: Some(Hole),
      middle: EHole,
    };
    set_child_in_parent(e.parent, e');
    // freshen_ana_in_parent(e.parent);
    e.parent = Deleted;
    e';
  | InsertNumLit(x) =>
    // Numlits have no lower Iexp, so we can just create a new upper for it to link to the NumLit middle
    switch (e.middle) {
    | EHole =>
      let e': Iexp.upper = {
        parent: e_parent,
        syn: Some(Num),
        middle: NumLit(x),
      };
      set_child_in_parent(e_parent, e');
      // freshen_ana_in_parent(e_parent);
      e.parent = Deleted;
      e';
    | _ => e
    }

  | WrapPlus(child) =>
    let make_plus_with_children = (e1, e2) => {
      // Create the new lower expressions with the correct children and new syn
      // But we can't instantiate the skip-up pointers yet
      let new_lower_left: Iexp.lower = {
        upper: dummy_upper,
        ana: Some(Num),
        marked: false,
        child: e1,
      };
      // In this case, we don't need to mark the syn of the hole as new, since
      // We can take the shortcut of computing consistency (trivially true)
      let new_lower_right: Iexp.lower = {
        upper: dummy_upper,
        ana: Some(Num),
        marked: false,
        child: e2,
      };
      // Continue to form the middle and upper expressions with the right
      // "children" (not pointers to children), and using the remembered parent
      let new_mid: Iexp.middle = Plus(new_lower_left, new_lower_right);
      let new_upper: Iexp.upper = {
        parent: e_parent,
        syn: Some(Num),
        middle: new_mid,
      };

      // Now the parents of the children and the child of the parent must be
      // updated, as well as the skip-up pointers.
      new_lower_left.upper = new_upper;
      new_lower_right.upper = new_upper;
      set_child_in_parent(e_parent, new_upper);
      e1.parent = Lower(new_lower_left);
      e2.parent = Lower(new_lower_right);
      set_child_in_parent(e1.parent, e1);
      set_child_in_parent(e2.parent, e2);
      new_upper;
    };
    switch (child) {
    | One => make_plus_with_children(e, exp_hole_upper)
    | Two => make_plus_with_children(exp_hole_upper, e)
    | Three => e
    };

  | WrapAp(child) =>
    // child 1 = exp becomes fun
    // child 2 = exp becomes arg
    let make_ap_with_children = (e1, e2) => {
      let new_lower_left: Iexp.lower = {
        upper: dummy_upper,
        ana: None,
        marked: false,
        child: e1,
      };
      let new_lower_right: Iexp.lower = {
        upper: dummy_upper,
        ana: None,
        marked: false,
        child: e2,
      };
      let new_mid: Iexp.middle = Ap(new_lower_left, false, new_lower_right);
      let new_upper: Iexp.upper = {
        parent: e_parent,
        syn: None,
        middle: new_mid,
      };
      new_lower_left.upper = new_upper;
      new_lower_right.upper = new_upper;
      set_child_in_parent(e_parent, new_upper);
      // Note that e1 or e2 is e, so modifying them modifies e
      e1.parent = Lower(new_lower_left);
      e2.parent = Lower(new_lower_right);
      set_child_in_parent(e1.parent, e1);
      set_child_in_parent(e2.parent, e2);
      new_upper;
    };
    switch (child) {
    | One =>
      // freshen_typ(e.syn); // TODO this will need to return a worker list
      make_ap_with_children(e, exp_hole_upper)
    | Two =>
      // freshen_typ(e.syn); // TODO this will need to return a worker list
      make_ap_with_children(exp_hole_upper, e)
    | Three => e
    };
  };
};
