open Hazelnut;

module Ityp: {
  [@deriving sexp]
  type lower = {
    mutable upper,
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

module Iexp: {
  [@deriving sexp]
  type lower = {
    mutable upper,
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

  and child_ref = {mutable root_child: upper}

  and parent =
    | Deleted // root of a subtree that has been deleted
    | Root(child_ref) // root of the main program
    | Lower(lower); // child location of a constuctor
};

module Child: {
  [@deriving (sexp, compare)]
  type t =
    | One
    | Two
    | Three;
};

module Iaction: {
  [@deriving sexp]
  type t =
    | MoveUp
    | MoveDown(Child.t)
    | Delete
    | InsertNumLit(int)
    | WrapPlus1
    | WrapAp1;
};

let initial_cursor: Iexp.upper;
let initial_program: Iexp.parent;
let hexp_of_iexp: Iexp.upper => Hexp.t;
let apply_action: (Iexp.upper, Iaction.t) => Iexp.upper;
