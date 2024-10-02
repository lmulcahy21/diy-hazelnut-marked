open Hazelnut;

module Ityp: {
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

module Iexp: {
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

type iaction =
  | Delete
  | InsertNumLit(int)
  | WrapPlus1
  | WrapAp1;

let hexp_of_iexp: Iexp.upper => Hexp.t;
let apply_action: (Iexp.upper, iaction) => Iexp.upper;
