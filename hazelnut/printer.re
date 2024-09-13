open Hazelnut;

module Pexp = {
  type t =
    | Cursor(t)
    | Arrow(t, t)
    | Num
    | Var(string)
    | Lam(string, t, t)
    | Ap(t, t)
    | NumLit(int)
    | Plus(t, t)
    | Asc(t, t)
    | EHole(string)
    | MarkHole(t, string, string);
};

let string_of_id = (u: Id.t): string => string_of_int(u);

let rec string_of_prov: Prov.t => string =
  fun
  | Surface(u) => string_of_id(u)
  | Syn(u) => "<=(" ++ string_of_id(u) ++ ")"
  | LArrow(p) => "->L(" ++ string_of_prov(p) ++ ")"
  | RArrow(p) => "->R(" ++ string_of_prov(p) ++ ")";

let string_of_mark: Mark.t => string = {
  fun
  | Free => "Free"
  | NonArrowAp => "NonArrowAp"
  | LamAscIncon => "LamAscIncon"
  | Inconsistent => "Inconsistent";
};

let rec pexp_of_htyp: Htyp.t => Pexp.t =
  fun
  | Arrow(t1, t2) => Arrow(pexp_of_htyp(t1), pexp_of_htyp(t2))
  | Num => Num
  | Hole(p) => EHole(string_of_prov(p))
  | EHole => EHole("");

let rec pexp_of_hexp: Hexp.t => Pexp.t =
  fun
  | Var(x) => Var(x)
  | Lam(x, a, e) => Lam(x, pexp_of_htyp(a), pexp_of_hexp(e))
  | Ap(e1, e2) => Ap(pexp_of_hexp(e1), pexp_of_hexp(e2))
  | NumLit(n) => NumLit(n)
  | Plus(e1, e2) => Plus(pexp_of_hexp(e1), pexp_of_hexp(e2))
  | Asc(e, t) => Asc(pexp_of_hexp(e), pexp_of_htyp(t))
  | EHole(u) => EHole(string_of_id(u))
  | Mark(e, u, m) =>
    MarkHole(pexp_of_hexp(e), string_of_id(u), string_of_mark(m));

let rec pexp_of_ztyp: Ztyp.t => Pexp.t =
  fun
  | Cursor(t) => Cursor(pexp_of_htyp(t))
  | LArrow(t1, t2) => Arrow(pexp_of_ztyp(t1), pexp_of_htyp(t2))
  | RArrow(t1, t2) => Arrow(pexp_of_htyp(t1), pexp_of_ztyp(t2));

let rec pexp_of_zexp: Zexp.t => Pexp.t =
  fun
  | Cursor(e) => Cursor(pexp_of_hexp(e))
  | LLam(x, a, e) => Lam(x, pexp_of_ztyp(a), pexp_of_hexp(e))
  | RLam(x, a, e) => Lam(x, pexp_of_htyp(a), pexp_of_zexp(e))
  | LAp(e1, e2) => Ap(pexp_of_zexp(e1), pexp_of_hexp(e2))
  | RAp(e1, e2) => Ap(pexp_of_hexp(e1), pexp_of_zexp(e2))
  | LPlus(e1, e2) => Plus(pexp_of_zexp(e1), pexp_of_hexp(e2))
  | RPlus(e1, e2) => Plus(pexp_of_hexp(e1), pexp_of_zexp(e2))
  | LAsc(e, t) => Asc(pexp_of_zexp(e), pexp_of_htyp(t))
  | RAsc(e, t) => Asc(pexp_of_hexp(e), pexp_of_ztyp(t))
  | Mark(e, u, m) =>
    MarkHole(pexp_of_zexp(e), string_of_id(u), string_of_mark(m));

// Lower is tighter
let rec prec: Pexp.t => int =
  fun
  | Cursor(e) => prec(e)
  | Arrow(_) => 1
  | Num => 0
  | Var(_) => 0
  | Lam(_) => 0
  | Ap(_) => 2
  | NumLit(_) => 0
  | Plus(_) => 3
  | Asc(_) => 4
  | EHole(_) => 0
  | MarkHole(_) => 0;

module Side = {
  type t =
    | Left
    | Right
    | Atom;
};

let rec assoc: Pexp.t => Side.t =
  fun
  | Cursor(e) => assoc(e)
  | Arrow(_) => Right
  | Num => Atom
  | Var(_) => Atom
  | Lam(_) => Atom
  | Ap(_) => Left
  | NumLit(_) => Atom
  | Plus(_) => Left
  | Asc(_) => Left
  | EHole(_) => Atom
  | MarkHole(_) => Atom;

let rec string_of_pexp: Pexp.t => string =
  fun
  | Cursor(e) => "👉" ++ string_of_pexp(e) ++ "👈"
  | Arrow(t1, t2) as outer =>
    "("
    ++ paren(t1, outer, Side.Left)
    ++ " -> "
    ++ paren(t2, outer, Side.Right)
    ++ ")"
  | Num => "Num"
  | Var(x) => x
  | Lam(x, a, e) =>
    "(fun "
    ++ x
    ++ ": "
    ++ string_of_pexp(a)
    ++ " -> "
    ++ string_of_pexp(e)
    ++ ")"
  | Ap(e1, e2) as outer =>
    "("
    ++ paren(e1, outer, Side.Left)
    ++ " "
    ++ paren(e2, outer, Side.Right)
    ++ ")"
  | NumLit(n) => string_of_int(n)
  | Plus(e1, e2) as outer =>
    paren(e1, outer, Side.Left) ++ " + " ++ paren(e2, outer, Side.Right)
  | Asc(e, t) as outer =>
    paren(e, outer, Side.Left) ++ " : " ++ paren(t, outer, Side.Right)
  | EHole(p) => "{ " ++ p ++ " }"
  | MarkHole(e, u, m) =>
    "{ " ++ string_of_pexp(e) ++ " | " ++ m ++ " | " ++ u ++ " }"

and paren = (inner: Pexp.t, outer: Pexp.t, side: Side.t): string => {
  let unparenned = string_of_pexp(inner);
  let parenned = "(" ++ unparenned ++ ")";

  let prec_inner = prec(inner);
  let prec_outer = prec(outer);

  if (prec_inner < prec_outer) {
    unparenned;
  } else if (prec_inner > prec_outer) {
    parenned;
  } else {
    switch (assoc(inner), side) {
    | (Side.Left, Side.Right)
    | (Side.Right, Side.Left) => parenned
    | _ => unparenned
    };
  };
};

let string_of_htyp = t => string_of_pexp(pexp_of_htyp(t));
let string_of_zexp = z => string_of_pexp(pexp_of_zexp(z));
