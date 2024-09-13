open Core;
open Incr_dom;
open Monad_lib.Monad;
module Hazelnut = Hazelnut_lib.Hazelnut;
module Inference = Hazelnut_lib.Inference;
module Printer = Hazelnut_lib.Printer;

[@deriving (sexp, fields, compare)]
type state = {
  e: Hazelnut.Zexp.t,
  warning: option(string),
  var_input: string,
  lam_input: string,
  let_input: string,
  lit_input: string,
  bool_input: string,
};

module Model = {
  [@deriving (sexp, fields, compare)]
  type t = {state};

  let set = (s: state): t => {state: s};

  let init = (): t =>
    set({
      e: Cursor(EHole(Hazelnut.fresh_id())),
      warning: None,
      var_input: "",
      lam_input: "",
      let_input: "",
      lit_input: "",
      bool_input: "true | false",
    });

  let cutoff = (t1: t, t2: t): bool => compare(t1, t2) == 0;
};

module Action = {
  [@deriving sexp]
  type input_location =
    | Var
    | Lam
    | Let
    | NumLit
    | BoolLit;

  [@deriving sexp]
  type action =
    | HazelnutAction(Hazelnut.Action.t)
    | UpdateInput(input_location, string)
    | ShowWarning(string);

  [@deriving sexp]
  type t = list(action);
};

module State = {
  type t = unit;
};

let apply_action =
    (model: Model.t, actions: Action.t, _, ~schedule_action as _): Model.t => {
  let f = (model: Model.t, action: Action.action): Model.t => {
    let state = model.state;

    let warn = (warning: string): Model.t =>
      Model.set({...state, warning: Some(warning)});

    switch (action) {
    | HazelnutAction(action) =>
      try({
        let e = Hazelnut.exp_action(state.e, action);

        let new_state = {...state, e, warning: None};

        Model.set(new_state);
      }) {
      | Hazelnut.Unimplemented => warn("Unimplemented")
      }
    | UpdateInput(Var, var_input) => Model.set({...state, var_input})
    | UpdateInput(Lam, lam_input) => Model.set({...state, lam_input})
    | UpdateInput(Let, let_input) => Model.set({...state, let_input})
    | UpdateInput(NumLit, lit_input) => Model.set({...state, lit_input})
    | UpdateInput(BoolLit, bool_input) => Model.set({...state, bool_input})
    | ShowWarning(warning) => Model.set({...state, warning: Some(warning)})
    };
  };

  List.fold_left(actions, ~init=model, ~f);
};

let on_startup = (~schedule_action as _, _) => Async_kernel.return();

let view =
    (m: Incr.t(Model.t), ~inject: Action.t => Ui_effect.t(Base.unit))
    : Ui_incr.t(Vdom.Node.t) => {
  open Incr.Let_syntax;
  open Vdom;

  let%map body = {
    let%map state = m >>| Model.state;

    let e_cursor = state.e;

    let e_no_cursor = Hazelnut.erase_exp(e_cursor);

    let (e_marked, t, cs) =
      Hazelnut.mark_syn(Hazelnut.TypCtx.empty, e_no_cursor);

    Inference.go(cs);

    let e_folded = Hazelnut.fold_zexp_mexp(e_cursor, e_marked);

    let expression =
      Node.div([
        Node.p([Node.textf("%s", Printer.string_of_zexp(e_folded))]),
        Node.p([Node.textf("%s", Printer.string_of_htyp(t))]),
      ]);

    let buttons = {
      let button =
          (
            label: string,
            action: Action.action,
            input: option((Action.input_location, string)),
          )
          : Node.t => {
        let button_node = {
          let actions =
            switch (input) {
            | Some((input_location, _)) => [
                action,
                Action.UpdateInput(input_location, ""),
              ]
            | None => [action]
            };

          Node.button(
            ~attrs=[Attr.on_click(_ev => inject(actions))],
            [Node.text(label)],
          );
        };

        let input_node = {
          let+ (input_location, input_value) = input;
          Node.input(
            ~attrs=[
              Attr.type_("text"),
              Attr.string_property("value", input_value),
              Attr.on_input((_ev, text) =>
                inject([Action.UpdateInput(input_location, text)])
              ),
            ],
            (),
          );
        };

        Node.div(
          switch (input_node) {
          | Some(input_node) => [button_node, input_node]
          | None => [button_node]
          },
        );
      };

      let move_buttons =
        Node.div([
          button(
            "Move to Parent",
            Action.HazelnutAction(Move(Parent)),
            None,
          ),
          button(
            "Move to Child 1",
            Action.HazelnutAction(Move(Child(One))),
            None,
          ),
          button(
            "Move to Child 2",
            Action.HazelnutAction(Move(Child(Two))),
            None,
          ),
          button(
            "Move to Child 3",
            Action.HazelnutAction(Move(Child(Three))),
            None,
          ),
        ]);

      let construct_buttons =
        Node.div([
          button(
            "Construct Arrow",
            Action.HazelnutAction(Construct(Arrow)),
            None,
          ),
          button(
            "Construct Num",
            Action.HazelnutAction(Construct(Num)),
            None,
          ),
          button(
            "Construct Asc",
            Action.HazelnutAction(Construct(Asc)),
            None,
          ),
          button(
            "Construct Var",
            Action.HazelnutAction(Construct(Var(state.var_input))),
            Some((Var, state.var_input)),
          ),
          button(
            "Construct Lam",
            Action.HazelnutAction(Construct(Lam(state.lam_input))),
            Some((Lam, state.lam_input)),
          ),
          button(
            "Construct Ap",
            Action.HazelnutAction(Construct(Ap)),
            None,
          ),
          button(
            "Construct NumLit",
            try(
              Action.HazelnutAction(
                Construct(NumLit(int_of_string(state.lit_input))),
              )
            ) {
            | Failure(_) => Action.ShowWarning("Invalid input")
            },
            Some((NumLit, state.lit_input)),
          ),
          button(
            "Construct Plus",
            Action.HazelnutAction(Construct(Plus)),
            None,
          ),
        ]);

      let delete_button =
        Node.div([button("Delete", Action.HazelnutAction(Del), None)]);

      Node.div([move_buttons, construct_buttons, delete_button]);
    };

    let warning =
      Node.p(
        switch (state.warning) {
        | Some(warning) => [Node.text(warning)]
        | None => []
        },
      );

    Node.div([expression, buttons, warning]);
  };

  Node.body([body]);
};

let create = (model, ~old_model as _, ~inject) => {
  open Incr.Let_syntax;
  let%map apply_action = {
    let%map model = model;
    apply_action(model);
  }
  and view = view(model, ~inject)
  and model = model;
  Component.create(~apply_action, model, view);
};

let initial_model = Model.init();
