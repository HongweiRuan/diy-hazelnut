open Sexplib.Std;
// open Monad_lib.Monad; // Uncomment this line to use the maybe monad

let compare_string = String.compare;
let compare_int = Int.compare;

module Htyp = {
  [@deriving (sexp, compare)]
  type t =
    | Arrow(t, t)
    | Num
    | Hole;
};

module Hexp = {
  [@deriving (sexp, compare)]
  type t =
    | Var(string)
    | Lam(string, t)
    | Ap(t, t)
    | Lit(int)
    | Plus(t, t)
    | Asc(t, Htyp.t)
    | EHole
    | NEHole(t);
};

module Ztyp = {
  [@deriving (sexp, compare)]
  type t =
    | Cursor(Htyp.t)
    | LArrow(t, Htyp.t)
    | RArrow(Htyp.t, t);
};

module Zexp = {
  [@deriving (sexp, compare)]
  type t =
    | Cursor(Hexp.t)
    | Lam(string, t)
    | LAp(t, Hexp.t)
    | RAp(Hexp.t, t)
    | LPlus(t, Hexp.t)
    | RPlus(Hexp.t, t)
    | LAsc(t, Htyp.t)
    | RAsc(Hexp.t, Ztyp.t)
    | NEHole(t);
};

module Child = {
  [@deriving (sexp, compare)]
  type t =
    | One
    | Two;
};

module Dir = {
  [@deriving (sexp, compare)]
  type t =
    | Child(Child.t)
    | Parent;
};

module Shape = {
  [@deriving (sexp, compare)]
  type t =
    | Arrow
    | Num
    | Asc
    | Var(string)
    | Lam(string)
    | Ap
    | Lit(int)
    | Plus
    | NEHole;
};

module Action = {
  [@deriving (sexp, compare)]
  type t =
    | Move(Dir.t)
    | Construct(Shape.t)
    | Del
    | Finish;
};

module TypCtx = Map.Make(String);
type typctx = TypCtx.t(Htyp.t);

exception Unimplemented;

// Effect: give the cursor erasure of a expression
let rec erase_exp = (e: Zexp.t): Hexp.t =>
  switch (e) {
  | Zexp.Cursor(e) => e
  | Zexp.Lam(x, e) => Hexp.Lam(x, erase_exp(e))
  | Zexp.LAp(e1, e2) => Hexp.Ap(erase_exp(e1), e2)
  | Zexp.RAp(e1, e2) => Hexp.Ap(e1, erase_exp(e2))
  | Zexp.LPlus(e1, e2) => Hexp.Plus(erase_exp(e1), e2)
  | Zexp.RPlus(e1, e2) => Hexp.Plus(e1, erase_exp(e2))
  | Zexp.LAsc(e, t) => Hexp.Asc(erase_exp(e), t)
  | Zexp.RAsc(e, t) => Hexp.Asc(e, erase_typ(t))
  | Zexp.NEHole(e) => Hexp.NEHole(erase_exp(e))
  }

and erase_typ = (t: Ztyp.t): Htyp.t =>
  switch (t) {
  | Ztyp.Cursor(t) => t
  | Ztyp.LArrow(t1, t2) => Htyp.Arrow(erase_typ(t1), t2)
  | Ztyp.RArrow(t1, t2) => Htyp.Arrow(t1, erase_typ(t2))
  };

let rec consistent = (t1: Htyp.t, t2: Htyp.t): bool => {
  switch (t1) {
  | Htyp.Arrow(t1Typ1, t1Typ2) =>
    switch (t2) {
    | Htyp.Arrow(t2Typ1, t2Typ2) =>
      consistent(t1Typ1, t2Typ1) && consistent(t1Typ2, t2Typ2)
    | Htyp.Hole => true
    | _ => false
    }
  | Htyp.Num =>
    switch (t2) {
    | Htyp.Num => true
    | Htyp.Hole => true
    | _ => false
    }
  | Htyp.Hole => true
  };
};

let matchArrow = (t: Htyp.t): option(Htyp.t) => {
  switch (t) {
  | Htyp.Arrow(ht1, ht2) => Some(Htyp.Arrow(ht1, ht2))
  | Htyp.Hole => Some(Htyp.Arrow(Htyp.Hole, Htyp.Hole))
  | _ => None
  };
};

let rec syn = (ctx: typctx, e: Hexp.t): option(Htyp.t) => {
  switch (e) {
  | Hexp.Var(str) => TypCtx.find_opt(str, ctx)
  | Hexp.Ap(e1, e2) =>
    let t1 = syn(ctx, e1);
    switch (t1) {
    | Some(typ) =>
      let t1Matched = matchArrow(typ);
      switch (t1Matched) {
      | Some(Htyp.Arrow(t2, t)) =>
        if (ana(ctx, e2, t2)) {
          Some(t);
        } else {
          None;
        }
      | _ => None
      };
    | _ => None
    };
  | Hexp.Lit(_) => Some(Htyp.Num)
  | Hexp.Plus(e1, e2) =>
    if (ana(ctx, e1, Htyp.Num) && ana(ctx, e2, Htyp.Num)) {
      Some(Htyp.Num);
    } else {
      None;
    }
  | Hexp.Asc(e1, t) =>
    if (ana(ctx, e1, t)) {
      Some(t);
    } else {
      None;
    }
  | Hexp.EHole => Some(Htyp.Hole)
  | Hexp.NEHole(e1) =>
    if (syn(ctx, e1) != None) {
      Some(Htyp.Hole);
    } else {
      None;
    }
  | _ => None
  };
}

and ana = (ctx: typctx, e: Hexp.t, t: Htyp.t): bool => {
  switch (e) {
  | Hexp.Lam(str, e1) =>
    let tMatched = matchArrow(t);
    switch (tMatched) {
    | Some(Htyp.Arrow(t1, t2)) =>
      let newCtx = TypCtx.add(str, t1, ctx);
      ana(newCtx, e1, t2);
    | _ => false
    };
  | _ =>
    let t1 = syn(ctx, e);
    switch (t1) {
    | Some(typ) => consistent(t, typ)
    | _ => false
    };
  };
};

// return the ztype after performing an action
let rec type_action = (t: Ztyp.t, a: Action.t): option(Ztyp.t) => {
  switch (a) {
  | Move(dr) =>
    switch (t) {
    | Cursor(Arrow(ht1, ht2)) =>
      switch (dr) {
      | Child(One) => Some(LArrow(Cursor(ht1), ht2))
      | Child(Two) => Some(RArrow(ht1, Cursor(ht2)))
      | _ => type_action_helper(t, a)
      }
    | LArrow(Cursor(ht1), ht2) =>
      switch (dr) {
      | Parent => Some(Cursor(Arrow(ht1, ht2)))
      | _ => type_action_helper(t, a)
      }
    | RArrow(ht1, Cursor(ht2)) =>
      switch (dr) {
      | Parent => Some(Cursor(Arrow(ht1, ht2)))
      | _ => type_action_helper(t, a)
      }
    | _ => type_action_helper(t, a)
    }

  | Del =>
    switch (t) {
    | Cursor(_) => Some(Cursor(Hole))
    | _ => type_action_helper(t, a)
    }

  | Construct(Arrow) =>
    switch (t) {
    | Cursor(zt1) => Some(RArrow(zt1, Cursor(Hole)))
    | _ => type_action_helper(t, a)
    }

  | Construct(Num) =>
    switch (t) {
    | Cursor(Hole) => Some(Cursor(Num))
    | _ => type_action_helper(t, a)
    }

  | _ => type_action_helper(t, a)
  };
}

and type_action_helper = (t: Ztyp.t, a: Action.t): option(Ztyp.t) => {
  switch (t) {
  | LArrow(zt1, ht1) =>
    switch (type_action(zt1, a)) {
    | Some(typ) => Some(LArrow(typ, ht1))
    | _ => None
    }
  | RArrow(ht1, zt1) =>
    switch (type_action(zt1, a)) {
    | Some(typ) => Some(RArrow(ht1, typ))
    | _ => None
    }
  | _ => None
  };
};



let rec syn_action =
        (ctx: typctx, (e: Zexp.t, t: Htyp.t), a: Action.t)
        : option((Zexp.t, Htyp.t)) => {
  switch (a) {
  | Move(_) =>
    switch (move(e, a)) {
    | Some(ze) => Some((ze, t))
    | _ => None
    }
  | Construct(shape) =>
    switch (shape) {
    | Shape.Asc =>
      switch (e) {
      | Cursor(he) => Some((RAsc(he, Cursor(t)), t))
      | _ => zipper_syn(ctx, (e, t), a)
      }
    | Shape.Var(str) =>
      if (TypCtx.mem(str, ctx)) {
        switch (e) {
        | Cursor(EHole) =>
          switch (t) {
          | Hole => Some((Cursor(Var(str)), TypCtx.find(str, ctx)))
          | _ => zipper_syn(ctx, (e, t), a)
          }
        | _ => zipper_syn(ctx, (e, t), a)
        };
      } else {
        zipper_syn(ctx, (e, t), a);
      }
    | Shape.Lam(str) =>
      switch (e) {
      | Cursor(EHole) =>
        switch (t) {
        | Hole =>
          Some((
            RAsc(Lam(str, EHole), LArrow(Cursor(Hole), Hole)),
            Arrow(Hole, Hole),
          ))
        | _ => zipper_syn(ctx, (e, t), a)
        }
      | _ => zipper_syn(ctx, (e, t), a)
      }
    | Shape.Ap =>
      switch (e) {
      | Cursor(he) =>
        switch (matchArrow(t)) {
        | Some(Arrow(_, t2)) => Some((RAp(he, Cursor(EHole)), t2))
        | _ =>
          // equavalent to t inconsistent with (Hole arrow Hole), i.e. t is Num
          Some((RAp(NEHole(he), Cursor(EHole)), Hole))
        }
      | _ => zipper_syn(ctx, (e, t), a)
      }
    | Shape.Lit(i) =>
      switch (e) {
      | Cursor(EHole) =>
        switch (t) {
        | Hole => Some((Cursor(Lit(i)), Num))
        | _ => zipper_syn(ctx, (e, t), a)
        }
      | _ => zipper_syn(ctx, (e, t), a)
      }
    | Shape.Plus =>
      switch (e) {
      | Cursor(he) =>
        if (consistent(t, Num)) {
          Some((RPlus(he, Cursor(EHole)), Num));
        } else {
          Some((RPlus(NEHole(he), Cursor(EHole)), Num));
        }
      | _ => zipper_syn(ctx, (e, t), a)
      }
    | Shape.NEHole =>
      switch (e) {
      | Cursor(he) => Some((NEHole(Cursor(he)), Hole))
      | _ => zipper_syn(ctx, (e, t), a)
      }
    | _ => None
    }
  | Del =>
    switch (e) {
    | Cursor(_) => Some((Cursor(EHole), Hole))
    | _ => zipper_syn(ctx, (e, t), a)
    }
  | Finish =>
    switch (e) {
    | Cursor(NEHole(he)) =>
      switch (t) {
      | Hole =>
        switch (syn(ctx, he)) {
        | Some(t_new) => Some((Cursor(he), t_new))
        | _ => zipper_syn(ctx, (e, t), a)
        }
      | _ => zipper_syn(ctx, (e, t), a)
      }
    | _ => zipper_syn(ctx, (e, t), a)
    }
  };
}

// return the zexp after performing action
and move = (e: Zexp.t, a: Action.t): option(Zexp.t) => {
  switch (a) {
  | Move(Child(One)) =>
    switch (e) {
    | Cursor(Asc(he, ht)) => Some(LAsc(Cursor(he), ht))
    | Cursor(Lam(st, he)) => Some(Lam(st, Cursor(he)))
    | Cursor(Plus(he1, he2)) => Some(LPlus(Cursor(he1), he2))
    | Cursor(Ap(he1, he2)) => Some(LAp(Cursor(he1), he2))
    | Cursor(NEHole(he)) => Some(NEHole(Cursor(he)))
    | _ => None
    }
  | Move(Child(Two)) =>
    switch (e) {
    | Cursor(Asc(he, ht)) => Some(RAsc(he, Cursor(ht)))
    | Cursor(Plus(he1, he2)) => Some(RPlus(he1, Cursor(he2)))
    | Cursor(Ap(he1, he2)) => Some(RAp(he1, Cursor(he2)))
    | _ => None
    }
  | Move(Parent) =>
    switch (e) {
    | LAsc(Cursor(he), ht) => Some(Cursor(Asc(he, ht)))
    | RAsc(he, Cursor(ht)) => Some(Cursor(Asc(he, ht)))
    | Lam(st, Cursor(he)) => Some(Cursor(Lam(st, he)))
    | LPlus(Cursor(he1), he2) => Some(Cursor(Plus(he1, he2)))
    | RPlus(he1, Cursor(he2)) => Some(Cursor(Plus(he1, he2)))
    | LAp(Cursor(he1), he2) => Some(Cursor(Ap(he1, he2)))
    | RAp(he1, Cursor(he2)) => Some(Cursor(Ap(he1, he2)))
    | NEHole(Cursor(he)) => Some(Cursor(NEHole(he)))
    | _ => None
    }
  | _ => None
  };
}


// chapter 3.3.8
and zipper_syn =
    (ctx: typctx, (e: Zexp.t, t: Htyp.t), a: Action.t)
    : option((Zexp.t, Htyp.t)) => {
  switch (e) {
  | LAsc(ze, ht) =>
    switch (ana_action(ctx, ze, a, ht)) {
    | Some(ze2) => Some((LAsc(ze2, ht), ht))
    | _ => None
    }
  | RAsc(he, zt) =>
    switch (type_action(zt, a)) {
    | Some(zt2) =>
      if (ana(ctx, he, erase_typ(zt2))) {
        Some((RAsc(he, zt2), erase_typ(zt2)));
      } else {
        None;
      }
    | _ => None
    }

  | LAp(ze, he) =>
    switch (syn(ctx, erase_exp(ze))) {
    | Some(ht) =>
      switch (syn_action(ctx, (ze, ht), a)) {
      | Some((ze2, ht2)) =>
        switch (matchArrow(ht2)) {
        | Some(Arrow(ht3, ht4)) =>
          if (ana(ctx, he, ht3)) {
            Some((LAp(ze2, he), ht4));
          } else {
            None;
          }
        | _ => None
        }
      | _ => None
      }
    | _ => None
    }

  | RAp(he, ze) =>
    switch (syn(ctx, he)) {
    | Some(ht) =>
      switch (matchArrow(ht)) {
      | Some(Arrow(t1, t2)) =>
        switch (ana_action(ctx, ze, a, t1)) {
        | Some(ze2) => Some((RAp(he, ze2), t2))
        | _ => None
        }
      | _ => None
      }
    | _ => None
    }

  | LPlus(ze, he) =>
    switch (t) {
    | Num =>
      switch (ana_action(ctx, ze, a, Num)) {
      | Some(ze2) => Some((LPlus(ze2, he), Num))
      | _ => None
      }
    | _ => None
    }
  | RPlus(he, ze) =>
    switch (t) {
    | Num =>
      switch (ana_action(ctx, ze, a, Num)) {
      | Some(ze2) => Some((RPlus(he, ze2), Num))
      | _ => None
      }
    | _ => None
    }
  | NEHole(ze) =>
    switch (t) {
    | Hole =>
      switch (syn(ctx, erase_exp(ze))) {
      | Some(t2) =>
        switch (syn_action(ctx, (ze, t2), a)) {
        | Some((ze2, _)) => Some((NEHole(ze2), Hole))
        | _ => None
        }
      | _ => None
      }
    | _ => None
    }
  | _ => None
  };
}

// operates differently depending on whether the H-expression
// under the cursor is being analyzed against a type.
and ana_action =
    (ctx: typctx, e: Zexp.t, a: Action.t, t: Htyp.t): option(Zexp.t) => {
  switch (a) {
  | Move(_) =>
    switch (move(e, a)) {
    | Some(e_new) => Some(e_new)
    | _ => zipper_ana_action(ctx, e, a, t)
    }

  | Del =>
    switch (e) {
    | Cursor(_) => Some(Cursor(EHole))
    | _ => zipper_ana_action(ctx, e, a, t)
    }

  | Construct(Asc) =>
    switch (e) {
    | Cursor(he) => Some(RAsc(he, Cursor(t)))
    | _ => zipper_ana_action(ctx, e, a, t)
    }
  | Construct(Var(st)) =>
    switch (e) {
    | Cursor(EHole) =>
      if (TypCtx.mem(st, ctx)) {
        if (!consistent(TypCtx.find(st, ctx), t)) {
          Some(NEHole(Cursor(Var(st))));
        } else {
          zipper_ana_action(ctx, e, a, t);
        };
      } else {
        zipper_ana_action(ctx, e, a, t);
      }
    | _ => zipper_ana_action(ctx, e, a, t)
    }
  | Construct(Lam(st)) =>
    switch (e) {
    | Cursor(EHole) =>
      switch (matchArrow(t)) {
      | Some(Arrow(_, _)) => Some(Lam(st, Cursor(EHole)))
      | _ =>
        Some(NEHole(RAsc(Lam(st, EHole), LArrow(Cursor(Hole), Hole))))
      }
    | _ => zipper_ana_action(ctx, e, a, t)
    }
  | Construct(Lit(i)) =>
    switch (e) {
    | Cursor(EHole) =>
      if (!consistent(t, Num)) {
        Some(NEHole(Cursor(Lit(i))));
      } else {
        zipper_ana_action(ctx, e, a, t);
      }
    | _ => zipper_ana_action(ctx, e, a, t)
    }

  | Finish =>
    switch (e) {
    | Cursor(NEHole(he)) =>
      if (ana(ctx, he, t)) {
        Some(Cursor(he));
      } else {
        zipper_ana_action(ctx, e, a, t);
      }
    | _ => zipper_ana_action(ctx, e, a, t)
    }
  | _ => zipper_ana_action(ctx, e, a, t)
  };
}


// similar to ana
and zipper_ana_action =
    (ctx: typctx, e: Zexp.t, a: Action.t, t: Htyp.t): option(Zexp.t) => {
  switch (e) {
  | Lam(st, ze) =>
    switch (matchArrow(t)) {
    | Some(Arrow(t1, t2)) =>
      let ctx_new = TypCtx.add(st, t1, ctx);
      switch (ana_action(ctx_new, ze, a, t2)) {
      | Some(ze_new) => Some(Lam(st, ze_new))
      | _ => subsumption(ctx, e, a, t)
      };
    | _ => subsumption(ctx, e, a, t)
    }
  | _ => subsumption(ctx, e, a, t)
  };
}

// chapter 3.3.3
and subsumption =
    (ctx: typctx, e: Zexp.t, a: Action.t, t: Htyp.t): option(Zexp.t) => {
  switch (syn(ctx, erase_exp(e))) {
  | Some(t_new) =>
    switch (syn_action(ctx, (e, t_new), a)) {
    | Some((ze_new, t_new2)) =>
      if (consistent(t, t_new2)) {
        Some(ze_new);
      } else {
        None;
      }
    | _ => None
    }
  | _ => None
  };
};
