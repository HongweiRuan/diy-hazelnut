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

let matchedArrow = (t: Htyp.t): option(Htyp.t) => {
  switch (t) {
  | Htyp.Arrow(ht1, ht2) => Some(Htyp.Arrow(ht1, ht2))
  | Htyp.Hole => Some(Htyp.Arrow(Htyp.Hole, Htyp.Hole))
  | _ => None
  };
};


let rec syn = (ctx: typctx, e: Hexp.t): option(Htyp.t) => {
  switch (e) {
  | Hexp.Var(str) =>
    if (TypCtx.mem(str, ctx)) {
      Some(TypCtx.find(str, ctx));
    } else {
      None;
    }
  | Hexp.Ap(e1, e2) =>
    let t1 = syn(ctx, e1);
    switch (t1) {
    | Some(typ) =>
      let t1Matched = matchedArrow(typ);
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
    let tMatched = matchedArrow(t);
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

let syn_action =
    (ctx: typctx, (e: Zexp.t, t: Htyp.t), a: Action.t)
    : option((Zexp.t, Htyp.t)) => {
  // Used to suppress unused variable warnings
  // Okay to remove
  let _ = ctx;
  let _ = e;
  let _ = t;
  let _ = a;

  raise(Unimplemented);
}

and ana_action =
    (ctx: typctx, e: Zexp.t, a: Action.t, t: Htyp.t): option(Zexp.t) => {
  // Used to suppress unused variable warnings
  // Okay to remove
  let _ = ctx;
  let _ = e;
  let _ = a;
  let _ = t;

  raise(Unimplemented);
};
