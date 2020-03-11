Require Import lang_spec.
Require Import VarSet.

(* TODO There has to be a library function for this somewhere but I can't find it *)
Fixpoint eq (n m : nat) : bool :=
  match n, m with
  | O, O => true
  | S n', S m' => eq n' m'
  | _, _ => false
  end.

Fixpoint substitute (e : expr) (s : expr) (x : var) : expr :=
  match e with
  | evar y =>
    if eq x y then s else e
  | (econst c) => e
  | lam y T e' =>
    if (eq x y) then e else lam y T (substitute e' s x)
  | e1 @ e2 => (substitute e1 s x) @ (substitute e2 s x)
  end.


Fixpoint expr_freevars (e : expr) : VarSet.t :=
  match e with
  | evar y => VarSet.singleton y
  | econst c => VarSet.empty
  | lam y T e' => VarSet.diff (expr_freevars e') (VarSet.singleton y)
  | e1 @ e2 => VarSet.union (expr_freevars e1) (expr_freevars e2)
  end.

Fixpoint config_freevars (c : config) : VarSet.t :=
  match c with
  | (c1 $$ c2) => VarSet.union (config_freevars c1) (config_freevars c2)
  | x ** c => VarSet.diff (config_freevars c) (VarSet.singleton x)
  | cellmake x v => VarSet.union (VarSet.singleton x) (expr_freevars v)
  | (x <- e) => VarSet.union (expr_freevars e) (VarSet.singleton x)
  | h ~ x => VarSet.union (VarSet.singleton h) (VarSet.singleton x)
  | h ~ used => VarSet.singleton h
  end.

Fixpoint config_declvars (c : config) : VarSet.t :=
  match c with
  | c1 $$ c2 => VarSet.union (config_declvars c1) (config_declvars c2)
  | x ** c => VarSet.diff (config_declvars c) (VarSet.singleton x)
  | x c= v => VarSet.singleton x
  | x <- v => VarSet.singleton x
  | h ~ x => VarSet.union (VarSet.singleton h) (VarSet.singleton x)
  | h ~ used => VarSet.singleton h
  end.
