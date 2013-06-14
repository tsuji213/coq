
Require Import SfLib.
Require Import Logic.
Require Import Basics.

Inductive ty : Type :=
  | ty_Bool : ty
  | ty_arrow : ty -> ty -> ty.

Inductive tm : Type :=
  | tm_var : id -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : id -> ty -> tm -> tm
  | tm_true : tm
  | tm_false : tm
  | tm_if : tm -> tm -> tm -> tm.

Tactic Notation "tm_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "tm_var" | Case_aux c "tm_app"
  | Case_aux c "tm_abs" | Case_aux c "tm_true"
  | Case_aux c "tm_false" | Case_aux c "tm_if" ].

Definition context := partial_map ty.

Inductive option (A:Type) : Type :=
  | Some : A -> option A
  | None : option A.

(*
Definition option_map (A B:Type) (f:A->B) o (a:A):=
  match o with
    | Some a => Some (f a)
    | None => None
  end.
*)

Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall (Γ:context) (x: id) (T : ty),
      extend Γ x T = Some T ->
      has_type Γ (tm_var x) T
  | T_Abs : forall Γ x T11 T12 t12,
      has_type (extend Γ x T11) t12 T12 ->
      has_type Γ (tm_abs x T11 t12) (ty_arrow T11 T12)
  | T_App : forall T11 T12 Γ t1 t2,
      has_type Γ t1 (ty_arrow T11 T12) ->
      has_type Γ t2 T11 ->
      has_type Γ (tm_app t1 t2) T12
  | T_True : forall Γ,
       has_type Γ tm_true ty_Bool
  | T_False : forall Γ,
       has_type Γ tm_false ty_Bool
  | T_If : forall t1 t2 t3 T Γ,
       has_type Γ t1 ty_Bool ->
       has_type Γ t2 T ->
       has_type Γ t3 T ->
       has_type Γ (tm_if t1 t2 t3) T.

Tactic Notation "has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_Var" | Case_aux c "T_Abs"
  | Case_aux c "T_App" | Case_aux c "T_True"
  | Case_aux c "T_False" | Case_aux c "T_If" ].

Hint Constructors has_type.



