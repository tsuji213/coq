Require Import SfLib.
Require Import Logic.
Require Import Basics.
Require Import Datatypes.

Inductive id : Type :=
  Id : nat -> id.

Fixpoint beq_nat n m : bool :=
  match n, m with
    | O, O => true
    | O, S _ => false
    | S _, O => false
    | S n1, S m1 => beq_nat n1 m1
  end.

Definition beq_id id1 id2 :=
  match (id1, id2) with
    (Id n1, Id n2) => beq_nat n1 n2
  end.

Lemma beq_nat_refl : forall n, true = beq_nat n n.
Proof.
 Admitted.

Theorem beq_id_refl : forall i,
  true = beq_id i i.
Proof.
  intros. destruct i.
  apply beq_nat_refl. Qed.

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
(*
Inductive option (A:Type) : Type :=
  | Some : A -> option A
  | None : option A.

Implicit Arguments None [A].

Definition option_map (A B:Type) (f:A->B) o :=
  match o with
    | Some a => Some (f a)
    | None => None
  end.
*)
Definition context := partial_map ty.
(*
Module Context.

Definition partial_map (A:Type) := id -> option A.

Definition empty {A:Type} : partial_map A := (fun _ => None).

Definition extend {A:Type} (Γ : partial_map A) (x:id) (T : A) :=
  fun x' => if beq_id x x' then Some T else Γ x'.

Lemma extend_eq : forall A (ctxt: partial_map A) x T,
  (extend ctxt x T) x = Some T.
Proof.
  intros. unfold extend. rewrite <- beq_id_refl. auto.
Qed.

Lemma extend_neq : forall A (ctxt: partial_map A) x1 T x2,
  beq_id x2 x1 = false ->
  (extend ctxt x2 T) x1 = ctxt x1.
Proof.
  intros. unfold extend. rewrite H. auto.
Qed.

End Context.
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



