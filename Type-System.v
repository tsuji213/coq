Inductive term : Type :=
 | term_Valid_Claim   : term
 | term_Invalid_Claim : term
 | term_Evidence      : term
 | term_Undeveloped   : term
 | term_Condition     : term -> term
 | term_Intersection  : term -> term -> term
 | term_Supported     : term -> term
 | term_Strategy      : term -> term
 | term_Function      : term -> term
 | term_Alternative   : term -> term -> term
 | term_Recursion     : term -> term -> term -> term.


Inductive bool_value : term -> Prop :=
 | true : bool_value term_Valid_Claim
 | false : bool_value term_Invalid_Claim.

Hint Constructors bool_value.

Reserved Notation "t1 '==>' t2" (at level 40).

Inductive reduction : term -> term -> Prop :=
 | E_TRE : term_Evidence ==> term_Valid_Claim
 | E_FLS : term_Undeveloped ==> term_Invalid_Claim
 | E_IFT : (term_Condition term_Valid_Claim) ==> term_Evidence
 | E_IFF : (term_Condition term_Invalid_Claim) ==> term_Invalid_Claim
 | E_INTT : forall t, (term_Intersection term_Valid_Claim t) ==> t
 | E_INTF : forall t, (term_Intersection term_Invalid_Claim t) ==> term_Invalid_Claim
 | E_STR : forall t, (term_Strategy t) ==> term_Supported t
 | E_GOL : forall t t', t ==> t' -> (term_Strategy t) ==> term_Supported t
 | E_IF : forall t t', t ==> t' -> (term_Condition t) ==> term_Condition t'
 | E_INS : forall t1 t1' t2, t1 ==> t1' -> (term_Intersection t1 t2) ==> term_Intersection t1' t2
 | E_SPT : forall t, term_Alternative term_Valid_Claim t ==> term_Valid_Claim
 | E_SPF : forall t, term_Alternative term_Invalid_Claim t ==> term_Supported t
 | E_SPE : forall t1 t1' t2, t1 ==> t1' -> (term_Alternative t1 t2) ==> term_Alternative t1' t2

where "t1 '==>' t2" := (reduction t1 t2).

Hint Constructors reduction.

Inductive T : Type :=
 | T_Bool : T
 | T_Env : T.

Inductive has_Type : term -> T -> Prop :=
 | T_TRE : has_Type term_Valid_Claim T_Bool
 | T_FLS : has_Type term_Invalid_Claim T_Bool
 | T_EVI : has_Type term_Evidence T_Bool
 | T_UND : has_Type term_Undeveloped T_Bool
 | T_CON : forall t, has_Type term_Evidence T_Bool ->
                     has_Type t T_Bool ->
                     has_Type (term_Condition t) T_Bool
 | T_INS : forall t1 t2 Ty, has_Type t1 Ty ->
                            has_Type t2 Ty ->
                            has_Type (term_Intersection t1 t2) Ty
 | T_SUP : forall t Ty, has_Type t Ty ->
                        has_Type (term_Supported t) Ty
 | T_STR : forall t Ty, has_Type t Ty ->
                        has_Type (term_Strategy t) Ty
 | T_SPE : forall t1 t2 Ty, has_Type t1 Ty ->
                            has_Type t2 Ty ->
                            has_Type (term_Alternative t1 t2) Ty.

Hint Constructors has_Type.

(* ------<<< Theorem progress >>>------ *)

Theorem progress : forall t Ty, has_Type t Ty -> bool_value t \/ exists t', t ==> t'.
Proof with auto.
intros.
