Require Export preservation.

Definition normal_form {X:Type} (R:relation X) (t:X) : Prop :=
  ~ (exists t', R t t').

Notation reduction_normal_form := (normal_form reduction).

Definition stuck (t:term) : Prop :=
  reduction_normal_form t /\ ~ bool_value t.

Hint Unfold stuck.

