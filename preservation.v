Require Export Type_System.

Theorem preservation : forall t t' T, has_Type t T ->
                                      t ==> t' ->
                                      has_Type t' T.

Proof with auto.
