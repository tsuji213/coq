Require Export Type_System.

Theorem preservation : forall t t' T, has_Type t T ->
                                      t ==> t' ->
                                      has_Type t' T.

Proof with auto.
intros.
generalize dependent t'.
has_type_cases (induction H) Case;
intros.
try (solve by inversion).
try (solve by inversion).

Case "T_EVI".
inversion H0.
auto.

Case "T_UND".
inversion H0.
auto.

Case "T_CON".
inversion H1.
subst.

SCase "E_IFT".
assumption.
SCase "E_IFF".
auto.

apply T_CON;
try assumption.
apply IHhas_Type2.
assumption.

Case "T_INS".
inversion H1.
subst.
SCase "E_INTT". assumption.
SCase "E_INTF".
subst.
assumption.

apply T_INS; try assumption.
apply IHhas_Type1.
assumption.


Case "T_SUP".
inversion H0.
subst.

SCase "E_GOLT". 
auto.
SCase "E_GOLF".
subst.
auto.

subst.
apply IHhas_Type.
auto.

Case "T_STR".
inversion H0.
subst.

SCase "E_STRT". assumption.
SCase "E_STRF".
subst.
assumption.

apply T_SUP.
subst.
apply IHhas_Type.
assumption.

Case "T_SPE".
inversion H1.
subst.

SCase "E_SPT". assumption.
SCase "E_SPF". 
subst.
apply T_SUP.
assumption.

apply T_SPE.
subst.
apply IHhas_Type1.
assumption.
auto.
Qed.

Check preservation.
