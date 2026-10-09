(******************************************************************************)
(*  Constitution.v                                                            *)
(*                                                                            *)
(*  Top level.  The Constitution is a predicate on a World (Constitutional);  *)
(*  this file states that some World satisfies it, and draws consequences     *)
(*  from individual clauses that hold for every World satisfying it.          *)
(******************************************************************************)

From CV Require Import Types Act Data World Preamble Art1_Congress Art1_Lawmaking
  Art1_Limits Art2 Art3 Art4 Art5_7 Amend_BoR Amend_11_19 Amend_20_27
  Constitutional Witness WitnessCheck.
From Stdlib Require Import List Arith Lia.
Import ListNotations.

(* The Constitution is satisfiable: the witness World meets every clause. *)
Theorem constitution_satisfiable : exists w : World, Constitutional w.
Proof.
  exists witness_world. exact witness_constitutional.
Qed.

(* Art. I, s. 7, cl. 2: every enacted measure passed both Houses and was presented
   to the President. *)
Theorem enacted_law_passed_both_houses :
  forall w, Constitutional w ->
  forall m, In (EnactLaw m) (w_acts w) -> passed_both m /\ m.(m_presented) = true.
Proof.
  intros w H m Hm.
  assert (H72 : I_7_2 w) by (unfold Constitutional in H; decompose [and] H; assumption).
  unfold I_7_2, forall_laws, forall_acts in H72.
  specialize (H72 (EnactLaw m) Hm). simpl in H72.
  destruct H72 as [_ [Hp Hpres]]. split; assumption.
Qed.

(* Art. I, s. 7, cl. 2: a vetoed measure that became law was passed over by two
   thirds of each House. *)
Theorem vetoed_law_overridden :
  forall w, Constitutional w ->
  forall m, In (EnactLaw m) (w_acts w) -> m.(m_action) = Vetoed -> overridden m.
Proof.
  intros w H m Hm Hv.
  assert (H73 : I_7_3 w) by (unfold Constitutional in H; decompose [and] H; assumption).
  unfold I_7_3, forall_laws, forall_acts in H73.
  specialize (H73 (EnactLaw m) Hm). simpl in H73.
  apply H73. exact Hv.
Qed.

(* Article V: an amendment is ratified only by three fourths of the States. *)
Theorem ratification_three_fourths :
  forall w, Constitutional w ->
  forall n s mode y, In (RatifyAmendment n s mode y) (w_acts w) -> three_fourths_of_states s.
Proof.
  intros w H n s mode y Hn.
  assert (HV2 : V_2 w) by (unfold Constitutional in H; decompose [and] H; assumption).
  unfold V_2, forall_acts in HV2.
  specialize (HV2 (RatifyAmendment n s mode y) Hn). simpl in HV2. exact HV2.
Qed.

(* Art. I, s. 9, cl. 3: no enacted measure is a bill of attainder or ex post facto law. *)
Theorem enacted_law_not_attainder :
  forall w, Constitutional w ->
  forall m, In (EnactLaw m) (w_acts w) -> ~ In Attainder (m_features m).
Proof.
  intros w H m Hm.
  assert (H93 : I_9_3 w) by (unfold Constitutional in H; decompose [and] H; assumption).
  unfold I_9_3, forall_laws, forall_acts in H93.
  specialize (H93 (EnactLaw m) Hm). simpl in H93. exact (proj1 H93).
Qed.

(* Art. II, s. 1, cl. 5 and Amendment XXII, s. 1: a registered presidential candidate
   is eligible under both rules. *)
Theorem registered_candidate_eligible :
  forall w, Constitutional w ->
  forall p, In (CandidateRegistration p) (w_acts w) ->
  eligible_for_president p /\ eligible_after_22 p.
Proof.
  intros w H p Hp.
  assert (H17 : II_1_7 w) by (unfold Constitutional in H; decompose [and] H; assumption).
  assert (H221 : A22_s1 w) by (unfold Constitutional in H; decompose [and] H; assumption).
  unfold II_1_7, A22_s1, forall_acts in H17, H221.
  split.
  - exact (H17 (CandidateRegistration p) Hp).
  - exact (H221 (CandidateRegistration p) Hp).
Qed.

(* Amendment XXV, s. 1: absent an inability and a vacancy in the Vice Presidency,
   the Vice President succeeds the President. *)
Theorem succession_by_vice_president :
  forall w, Constitutional w ->
  forall t s, In (Succession t s false) (w_acts w) -> t <> TriggerInability ->
  s = SuccessorVicePresident.
Proof.
  intros w H t s Hs Ht.
  assert (HA : A25_s1 w) by (unfold Constitutional in H; decompose [and] H; assumption).
  unfold A25_s1, forall_acts in HA.
  specialize (HA (Succession t s false) Hs). simpl in HA.
  exact (HA Ht eq_refl).
Qed.
