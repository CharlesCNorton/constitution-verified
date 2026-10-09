(******************************************************************************)
(*  WitnessCheck.v                                                            *)
(*                                                                            *)
(*  Every clause of the Constitution holds of the witness World.  The clause  *)
(*  predicates are unfolded and each conjunct is discharged: act-based clauses *)
(*  by expanding the witness act list, structural clauses by computation on   *)
(*  the witness fields, and quantified membership clauses by the lemmas of    *)
(*  Witness.v.                                                                *)
(******************************************************************************)

From CV Require Import Types Act Data World Preamble Art1_Congress Art1_Lawmaking
  Art1_Limits Art2 Art3 Art4 Art5_7 Amend_BoR Amend_11_19 Amend_20_27
  Constitutional Witness.
From Stdlib Require Import List Arith Lia.
Import ListNotations.

Lemma categories_listed : forall c : CaseCategory, In c listed_categories.
Proof. destruct c; simpl; tauto. Qed.

Lemma resolution_navy_effective : resolution_effective resolution_navy.
Proof.
  unfold resolution_effective, passed_both, passes, quorum_met, resolution_navy,
    v_house, v_senate.
  simpl. repeat split; first [ reflexivity | lia | (left; reflexivity) ].
Qed.

Ltac unfold_helpers :=
  try unfold quorum_met;
  try unfold passes;
  try unfold two_thirds_present;
  try unfold passed_both;
  try unfold overridden;
  try unfold resolution_effective;
  try unfold eligible_for_president;
  try unfold eligible_after_22;
  try unfold representative_qualified;
  try unfold senator_qualified;
  try unfold two_thirds_of_states;
  try unfold three_fourths_of_states;
  try unfold ballot_valid.

(* Each leaf is a single conjunct, and each alternative must close its goal.
   The population bound and the membership lemmas are matched exactly, without
   computation; every other leaf is decided by simplification or by computing
   its closed value. *)
Ltac solve_leaf :=
  first
    [ exact pop_leq_witness
    | exact house_qualified
    | exact senate_qualified
    | exact senate_two_per_state
    | exact seats_ge_one
    | exact witness_ballots_valid
    | exact preamble_ends_nodup
    | exact categories_listed
    | exact resolution_navy_effective
    | (unfold_helpers; try simpl;
       first
         [ solve [trivial]
         | solve [reflexivity]
         | solve [congruence]
         | solve [lia]
         | solve [intuition congruence]
         | solve [intuition lia]
         | solve [vm_compute; reflexivity]
         | solve [vm_compute; lia]
         | solve [repeat split; vm_compute; reflexivity]
         | solve [repeat split; vm_compute; lia]
         | solve [intros; reflexivity]
         | solve [intros; intuition congruence] ]) ].

(* An act-based clause: expand the witness act list and discharge each act. *)
Ltac solve_acts :=
  apply forall_acts_of_Forall;
  rewrite witness_acts_eq; unfold witness_acts;
  repeat (apply Forall_cons; [ solve_leaf | idtac ]);
  apply Forall_nil.

Theorem witness_constitutional : Constitutional witness_world.
Proof.
  unfold Constitutional.
  unfold P_1,
    I_1_1, I_2_1, I_2_2, I_2_3, I_2_4, I_2_5, I_2_6, I_2_7, I_2_8, I_2_9, I_2_10,
    I_3_1, I_3_2, I_3_3, I_3_4, I_3_5, I_3_6, I_3_7, I_3_8, I_4_1, I_4_2,
    I_5_1, I_5_2, I_5_3, I_5_4, I_6_1, I_6_2, I_6_3, I_6_4, I_6_5,
    I_7_1, I_7_2, I_7_3, I_7_4, I_7_5,
    I_8_1, I_8_2, I_8_3, I_8_4, I_8_5, I_8_6, I_8_7, I_8_8, I_8_9, I_8_10,
    I_8_11, I_8_12, I_8_13, I_8_14, I_8_15, I_8_16, I_8_17, I_8_18,
    I_9_1, I_9_2, I_9_3, I_9_4, I_9_5, I_9_6, I_9_7, I_9_8, I_10_1, I_10_2, I_10_3,
    II_1_1, II_1_2, II_1_3, II_1_4, II_1_5, II_1_6, II_1_7, II_1_8, II_1_9, II_1_10,
    II_2_1, II_2_2, II_2_3, II_2_4, II_3_1, II_3_2, II_3_3, II_3_4, II_4_1,
    III_1_1, III_1_2, III_2_1, III_2_2, III_2_3, III_3_1, III_3_2, III_3_3,
    IV_1_1, IV_2_1, IV_2_2, IV_2_3, IV_3_1, IV_3_2, IV_4_1, IV_4_2, IV_4_3,
    V_1, V_2, V_3, V_4, VI_1, VI_2, VI_3, VI_4, VII_1, BR1789_1,
    A1_1, A1_2, A1_3, A1_4, A1_5, A1_6, A2_1, A3_1, A3_2, A4_1, A4_2, A4_3,
    A5_1, A5_2, A5_3, A5_4, A5_5, A6_1, A6_2, A6_3, A6_4, A6_5, A6_6, A6_7,
    A7_1, A7_2, A8_1, A8_2, A8_3, A9_1, A10_1,
    A11_1, A12_1, A12_2, A12_3, A12_4, A12_5, A13_s1, A13_s2,
    A14_s1_cit, A14_s1_priv, A14_s1_dp, A14_s1_ep, A14_s2_basis, A14_s2_reduce,
    A14_s3, A14_s4_debt, A14_s4_rebel, A14_s5, A15_s1, A15_s2, A16_1,
    A17_s1, A17_s2, A17_s3, A18_s1, A18_s2, A18_s3, A19_s1, A19_s2,
    A20_s1, A20_s2, A20_s3, A20_s4, A20_s5, A20_s6, A21_s1, A21_s2, A21_s3,
    A22_s1, A22_s2, A23_s1, A23_s2, A24_s1, A24_s2,
    A25_s1, A25_s2, A25_s3, A25_s4_a, A25_s4_b, A25_s4_c, A26_s1, A26_s2, A27_s1.
  repeat (match goal with |- _ /\ _ => split end).
  all: first [ solve_acts | solve_leaf ].
Qed.
