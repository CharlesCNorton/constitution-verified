(******************************************************************************)
(*  Constitutional.v                                                          *)
(*                                                                            *)
(*  The Constitution as a single predicate on a World: the conjunction of     *)
(*  every clause in CLAUSES.tsv, in the order of that manifest.               *)
(******************************************************************************)

From CV Require Import Types Act Data World Preamble Art1_Congress
  Art1_Lawmaking Art1_Limits Art2 Art3 Art4 Art5_7 Amend_BoR Amend_11_19
  Amend_20_27.

Definition Constitutional (w : World) : Prop :=
  (* Preamble *)
  P_1 w /\
  (* Article I, s. 1 to 6 *)
  I_1_1 w /\ I_2_1 w /\ I_2_2 w /\ I_2_3 w /\ I_2_4 w /\ I_2_5 w /\ I_2_6 w /\
  I_2_7 w /\ I_2_8 w /\ I_2_9 w /\ I_2_10 w /\
  I_3_1 w /\ I_3_2 w /\ I_3_3 w /\ I_3_4 w /\ I_3_5 w /\ I_3_6 w /\ I_3_7 w /\
  I_3_8 w /\
  I_4_1 w /\ I_4_2 w /\
  I_5_1 w /\ I_5_2 w /\ I_5_3 w /\ I_5_4 w /\
  I_6_1 w /\ I_6_2 w /\ I_6_3 w /\ I_6_4 w /\ I_6_5 w /\
  (* Article I, s. 7 and 8 *)
  I_7_1 w /\ I_7_2 w /\ I_7_3 w /\ I_7_4 w /\ I_7_5 w /\
  I_8_1 w /\ I_8_2 w /\ I_8_3 w /\ I_8_4 w /\ I_8_5 w /\ I_8_6 w /\ I_8_7 w /\
  I_8_8 w /\ I_8_9 w /\ I_8_10 w /\ I_8_11 w /\ I_8_12 w /\ I_8_13 w /\
  I_8_14 w /\ I_8_15 w /\ I_8_16 w /\ I_8_17 w /\ I_8_18 w /\
  (* Article I, s. 9 and 10 *)
  I_9_1 w /\ I_9_2 w /\ I_9_3 w /\ I_9_4 w /\ I_9_5 w /\ I_9_6 w /\ I_9_7 w /\
  I_9_8 w /\
  I_10_1 w /\ I_10_2 w /\ I_10_3 w /\
  (* Article II *)
  II_1_1 w /\ II_1_2 w /\ II_1_3 w /\ II_1_4 w /\ II_1_5 w /\ II_1_6 w /\
  II_1_7 w /\ II_1_8 w /\ II_1_9 w /\ II_1_10 w /\
  II_2_1 w /\ II_2_2 w /\ II_2_3 w /\ II_2_4 w /\
  II_3_1 w /\ II_3_2 w /\ II_3_3 w /\ II_3_4 w /\
  II_4_1 w /\
  (* Article III *)
  III_1_1 w /\ III_1_2 w /\ III_2_1 w /\ III_2_2 w /\ III_2_3 w /\
  III_3_1 w /\ III_3_2 w /\ III_3_3 w /\
  (* Article IV *)
  IV_1_1 w /\ IV_2_1 w /\ IV_2_2 w /\ IV_2_3 w /\ IV_3_1 w /\ IV_3_2 w /\
  IV_4_1 w /\ IV_4_2 w /\ IV_4_3 w /\
  (* Articles V, VI and VII *)
  V_1 w /\ V_2 w /\ V_3 w /\ V_4 w /\
  VI_1 w /\ VI_2 w /\ VI_3 w /\ VI_4 w /\
  VII_1 w /\
  (* The first article of the 1789 resolution, not ratified *)
  BR1789_1 w /\
  (* Amendments I to X *)
  A1_1 w /\ A1_2 w /\ A1_3 w /\ A1_4 w /\ A1_5 w /\ A1_6 w /\ A2_1 w /\
  A3_1 w /\ A3_2 w /\ A4_1 w /\ A4_2 w /\ A4_3 w /\
  A5_1 w /\ A5_2 w /\ A5_3 w /\ A5_4 w /\ A5_5 w /\
  A6_1 w /\ A6_2 w /\ A6_3 w /\ A6_4 w /\ A6_5 w /\ A6_6 w /\ A6_7 w /\
  A7_1 w /\ A7_2 w /\ A8_1 w /\ A8_2 w /\ A8_3 w /\ A9_1 w /\ A10_1 w /\
  (* Amendments XI to XIX *)
  A11_1 w /\
  A12_1 w /\ A12_2 w /\ A12_3 w /\ A12_4 w /\ A12_5 w /\
  A13_s1 w /\ A13_s2 w /\
  A14_s1_cit w /\ A14_s1_priv w /\ A14_s1_dp w /\ A14_s1_ep w /\
  A14_s2_basis w /\ A14_s2_reduce w /\ A14_s3 w /\
  A14_s4_debt w /\ A14_s4_rebel w /\ A14_s5 w /\
  A15_s1 w /\ A15_s2 w /\ A16_1 w /\
  A17_s1 w /\ A17_s2 w /\ A17_s3 w /\
  A18_s1 w /\ A18_s2 w /\ A18_s3 w /\
  A19_s1 w /\ A19_s2 w /\
  (* Amendments XX to XXVII *)
  A20_s1 w /\ A20_s2 w /\ A20_s3 w /\ A20_s4 w /\ A20_s5 w /\ A20_s6 w /\
  A21_s1 w /\ A21_s2 w /\ A21_s3 w /\
  A22_s1 w /\ A22_s2 w /\
  A23_s1 w /\ A23_s2 w /\
  A24_s1 w /\ A24_s2 w /\
  A25_s1 w /\ A25_s2 w /\ A25_s3 w /\ A25_s4_a w /\ A25_s4_b w /\ A25_s4_c w /\
  A26_s1 w /\ A26_s2 w /\
  A27_s1 w.
