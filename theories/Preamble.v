(******************************************************************************)
(*  Preamble.v                                                                *)
(*                                                                            *)
(*  The Preamble declares six ends of the Constitution.  It confers no power  *)
(*  and imposes no duty of its own; the clause records the declared ends.     *)
(******************************************************************************)

From CV Require Import Types Act Data World.
From Stdlib Require Import List Arith Lia.
Import ListNotations.

Inductive PreambleEnd : Type :=
  | FormMorePerfectUnion | EstablishJustice | InsureDomesticTranquility
  | ProvideCommonDefence | PromoteGeneralWelfare | SecureBlessingsOfLiberty.

Definition preamble_ends : list PreambleEnd :=
  [FormMorePerfectUnion; EstablishJustice; InsureDomesticTranquility;
   ProvideCommonDefence; PromoteGeneralWelfare; SecureBlessingsOfLiberty].

Lemma preamble_ends_nodup : NoDup preamble_ends.
Proof. unfold preamble_ends; repeat constructor; simpl; intuition discriminate. Qed.

(* Preamble: the six declared ends, each named once. *)
Definition P_1 (w : World) : Prop :=
  length preamble_ends = 6 /\ NoDup preamble_ends.
