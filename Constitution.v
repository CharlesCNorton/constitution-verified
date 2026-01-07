(******************************************************************************)
(*                                                                            *)
(*                         U.S. CONSTITUTIONAL STRUCTURE                      *)
(*                                                                            *)
(*     Enumerated powers of Congress (Art. I § 8), executive authority        *)
(*     (Art. II), judicial review (Marbury), amendment procedures             *)
(*     (Art. V), and federalism constraints (10th Amendment).                 *)
(*                                                                            *)
(*     "We the People of the United States, in Order to form a more           *)
(*      perfect Union..."                                                     *)
(*     - Preamble, 1787                                                       *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: January 6, 2026                                                  *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

Require Import List.
Require Import Arith.
Require Import Bool.
Import ListNotations.

Inductive Branch : Type :=
  | Legislative
  | Executive
  | Judicial.

Inductive Chamber : Type :=
  | House
  | Senate.

Record Congress := mkCongress {
  house_members : nat;
  senate_members : nat
}.

Definition standard_congress : Congress :=
  mkCongress 435 100.

Inductive EnumeratedPower : Type :=
  | TaxAndSpend
  | BorrowMoney
  | RegulateCommerce
  | EstablishNaturalization
  | CoinMoney
  | PunishCounterfeiting
  | EstablishPostOffices
  | PromoteScienceArts
  | ConstituteTribunals
  | DefinePiracies
  | DeclareWar
  | RaiseArmies
  | ProvideNavy
  | RegulateForces
  | CallMilitia
  | OrganizeMilitia
  | ExclusiveLegislationDC
  | NecessaryAndProper.

Definition all_enumerated_powers : list EnumeratedPower :=
  [ TaxAndSpend; BorrowMoney; RegulateCommerce; EstablishNaturalization;
    CoinMoney; PunishCounterfeiting; EstablishPostOffices; PromoteScienceArts;
    ConstituteTribunals; DefinePiracies; DeclareWar; RaiseArmies;
    ProvideNavy; RegulateForces; CallMilitia; OrganizeMilitia;
    ExclusiveLegislationDC; NecessaryAndProper ].

Definition enumerated_power_count : nat := length all_enumerated_powers.

Lemma eighteen_enumerated_powers : enumerated_power_count = 18.
Proof.
  reflexivity.
Qed.

Definition two_thirds (total : nat) : nat := (2 * total + 2) / 3.

Definition veto_override_threshold (c : Congress) : nat :=
  two_thirds (house_members c) + two_thirds (senate_members c).

Definition house_override : nat := two_thirds 435.
Definition senate_override : nat := two_thirds 100.

Lemma house_two_thirds_is_290 : house_override = 290.
Proof.
  reflexivity.
Qed.

Lemma senate_two_thirds_is_67 : senate_override = 67.
Proof.
  reflexivity.
Qed.

Definition total_states : nat := 50.

Definition three_fourths_states : nat := (3 * total_states + 3) / 4.

Lemma amendment_ratification_requires_38 : three_fourths_states = 38.
Proof.
  reflexivity.
Qed.

Inductive AmendmentPath : Type :=
  | CongressProposal
  | ConventionProposal.

Inductive RatificationMethod : Type :=
  | StateLegislatures
  | StateConventions.

Record AmendmentProcess := mkAmendmentProcess {
  proposal_path : AmendmentPath;
  ratification_method : RatificationMethod;
  states_required : nat
}.

Definition standard_amendment : AmendmentProcess :=
  mkAmendmentProcess CongressProposal StateLegislatures 38.

Inductive JudicialReviewOutcome : Type :=
  | Constitutional
  | Unconstitutional
  | StandingDenied
  | Moot
  | PoliticalQuestion.

Definition is_justiciable (outcome : JudicialReviewOutcome) : bool :=
  match outcome with
  | Constitutional => true
  | Unconstitutional => true
  | StandingDenied => false
  | Moot => false
  | PoliticalQuestion => false
  end.

Inductive PowerHolder : Type :=
  | Federal
  | State
  | Reserved.

Definition tenth_amendment_analysis (power_enumerated : bool) (power_prohibited_to_states : bool) : PowerHolder :=
  if power_enumerated then Federal
  else if power_prohibited_to_states then Federal
  else Reserved.

Lemma unenumerated_unpermitted_reserved :
  forall pe ps, pe = false -> ps = false -> tenth_amendment_analysis pe ps = Reserved.
Proof.
  intros pe ps Hpe Hps.
  unfold tenth_amendment_analysis.
  rewrite Hpe. rewrite Hps.
  reflexivity.
Qed.

Inductive SupremacyResolution : Type :=
  | FederalPrevails
  | StateLawValid
  | NoConflict.

Definition supremacy_clause (federal_law_exists : bool) (state_law_conflicts : bool) : SupremacyResolution :=
  if federal_law_exists then
    if state_law_conflicts then FederalPrevails
    else NoConflict
  else StateLawValid.

Lemma federal_preempts_conflicting_state :
  supremacy_clause true true = FederalPrevails.
Proof.
  reflexivity.
Qed.

Definition electoral_votes (state_house_seats : nat) : nat :=
  state_house_seats + 2.

Definition total_electoral_votes : nat := 435 + 100 + 3.

Definition electoral_majority : nat := (total_electoral_votes / 2) + 1.

Lemma electoral_college_majority_is_270 : electoral_majority = 270.
Proof.
  reflexivity.
Qed.

Inductive ImpeachmentStage : Type :=
  | HouseInvestigation
  | HouseVote
  | SenateTrialPending
  | SenateTrialActive
  | Acquitted
  | Convicted.

Definition impeachment_conviction_threshold : nat := two_thirds 100.

Lemma conviction_requires_67_senators : impeachment_conviction_threshold = 67.
Proof.
  reflexivity.
Qed.
