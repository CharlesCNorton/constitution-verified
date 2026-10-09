(******************************************************************************)
(*  Witness.v                                                                 *)
(*                                                                            *)
(*  A concrete World for the clauses to be checked against.  The House and    *)
(*  Senate are generated from the 2020 apportionment; the electors from the   *)
(*  same table plus the District's three.  The acts are a set of compliant    *)
(*  acts that exercise the clauses.  The record is a model instance: it does  *)
(*  not assert a historical vote tally, and no act is claimed to have occurred.*)
(*  WitnessCheck.v shows that every clause holds of it.                       *)
(******************************************************************************)

From CV Require Import Types Act Data World Preamble.
From Stdlib Require Import List Arith Lia.
Import ListNotations.

(* ======================== Members ======================== *)

Definition house_member (s : USState) : Person :=
  mkPerson s 35 10 15 true false true 0 0 0 false.

Definition senator_seat (i : nat) : Person :=
  mkPerson (nth (i / 2) all_states Alabama) 40 15 20 true false true
           (Nat.modulo i 3 + 1) 0 0 false.

Definition witness_house : list Person :=
  flat_map (fun s => repeat (house_member s) (seats_2020 s)) all_states.

Definition witness_senate : list Person :=
  map senator_seat (seq 0 100).

Definition witness_president : Person :=
  mkPerson Ohio 55 30 30 true false true 0 1 0 false.

Definition witness_vice_president : Person :=
  mkPerson Virginia 60 40 40 true false true 0 0 0 false.

Definition witness_ballots : list ElectorBallot :=
  flat_map (fun s => repeat (mkBallot (Some s) Ohio Virginia) (seats_2020 s + 2)) all_states
  ++ repeat (mkBallot None Ohio Virginia) 3.

Definition witness_in_force (n : nat) : bool :=
  (1 <=? n) && (n <=? 27) && negb (n =? 18).

(* ======================== Measures and votes ======================== *)

Definition v_house : Vote := mkVote 435 435 300 135 true false.
Definition v_senate : Vote := mkVote 100 100 60 40 true false.
Definition v_override_house : Vote := mkVote 435 435 290 145 true false.
Definition v_override_senate : Vote := mkVote 100 100 67 33 true false.

Definition law_tax : Measure :=
  mkMeasure BillKind (Under Taxing) House true v_house v_senate true Signed 0 false
            None None [] false false None true false.

Definition law_army : Measure :=
  mkMeasure BillKind (Under Armies) Senate false v_house v_senate true Signed 0 false
            None None [] false false (Some 2) false false.

Definition law_copyright : Measure :=
  mkMeasure BillKind (Under Copyright) Senate false v_house v_senate true Signed 0 false
            None None [] false true None false false.

Definition law_veto_overridden : Measure :=
  mkMeasure BillKind (Under Commerce) House false v_house v_senate true Vetoed 0 false
            (Some v_override_house) (Some v_override_senate) [] false false None false false.

Definition law_ten_days : Measure :=
  mkMeasure BillKind (Under Coinage) House false v_house v_senate true NoAction 10 false
            None None [] false false None false false.

Definition resolution_navy : Measure :=
  mkMeasure ResolutionKind (Under Navy) Senate false v_house v_senate true Signed 0 false
            None None [] false false None false false.

(* ======================== Acts ======================== *)

Definition witness_acts : list Act :=
  [ EnactLaw law_tax; EnactLaw law_army; EnactLaw law_copyright;
    EnactLaw law_veto_overridden; EnactLaw law_ten_days; ResolveAct resolution_navy;
    RollCall House v_house; RollCall Senate v_senate; Expel House v_override_house;
    SeatMember House true; SeatMember Senate true;
    MemberArrest ChargeTreason true; MemberSpeech false; MemberPay true true;
    OfficeGrant false false; DualOffice false false; ElectionRules true false false;
    FillVacancy House (WritOfElection true); FillVacancy Senate (WritOfElection true);
    ImpeachBy House; SenateTie false 0 0;
    Borrow true; DeclareWar true; MilitiaCall ExecuteLaws; MilitiaOrganization true true;
    DistrictLegislation SeatOfGovernment 100 true false;
    DistrictLegislation PurchasedPlace 5 false true;
    ImportationBan 1808; ImportationTax 1800 10; SuspendHabeas CauseRebellion true;
    DirectTax true; IncomeTax true; ExportTax false; PortRegulation false false;
    Draw 1000 true; TitleGrant false; ForeignPresent false true;
    StateDuty false true true true; StateTonnage true; StateWar true;
    PresidentDecision 538 306 false 2 true true;
    VPDecision 538 300 false 2 true true;
    CandidateRegistration witness_president; VPCandidacy witness_vice_president;
    Succession TriggerDeath SuccessorVicePresident false;
    PresidentPay false false; ForeignEmolument false; ExecutiveAct true true;
    MilitiaCommand true; OpinionRequest true; Pardon false;
    TreatyRatify (mkVote 100 100 67 33 true false);
    Appointment true true false None; RecessCommission true true;
    ReceiveEnvoy true; CommissionOfficer true;
    JudgeCompensation false;
    CourtCase ArisingUnder AppellateForum; CourtCase StateParty OriginalForum;
    CriminalTrial true (Some Ohio) Ohio false false;
    TreasonCharge true false; TreasonConviction false true; TreasonPunishment true false false;
    RecordRecognition false; CitizenPrivilege false; Extradition true false;
    TerritoryDisposal true; StateGovernment true; InvasionProtection true true;
    DomesticViolenceAid true false false true;
    DebtAct true false; StateLawEnforced false; OfficerEntry OfficeSenator true false;
    ArmsRestriction false; Quartering false false false false; Search true;
    WarrantIssued true true true; CapitalCharge true false true; Prosecution false;
    CompelledTestimony false false; Deprivation true; Taking true true;
    CriminalProsecution true true true true true true true true;
    CivilSuit 25 true false;
    Sanction SanctionBail false; Sanction SanctionFine false; Sanction SanctionPunishment false;
    DenialByEnumeration false; SuitAgainstState false; ServitudeAct false false;
    EnforcementLaw 13; EnforcementLaw 14;
    Citizenship true true true true;
    StateAbridges Ohio false; StateDeprivation Ohio true; EqualProtectionDenial Ohio false;
    SuffrageDenial Ohio 0 10 10 10 false;
    Disqualified OfficeSenator false false false;
    PublicDebt true false; RebellionClaim DebtInAid false;
    VoteDenialRace false true; SenatorElection true 6 true; VoteDenialSex false true;
    TransportLiquor false false false; DCElectors 3; PollTaxDenial false false false;
    VoteDenialAge 20 false; PayChange true true ].

(* ======================== The World ======================== *)

Definition witness_world : World :=
  {| w_reps := seats_2020;
     w_census_years := census_years;
     w_interim_superseded := true;
     w_basis_excludes_untaxed_indians := true;
     w_house := witness_house;
     w_senate := witness_senate;
     w_senate_class_sizes := [34; 33; 33];
     w_house_term_years := 2;
     w_senate_term_years := 6;
     w_elector_quals_match := true;
     w_speaker_by_house := true;
     w_pro_tempore_by_senate := true;
     w_supreme_court_established := true;
     w_electors := fun s => seats_2020 s + 2;
     w_dc_electors := 3;
     w_dc_entitled := dc_entitled_members;
     w_ballots := witness_ballots;
     w_elector_day_uniform := true;
     w_president := witness_president;
     w_vice_president := witness_vice_president;
     w_pres_term_years := 4;
     w_pres_term_end := (20, 1);
     w_congress_term_end := (3, 1);
     w_ratified_states := ratification_order;
     w_in_force := witness_in_force;
     w_art1_1789_ratified := false;
     w_sessions_each_year := true;
     w_statement_published := true;
     w_state_of_union_given := true;
     w_acts := witness_acts |}.

Lemma witness_acts_eq : w_acts witness_world = witness_acts.
Proof. reflexivity. Qed.

(* ======================== Totals and facts about the members ======================== *)

Lemma total_reps_witness : total_reps witness_world = 435.
Proof. vm_compute. reflexivity. Qed.

Lemma total_electors_witness : total_electors witness_world = 538.
Proof. vm_compute. reflexivity. Qed.

Lemma min_state_electors_witness : min_state_electors witness_world = 3.
Proof. vm_compute. reflexivity. Qed.

Lemma pop_leq_witness :
  total_reps witness_world * (30 * 1000) <= apportionment_population_2020.
Proof.
  rewrite total_reps_witness. unfold apportionment_population_2020. lia.
Qed.

Lemma house_qualified : forall p, In p witness_house -> representative_qualified p.
Proof.
  intros p Hp. unfold witness_house in Hp. apply in_flat_map in Hp.
  destruct Hp as [s [_ Hs]]. apply repeat_spec in Hs. subst p.
  unfold representative_qualified, house_member. simpl. intuition lia.
Qed.

Lemma senate_qualified : forall p, In p witness_senate -> senator_qualified p.
Proof.
  intros p Hp. unfold witness_senate in Hp. apply in_map_iff in Hp.
  destruct Hp as [i [Hi _]]. subst p.
  unfold senator_qualified, senator_seat. simpl. intuition lia.
Qed.

Lemma senate_two_per_state : forall s : USState, members_from witness_senate s = 2.
Proof. destruct s; vm_compute; reflexivity. Qed.

Lemma seats_ge_one : forall s : USState, 1 <= seats_2020 s.
Proof. destruct s; simpl; lia. Qed.

Lemma witness_ballots_valid : forall b, In b witness_ballots -> ballot_valid b.
Proof.
  intros b Hb. unfold witness_ballots in Hb. apply in_app_or in Hb.
  destruct Hb as [Hb | Hb].
  - apply in_flat_map in Hb. destruct Hb as [s [_ Hs]]. apply repeat_spec in Hs.
    subst b. unfold ballot_valid. destruct s; simpl;
      first [ left; discriminate | right; discriminate ].
  - apply repeat_spec in Hb. subst b. unfold ballot_valid. simpl. trivial.
Qed.
