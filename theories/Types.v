(******************************************************************************)
(*  Types.v                                                                   *)
(*                                                                            *)
(*  Enumerations and records shared by the clause modules: the States, the    *)
(*  Chambers, the enumerated powers of Article I, section 8, votes, bills     *)
(*  (Measure), persons, electoral ballots, and the content features a law may *)
(*  carry.  Thresholds in the text are stated here once, as predicates.       *)
(******************************************************************************)

From Stdlib Require Import List Bool Arith Lia.
Import ListNotations.

Definition total_states : nat := 50.

(* ======================== States ======================== *)

Inductive USState : Type :=
  | Alabama | Alaska | Arizona | Arkansas | California | Colorado
  | Connecticut | Delaware | Florida | Georgia | Hawaii | Idaho | Illinois
  | Indiana | Iowa | Kansas | Kentucky | Louisiana | Maine | Maryland
  | Massachusetts | Michigan | Minnesota | Mississippi | Missouri | Montana
  | Nebraska | Nevada | NewHampshire | NewJersey | NewMexico | NewYork
  | NorthCarolina | NorthDakota | Ohio | Oklahoma | Oregon | Pennsylvania
  | RhodeIsland | SouthCarolina | SouthDakota | Tennessee | Texas | Utah
  | Vermont | Virginia | Washington | WestVirginia | Wisconsin | Wyoming.

Definition all_states : list USState :=
  [ Alabama; Alaska; Arizona; Arkansas; California; Colorado; Connecticut;
    Delaware; Florida; Georgia; Hawaii; Idaho; Illinois; Indiana; Iowa; Kansas;
    Kentucky; Louisiana; Maine; Maryland; Massachusetts; Michigan; Minnesota;
    Mississippi; Missouri; Montana; Nebraska; Nevada; NewHampshire; NewJersey;
    NewMexico; NewYork; NorthCarolina; NorthDakota; Ohio; Oklahoma; Oregon;
    Pennsylvania; RhodeIsland; SouthCarolina; SouthDakota; Tennessee; Texas;
    Utah; Vermont; Virginia; Washington; WestVirginia; Wisconsin; Wyoming ].

Lemma all_states_length : length all_states = total_states.
Proof. reflexivity. Qed.

Lemma all_states_complete : forall s : USState, In s all_states.
Proof. destruct s; simpl; tauto. Qed.

Lemma all_states_nodup : NoDup all_states.
Proof. unfold all_states; repeat constructor; simpl; intuition discriminate. Qed.

(* ======================== Chambers and powers ======================== *)

Inductive Chamber : Type := House | Senate.

(* The seventeen enumerated powers of Article I, section 8, clauses 1 to 17.
   Clause 18 (necessary and proper) is an authority of its own, below. *)
Inductive EnumeratedPower : Type :=
  | Taxing | Borrowing | Commerce | Naturalization | Coinage | Counterfeiting
  | PostOffices | Copyright | Tribunals | Piracies | WarPower | Armies | Navy
  | ForceRules | CallForthMilitia | OrganizeMilitia | ExclusiveDC.

Definition power_clause (p : EnumeratedPower) : nat :=
  match p with
  | Taxing => 1 | Borrowing => 2 | Commerce => 3 | Naturalization => 4
  | Coinage => 5 | Counterfeiting => 6 | PostOffices => 7 | Copyright => 8
  | Tribunals => 9 | Piracies => 10 | WarPower => 11 | Armies => 12
  | Navy => 13 | ForceRules => 14 | CallForthMilitia => 15
  | OrganizeMilitia => 16 | ExclusiveDC => 17
  end.

Inductive Authority : Type :=
  | Under (p : EnumeratedPower)            (* an enumerated power, cl. 1-17 *)
  | NecessaryProper (p : EnumeratedPower)  (* cl. 18, executing an enumerated power *)
  | Unauthorized.                          (* no power of Congress is cited *)

(* ======================== Votes ======================== *)

Record Vote : Type := mkVote {
  v_members : nat;          (* Members of the chamber *)
  v_present : nat;          (* Members present *)
  v_yeas : nat;
  v_nays : nat;
  v_recorded : bool;        (* yeas and nays entered on the Journal *)
  v_fifth_demanded : bool   (* one fifth of those present asked for yeas and nays *)
}.

(* A majority of the Members is a quorum to do business (Art. I, s. 5, cl. 1). *)
Definition quorum_met (v : Vote) : Prop :=
  v.(v_members) < 2 * v.(v_present).

(* Passage by a majority of those voting, with a quorum present. *)
Definition passes (v : Vote) : Prop :=
  quorum_met v /\ v.(v_nays) < v.(v_yeas).

(* Two thirds of the Members present concur (Art. I, s. 3, cl. 6; s. 5, cl. 2). *)
Definition two_thirds_present (v : Vote) : Prop :=
  2 * v.(v_present) <= 3 * v.(v_yeas).

(* Three quarters of the States (Art. V). *)
Definition three_fourths_of_states (k : nat) : Prop :=
  3 * total_states <= 4 * k.

(* Two thirds of the States (Art. V, convention application). *)
Definition two_thirds_of_states (k : nat) : Prop :=
  2 * total_states <= 3 * k.

(* ======================== Measures (bills and resolutions) ======================== *)

Inductive MeasureKind : Type := BillKind | ResolutionKind.

Inductive PresAction : Type := NoAction | Signed | Vetoed.

(* Content a law may carry.  Each clause forbids, or conditions, a feature. *)
Inductive ContentFeature : Type :=
  | EstablishesReligion          (* A1_1 *)
  | ProhibitsFreeExercise        (* A1_2 *)
  | AbridgesSpeech               (* A1_3 *)
  | AbridgesPress                (* A1_4 *)
  | AbridgesAssembly             (* A1_5 *)
  | AbridgesPetition             (* A1_6 *)
  | InfringesArms                (* A2_1 *)
  | PeacetimeQuartering          (* A3_1: quartering without the owner's consent *)
  | AuthorizesUnreasonableSearch (* A4_1 *)
  | WarrantWithoutCause          (* A4_2 *)
  | WarrantWithoutOath           (* A4_2 *)
  | WarrantWithoutParticularity  (* A4_3 *)
  | CapitalWithoutIndictment     (* A5_1 *)
  | DoubleJeopardy               (* A5_2 *)
  | CompelledSelfIncrimination   (* A5_3 *)
  | DeprivationWithoutProcess    (* A5_4 *)
  | TakingWithoutCompensation    (* A5_5 *)
  | DenySpeedyTrial              (* A6_1 *)
  | DenyPublicTrial              (* A6_2 *)
  | DenyImpartialJury            (* A6_3 *)
  | DenyNotice                   (* A6_4 *)
  | DenyConfrontation            (* A6_5 *)
  | DenyCompulsoryProcess        (* A6_6 *)
  | DenyCounsel                  (* A6_7 *)
  | DenyCivilJury                (* A7_1 *)
  | ReexaminesJury               (* A7_2 *)
  | ExcessiveBail                (* A8_1 *)
  | ExcessiveFines               (* A8_2 *)
  | CruelPunishment              (* A8_3 *)
  | DeniesRetainedRights         (* A9_1 *)
  | Attainder                    (* I_9_3 *)
  | ExPostFacto                  (* I_9_3 *)
  | UnapportionedDirectTax       (* I_9_4 *)
  | ExportDuty                   (* I_9_5 *)
  | PortPreference               (* I_9_6 *)
  | NobilityTitle                (* I_9_8 *)
  | ReligiousTestForOffice       (* VI_4 *)
  | PayChangeBeforeElection      (* A27_s1 *)
  | SuccessionDesignation        (* II_1_8: a law designating a successor *)
  | Enforces (amendment : nat).  (* enforcement legislation *)

Record Measure : Type := mkMeasure {
  m_kind : MeasureKind;
  m_authority : Authority;
  m_origin : Chamber;            (* the House in which the measure originated *)
  m_revenue : bool;              (* raises revenue (Art. I, s. 7, cl. 1) *)
  m_house : Vote;                (* passage vote in the House *)
  m_senate : Vote;               (* passage vote in the Senate *)
  m_presented : bool;            (* presented to the President *)
  m_action : PresAction;
  m_days_unreturned : nat;       (* days, Sundays excepted, after presentment *)
  m_adjournment_prevents : bool; (* adjournment prevents the return of the bill *)
  m_override_origin : option Vote; (* two thirds vote in the originating House *)
  m_override_other : option Vote;  (* two thirds vote in the other House *)
  m_features : list ContentFeature;
  m_uniform : bool;              (* uniform throughout the United States *)
  m_limited_times : bool;        (* exclusive rights for limited times *)
  m_army_years : option nat;     (* term of an appropriation for armies *)
  m_tax_for_debts_or_welfare : bool;
  m_indirect_tax : bool         (* duty, impost or excise *)
}.

(* Two thirds of each House, on reconsideration, with the yeas and nays
   entered on each Journal (Art. I, s. 7, cl. 2). *)
Definition overridden (m : Measure) : Prop :=
  match m.(m_override_origin), m.(m_override_other) with
  | Some vo, Some vx =>
      quorum_met vo /\ two_thirds_present vo /\ vo.(v_recorded) = true /\
      quorum_met vx /\ two_thirds_present vx /\ vx.(v_recorded) = true
  | _, _ => False
  end.

Definition passed_both (m : Measure) : Prop :=
  passes m.(m_house) /\ passes m.(m_senate).

(* A bill becomes law (Art. I, s. 7, cl. 2): it passed both Houses, was
   presented, and was signed; or was vetoed and passed over by two thirds of
   each House; or was not returned within ten days (Sundays excepted) unless
   adjournment prevented its return. *)
Definition enacted (m : Measure) : Prop :=
  m.(m_kind) = BillKind /\ passed_both m /\ m.(m_presented) = true /\
  (m.(m_action) = Signed \/
   (m.(m_action) = Vetoed /\ overridden m) \/
   (m.(m_action) = NoAction /\ 10 <= m.(m_days_unreturned) /\
    m.(m_adjournment_prevents) = false)).

(* Orders, resolutions and votes (Art. I, s. 7, cl. 3). *)
Definition resolution_effective (m : Measure) : Prop :=
  m.(m_kind) = ResolutionKind /\ passed_both m /\ m.(m_presented) = true /\
  (m.(m_action) = Signed \/ (m.(m_action) = Vetoed /\ overridden m)).

(* ======================== Persons ======================== *)

Record Person : Type := mkPerson {
  p_state : USState;               (* State of inhabitance, or State represented *)
  p_age : nat;
  p_citizen_years : nat;           (* years a citizen of the United States *)
  p_residence_years : nat;         (* years resident within the United States *)
  p_natural_born : bool;
  p_citizen_at_adoption : bool;
  p_inhabitant_when_elected : bool;
  p_senate_class : nat;            (* 1, 2 or 3 for a Senator; 0 otherwise *)
  p_elections_won : nat;           (* times elected President *)
  p_years_in_others_term : nat;    (* years as President or acting President in another's elected term *)
  p_grandfathered : bool           (* Amendment XXII, s. 1: holding the office when proposed *)
}.

Definition eligible_for_president (p : Person) : Prop :=
  (p.(p_natural_born) = true \/ p.(p_citizen_at_adoption) = true) /\
  35 <= p.(p_age) /\ 14 <= p.(p_residence_years).

(* Amendment XXII, s. 1. *)
Definition eligible_after_22 (p : Person) : Prop :=
  p.(p_grandfathered) = true \/
  (p.(p_elections_won) < 2 /\
   (2 < p.(p_years_in_others_term) -> p.(p_elections_won) < 1)).

Definition representative_qualified (p : Person) : Prop :=
  25 <= p.(p_age) /\ 7 <= p.(p_citizen_years) /\
  p.(p_inhabitant_when_elected) = true.

Definition senator_qualified (p : Person) : Prop :=
  30 <= p.(p_age) /\ 9 <= p.(p_citizen_years) /\
  p.(p_inhabitant_when_elected) = true.

(* ======================== Electors ======================== *)

Record ElectorBallot : Type := mkBallot {
  eb_elector_state : option USState;     (* None for an elector of the District of Columbia *)
  eb_president_state : USState;          (* State of inhabitance of the President candidate *)
  eb_vice_president_state : USState      (* ... and of the Vice President candidate *)
}.

(* Art. II, s. 1, cl. 3 and Amendment XII: at least one of the two persons
   voted for is not an inhabitant of the elector's State. *)
Definition ballot_valid (b : ElectorBallot) : Prop :=
  match b.(eb_elector_state) with
  | Some s => b.(eb_president_state) <> s \/ b.(eb_vice_president_state) <> s
  | None => True
  end.

(* ======================== Other categories ======================== *)

Inductive OfficeKind : Type :=
  | OfficeSenator | OfficeRepresentative | OfficeElector | OfficeCivil
  | OfficeMilitary | OfficeStateLegislator | OfficeExecutive | OfficeJudicial.

Inductive ArrestCharge : Type :=
  | ChargeTreason | ChargeFelony | ChargeBreachOfPeace | ChargeOther.

Inductive FillMethod : Type :=
  | WritOfElection (by_executive : bool)
  | TempAppointment (recess : bool) (legislature_empowered : bool).

Inductive CaseCategory : Type :=
  | ArisingUnder | AmbassadorsOrMinisters | Admiralty | UnitedStatesParty
  | StateParty | BetweenStates | StateAndOtherStateCitizens
  | CitizensOfDifferentStates | LandGrantsOfDifferentStates
  | StateOrCitizensAndForeign.

Inductive Forum : Type := OriginalForum | AppellateForum.

Inductive VestTarget : Type := ToPresident | ToCourts | ToDepartmentHeads.

Inductive RemovalGround : Type :=
  | GroundTreason | GroundBribery | GroundHighCrimes | GroundOther.

Inductive SuccessionTrigger : Type :=
  | TriggerRemoval | TriggerDeath | TriggerResignation | TriggerInability.

Inductive SanctionKind : Type := SanctionBail | SanctionFine | SanctionPunishment.

Inductive RebellionClaimKind : Type := DebtInAid | EmancipationClaim.

Inductive MilitiaPurpose : Type :=
  | ExecuteLaws | SuppressInsurrection | RepelInvasion | OtherPurpose.

Inductive HabeasCause : Type := CauseRebellion | CauseInvasion | CauseOther.

Inductive ExclusiveKind : Type := SeatOfGovernment | PurchasedPlace.

Inductive StateBanKind : Type :=
  | TreatyBan | AllianceBan | ConfederationBan | MarqueBan | CoinBan
  | CreditBillBan | NonSpecieTenderBan | AttainderBan | ExPostFactoBan
  | ContractImpairBan | NobilityBan.

Inductive RatifyMode : Type := ByLegislatures | ByConventions.

Inductive SuccessorKind : Type := SuccessorVicePresident | SuccessorDesignatedByLaw.
