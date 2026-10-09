(******************************************************************************)
(*  Art2.v                                                                    *)
(*                                                                            *)
(*  Article II: the executive power, the election of the President and Vice  *)
(*  President, qualifications, succession and compensation, the powers of     *)
(*  the President, and removal on impeachment.  Clauses modified by the       *)
(*  Twelfth, Twentieth, Twenty-second and Twenty-fifth Amendments are         *)
(*  stated here in their modified form, with the amendment named in the       *)
(*  comment.                                                                  *)
(******************************************************************************)

From CV Require Import Types Act Data World.
From Stdlib Require Import List Arith Lia.
Import ListNotations.

(* Art. II, s. 1, cl. 1: the executive power vested in a President for a term
   of four years, elected with a Vice President for the same term. *)
Definition II_1_1 (w : World) : Prop :=
  w.(w_pres_term_years) = 4.

(* Art. II, s. 1, cl. 2: each State appoints electors equal to its Senators and
   Representatives; no Senator, Representative, or holder of federal office of
   trust or profit is appointed an elector. *)
Definition II_1_2 (w : World) : Prop :=
  (forall s : USState, w.(w_electors) s = w.(w_reps) s + 2) /\
  forall_acts (fun a => match a with
    | ElectorAppointment s n disqualified =>
        n = w.(w_electors) s /\ disqualified = false
    | _ => True
    end) w.

(* Art. II, s. 1, cl. 3: electors vote by ballot for two persons, one at least
   not an inhabitant of the elector's State; the lists are counted before the
   two Houses.  Each elector casts one ballot. *)
Definition II_1_3 (w : World) : Prop :=
  length w.(w_ballots) = total_electors w.

(* Art. II, s. 1, cl. 3: the person with a majority of the electors appointed
   is President; if no person has a majority, the House of Representatives
   chooses from the five highest (Amendment XII reduces this to three). *)
Definition II_1_4 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | PresidentDecision total top house considered _ _ =>
        total = total_electors w /\
        (2 * top > total -> house = false) /\
        (house = true -> considered <= 5)
    | _ => True
    end) w.

(* Art. II, s. 1, cl. 3: the person with a majority of the electors is Vice
   President; the Senate chooses among those with equal votes (Amendment XII
   gives the rule in full). *)
Definition II_1_5 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | VPDecision total top senate _ _ _ =>
        total = total_electors w /\ (senate = true -> 2 * top <= total)
    | _ => True
    end) w.

(* Art. II, s. 1, cl. 4: Congress determines the time of choosing electors and
   the day of their vote, the same throughout the United States. *)
Definition II_1_6 (w : World) : Prop :=
  w.(w_elector_day_uniform) = true.

(* Art. II, s. 1, cl. 5: no person is eligible to the presidency unless a natural
   born citizen, or a citizen at the adoption of the Constitution, aged thirty-
   five years, and fourteen years a resident within the United States.  The
   Twenty-second Amendment's limit on election is part of registration; see
   A22_s1. *)
Definition II_1_7 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | CandidateRegistration p => eligible_for_president p
    | _ => True
    end) w.

(* Art. II, s. 1, cl. 6: on the removal, death, resignation, or inability of the
   President, the powers devolve on the Vice President; Congress may provide by
   law for the case of both offices.  Amendment XXV, s. 1 makes the Vice
   President's succession mandatory; see A25_s1. *)
Definition II_1_8 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | Succession _ SuccessorDesignatedByLaw vp_vacant =>
        vp_vacant = true /\
        exists m, In (EnactLaw m) w.(w_acts) /\ In SuccessionDesignation m.(m_features)
    | _ => True
    end) w.

(* Art. II, s. 1, cl. 7: the President's compensation is neither increased nor
   diminished during the term, and no other emolument is received from the
   United States or any State. *)
Definition II_1_9 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | PresidentPay during changed => ~ (during = true /\ changed = true)
    | ForeignEmolument received => received = false
    | _ => True
    end) w.

(* Art. II, s. 1, cl. 8: the oath or affirmation is taken before the President
   enters on the execution of the office. *)
Definition II_1_10 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | ExecutiveAct sworn _ => sworn = true
    | _ => True
    end) w.

(* Art. II, s. 2, cl. 1: Commander in Chief of the Army and Navy, and of the
   militia when called into the actual service of the United States; the
   President may require written opinions of the principal officers of the
   executive departments; reprieves and pardons, except in cases of
   impeachment. *)
Definition II_2_1 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | MilitiaCommand in_service => in_service = true
    | OpinionRequest principal => principal = true
    | Pardon impeachment => impeachment = false
    | _ => True
    end) w.

(* Art. II, s. 2, cl. 2: treaties made with the advice and consent of the
   Senate, two thirds of the Senators present concurring. *)
Definition II_2_2 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | TreatyRatify v => quorum_met v /\ two_thirds_present v
    | _ => True
    end) w.

(* Art. II, s. 2, cl. 2: nominations made with the advice and consent of the
   Senate, under a law establishing the office; inferior officers may be vested
   by law in the President alone, the courts, or the heads of departments. *)
Definition II_2_3 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | Appointment est confirmed inferior vested =>
        est = true /\ (confirmed = true \/ (inferior = true /\ vested <> None))
    | _ => True
    end) w.

(* Art. II, s. 2, cl. 3: a vacancy during the recess of the Senate filled by a
   commission expiring at the end of the next session. *)
Definition II_2_4 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | RecessCommission during expires => during = true /\ expires = true
    | _ => True
    end) w.

(* Art. II, s. 3, cl. 1: the President gives Congress information on the State
   of the Union and recommends measures. *)
Definition II_3_1 (w : World) : Prop :=
  w.(w_state_of_union_given) = true.

(* Art. II, s. 3, cl. 1: the President may convene both Houses on extraordinary
   occasions, and adjourn them if they disagree about the time of adjournment. *)
Definition II_3_2 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | ConveneHouses extraordinary => extraordinary = true
    | AdjournHouses disagreement => disagreement = true
    | _ => True
    end) w.

(* Art. II, s. 3, cl. 1: the President receives ambassadors and other public
   ministers. *)
Definition II_3_3 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | ReceiveEnvoy accepted => accepted = true
    | _ => True
    end) w.

(* Art. II, s. 3, cl. 1: the President takes care that the laws be faithfully
   executed, and commissions all the officers of the United States. *)
Definition II_3_4 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | ExecutiveAct _ faithful => faithful = true
    | CommissionOfficer appointed => appointed = true
    | _ => True
    end) w.

(* Art. II, s. 4: removal from office on impeachment and conviction for treason,
   bribery, or other high crimes and misdemeanors. *)
Definition II_4_1 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | RemovalOnImpeachment conviction ground =>
        conviction = true /\ ground <> GroundOther
    | _ => True
    end) w.
