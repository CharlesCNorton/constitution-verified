(******************************************************************************)
(*  Amend_20_27.v                                                             *)
(*                                                                            *)
(*  Amendments XX to XXVII.                                                   *)
(******************************************************************************)

From CV Require Import Types Act Data World.
From Stdlib Require Import List Arith Lia.
Import ListNotations.

(* Amendment XX, s. 1: the terms of the President and Vice President end at noon on
   20 January; those of Senators and Representatives at noon on 3 January. *)
Definition A20_s1 (w : World) : Prop :=
  w.(w_pres_term_end) = (20, 1) /\ w.(w_congress_term_end) = (3, 1).

(* Amendment XX, s. 2: Congress assembles at least once in every year, the meeting
   beginning at noon on 3 January unless it appoints a different day by law. *)
Definition A20_s2 (w : World) : Prop :=
  w.(w_sessions_each_year) = true.

(* Amendment XX, s. 3: if the President-elect dies before the term begins, the
   Vice President-elect becomes President; if no President has qualified, the
   Vice President-elect acts; Congress provides by law for the case where neither
   has qualified. *)
Definition A20_s3 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | InauguralSuccession died vp_became not_qualified vp_acts =>
        (died = true -> vp_became = true) /\ (not_qualified = true -> vp_acts = true)
    | _ => True
    end) w.

(* Amendment XX, s. 4: Congress may provide by law for the death of a person from
   whom the House or the Senate may choose a President or Vice President. *)
Definition A20_s4 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | ChoiceDeathLaw provided => provided = true
    | _ => True
    end) w.

(* Amendment XX, s. 5: sections 1 and 2 take effect on 15 October after
   ratification; the amendment is in force. *)
Definition A20_s5 (w : World) : Prop :=
  w.(w_in_force) 20 = true.

(* Amendment XX, s. 6: the amendment is inoperative unless ratified within seven
   years of its submission. *)
Definition A20_s6 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | RatifyAmendment 20 _ _ years => years <= 7
    | _ => True
    end) w.

(* Amendment XXI, s. 1: the Eighteenth Amendment is repealed. *)
Definition A21_s1 (w : World) : Prop :=
  w.(w_in_force) 18 = false /\ w.(w_in_force) 21 = true.

(* Amendment XXI, s. 2: the transportation or importation into any State, Territory
   or possession, for delivery or use, of intoxicating liquor in violation of its
   laws, is prohibited. *)
Definition A21_s2 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | TransportLiquor into violates for_use => ~ (into = true /\ violates = true /\ for_use = true)
    | _ => True
    end) w.

(* Amendment XXI, s. 3: ratification by conventions in the several States, within
   seven years. *)
Definition A21_s3 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | RatifyAmendment 21 _ mode years => mode = ByConventions /\ years <= 7
    | _ => True
    end) w.

(* Amendment XXII, s. 1: no person may be elected President more than twice, nor
   one who has held the office for more than two years of another's term more
   than once; the Article does not apply to the person holding the office when
   it was proposed. *)
Definition A22_s1 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | CandidateRegistration p => eligible_after_22 p
    | _ => True
    end) w.

(* Amendment XXII, s. 2: ratification by three fourths of the States by their
   legislatures, within seven years. *)
Definition A22_s2 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | RatifyAmendment 22 _ mode years => mode = ByLegislatures /\ years <= 7
    | _ => True
    end) w.

(* Amendment XXIII, s. 1: the District appoints electors, in a number equal to the
   Senators and Representatives it would have as a State, but not more than the
   least populous State; they are additional to the States' electors. *)
Definition A23_s1 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | DCElectors n => n = Nat.min (w.(w_dc_entitled)) (min_state_electors w)
    | _ => True
    end) w /\
  w.(w_dc_electors) = Nat.min (w.(w_dc_entitled)) (min_state_electors w).

(* Amendment XXIII, s. 2: enforcement by appropriate legislation. *)
Definition A23_s2 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | EnforcementLaw n => n = 23 -> w.(w_in_force) 23 = true
    | _ => True
    end) w.

(* Amendment XXIV, s. 1: no denial of the right to vote in a federal election for
   failure to pay a poll tax or other tax. *)
Definition A24_s1 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | PollTaxDenial federal nonpayment denied =>
        ~ (federal = true /\ nonpayment = true /\ denied = true)
    | _ => True
    end) w.

(* Amendment XXIV, s. 2: enforcement by appropriate legislation. *)
Definition A24_s2 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | EnforcementLaw n => n = 24 -> w.(w_in_force) 24 = true
    | _ => True
    end) w.

(* Amendment XXV, s. 1: on the removal, death or resignation of the President, the
   Vice President becomes President. *)
Definition A25_s1 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | Succession trigger successor vp_vacant =>
        trigger <> TriggerInability -> vp_vacant = false -> successor = SuccessorVicePresident
    | _ => True
    end) w.

(* Amendment XXV, s. 2: on a vacancy in the Vice Presidency, the President nominates
   a Vice President, who takes office on confirmation by a majority of both Houses. *)
Definition A25_s2 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | VPNomination confirmed => confirmed = true
    | _ => True
    end) w.

(* Amendment XXV, s. 3: on the President's written declaration that he is unable to
   discharge the powers of the office, the Vice President acts as Acting President
   until the President declares otherwise in writing. *)
Definition A25_s3 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | PresidentDeclaration written declares vp_acts =>
        written = true -> vp_acts = declares
    | _ => True
    end) w.

(* Amendment XXV, s. 4: when the Vice President and a majority of the principal
   officers of the executive departments (or other body Congress provides) declare
   the President unable, the Vice President immediately assumes the powers of the
   office as Acting President. *)
Definition A25_s4_a (w : World) : Prop :=
  forall_acts (fun a => match a with
    | CabinetDeclaration declared transmitted immediate =>
        (declared = true /\ transmitted = true) -> immediate = true
    | _ => True
    end) w.

(* Amendment XXV, s. 4: a contested declaration is made within four days, and
   Congress decides within twenty-one days, assembling within forty-eight hours if
   not in session. *)
Definition A25_s4_b (w : World) : Prop :=
  forall_acts (fun a => match a with
    | PresidentContest within_four days _ _ => within_four = true /\ days <= 21
    | _ => True
    end) w.

(* Amendment XXV, s. 4: the Vice President continues as Acting President only if
   two thirds of both Houses determine that the President is unable. *)
Definition A25_s4_c (w : World) : Prop :=
  forall_acts (fun a => match a with
    | PresidentContest _ _ two_thirds vp_continues => vp_continues = two_thirds
    | _ => True
    end) w.

(* Amendment XXVI, s. 1: the right to vote of citizens eighteen years of age or
   older not denied or abridged on account of age. *)
Definition A26_s1 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | VoteDenialAge age denied => denied = true -> age < 18
    | _ => True
    end) w.

(* Amendment XXVI, s. 2: enforcement by appropriate legislation. *)
Definition A26_s2 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | EnforcementLaw n => n = 26 -> w.(w_in_force) 26 = true
    | _ => True
    end) w.

(* Amendment XXVII: a law varying the compensation of Senators and Representatives
   takes effect only after an election of Representatives has intervened. *)
Definition A27_s1 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | PayChange election in_force => in_force = true -> election = true
    | _ => True
    end) w /\
  forall_laws (fun m => ~ In PayChangeBeforeElection m.(m_features)) w.
