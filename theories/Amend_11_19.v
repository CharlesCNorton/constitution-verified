(******************************************************************************)
(*  Amend_11_19.v                                                             *)
(*                                                                            *)
(*  Amendments XI to XIX.  Section numbers follow the amendments; where a     *)
(*  section has several clauses the identifier gives the section and the      *)
(*  clause, as in A14_s1_priv.                                                *)
(******************************************************************************)

From CV Require Import Types Act Data World.
From Stdlib Require Import List Arith Lia.
Import ListNotations.

(* Amendment XI: the judicial power does not extend to a suit against one State
   by citizens of another State, or by citizens or subjects of a foreign State. *)
Definition A11_1 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | SuitAgainstState other_or_foreign => other_or_foreign = false
    | _ => True
    end) w.

(* Amendment XII: electors vote by separate ballots for President and Vice
   President; at least one of the two persons is not an inhabitant of the
   elector's State. *)
Definition A12_1 (w : World) : Prop :=
  forall b, In b w.(w_ballots) -> ballot_valid b.

(* Amendment XII: the President is the person with a majority of the electors.
   If none has a majority, the House chooses from the three highest, with each
   State casting one vote, a quorum of two thirds of the States, and a majority
   of all the States. *)
Definition A12_2 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | PresidentDecision _ _ house considered quorum majority =>
        house = true -> considered <= 3 /\ quorum = true /\ majority = true
    | _ => True
    end) w.

(* Amendment XII: the Vice President is the person with a majority of the
   electors.  If none has a majority, the Senate chooses from the two highest,
   with a quorum of two thirds of the whole Senate and a majority of the whole
   Senate. *)
Definition A12_3 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | VPDecision _ _ senate considered quorum majority =>
        senate = true -> considered <= 2 /\ quorum = true /\ majority = true
    | _ => True
    end) w.

(* Amendment XII: no person constitutionally ineligible to the office of
   President is eligible to that of Vice President. *)
Definition A12_4 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | VPCandidacy p => eligible_for_president p
    | _ => True
    end) w.

(* Amendment XII: the clause that the President shall act if the House does not
   choose before the fourth of March.  Superseded by Amendment XX, s. 3. *)
Definition A12_5 (w : World) : Prop :=
  w.(w_in_force) 20 = true.

(* Amendment XIII, s. 1: neither slavery nor involuntary servitude, except as
   punishment for crime after conviction. *)
Definition A13_s1 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | ServitudeAct involuntary punishment => involuntary = false \/ punishment = true
    | _ => True
    end) w.

(* Amendment XIII, s. 2: enforcement by appropriate legislation. *)
Definition A13_s2 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | EnforcementLaw n => n = 13 -> w.(w_in_force) 13 = true
    | _ => True
    end) w.

(* Amendment XIV, s. 1: persons born or naturalized in the United States and
   subject to its jurisdiction are citizens of the United States and of the
   State where they reside. *)
Definition A14_s1_cit (w : World) : Prop :=
  forall_acts (fun a => match a with
    | Citizenship born jurisdiction us_citizen state_citizen =>
        (born = true /\ jurisdiction = true) -> us_citizen = true /\ state_citizen = true
    | _ => True
    end) w.

(* Amendment XIV, s. 1: no State abridges the privileges or immunities of citizens
   of the United States. *)
Definition A14_s1_priv (w : World) : Prop :=
  forall_acts (fun a => match a with
    | StateAbridges _ abridged => abridged = false
    | _ => True
    end) w.

(* Amendment XIV, s. 1: no State deprives any person of life, liberty, or
   property without due process of law. *)
Definition A14_s1_dp (w : World) : Prop :=
  forall_acts (fun a => match a with
    | StateDeprivation _ due_process => due_process = true
    | _ => True
    end) w.

(* Amendment XIV, s. 1: no State denies any person the equal protection of the
   laws. *)
Definition A14_s1_ep (w : World) : Prop :=
  forall_acts (fun a => match a with
    | EqualProtectionDenial _ denied => denied = false
    | _ => True
    end) w.

(* Amendment XIV, s. 2: Representatives apportioned by the whole number of persons
   in each State, excluding Indians not taxed. *)
Definition A14_s2_basis (w : World) : Prop :=
  w.(w_basis_excludes_untaxed_indians) = true.

(* Amendment XIV, s. 2: where the right to vote for President or Vice President,
   Representatives, executive or judicial officers, or State legislators is denied
   to male citizens of twenty-one years, except for rebellion or other crime, the
   basis is reduced in the proportion those denied bear to all such male citizens. *)
Definition A14_s2_reduce (w : World) : Prop :=
  forall_acts (fun a => match a with
    | SuffrageDenial _ denied male21 before after excepted =>
        denied <= male21 /\
        (denied = 0 \/ excepted = true \/ after * male21 = before * (male21 - denied))
    | _ => True
    end) w.

(* Amendment XIV, s. 3: no person who, having sworn to support the Constitution,
   engaged in insurrection or rebellion, or gave aid or comfort to its enemies,
   holds office, unless two thirds of each House removes the disability. *)
Definition A14_s3 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | Disqualified _ prior insurrection removed =>
        (prior = true /\ insurrection = true) -> removed = true
    | _ => True
    end) w.

(* Amendment XIV, s. 4: the validity of the public debt authorized by law shall
   not be questioned. *)
Definition A14_s4_debt (w : World) : Prop :=
  forall_acts (fun a => match a with
    | PublicDebt authorized questioned => authorized = true -> questioned = false
    | _ => True
    end) w.

(* Amendment XIV, s. 4: neither the United States nor any State assumes or pays a
   debt incurred in aid of insurrection or rebellion, or a claim for the loss or
   emancipation of a slave. *)
Definition A14_s4_rebel (w : World) : Prop :=
  forall_acts (fun a => match a with
    | RebellionClaim _ paid_or_assumed => paid_or_assumed = false
    | _ => True
    end) w.

(* Amendment XIV, s. 5: enforcement by appropriate legislation. *)
Definition A14_s5 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | EnforcementLaw n => n = 14 -> w.(w_in_force) 14 = true
    | _ => True
    end) w.

(* Amendment XV, s. 1: the right to vote not denied or abridged on account of race,
   color, or previous condition of servitude. *)
Definition A15_s1 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | VoteDenialRace denied race => ~ (denied = true /\ race = true)
    | _ => True
    end) w.

(* Amendment XV, s. 2: enforcement by appropriate legislation. *)
Definition A15_s2 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | EnforcementLaw n => n = 15 -> w.(w_in_force) 15 = true
    | _ => True
    end) w.

(* Amendment XVI: Congress may lay and collect taxes on incomes, from whatever
   source derived, without apportionment among the States.  The income tax act is
   recorded only for taxes on incomes. *)
Definition A16_1 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | IncomeTax on_incomes => on_incomes = true
    | _ => True
    end) w.

(* Amendment XVII, s. 1: two Senators from each State, elected by the people for six
   years, one vote each; the electors have the qualifications of the most numerous
   branch of the State legislature. *)
Definition A17_s1 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | SenatorElection chosen term electors =>
        chosen = true /\ term = 6 /\ electors = true
    | _ => True
    end) w.

(* Amendment XVII, s. 2: a Senate vacancy filled by writs of election issued by the
   executive; the legislature may empower the executive to make temporary
   appointments until the people fill the vacancy. *)
Definition A17_s2 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | FillVacancy Senate (TempAppointment _ legislature_empowered) =>
        legislature_empowered = true
    | _ => True
    end) w.

(* Amendment XVII, s. 3: the amendment does not affect the election or term of a
   Senator chosen before it became valid.  The record holds no Senator elected
   before that date, so the saving clause adds no condition to this record. *)
Definition A17_s3 (w : World) : Prop := True.

(* Amendment XVIII, s. 1: the prohibition of intoxicating liquors.  Repealed by
   Amendment XXI, s. 1; it is not in force. *)
Definition A18_s1 (w : World) : Prop :=
  w.(w_in_force) 18 = false.

(* Amendment XVIII, s. 2: concurrent power to enforce the prohibition.  Repealed;
   not in force. *)
Definition A18_s2 (w : World) : Prop :=
  w.(w_in_force) 18 = false.

(* Amendment XVIII, s. 3: the article is inoperative unless ratified within seven
   years of its submission. *)
Definition A18_s3 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | RatifyAmendment 18 _ _ years => years <= 7
    | _ => True
    end) w.

(* Amendment XIX, s. 1: the right to vote not denied or abridged on account of sex. *)
Definition A19_s1 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | VoteDenialSex denied sex => ~ (denied = true /\ sex = true)
    | _ => True
    end) w.

(* Amendment XIX, s. 2: enforcement by appropriate legislation. *)
Definition A19_s2 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | EnforcementLaw n => n = 19 -> w.(w_in_force) 19 = true
    | _ => True
    end) w.
