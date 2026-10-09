(******************************************************************************)
(*  Art1_Congress.v                                                           *)
(*                                                                            *)
(*  Article I, sections 1 to 6: the Congress, its members, elections,         *)
(*  sessions, internal order and privileges.  One definition per clause; the  *)
(*  identifier is the clause in CLAUSES.tsv.                                  *)
(******************************************************************************)

From CV Require Import Types Act Data World.
From Stdlib Require Import List Arith Lia.
Import ListNotations.

(* Art. I, s. 1: legislative powers vested in a Congress of a Senate and a
   House of Representatives. *)
Definition I_1_1 (w : World) : Prop :=
  length w.(w_senate) = 2 * total_states /\ length w.(w_house) = total_reps w.

(* Art. I, s. 2, cl. 1: House members chosen every second year. *)
Definition I_2_1 (w : World) : Prop :=
  w.(w_house_term_years) = 2.

(* Art. I, s. 2, cl. 1: electors of Representatives have the qualifications
   of the most numerous branch of the State legislature. *)
Definition I_2_2 (w : World) : Prop :=
  w.(w_elector_quals_match) = true.

(* Art. I, s. 2, cl. 2: age 25, seven years a citizen, inhabitant when elected. *)
Definition I_2_3 (w : World) : Prop :=
  forall p, In p w.(w_house) -> representative_qualified p.

(* Each enumeration in the given list: the first lies within three years of
   the first meeting (1789), and each later one within ten years of the last. *)
Fixpoint census_spaced (prev : nat) (l : list nat) : Prop :=
  match l with
  | [] => True
  | y :: t => prev < y /\ y <= prev + 10 /\ census_spaced y t
  end.

(* Art. I, s. 2, cl. 3: enumeration within three years after the first
   meeting, and within every subsequent term of ten years. *)
Definition I_2_4 (w : World) : Prop :=
  match w.(w_census_years) with
  | [] => False
  | y :: t => 1789 <= y /\ y <= 1789 + 3 /\ census_spaced y t
  end.

(* Art. I, s. 2, cl. 3, three-fifths rule: superseded by Amendment XIV, s. 2. *)
Definition I_2_5 (w : World) : Prop :=
  w.(w_in_force) 14 = true.

(* Art. I, s. 2, cl. 3: not more than one Representative for every thirty
   thousand persons, and at least one for each State. *)
Definition I_2_6 (w : World) : Prop :=
  total_reps w * (30 * 1000) <= apportionment_population_2020 /\
  forall s : USState, 1 <= w.(w_reps) s.

(* Art. I, s. 2, cl. 3, interim apportionment of sixty-five Representatives:
   superseded once the first enumeration has been made. *)
Definition I_2_7 (w : World) : Prop :=
  w.(w_interim_superseded) = true /\
  fold_right plus 0 (map interim_1789 all_states) = 65.

(* Art. I, s. 2, cl. 4: House vacancies filled by writs of election issued by
   the executive authority of the State. *)
Definition I_2_8 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | FillVacancy House (WritOfElection b) => b = true
    | FillVacancy House (TempAppointment _ _) => False
    | _ => True
    end) w.

(* Art. I, s. 2, cl. 5: the House chooses its Speaker and other officers. *)
Definition I_2_9 (w : World) : Prop :=
  w.(w_speaker_by_house) = true.

(* Art. I, s. 2, cl. 5: the House has the sole power of impeachment. *)
Definition I_2_10 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | ImpeachBy ch => ch = House
    | _ => True
    end) w.

(* Art. I, s. 3, cl. 1: two Senators from each State, for six years. *)
Definition I_3_1 (w : World) : Prop :=
  (forall s : USState, members_from w.(w_senate) s = 2) /\
  w.(w_senate_term_years) = 6.

(* Art. I, s. 3, cl. 2: the Senate divided as equally as may be into three
   classes; one third chosen every second year. *)
Definition I_3_2 (w : World) : Prop :=
  match w.(w_senate_class_sizes) with
  | [a; b; c] =>
      a + b + c = length w.(w_senate) /\
      a <= b + 1 /\ b <= a + 1 /\ b <= c + 1 /\ c <= b + 1 /\ a <= c + 1 /\ c <= a + 1 /\
      senators_in_class w 1 = a /\ senators_in_class w 2 = b /\
      senators_in_class w 3 = c
  | _ => False
  end.

(* Art. I, s. 3, cl. 2: recess vacancies filled by temporary appointment of
   the executive, until the legislature meets; Amendment XVII, s. 2 supersedes
   the recess condition once in force. *)
Definition I_3_3 (w : World) : Prop :=
  w.(w_in_force) 17 = true \/
  forall_acts (fun a => match a with
    | FillVacancy Senate (TempAppointment recess _) => recess = true
    | _ => True
    end) w.

(* Art. I, s. 3, cl. 3: age 30, nine years a citizen, inhabitant when elected. *)
Definition I_3_4 (w : World) : Prop :=
  forall p, In p w.(w_senate) -> senator_qualified p.

(* Art. I, s. 3, cl. 4: the Vice President votes only when the Senate is equally
   divided. *)
Definition I_3_5 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | SenateTie vp yeas nays => vp = true -> yeas = nays
    | _ => True
    end) w.

(* Art. I, s. 3, cl. 5: the Senate chooses its other officers and a President
   pro tempore. *)
Definition I_3_6 (w : World) : Prop :=
  w.(w_pro_tempore_by_senate) = true.

(* Art. I, s. 3, cl. 6: the Senate tries impeachments under oath; the Chief
   Justice presides over the trial of the President; conviction requires the
   concurrence of two thirds of the Members present. *)
Definition I_3_7 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | SenateConviction oath president cj v =>
        oath = true /\ (president = true -> cj = true) /\ two_thirds_present v
    | _ => True
    end) w.

(* Art. I, s. 3, cl. 7: judgment extends only to removal and disqualification;
   the convicted party remains liable to prosecution under law. *)
Definition I_3_8 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | ImpeachmentJudgment _ _ other later => other = false /\ later = false
    | _ => True
    end) w.

(* Art. I, s. 4, cl. 1: the times, places and manner of elections are
   prescribed by the State legislature; Congress may alter them, except as to
   the places of choosing Senators. *)
Definition I_4_1 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | ElectionRules by_state by_congress senate_places =>
        by_state = true \/ (by_congress = true /\ senate_places = false)
    | _ => True
    end) w.

(* Art. I, s. 4, cl. 2: Congress assembles at least once in every year. *)
Definition I_4_2 (w : World) : Prop :=
  w.(w_sessions_each_year) = true.

(* Art. I, s. 5, cl. 1: each House judges its own elections and qualifications;
   a majority of each is a quorum to do business; a smaller number may
   adjourn and compel attendance.  Business is conducted only with a quorum. *)
Definition I_5_1 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | RollCall _ v => quorum_met v
    | SeatMember _ judged => judged = true
    | _ => True
    end) w.

(* Art. I, s. 5, cl. 2: each House expels a Member with the concurrence of two
   thirds. *)
Definition I_5_2 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | Expel _ v => quorum_met v /\ two_thirds_present v
    | _ => True
    end) w.

(* Art. I, s. 5, cl. 3: the yeas and nays of any question are entered on the
   Journal at the desire of one fifth of those present. *)
Definition I_5_3 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | RollCall _ v => v.(v_fifth_demanded) = true -> v.(v_recorded) = true
    | _ => True
    end) w.

(* Art. I, s. 5, cl. 4: neither House adjourns for more than three days without
   the other's consent, nor to any other place. *)
Definition I_5_4 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | Adjourn _ days other same => (days <= 3 \/ other = true) /\ same = true
    | _ => True
    end) w.

(* Art. I, s. 6, cl. 1: compensation set by law and paid from the Treasury. *)
Definition I_6_1 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | MemberPay set_by_law paid => set_by_law = true /\ paid = true
    | _ => True
    end) w.

(* Art. I, s. 6, cl. 1: privilege from arrest during attendance, except for
   treason, felony and breach of the peace. *)
Definition I_6_2 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | MemberArrest ChargeOther attending => attending = false
    | _ => True
    end) w.

(* Art. I, s. 6, cl. 1: no questioning of speech or debate in any other place. *)
Definition I_6_3 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | MemberSpeech questioned => questioned = false
    | _ => True
    end) w.

(* Art. I, s. 6, cl. 2: no Member appointed during the term to an office
   created, or whose emoluments were raised, during that term. *)
Definition I_6_4 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | OfficeGrant appointed created => ~ (appointed = true /\ created = true)
    | _ => True
    end) w.

(* Art. I, s. 6, cl. 2: no holder of federal office may be a Member. *)
Definition I_6_5 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | DualOffice member federal => ~ (member = true /\ federal = true)
    | _ => True
    end) w.
