(******************************************************************************)
(*  Art5_7.v                                                                  *)
(*                                                                            *)
(*  Article V (amendment), Article VI (debts, supremacy, oaths and religious  *)
(*  tests) and Article VII (ratification).                                    *)
(******************************************************************************)

From CV Require Import Types Act Data World.
From Stdlib Require Import List Arith Lia.
Import ListNotations.

(* Art. V: Congress proposes amendments on the vote of two thirds of both Houses,
   or, on the application of two thirds of the States, calls a convention for
   that purpose.  The two Houses' votes are counted as two thirds of the Members
   present, as in Art. I, s. 3, cl. 6. *)
Definition V_1 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | ProposeByCongress _ house senate =>
        quorum_met house /\ two_thirds_present house /\
        quorum_met senate /\ two_thirds_present senate
    | CallConvention _ applications => two_thirds_of_states applications
    | _ => True
    end) w.

(* Art. V: an amendment is valid when ratified by three fourths of the States,
   by their legislatures or by conventions, as Congress proposes. *)
Definition V_2 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | RatifyAmendment _ states _ _ => three_fourths_of_states states
    | _ => True
    end) w.

(* Art. V, proviso: no amendment made before 1808 may affect the first and fourth
   clauses of the ninth section of the first article. *)
Definition V_3 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | EarlyAmendment _ year touches => 1808 <= year \/ touches = false
    | _ => True
    end) w.

(* Art. V, proviso: no State, without its consent, is deprived of its equal
   suffrage in the Senate. *)
Definition V_4 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | SenateSuffrageChange _ _ deprived consent => deprived = true -> consent = true
    | _ => True
    end) w.

(* Art. VI, cl. 1: debts and engagements contracted before the Constitution are
   as valid against the United States under it as under the Confederation. *)
Definition VI_1 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | DebtAct pre repudiated => ~ (pre = true /\ repudiated = true)
    | _ => True
    end) w.

(* Art. VI, cl. 2: the Constitution, the laws made in pursuance of it, and the
   treaties are the supreme law of the land; the judges of every State are bound
   by them, notwithstanding any State law to the contrary. *)
Definition VI_2 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | StateLawEnforced conflicts => conflicts = false
    | _ => True
    end) w.

(* Art. VI, cl. 3: Senators, Representatives, Members of the State legislatures,
   and the executive and judicial officers of the United States and of the
   States are bound by oath or affirmation to support the Constitution, before
   they enter on their office. *)
Definition VI_3 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | OfficerEntry _ oath _ => oath = true
    | _ => True
    end) w.

(* Art. VI, cl. 3: no religious test as a qualification to any office or public
   trust under the United States; and no law requires one. *)
Definition VI_4 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | OfficerEntry _ _ religious => religious = false
    | _ => True
    end) w /\
  forall_laws (fun m => ~ In ReligiousTestForOffice m.(m_features)) w.

(* Art. VII: the ratification of the Conventions of nine States is sufficient for
   the establishment of the Constitution between the States so ratifying. *)
Definition VII_1 (w : World) : Prop :=
  9 <= length w.(w_ratified_states).
