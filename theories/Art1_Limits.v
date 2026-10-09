(******************************************************************************)
(*  Art1_Limits.v                                                             *)
(*                                                                            *)
(*  Article I, sections 9 and 10: the limits on Congress and on the States.   *)
(******************************************************************************)

From CV Require Import Types Act Data World.
From Stdlib Require Import List Arith Lia.
Import ListNotations.

(* Art. I, s. 9, cl. 1: migration or importation not prohibited by Congress
   before 1808; a tax of not more than ten dollars per person may be imposed
   before that year. *)
Definition I_9_1 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | ImportationBan y => 1808 <= y
    | ImportationTax y d => y < 1808 /\ d <= 10
    | _ => True
    end) w.

(* Art. I, s. 9, cl. 2: habeas corpus suspended only in cases of rebellion or
   invasion, when the public safety requires it. *)
Definition I_9_2 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | SuspendHabeas CauseOther _ => False
    | SuspendHabeas _ public_safety => public_safety = true
    | _ => True
    end) w.

(* Art. I, s. 9, cl. 3: no bill of attainder or ex post facto law. *)
Definition I_9_3 (w : World) : Prop :=
  forall_laws (fun m =>
    ~ In Attainder m.(m_features) /\ ~ In ExPostFacto m.(m_features)) w.

(* Art. I, s. 9, cl. 4: no capitation or other direct tax unless apportioned to
   the census.  Income taxes are carried by Amendment XVI. *)
Definition I_9_4 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | DirectTax apportioned => apportioned = true
    | _ => True
    end) w /\
  forall_laws (fun m => ~ In UnapportionedDirectTax m.(m_features)) w.

(* Art. I, s. 9, cl. 5: no tax or duty on articles exported from any State. *)
Definition I_9_5 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | ExportTax on_exports => on_exports = false
    | _ => True
    end) w /\
  forall_laws (fun m => ~ In ExportDuty m.(m_features)) w.

(* Art. I, s. 9, cl. 6: no preference among the ports of the States, and no
   obligation for vessels bound to or from one State to enter, clear or pay
   duties in another. *)
Definition I_9_6 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | PortRegulation preference vessels => preference = false /\ vessels = false
    | _ => True
    end) w /\
  forall_laws (fun m => ~ In PortPreference m.(m_features)) w.

(* Art. I, s. 9, cl. 7: money drawn from the Treasury only in consequence of
   appropriations made by law; a regular statement and account of public money
   published from time to time. *)
Definition I_9_7 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | Draw _ appropriated => appropriated = true
    | _ => True
    end) w /\
  w.(w_statement_published) = true.

(* Art. I, s. 9, cl. 8: no title of nobility granted by the United States; no
   holder of office accepts a present, emolument, office or title from a
   foreign State without the consent of Congress. *)
Definition I_9_8 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | TitleGrant by_united_states => by_united_states = false
    | ForeignPresent office_holder consent => office_holder = false \/ consent = true
    | _ => True
    end) w /\
  forall_laws (fun m => ~ In NobilityTitle m.(m_features)) w.

(* Art. I, s. 10, cl. 1: no State makes a treaty, alliance or confederation,
   grants letters of marque, coins money, emits bills of credit, makes anything
   but gold and silver a tender, passes a bill of attainder or ex post facto
   law, impairs contracts, or grants a title of nobility. *)
Definition I_10_1 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | StateBan _ => False
    | _ => True
    end) w.

(* Art. I, s. 10, cl. 2: no State lays imposts or duties on imports or exports
   without the consent of Congress, except what is absolutely necessary for its
   inspection laws; the net produce goes to the Treasury, and the laws are
   subject to Congress's revision. *)
Definition I_10_2 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | StateDuty consent inspection net revisable =>
        (consent = true \/ inspection = true) /\ net = true /\ revisable = true
    | _ => True
    end) w.

(* Art. I, s. 10, cl. 3: no State, without the consent of Congress, lays a
   tonnage duty, keeps troops or ships of war in time of peace, or enters into
   an agreement or compact with another State or a foreign power; and no State
   engages in war unless actually invaded or in imminent danger. *)
Definition I_10_3 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | StateTonnage consent => consent = true
    | StatePeaceForces consent => consent = true
    | StateCompact consent => consent = true
    | StateWar invaded_or_imminent => invaded_or_imminent = true
    | _ => True
    end) w.
