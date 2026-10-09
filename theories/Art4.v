(******************************************************************************)
(*  Art4.v                                                                    *)
(*                                                                            *)
(*  Article IV: the relations among the States, the admission of States and   *)
(*  the territories, and the guarantees to the States.                        *)
(******************************************************************************)

From CV Require Import Types Act Data World.
From Stdlib Require Import List Arith Lia.
Import ListNotations.

(* Art. IV, s. 1: full faith and credit to the public acts, records and judicial
   proceedings of every State. *)
Definition IV_1_1 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | RecordRecognition refused => refused = false
    | _ => True
    end) w.

(* Art. IV, s. 2, cl. 1: the citizens of each State are entitled to all the
   privileges and immunities of citizens in the several States. *)
Definition IV_2_1 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | CitizenPrivilege discriminates => discriminates = false
    | _ => True
    end) w.

(* Art. IV, s. 2, cl. 2: a person charged with a crime who flees from justice to
   another State is delivered up on demand of the executive authority. *)
Definition IV_2_2 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | Extradition proper refused => ~ (proper = true /\ refused = true)
    | _ => True
    end) w.

(* Art. IV, s. 2, cl. 3: the delivery of persons held to service or labour who
   escape into another State.  Superseded by Amendment XIII, s. 1. *)
Definition IV_2_3 (w : World) : Prop :=
  w.(w_in_force) 13 = true.

(* Art. IV, s. 3, cl. 1: new States admitted by Congress; no new State formed
   within the jurisdiction of another, and no State formed by the junction of
   two or more States or parts of States, without the consent of the legislatures
   concerned and of Congress. *)
Definition IV_3_1 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | FormState admitted within merger legislatures congress =>
        admitted = true /\ within = false /\
        (merger = false \/ (legislatures = true /\ congress = true))
    | _ => True
    end) w.

(* Art. IV, s. 3, cl. 2: Congress has power to dispose of and make needful rules
   respecting the territory and property of the United States. *)
Definition IV_3_2 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | TerritoryDisposal by_congress => by_congress = true
    | _ => True
    end) w.

(* Art. IV, s. 4: the United States guarantees to every State a Republican Form
   of Government. *)
Definition IV_4_1 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | StateGovernment republican => republican = true
    | _ => True
    end) w.

(* Art. IV, s. 4: the United States protects each State against invasion. *)
Definition IV_4_2 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | InvasionProtection invaded protected => invaded = true -> protected = true
    | _ => True
    end) w.

(* Art. IV, s. 4: on application of the legislature, or of the executive when the
   legislature cannot be convened, the United States protects each State against
   domestic violence. *)
Definition IV_4_3 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | DomesticViolenceAid by_legislature by_executive cannot_convene granted =>
        granted = true -> (by_legislature = true \/ (by_executive = true /\ cannot_convene = true))
    | _ => True
    end) w.
