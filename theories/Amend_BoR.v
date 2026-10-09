(******************************************************************************)
(*  Amend_BoR.v                                                               *)
(*                                                                            *)
(*  The first ten amendments (the Bill of Rights), and the first article of   *)
(*  the 1789 joint resolution, which was not ratified.  Prohibitions on what  *)
(*  Congress may enact are stated over the features of enacted measures;     *)
(*  prohibitions on governmental acts are stated over the acts.               *)
(******************************************************************************)

From CV Require Import Types Act Data World.
From Stdlib Require Import List Arith Lia.
Import ListNotations.

(* First article of the joint resolution of 25 September 1789 (apportionment):
   not ratified, and therefore not part of the Constitution. *)
Definition BR1789_1 (w : World) : Prop :=
  w.(w_art1_1789_ratified) = false.

(* Amendment I: no law respecting an establishment of religion. *)
Definition A1_1 (w : World) : Prop :=
  forall_laws (fun m => ~ In EstablishesReligion m.(m_features)) w.

(* Amendment I: no law prohibiting the free exercise of religion. *)
Definition A1_2 (w : World) : Prop :=
  forall_laws (fun m => ~ In ProhibitsFreeExercise m.(m_features)) w.

(* Amendment I: no law abridging the freedom of speech. *)
Definition A1_3 (w : World) : Prop :=
  forall_laws (fun m => ~ In AbridgesSpeech m.(m_features)) w.

(* Amendment I: no law abridging the freedom of the press. *)
Definition A1_4 (w : World) : Prop :=
  forall_laws (fun m => ~ In AbridgesPress m.(m_features)) w.

(* Amendment I: no law abridging the right peaceably to assemble. *)
Definition A1_5 (w : World) : Prop :=
  forall_laws (fun m => ~ In AbridgesAssembly m.(m_features)) w.

(* Amendment I: no law abridging the right to petition for a redress of
   grievances. *)
Definition A1_6 (w : World) : Prop :=
  forall_laws (fun m => ~ In AbridgesPetition m.(m_features)) w.

(* Amendment II: the right of the people to keep and bear arms shall not be
   infringed, by law or by act. *)
Definition A2_1 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | ArmsRestriction infringes => infringes = false
    | _ => True
    end) w /\
  forall_laws (fun m => ~ In InfringesArms m.(m_features)) w.

(* Amendment III: no soldier quartered in a house in time of peace without the
   owner's consent. *)
Definition A3_1 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | Quartering in_peace owner _ _ => in_peace = true -> owner = true
    | _ => True
    end) w /\
  forall_laws (fun m => ~ In PeacetimeQuartering m.(m_features)) w.

(* Amendment III: in time of war, quartering only in a manner prescribed by law. *)
Definition A3_2 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | Quartering _ _ in_war by_law => in_war = true -> by_law = true
    | _ => True
    end) w.

(* Amendment IV: the right to be secure against unreasonable searches and
   seizures. *)
Definition A4_1 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | Search reasonable => reasonable = true
    | _ => True
    end) w /\
  forall_laws (fun m => ~ In AuthorizesUnreasonableSearch m.(m_features)) w.

(* Amendment IV: warrants issue only upon probable cause, supported by oath or
   affirmation. *)
Definition A4_2 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | WarrantIssued probable oath _ => probable = true /\ oath = true
    | _ => True
    end) w /\
  forall_laws (fun m => ~ In WarrantWithoutCause m.(m_features) /\
                        ~ In WarrantWithoutOath m.(m_features)) w.

(* Amendment IV: warrants particularly describe the place to be searched, and
   the persons or things to be seized. *)
Definition A4_3 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | WarrantIssued _ _ particular => particular = true
    | _ => True
    end) w /\
  forall_laws (fun m => ~ In WarrantWithoutParticularity m.(m_features)) w.

(* Amendment V: no capital or otherwise infamous crime without presentment or
   indictment of a grand jury, except in the land or naval forces, or the militia
   in actual service. *)
Definition A5_1 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | CapitalCharge grand_jury military capital => capital = true -> grand_jury = true \/ military = true
    | _ => True
    end) w /\
  forall_laws (fun m => ~ In CapitalWithoutIndictment m.(m_features)) w.

(* Amendment V: no person twice put in jeopardy of life or limb for the same
   offence. *)
Definition A5_2 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | Prosecution double_jeopardy => double_jeopardy = false
    | _ => True
    end) w /\
  forall_laws (fun m => ~ In DoubleJeopardy m.(m_features)) w.

(* Amendment V: no person compelled in a criminal case to be a witness against
   himself. *)
Definition A5_3 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | CompelledTestimony criminal compelled => ~ (criminal = true /\ compelled = true)
    | _ => True
    end) w /\
  forall_laws (fun m => ~ In CompelledSelfIncrimination m.(m_features)) w.

(* Amendment V: no deprivation of life, liberty, or property without due process
   of law. *)
Definition A5_4 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | Deprivation due_process => due_process = true
    | _ => True
    end) w /\
  forall_laws (fun m => ~ In DeprivationWithoutProcess m.(m_features)) w.

(* Amendment V: no private property taken for public use without just
   compensation. *)
Definition A5_5 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | Taking public just => public = true -> just = true
    | _ => True
    end) w /\
  forall_laws (fun m => ~ In TakingWithoutCompensation m.(m_features)) w.

(* Amendment VI: the right to a speedy trial.  The eight rights are fields of
   CriminalProsecution: speedy, public, impartial jury (with the district fixed
   by law), notice, confrontation, compulsory process, and counsel. *)
Definition A6_1 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | CriminalProsecution speedy _ _ _ _ _ _ _ => speedy = true
    | _ => True
    end) w /\
  forall_laws (fun m => ~ In DenySpeedyTrial m.(m_features)) w.

(* Amendment VI: the right to a public trial. *)
Definition A6_2 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | CriminalProsecution _ public _ _ _ _ _ _ => public = true
    | _ => True
    end) w /\
  forall_laws (fun m => ~ In DenyPublicTrial m.(m_features)) w.

(* Amendment VI: an impartial jury of the State and district wherein the crime
   was committed, the district previously ascertained by law. *)
Definition A6_3 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | CriminalProsecution _ _ impartial district _ _ _ _ => impartial = true /\ district = true
    | _ => True
    end) w /\
  forall_laws (fun m => ~ In DenyImpartialJury m.(m_features)) w.

(* Amendment VI: the right to be informed of the nature and cause of the
   accusation. *)
Definition A6_4 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | CriminalProsecution _ _ _ _ informed _ _ _ => informed = true
    | _ => True
    end) w /\
  forall_laws (fun m => ~ In DenyNotice m.(m_features)) w.

(* Amendment VI: the right to be confronted with the witnesses. *)
Definition A6_5 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | CriminalProsecution _ _ _ _ _ confronted _ _ => confronted = true
    | _ => True
    end) w /\
  forall_laws (fun m => ~ In DenyConfrontation m.(m_features)) w.

(* Amendment VI: compulsory process for obtaining witnesses. *)
Definition A6_6 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | CriminalProsecution _ _ _ _ _ _ compulsory _ => compulsory = true
    | _ => True
    end) w /\
  forall_laws (fun m => ~ In DenyCompulsoryProcess m.(m_features)) w.

(* Amendment VI: the assistance of counsel for the defence. *)
Definition A6_7 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | CriminalProsecution _ _ _ _ _ _ _ counsel => counsel = true
    | _ => True
    end) w /\
  forall_laws (fun m => ~ In DenyCounsel m.(m_features)) w.

(* Amendment VII: trial by jury preserved in suits at common law where the value
   in controversy exceeds twenty dollars. *)
Definition A7_1 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | CivilSuit amount jury _ => 20 < amount -> jury = true
    | _ => True
    end) w /\
  forall_laws (fun m => ~ In DenyCivilJury m.(m_features)) w.

(* Amendment VII: no fact tried by a jury re-examined other than according to the
   rules of the common law. *)
Definition A7_2 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | CivilSuit _ _ reexamined => reexamined = false
    | _ => True
    end) w /\
  forall_laws (fun m => ~ In ReexaminesJury m.(m_features)) w.

(* Amendment VIII: no excessive bail. *)
Definition A8_1 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | Sanction SanctionBail excessive => excessive = false
    | _ => True
    end) w /\
  forall_laws (fun m => ~ In ExcessiveBail m.(m_features)) w.

(* Amendment VIII: no excessive fines. *)
Definition A8_2 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | Sanction SanctionFine excessive => excessive = false
    | _ => True
    end) w /\
  forall_laws (fun m => ~ In ExcessiveFines m.(m_features)) w.

(* Amendment VIII: no cruel and unusual punishments. *)
Definition A8_3 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | Sanction SanctionPunishment cruel => cruel = false
    | _ => True
    end) w /\
  forall_laws (fun m => ~ In CruelPunishment m.(m_features)) w.

(* Amendment IX: the enumeration of rights shall not be construed to deny or
   disparage others retained by the people. *)
Definition A9_1 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | DenialByEnumeration denies => denies = false
    | _ => True
    end) w /\
  forall_laws (fun m => ~ In DeniesRetainedRights m.(m_features)) w.

(* Amendment X: powers not delegated to the United States are reserved to the
   States or to the people.  Every enactment of the United States therefore
   cites an authority delegated to it. *)
Definition A10_1 (w : World) : Prop :=
  forall_laws (fun m => m.(m_authority) <> Unauthorized) w.
