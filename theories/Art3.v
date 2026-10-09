(******************************************************************************)
(*  Art3.v                                                                    *)
(*                                                                            *)
(*  Article III: the judicial power, its extent and forum, trial by jury, and *)
(*  treason.  The Eleventh Amendment's limit on suits against a State is in   *)
(*  Amend_11_19.v.                                                            *)
(******************************************************************************)

From CV Require Import Types Act Data World.
From Stdlib Require Import List Arith Lia.
Import ListNotations.

(* The categories of cases and controversies named in Article III, section 2. *)
Definition listed_categories : list CaseCategory :=
  [ArisingUnder; AmbassadorsOrMinisters; Admiralty; UnitedStatesParty;
   StateParty; BetweenStates; StateAndOtherStateCitizens;
   CitizensOfDifferentStates; LandGrantsOfDifferentStates;
   StateOrCitizensAndForeign].

(* Categories in which a State is a party. *)
Definition state_party_case (c : CaseCategory) : bool :=
  match c with
  | StateParty | BetweenStates | StateAndOtherStateCitizens
  | StateOrCitizensAndForeign => true
  | _ => false
  end.

(* Art. III, s. 1: the judicial power vested in one Supreme Court and in such
   inferior courts as Congress establishes. *)
Definition III_1_1 (w : World) : Prop :=
  w.(w_supreme_court_established) = true.

(* Art. III, s. 1: judges hold office during good behaviour; their compensation
   is not diminished during their continuance in office. *)
Definition III_1_2 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | JudgeRemoval conviction => conviction = true
    | JudgeCompensation diminished => diminished = false
    | _ => True
    end) w.

(* Art. III, s. 2, cl. 1: the judicial power extends to the enumerated cases and
   controversies, and to no others. *)
Definition III_2_1 (w : World) : Prop :=
  (forall c : CaseCategory, In c listed_categories) /\
  forall_acts (fun a => match a with
    | CourtCase cat _ => In cat listed_categories
    | _ => True
    end) w.

(* Art. III, s. 2, cl. 2: original jurisdiction in cases affecting ambassadors,
   public ministers and consuls, and in cases in which a State is a party;
   appellate jurisdiction in the other cases, with the exceptions Congress
   makes. *)
Definition III_2_2 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | CourtCase cat forum =>
        (forum = OriginalForum <-> (cat = AmbassadorsOrMinisters \/ state_party_case cat = true))
    | _ => True
    end) w.

(* Art. III, s. 2, cl. 3: the trial of all crimes, except impeachment, is by jury,
   in the State where the crime was committed; if committed within no State, at
   the place Congress has directed by law. *)
Definition III_2_3 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | CriminalTrial jury crime trial place impeachment =>
        impeachment = true \/
        (jury = true /\ (crime = Some trial \/ (crime = None /\ place = true)))
    | _ => True
    end) w.

(* Art. III, s. 3, cl. 1: treason consists only in levying war against the
   United States, or in adhering to their enemies, giving them aid and comfort. *)
Definition III_3_1 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | TreasonCharge levied adhered => levied = true \/ adhered = true
    | _ => True
    end) w.

(* Art. III, s. 3, cl. 1: no conviction of treason except on the testimony of two
   witnesses to the same overt act, or on confession in open court. *)
Definition III_3_2 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | TreasonConviction two confession => two = true \/ confession = true
    | _ => True
    end) w.

(* Art. III, s. 3, cl. 2: Congress declares the punishment of treason; no
   attainder of treason works corruption of blood or forfeiture beyond the life
   of the person attainted. *)
Definition III_3_3 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | TreasonPunishment declared corruption forfeiture =>
        declared = true /\ corruption = false /\ forfeiture = false
    | _ => True
    end) w.
