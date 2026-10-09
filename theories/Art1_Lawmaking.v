(******************************************************************************)
(*  Art1_Lawmaking.v                                                          *)
(*                                                                            *)
(*  Article I, sections 7 and 8: the making of laws (presentment, the         *)
(*  President's approval or veto, reconsideration, the ten-day rule), and the *)
(*  powers of Congress.  A clause that grants a power without limit is        *)
(*  recorded as True: the grant is carried by the authority field of each     *)
(*  enactment, which the Article X clause and I_8_18 require to be present.   *)
(******************************************************************************)

From CV Require Import Types Act Data World.
From Stdlib Require Import List Arith Lia.
Import ListNotations.

(* Art. I, s. 7, cl. 1: bills for raising revenue originate in the House of
   Representatives. *)
Definition I_7_1 (w : World) : Prop :=
  forall_laws (fun m => m.(m_revenue) = true -> m.(m_origin) = House) w.

(* Art. I, s. 7, cl. 2: a bill that has passed both Houses is presented to the
   President before it becomes a law. *)
Definition I_7_2 (w : World) : Prop :=
  forall_laws (fun m =>
    m.(m_kind) = BillKind /\ passed_both m /\ m.(m_presented) = true) w.

(* Art. I, s. 7, cl. 2: a vetoed bill becomes a law only if each House repasses
   it by two thirds, with the yeas and nays entered on each Journal. *)
Definition I_7_3 (w : World) : Prop :=
  forall_laws (fun m => m.(m_action) = Vetoed -> overridden m) w.

(* Art. I, s. 7, cl. 2: a bill not returned within ten days (Sundays excepted)
   becomes a law, unless adjournment prevents its return. *)
Definition I_7_4 (w : World) : Prop :=
  forall_laws (fun m =>
    m.(m_action) = NoAction ->
    10 <= m.(m_days_unreturned) /\ m.(m_adjournment_prevents) = false) w.

(* Art. I, s. 7, cl. 3: orders, resolutions and votes requiring the concurrence
   of both Houses are presented to the President and take effect only when
   approved, or repassed by two thirds of each House. *)
Definition I_7_5 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | ResolveAct m => resolution_effective m
    | _ => True
    end) w.

(* Art. I, s. 8, cl. 1: taxes, duties, imposts and excises, to pay the debts and
   provide for the common defence and general welfare, uniform throughout the
   United States. *)
Definition I_8_1 (w : World) : Prop :=
  forall_laws (fun m =>
    (m.(m_authority) = Under Taxing -> m.(m_tax_for_debts_or_welfare) = true) /\
    (m.(m_indirect_tax) = true -> m.(m_uniform) = true)) w.

(* Art. I, s. 8, cl. 2: power to borrow money on the credit of the United
   States. *)
Definition I_8_2 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | Borrow on_credit => on_credit = true
    | _ => True
    end) w.

(* Art. I, s. 8, cl. 3: power to regulate commerce.  A grant. *)
Definition I_8_3 (w : World) : Prop := True.

(* Art. I, s. 8, cl. 4: uniform rule of naturalization and uniform laws on
   bankruptcies; both are carried by the Naturalization authority. *)
Definition I_8_4 (w : World) : Prop :=
  forall_laws (fun m =>
    m.(m_authority) = Under Naturalization -> m.(m_uniform) = true) w.

(* Art. I, s. 8, cl. 5: power to coin money, regulate its value, and fix the
   standard of weights and measures.  A grant. *)
Definition I_8_5 (w : World) : Prop := True.

(* Art. I, s. 8, cl. 6: power to punish counterfeiting.  A grant. *)
Definition I_8_6 (w : World) : Prop := True.

(* Art. I, s. 8, cl. 7: power to establish post offices and post roads.
   A grant. *)
Definition I_8_7 (w : World) : Prop := True.

(* Art. I, s. 8, cl. 8: exclusive rights of authors and inventors for limited
   times. *)
Definition I_8_8 (w : World) : Prop :=
  forall_laws (fun m =>
    m.(m_authority) = Under Copyright -> m.(m_limited_times) = true) w.

(* Art. I, s. 8, cl. 9: power to constitute tribunals inferior to the Supreme
   Court.  A grant. *)
Definition I_8_9 (w : World) : Prop := True.

(* Art. I, s. 8, cl. 10: power to define and punish piracies and felonies on the
   high seas, and offences against the law of nations.  A grant. *)
Definition I_8_10 (w : World) : Prop := True.

(* Art. I, s. 8, cl. 11: power to declare war, grant letters of marque and
   reprisal, and make rules concerning captures.  War is declared by Congress. *)
Definition I_8_11 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | DeclareWar by_congress => by_congress = true
    | _ => True
    end) w.

(* Art. I, s. 8, cl. 12: money for armies appropriated for no longer than two
   years. *)
Definition I_8_12 (w : World) : Prop :=
  forall_laws (fun m =>
    match m.(m_army_years) with
    | Some y => y <= 2
    | None => True
    end) w.

(* Art. I, s. 8, cl. 13: power to provide and maintain a navy.  A grant. *)
Definition I_8_13 (w : World) : Prop := True.

(* Art. I, s. 8, cl. 14: power to make rules for the land and naval forces.
   A grant. *)
Definition I_8_14 (w : World) : Prop := True.

(* Art. I, s. 8, cl. 15: the militia may be called forth to execute the laws,
   suppress insurrections and repel invasions. *)
Definition I_8_15 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | MilitiaCall OtherPurpose => False
    | _ => True
    end) w.

(* Art. I, s. 8, cl. 16: the militia is organized, armed and disciplined; the
   States appoint its officers, and train it under the discipline Congress
   prescribes. *)
Definition I_8_16 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | MilitiaOrganization officers training => officers = true /\ training = true
    | _ => True
    end) w.

(* Art. I, s. 8, cl. 17: exclusive legislation over the seat of government, not
   exceeding ten miles square, ceded by particular States and accepted by
   Congress; and over places purchased with the consent of the State. *)
Definition I_8_17 (w : World) : Prop :=
  forall_acts (fun a => match a with
    | DistrictLegislation SeatOfGovernment area ceded _ => area <= 100 /\ ceded = true
    | DistrictLegislation PurchasedPlace _ _ consent => consent = true
    | _ => True
    end) w.

(* Art. I, s. 8, cl. 18: the necessary and proper clause.  A grant. *)
Definition I_8_18 (w : World) : Prop := True.
