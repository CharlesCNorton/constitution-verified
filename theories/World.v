(******************************************************************************)
(*  World.v                                                                   *)
(*                                                                            *)
(*  A World is one state of the constitutional system: the apportionment and  *)
(*  membership of Congress, the electors, the officers, the amendments in     *)
(*  force, and the record of government acts.  Every clause is a predicate    *)
(*  on a World.                                                               *)
(******************************************************************************)

From CV Require Import Types Act Data.
From Stdlib Require Import List Arith Lia.
Import ListNotations.

Scheme Equality for USState.

Record World : Type := mkWorld {
  (* Article I, section 2, clause 3: apportionment *)
  w_reps : USState -> nat;            (* Representatives apportioned to each State *)
  w_census_years : list nat;          (* decennial enumerations *)
  w_interim_superseded : bool;        (* the first enumeration has been made *)
  w_basis_excludes_untaxed_indians : bool;   (* Amendment XIV, s. 2 basis *)
  (* Article I, sections 2 and 3: the members of the two Houses *)
  w_house : list Person;
  w_senate : list Person;             (* p_senate_class gives the class, 1 to 3 *)
  w_senate_class_sizes : list nat;
  w_house_term_years : nat;
  w_senate_term_years : nat;
  w_elector_quals_match : bool;       (* electors of Representatives: State's voter qualifications *)
  w_speaker_by_house : bool;          (* the House chooses its Speaker *)
  w_pro_tempore_by_senate : bool;     (* the Senate chooses a President pro tempore *)
  w_supreme_court_established : bool;
  (* Article II, section 1: electors and the officers *)
  w_electors : USState -> nat;
  w_dc_electors : nat;
  w_dc_entitled : nat;                (* Members the District would have as a State *)
  w_ballots : list ElectorBallot;
  w_elector_day_uniform : bool;       (* one day of voting throughout the United States *)
  w_president : Person;
  w_vice_president : Person;
  w_pres_term_years : nat;
  (* Article II, section 1 and Amendment XX, section 1: the terms' ends *)
  w_pres_term_end : nat * nat;        (* (day, month) at noon *)
  w_congress_term_end : nat * nat;
  (* Article VII, Article V and the Amendments *)
  w_ratified_states : list USState;   (* in order of ratification *)
  w_in_force : nat -> bool;           (* amendments numbered 1 to 27 *)
  w_art1_1789_ratified : bool;        (* the first article of the 1789 resolution *)
  (* Structural facts of the record *)
  w_sessions_each_year : bool;        (* Congress met at least once in each year *)
  w_statement_published : bool;       (* statement and account of public money *)
  w_state_of_union_given : bool;
  (* The acts of government *)
  w_acts : list Act
}.

(* Total Representatives. *)
Definition total_reps (w : World) : nat :=
  fold_right plus 0 (map (w_reps w) all_states).

(* Total electors: the States' electors and the District's. *)
Definition total_electors (w : World) : nat :=
  fold_right plus 0 (map (w_electors w) all_states) + w_dc_electors w.

(* Fewest electors of any State: the electors of the least populous State. *)
Definition min_state_electors (w : World) : nat :=
  fold_right min (w_electors w Alabama) (map (w_electors w) all_states).

(* Members of a list belonging to a State. *)
Definition members_from (l : list Person) (s : USState) : nat :=
  length (filter (fun p => if USState_eq_dec p.(p_state) s then true else false) l).

(* The Senators of a given class. *)
Definition senators_in_class (w : World) (k : nat) : nat :=
  length (filter (fun p => Nat.eqb p.(p_senate_class) k) w.(w_senate)).

(* Every act of the record satisfies the predicate. *)
Definition forall_acts (P : Act -> Prop) (w : World) : Prop :=
  forall a, In a (w.(w_acts)) -> P a.

(* Every enacted measure of the record satisfies the predicate: a condition on
   the EnactLaw acts. *)
Definition forall_laws (P : Measure -> Prop) (w : World) : Prop :=
  forall_acts (fun a => match a with EnactLaw m => P m | _ => True end) w.

(* A list of acts all satisfying P gives forall_acts P. *)
Lemma forall_acts_of_Forall : forall (P : Act -> Prop) (w : World),
  Forall P (w.(w_acts)) -> forall_acts P w.
Proof. intros P w H; exact (proj1 (Forall_forall P _) H). Qed.
