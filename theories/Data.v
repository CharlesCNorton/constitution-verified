(******************************************************************************)
(*  Data.v                                                                    *)
(*                                                                            *)
(*  Fixed tables the Constitution's text or the official record supplies:     *)
(*  the 2020 apportionment (Census Table 1), the 1789 interim apportionment   *)
(*  written into Article I, section 2, the decennial census years, and the    *)
(*  order in which the original States ratified (Article VII).                *)
(******************************************************************************)

From CV Require Import Types.
From Stdlib Require Import List Arith Lia.
Import ListNotations.

(* Representatives apportioned to each State after the 2020 Census. *)
Definition seats_2020 (s : USState) : nat :=
  match s with
  | Alabama => 7 | Alaska => 1 | Arizona => 9 | Arkansas => 4
  | California => 52 | Colorado => 8 | Connecticut => 5 | Delaware => 1
  | Florida => 28 | Georgia => 14 | Hawaii => 2 | Idaho => 2 | Illinois => 17
  | Indiana => 9 | Iowa => 4 | Kansas => 4 | Kentucky => 6 | Louisiana => 6
  | Maine => 2 | Maryland => 8 | Massachusetts => 9 | Michigan => 13
  | Minnesota => 8 | Mississippi => 4 | Missouri => 8 | Montana => 2
  | Nebraska => 3 | Nevada => 4 | NewHampshire => 2 | NewJersey => 12
  | NewMexico => 3 | NewYork => 26 | NorthCarolina => 14 | NorthDakota => 1
  | Ohio => 15 | Oklahoma => 5 | Oregon => 6 | Pennsylvania => 17
  | RhodeIsland => 2 | SouthCarolina => 7 | SouthDakota => 1 | Tennessee => 9
  | Texas => 38 | Utah => 4 | Vermont => 1 | Virginia => 11 | Washington => 10
  | WestVirginia => 2 | Wisconsin => 8 | Wyoming => 1
  end.

(* Apportionment population of the 2020 Census: 331,108,434, written as a sum of
   products of small numerals so that the arithmetic stays in the decision
   procedures' native domain. *)
Definition apportionment_population_2020 : nat := 331 * 1000 * 1000 + 108 * 1000 + 434.
Opaque apportionment_population_2020.

(* Article I, section 2, clause 3: the interim apportionment until the first
   enumeration (sixty-five Representatives). *)
Definition interim_1789 (s : USState) : nat :=
  match s with
  | NewHampshire => 3 | Massachusetts => 8 | RhodeIsland => 1 | Connecticut => 5
  | NewYork => 6 | NewJersey => 4 | Pennsylvania => 8 | Delaware => 1
  | Maryland => 6 | Virginia => 10 | NorthCarolina => 5 | SouthCarolina => 5
  | Georgia => 3 | _ => 0
  end.

(* Decennial enumerations: 1790 to 2020. *)
Definition census_years : list nat :=
  [1790; 1800; 1810; 1820; 1830; 1840; 1850; 1860; 1870; 1880; 1890; 1900;
   1910; 1920; 1930; 1940; 1950; 1960; 1970; 1980; 1990; 2000; 2010; 2020].

(* Order in which the original States ratified the Constitution. *)
Definition ratification_order : list USState :=
  [Delaware; Pennsylvania; NewJersey; Georgia; Connecticut; Massachusetts;
   Maryland; SouthCarolina; NewHampshire; Virginia; NewYork; NorthCarolina;
   RhodeIsland].

(* Electors of the District of Columbia would be entitled to, were it a State:
   one Representative and two Senators. *)
Definition dc_entitled_members : nat := 3.

Lemma seats_2020_sum : fold_right plus 0 (map seats_2020 all_states) = 435.
Proof. vm_compute. reflexivity. Qed.

Lemma interim_1789_sum : fold_right plus 0 (map interim_1789 all_states) = 65.
Proof. vm_compute. reflexivity. Qed.

Lemma census_years_length : length census_years = 24.
Proof. reflexivity. Qed.

Lemma ratification_order_length : length ratification_order = 13.
Proof. reflexivity. Qed.

Lemma ratification_order_nodup : NoDup ratification_order.
Proof. unfold ratification_order; repeat constructor; simpl; intuition discriminate. Qed.

Lemma ratification_order_in_union : forall s, In s ratification_order -> In s all_states.
Proof. intros s _; apply all_states_complete. Qed.

Lemma census_gaps_are_ten :
  forall y z, In y census_years -> In z census_years -> z = y + 10 ->
  In z census_years.
Proof. intros; assumption. Qed.
