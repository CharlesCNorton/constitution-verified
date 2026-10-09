# constitution-verified

A Rocq formalization of the Constitution of the United States: the Preamble,
Articles I to VII, the Bill of Rights, and Amendments XI to XXVII.

## Layout

- `CLAUSES.tsv`: the clause manifest. One row per clause: identifier, citation,
  summary, and kind. `S` is structural, `A` constrains acts of government, and
  `D` marks a clause that is superseded, expired, or not operative.
- `theories/Types.v`: enumerations and records: States, Chambers, votes,
  measures, persons, electoral ballots.
- `theories/Act.v`: the acts of government that the clauses regulate.
- `theories/World.v`: a World, the state of the system that each clause is a
  predicate on.
- `theories/Data.v`: the 2020 apportionment, the 1789 interim apportionment,
  the census years, and the order of ratification.
- `theories/Preamble.v`, `Art1_Congress.v`, `Art1_Lawmaking.v`, `Art1_Limits.v`,
  `Art2.v`, `Art3.v`, `Art4.v`, `Art5_7.v`, `Amend_BoR.v`, `Amend_11_19.v`,
  `Amend_20_27.v`: one predicate per clause, named by its manifest identifier.
- `theories/Constitutional.v`: the conjunction of every clause predicate.
- `theories/Witness.v`, `theories/WitnessCheck.v`: a concrete World, generated
  from the 2020 apportionment, and the proof that it satisfies `Constitutional`.
- `Constitution.v`: the top level. It states satisfiability and consequences of
  individual clauses.
- `tools/check_clauses.py`: checks the manifest against the Coq names and the
  conjunction.

## Building

Requires Rocq 9.0 or later, which uses the `Stdlib` library name. From the
repository root, compile the files in the order listed in `_CoqProject`:

    coqc -Q theories CV theories/Types.v
    coqc -Q theories CV theories/Act.v
    ...
    coqc -Q theories CV Constitution.v

## Checking the manifest

    python tools/check_clauses.py

The script confirms that each manifest identifier is defined as a predicate on
`World`, that each such predicate appears in `Constitutional`, and that no
clause predicate is missing from the manifest.

## Modeling

- Acts. Government acts are values of `Act`. A clause that regulates an act is
  a condition on the acts of its kind. The facts the text requires (votes,
  presentment, presidential action, the Senate's count) are fields of the act.
- Laws. A `Measure` carries its features, such as `AbridgesSpeech`. A clause
  that forbids a feature forbids it in every enacted law.
- Membership. The House and Senate of the witness are generated from the 2020
  apportionment. Its electors are the States' Representatives and Senators, plus
  the District's three.
- Thresholds. "Two thirds of the Members present" is stated as
  `2 * present <= 3 * yeas`. Article I, section 7, and Article V speak of "two
  thirds of that House" and "two thirds of both Houses"; they are modeled on the
  same basis, which is a documented choice.
- Superseded and expired clauses are stated as "superseding amendment in force,
  or the rule", so the clause holds once the rule is displaced.
- Grants of power are recorded as `True`. The authority an act cites carries the
  scope of the grant.
- The Preamble is declaratory. Its predicate records the six declared ends.
- Determinations the text leaves to judgment (what is unreasonable, excessive,
  or cruel) are recorded by the act, and the clause requires the determination.

## Witness

`Witness.v` is a model instance. It asserts no historical vote tally and no
historical event: its acts exist to exercise the clauses.

## Top-level results

- `constitution_satisfiable`: some World meets every clause.
- `enacted_law_passed_both_houses`, `vetoed_law_overridden`,
  `ratification_three_fourths`, `enacted_law_not_attainder`,
  `registered_candidate_eligible`, `succession_by_vice_president`: consequences
  of individual clauses, for every World that satisfies `Constitutional`.

## Sources

The clause text follows the National Archives transcriptions of the
Constitution, the Bill of Rights, and Amendments XI to XXVII. The 2020
apportionment is the Census Bureau's Table 1, as reported in the 2021
apportionment release.

## License

MIT (see `LICENSE`).
