# constitution-verified

Formalizing U.S. Constitutional structure.

## Scope

- **Article I § 8**: Enumerated congressional powers (18 clauses)
- **Article II**: Executive authority, veto override thresholds
- **Article V**: Amendment ratification (2/3 Congress + 3/4 states)
- **Judicial Review**: Marbury v. Madison decision procedure
- **10th Amendment**: Reserved powers constraint
- **Supremacy Clause**: Federal/state conflict resolution
- **Electoral College**: 538 votes, 270 majority

## Status

| EXISTS | SKELETON | NONTRIVIAL | PROVEN | STABLE | EXERCISED |
|--------|----------|------------|--------|--------|-----------|
| ✅ | ✅ | ✅ | ✅ | ✅ | ❌ |

## Key Theorems

- `eighteen_enumerated_powers`: Art. I § 8 contains exactly 18 clauses
- `house_two_thirds_is_290`: Veto override requires 290 House votes
- `senate_two_thirds_is_67`: Veto override requires 67 Senate votes
- `amendment_ratification_requires_38`: 3/4 of 50 states = 38
- `electoral_college_majority_is_270`: 538/2 + 1 = 270
- `conviction_requires_67_senators`: Impeachment conviction threshold
- `federal_preempts_conflicting_state`: Supremacy Clause resolution
- `unenumerated_unpermitted_reserved`: 10th Amendment logic

## Build

```bash
coqc Constitution.v
```

## License

MIT

## Author

Charles C. Norton
