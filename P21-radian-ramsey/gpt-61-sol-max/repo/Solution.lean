module

public import RadianRamsey.Radian
public import RadianRamsey.MathlibStatement


/-!
# Proved solution

`OAI.EuclideanRamsey.Radian.radian_configuration`, `radian_not_ramsey`, `radian_ramsey_iff` and
`radian_ramsey_iff_tan` (Theorem D) are proved in `RadianRamsey/Radian.lean`, and their
Mathlib-vocabulary forms `RadianRamsey.radian_configuration_mathlib`, `radian_ramsey_iff_mathlib`
and `radian_ramsey_iff_tan_mathlib` in `RadianRamsey/MathlibStatement.lean`. All of it sits on the
module-system port of OpenAI's EuclideanRamsey development (`OAI/`). `Space`, `Congruent` and
`Ramsey` come from `OAI/Combinatorics/EuclideanRamsey/Model.lean`, and `radianConfig` from
`RadianRamsey/Radian.lean`; Comparator checks that they are identical to the restatements in
`Challenge.lean`.
-/
