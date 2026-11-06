module

public import RadianRamsey.Radian
public import RadianRamsey.MathlibStatement
import OAI.Combinatorics.EuclideanRamsey.AdicLifting
import OAI.Combinatorics.EuclideanRamsey.CornerGroup
import OAI.Combinatorics.EuclideanRamsey.CorrectionPaths
import OAI.Combinatorics.EuclideanRamsey.DerivedFractions
import OAI.Combinatorics.EuclideanRamsey.DifferentialSplitting
import OAI.Combinatorics.EuclideanRamsey.FiniteEuclidean
import OAI.Combinatorics.EuclideanRamsey.Hessian
import OAI.Combinatorics.EuclideanRamsey.IndependentTensor
import OAI.Combinatorics.EuclideanRamsey.LatticeMoments
import OAI.Combinatorics.EuclideanRamsey.NineGeometry
import OAI.Combinatorics.EuclideanRamsey.PathFractions
import OAI.Combinatorics.EuclideanRamsey.PathWords
import OAI.Combinatorics.EuclideanRamsey.TensorDescent
import OAI.Combinatorics.EuclideanRamsey.TensorPresentation
import OAI.Combinatorics.EuclideanRamsey.UltrafilterStrings

public section

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
