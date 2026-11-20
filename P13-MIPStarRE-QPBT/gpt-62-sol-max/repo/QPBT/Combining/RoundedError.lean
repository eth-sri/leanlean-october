module

public import QPBT.Combining.PassingError
public import QPBT.Test.SoundnessDefs
public import QPBT.Test.LowDegreeGameMeasurements

/-! The scalar errors of the extended test, rounding, and polynomial-pair extraction. -/

@[expose] public section

namespace MIPStarRE.QPBT

noncomputable abbrev AdmissibleParams.degreeRatio (P : AdmissibleParams) : ℝ := P.degreeBudget / P.q

noncomputable abbrev AdmissibleParams.extendedLdError (P : AdmissibleParams)
    (a b point line : ℝ) : ℝ :=
  deltaLd a b (directPassingErrorEnvelope (point + line) P.degreeRatio) P.q (2 * P.m + 2) P.d 1

noncomputable abbrev roundedLdError (delta : ℝ) : ℝ :=
  delta + Real.sqrt (220 * delta ^ (1 / 4 : ℝ)) + 2 * Real.sqrt (2 * delta)

noncomputable abbrev AdmissibleParams.pairError (P : AdmissibleParams) (point delta : ℝ) : ℝ :=
  8 * (4 * roundedLdError delta + 8 * point) + (((12 * P.m * P.d + 4 * P.d + 14 : ℕ) : ℝ) / P.q)

end MIPStarRE.QPBT
