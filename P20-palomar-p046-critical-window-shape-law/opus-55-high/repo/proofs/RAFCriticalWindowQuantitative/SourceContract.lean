module

public import proofs.RAFCriticalWindowQuantitative.RationalPool
public import proofs.RAFCriticalWindowQuantitative.Endpoints

@[expose] public section

namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold RAFReactionQuotient MeasureTheory unitInterval RAF.Polymer RAF.Concrete
open scoped ENNReal

noncomputable def splitCatalyticProbability (n : ℕ) (p : I) : ENNReal :=
  uniformCatalysisMeasure n ((p : ℝ)*Fintype.card (Reaction n)/n) (HasRAFEvent n)

variable (n m K : ℕ) (p q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1)

def splitSourceInterval  : ℚ × ℚ :=
  (splitSeedEval n (10*seedIndex q hq hq1 m) q - 1/m,
    splitEscapeEval (rationalPool p $ Fintype.card $ Molecule n) K +
      (Fintype.card (Molecule $ K+2) : ℚ)*36*p)

def quotientSourceInterval  : ℚ × ℚ :=
  let hh : 0 < q/2 := rationalHalf_pos q hq
  let hh1 : q/2 ≤ 1 := rationalHalf_le_one q hq hq1
  (quotientSeedEval n (10*seedIndex (q/2) hh hh1 m) q - 1/m,
    quotientEscapeEval (rationalPool p $ Fintype.card $ Molecule n) K +
      (Fintype.card (Molecule $ K+2) : ℚ)*34*p)


theorem toReal_interval {P S E t : ℝ≥0∞} {m : ℕ} (hm : 0 < m) (hl : S ≤ P + (m : ℝ≥0∞)⁻¹)
    (hu : P ≤ E + t) (hE : E ≠ ⊤) (ht : t ≠ ⊤) :
    S.toReal - 1/m ≤ P.toReal ∧ P.toReal ≤ E.toReal + t.toReal := by
  have hP := ne_top_of_le_ne_top (by finiteness) hu
  have h1 := ENNReal.toReal_mono (by simp_all [hm.ne']) hl
  have h2 := ENNReal.toReal_mono (by finiteness) hu
  rw [ENNReal.toReal_add hP $ by simp_all [hm.ne']] at h1
  rw [ENNReal.toReal_add hE ht] at h2
  simp at h1
  grind

end RAFCriticalWindowQuantitative
