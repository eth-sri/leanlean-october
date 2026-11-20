module

public import AnalyticESC.Dimension.Distortion
public import AnalyticESC.Separation

@[expose] public section

namespace AnalyticESC

open Set MeasureTheory Filter Topology

/-- The cylinder `[w] = {ω ∈ Σ : ω₁ ⋯ ω_{|w|} = w}` of a finite word. -/
def wordCylinder {N n : ℕ} (w : Fin n → Fin N) : Set (ℕ → Fin N) :=
  (fun ω (k : Fin n) => ω k) ⁻¹' {w}

namespace IFS

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

/-- `ν` has the Gibbs property for the potential `s log|f'|`: `ν[w]` is comparable to `‖f_w'‖^s`,
uniformly over finite words `w`. -/
def IsGibbs (s : ℝ) (ν : Measure (ℕ → Fin N)) : Prop :=
  ∃ a > 0, ∃ b > 0, ∀ n (w : Fin n → Fin N),
    a * Φ.supDeriv (List.ofFn w) ^ s ≤ ν.real (wordCylinder w) ∧
      ν.real (wordCylinder w) ≤ b * Φ.supDeriv (List.ofFn w) ^ s

/-- The natural projection is measurable, so `ν ∘ π⁻¹` is the image measure of `ν`. -/
theorem measurable_natProj : Measurable Φ.natProj :=
  Φ.continuous_natProj.measurable

/-- The measure of the set of infinite words whose prefix of length `n` lies in `S` is the sum of
the measures of the cylinders of the words in `S`. -/
theorem sum_measureReal_wordCylinder (ν : Measure (ℕ → Fin N)) [IsFiniteMeasure ν] (n : ℕ)
    (S : Finset (Fin n → Fin N)) :
    ∑ v ∈ S, ν.real (wordCylinder v) =
      ν.real ((fun ω (k : Fin n) => ω k) ⁻¹' ↑S) := by
  have hm : Measurable fun (ω : ℕ → Fin N) (k : Fin n) => ω k := by fun_prop
  rw [← map_measureReal_apply hm MeasurableSet.of_discrete, ← sum_measureReal_singleton]
  simp [wordCylinder, map_measureReal_apply, hm, MeasurableSet.of_discrete]

end IFS

end AnalyticESC
