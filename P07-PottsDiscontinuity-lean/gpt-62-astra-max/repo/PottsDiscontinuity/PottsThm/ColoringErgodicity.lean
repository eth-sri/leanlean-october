module

public import Mathlib.Dynamics.Ergodic.Extreme
public import PottsDiscontinuity.PottsThm.ColoringFactor
public import PottsDiscontinuity.Frozen.Defs.IsTranslationErgodic

@[expose] public section

namespace PottsDiscontinuity.PottsThm
open MeasureTheory Filter Set
open scoped ENNReal

variable {C : Type*} [MeasurableSpace C] {μ : Measure (Vertex → C)} [IsProbabilityMeasure μ]

def spinShift (a : Vertex) : (Vertex → C) → Vertex → C := fun σ x => σ (x - a)

private theorem spinShift_def (a : Vertex) : spinShift (C := C) a = fun σ x => σ (x - a) := rfl

section
variable (h : MixingFamily spinShift μ cofinite)
include h

/-- Mixing under translations implies ergodicity even for a single horizontal step. -/
theorem horizontal_ergodic :
    Ergodic (spinShift (1,0)) μ := by
  apply Ergodic.of_preimage_eq (h.preserving (1,0))
  intro A hA hinv
  have hpre (n : ℕ) : spinShift ((n : ℤ),0) ⁻¹' A = A := by
    induction n with
    | zero => change (fun σ x => σ (x - (0 : Vertex))) ⁻¹' A = A; simp
    | succ n ih =>
      rw [show spinShift (((n+1 : ℕ) : ℤ),0) (C := C) = spinShift (1,0) ∘ spinShift ((n:ℤ),0) by
        funext σ x; apply congrArg σ; ext <;> simp <;> omega,
        preimage_comp, hinv, ih]
  have inj : Function.Injective (fun n : ℕ => ((n:ℤ), (0:ℤ))) := by
    intro n k e; grind
  have hz := zero_one_of_self_mixing hpre ((h.mixing hA hA).comp inj.tendsto_cofinite)
  simpa [eventuallyEmptyOrUniv_iff', prob_compl_eq_zero_iff hA] using hz

theorem translation_ergodic : IsTranslationErgodic μ := by
  constructor
  · intro a; simpa [spinShift_def] using (h.preserving (-a)).map_eq
  · intro A hA hi
    apply (horizontal_ergodic h).toPreErgodic.measure_self_or_compl_eq_zero hA.nullMeasurableSet
    apply Filter.Eventually.of_forall
    intro σ; apply propext
    simpa only [mem_preimage, spinShift_def, sub_eq_add_neg] using Set.ext_iff.mp (hi (-(1,0))) σ

end

/-- An invariant probability measure dominated by a horizontally ergodic
probability measure coincides with it. In particular no average of distinct
invariant colour phases can give the free mixing phase. -/
theorem mixing_ne_average {q : ℕ} (j : Fin q) {ν : Fin q → Measure (Vertex → C)}
    [∀ i, IsProbabilityMeasure (ν i)] (h : MixingFamily spinShift μ cofinite)
    (hj : MixingFamily spinShift (ν j) cofinite) (hne : ν j ≠ μ) :
    μ ≠ (q : ℝ≥0∞)⁻¹ • ∑ i, ν i := by
  intro eq
  apply hne ((horizontal_ergodic h).eq_of_absolutelyContinuous (hj.preserving _) ?_)
  rw [eq]
  exact (Measure.absolutelyContinuous_of_le (Finset.single_le_sum (f := ν)
    (fun i _ s => by simp) (Finset.mem_univ j))).trans (Measure.absolutelyContinuous_smul (by simp))

end PottsDiscontinuity.PottsThm
