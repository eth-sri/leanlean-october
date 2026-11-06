module

public import PottsDiscontinuity.Potts.PottsBoxLaws

/-! Finite observations of the actual Potts box measures. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

open Classical MeasureTheory
noncomputable section

variable {A : Type*} [Fintype A]

section
variable (q : ℕ) (v : A → ℤ × ℤ) (ξ : A → Set.Icc 1 q)
/-- A prescribed spin pattern on a finite family of observed vertices. -/
def spinObservationEvent  : Set (SpinSpace q) :=
  {σ | ∀ a, σ (v a) = ξ a}

theorem spinObservationEvent_isClopen  :
    IsClopen (spinObservationEvent q v ξ) :=
  (isClopen_discrete {η : A → Set.Icc 1 q | ∀ a, η a = ξ a}).preimage
    (continuous_pi (fun a => continuous_apply (v a)))
end

local instance spinObservationFiniteMeasurable (q : ℕ) (n : ℕ) : MeasurableSpace (SpinConfiguration q (box n)) := ⊤
local instance spinObservationFiniteDiscrete (q : ℕ) (n : ℕ) : DiscreteMeasurableSpace (SpinConfiguration q (box n)) :=
  by tauto

section
variable (q : ℕ)
/-- The finite observation formula is independent of which finite enumeration
of the vertex carrier is used by a finite coupling theorem. -/
theorem pottsBoxProbabilityMeasure_observed
    (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β) (i : Fin (q + 1)) (n : ℕ)
    [Fintype ↥(box n : Set (ℤ × ℤ))] [DecidableEq ↥(box n : Set (ℤ × ℤ))]
    (v : A → ℤ × ℤ) (hv : ∀ a, v a ∈ box n) (ξ : A → Set.Icc 1 q) :
    (pottsBoxProbabilityMeasure q hq β hβ i n).toMeasure.real (spinObservationEvent q v ξ) =
      ∑ σ : SpinConfiguration q (box n),
        if ∀ a, σ ⟨v a, hv a⟩ = ξ a then pottsProb q (box n) β i σ else 0 := by
  change (((pottsFiniteLaw q hq (box n) β hβ i).map (spinExtension q hq (box n))).toMeasure _).toReal = _
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top (spinObservationEvent_isClopen q v ξ).isOpen.measurableSet, ← Measure.real, finite_pmf_measureReal_sum]
  apply Finset.sum_congr
  · rfl
  · intro σ _
    rw [pottsFiniteLaw_apply, ENNReal.toReal_ofReal (pottsProb_nonneg q hq (box n) β hβ i σ)]
    have he : spinExtension q hq (box n) σ ∈ spinObservationEvent q v ξ ↔
        ∀ a, σ ⟨v a, hv a⟩ = ξ a := by
      change (∀ a, spinExtension q hq (box n) σ (v a) = ξ a) ↔ _
      grind [spinExtension]
    grind

theorem spinObservationEvent_subtype (B : Finset (ℤ × ℤ)) (ξ : SpinSpace q) :
    spinObservationEvent q (fun a : ↥B => a.val) (fun a => ξ a.val) = spinCylinder q B ξ := by
  simp [spinObservationEvent, spinCylinder]
end

end
end PottsDiscontinuity.Potts
