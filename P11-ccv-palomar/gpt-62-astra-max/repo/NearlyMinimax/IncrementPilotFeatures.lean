module

public import NearlyMinimax.PreconditionedPilot
public import NearlyMinimax.DyadicNesting


@[expose] public section

/-! The exact current/parent free-moment input of the determinant-cleared
increment polynomial, including the virtual identity parent at level zero. -/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace NearlyMinimax

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def anchoredFinIndex {d ℓ : ℕ} (i : Fin (anchoredDimension d ℓ)) : AnchoredIndex d ℓ :=
  (Fintype.equivFin (AnchoredIndex d ℓ)).symm i

def dyadicIncrementFeature {d ℓ : ℕ} (j : ℕ) (x : Covariate d)
    (v : incrementVariables (anchoredDimension d ℓ)) (z : Observation d) : ℝ :=
  match v with
  | Sum.inl m => match m with
    | Sum.inl it =>
      preconditionedPilotFeature j x (Sum.inl (anchoredFinIndex it.1, anchoredFinIndex it.2)) z
    | Sum.inr it =>
      if j = 0 then (if it.2.1 = it.2.2 then 1 else 0) else
        preconditionedPilotFeature (j - 1) x (Sum.inl (anchoredFinIndex it.2.1, anchoredFinIndex it.2.2)) z
  | Sum.inr pri =>
    if pri.1 && (j == 0) then 0 else
      preconditionedPilotFeature (if pri.1 then j - 1 else j) x
        (if pri.2.1 then Sum.inr (Sum.inr (anchoredFinIndex pri.2.2))
          else Sum.inr (Sum.inl (anchoredFinIndex pri.2.2))) z

def dyadicIncrementRawVector {d ℓ : ℕ} (j : ℕ) (x : Covariate d) (z : Observation d) :
    Fin (Fintype.card (incrementVariables (anchoredDimension d ℓ))) → ℝ :=
  fun a => dyadicIncrementFeature j x
    ((Fintype.equivFin (incrementVariables (anchoredDimension d ℓ))).symm a) z

section
variable {d ℓ : ℕ} (θ : RegressionParameter d) (j : ℕ) (x : Covariate d)

def dyadicIncrementRawMean :
    Fin (Fintype.card (incrementVariables (anchoredDimension d ℓ))) → ℝ :=
  fun a => ∫ z, dyadicIncrementRawVector j x z a ∂observationLaw θ

/-- Each increment coordinate is constant zero or one, or a preconditioned
pilot coordinate at a level no finer than `j`. This eliminates the parent
and current cases simultaneously for pointwise and joint properties. -/
theorem dyadicIncrementFeature_induction (v : incrementVariables (anchoredDimension d ℓ))
    (P : (Covariate d → Observation d → ℝ) → Prop) (h0 : P (fun _ _ => 0)) (h1 : P (fun _ _ => 1))
    (h : ∀ k ≤ j, ∀ a : LocalPilotIndex d ℓ, P (fun x z => preconditionedPilotFeature k x a z)) :
    P (fun x z => dyadicIncrementFeature j x v z) := by
  rcases v with (it | it) | ⟨parent, response, i⟩
  · exact h j le_rfl _
  · simp [dyadicIncrementFeature]; split_ifs <;> first | assumption | exact h _ (Nat.sub_le ..) _
  · cases parent <;> simp [dyadicIncrementFeature] <;> split_ifs <;>
      first | assumption | exact h _ le_rfl _ | exact h _ (Nat.sub_le ..) _

theorem dyadicIncrementFeature_measurable (v : incrementVariables (anchoredDimension d ℓ)) :
    Measurable (dyadicIncrementFeature j x v) :=
  dyadicIncrementFeature_induction j v (fun f => Measurable (f x)) measurable_const measurable_const
    (fun k _ => preconditionedPilotFeature_measurable k x)

theorem dyadicIncrementRawVector_measurable :
    Measurable (dyadicIncrementRawVector (ℓ := ℓ) j x) :=
  measurable_pi_iff.mpr (fun _ => dyadicIncrementFeature_measurable j x _)

end

section
variable {d ℓ : ℕ} {C : ModelConstants d} {θ : RegressionParameter d} (hθ : Admissible C θ) (j : ℕ)
    {x : Covariate d} (hx : x ∈ unitCube d) (v : incrementVariables (anchoredDimension d ℓ))
include hx hθ

theorem dyadicIncrementFeature_memLp_two :
    MemLp (dyadicIncrementFeature j x v) 2 (observationLaw θ) := by
  let := observationLaw_isProbability C θ hθ
  exact dyadicIncrementFeature_induction j v (fun f => MemLp (f x) 2 (observationLaw θ))
    (memLp_const _) (memLp_const _) (fun k _ => preconditionedPilotFeature_memLp_two hθ k hx)

/-- Original-law moment bound for every current/parent free coordinate;
the level-zero identity parent is covered by the same fixed constant. -/
theorem dyadicIncrementFeature_second_le :
    (∫ z, dyadicIncrementFeature j x v z ^ 2 ∂observationLaw θ) ≤
      preconditionedPilotMomentConstant C ℓ * dyadicPilotScale d j := by
  let := observationLaw_isProbability C θ hθ
  have hC := preconditionedPilotMomentConstant_pos C ℓ
  have hroot : 1 ≤ preconditionedPilotMomentConstant C ℓ := le_max_left _ _
  have hK : 1 ≤ dyadicPilotScale d j := by
    unfold dyadicPilotScale
    exact one_le_pow₀ (one_le_pow₀ (by norm_num))
  have hnon : 0 ≤ preconditionedPilotMomentConstant C ℓ * dyadicPilotScale d j :=
    mul_nonneg hC.le (dyadicPilotScale_pos d j).le
  apply dyadicIncrementFeature_induction j v
    (fun f => (∫ z, f x z ^ 2 ∂observationLaw θ) ≤ preconditionedPilotMomentConstant C ℓ * dyadicPilotScale d j)
  · simpa using hnon
  · simpa using mul_le_mul hroot hK (by norm_num) hC.le
  · intro k hk a
    exact (preconditionedPilotFeature_uniform_second_le hθ k hx a).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by norm_num) hk) d) hC.le)


theorem dyadicIncrementRawVector_second_le :
    (∫ z, ‖dyadicIncrementRawVector (ℓ := ℓ) j x z‖ ^ 2 ∂observationLaw θ) ≤
      Fintype.card (incrementVariables (anchoredDimension d ℓ)) *
        preconditionedPilotMomentConstant C ℓ * dyadicPilotScale d j := by
  let := observationLaw_isProbability C θ hθ
  apply (KernelMomentBounds.vector_second_le_sum_coordinates
    (dyadicIncrementRawVector_measurable j x) (fun _ => dyadicIncrementFeature_memLp_two hθ j hx _)).trans
  exact (Finset.sum_le_sum (fun a _ => dyadicIncrementFeature_second_le hθ j hx _)).trans_eq
    (by simp [mul_assoc])

end

section
variable {d ℓ : ℕ} (θ : RegressionParameter d) (j : ℕ) (x : Covariate d)

/-- The finite-coordinate current Gram and the two true vector moment families. -/
def dyadicFinPilotGram :
    Matrix (Fin (anchoredDimension d ℓ)) (Fin (anchoredDimension d ℓ)) ℝ :=
  anchoredFinReindex d ℓ (dyadicPreconditionedGram θ j x)

def dyadicFinPilotMoments :
    Bool → Fin (anchoredDimension d ℓ) → ℝ :=
  fun response i => preconditionedPilotPopulation θ j x
    (if response then Sum.inr (Sum.inr (anchoredFinIndex i))
      else Sum.inr (Sum.inl (anchoredFinIndex i)))

def dyadicIncrementPopulation :
    incrementVariables (anchoredDimension d ℓ) → ℝ :=
  incrementValuation (dyadicFinPilotGram θ j x)
    (if j = 0 then 1 else dyadicFinPilotGram θ (j - 1) x)
    (dyadicFinPilotMoments θ j x)
    (if j = 0 then 0 else dyadicFinPilotMoments θ (j - 1) x)

end

variable {d ℓ n : ℕ} {C : ModelConstants d} {θ : RegressionParameter d} (hθ : Admissible C θ) (j : ℕ)
    {x : Covariate d} (hx : x ∈ unitCube d)
include hθ

include hx in
/-- Original observation-law integration produces precisely the free-moment
population point, including the deterministic identity/zero root parent. -/
theorem dyadicIncrementFeature_integral (v : incrementVariables (anchoredDimension d ℓ)) :
    (∫ z, dyadicIncrementFeature j x v z ∂observationLaw θ) =
      dyadicIncrementPopulation θ j x v := by
  let := observationLaw_isProbability C θ hθ
  cases v with
  | inl v =>
    cases v with
    | inl v =>
      rcases v with ⟨i, t⟩
      simpa [dyadicIncrementFeature, dyadicIncrementPopulation, incrementValuation,
        RoughRegime.CombinedPolynomial.entryValuation, dyadicFinPilotGram,
        anchoredFinReindex, Matrix.reindexAlgEquiv, Matrix.reindex, anchoredFinIndex,
        preconditionedPilotPopulation] using
        preconditionedPilotPopulation_gram hθ j hx (anchoredFinIndex i) (anchoredFinIndex t)
    | inr v =>
      by_cases hj : j = 0
      · simp [dyadicIncrementFeature, dyadicIncrementPopulation, incrementValuation,
          RoughRegime.CombinedPolynomial.entryValuation, hj, Matrix.one_apply]
      · simpa [dyadicIncrementFeature, dyadicIncrementPopulation, incrementValuation,
          RoughRegime.CombinedPolynomial.entryValuation, dyadicFinPilotGram,
          anchoredFinReindex, Matrix.reindexAlgEquiv, Matrix.reindex, anchoredFinIndex, hj,
          preconditionedPilotPopulation] using
          preconditionedPilotPopulation_gram hθ (j - 1) hx
            (anchoredFinIndex v.2.1) (anchoredFinIndex v.2.2)
  | inr v =>
    rcases v with ⟨parent, response, i⟩
    cases parent <;> cases response <;> by_cases hj : j = 0
    all_goals simp [dyadicIncrementFeature, dyadicIncrementPopulation, incrementValuation,
      dyadicFinPilotMoments, hj, preconditionedPilotPopulation]

include hx in
theorem dyadicIncrementRawMean_eq_population :
    dyadicIncrementRawMean θ j x = fun a =>
      dyadicIncrementPopulation θ j x
        ((Fintype.equivFin (incrementVariables (anchoredDimension d ℓ))).symm a) := by
  funext a
  exact dyadicIncrementFeature_integral hθ j hx _

theorem dyadicFinPilotGram_eq_normalized (x : Covariate d) :
    dyadicFinPilotGram (ℓ := ℓ) θ j x =
      anchoredFinNormalizedGram (dyadicNormalizedAnchor j x) (dyadicNormalizedDensity θ j x) := by
  unfold dyadicFinPilotGram dyadicPreconditionedGram anchoredFinNormalizedGram
  rw [dyadicKnownGram_eq_normalized, dyadicPopulationGram_eq_normalized hθ]

include hx in
theorem dyadicFinPilotMoments_eq_normalized (t : Bool) (i : Fin (anchoredDimension d ℓ)) :
    dyadicFinPilotMoments θ j x t i =
      anchoredPreconditionedMoment (dyadicNormalizedAnchor j x) (dyadicNormalizedDensity θ j x)
        (if t then fun _ => 1 else θ.regression ∘ dyadicCellAffine j x) (anchoredFinIndex i) := by
  cases t
  · exact (by rw [preconditionedPilotPopulation_eq_sum hθ j hx]; simp only [localPilotRow, localPilotReplaceRow, dyadicPilotPopulation_response hθ j hx, dyadicKnownGram_eq_normalized, anchoredPreconditionedMoment, Matrix.mulVec, dotProduct, dyadicResponseMoment_eq_normalized hθ] : preconditionedPilotPopulation θ j x (Sum.inr (Sum.inl (anchoredFinIndex i))) = anchoredPreconditionedMoment (dyadicNormalizedAnchor j x) (dyadicNormalizedDensity θ j x) (θ.regression ∘ dyadicCellAffine j x) (anchoredFinIndex i))
  · exact (by rw [preconditionedPilotPopulation_eq_sum hθ j hx]; simp only [localPilotRow, localPilotReplaceRow, dyadicPilotPopulation_constant hθ, dyadicKnownGram_eq_normalized, anchoredPreconditionedMoment, Matrix.mulVec, dotProduct, dyadicConstantMoment_eq_normalized hθ] : preconditionedPilotPopulation θ j x (Sum.inr (Sum.inr (anchoredFinIndex i))) = anchoredPreconditionedMoment (dyadicNormalizedAnchor j x) (dyadicNormalizedDensity θ j x) (fun x => 1) (anchoredFinIndex i))

include hx in
theorem dyadicIncrementRawVector_sample_facts :
    iIndepFun (fun i z => dyadicIncrementRawVector (ℓ := ℓ) j x (z i)) (sampleLaw θ n) ∧
    (∀ i, Measurable (fun z : Fin n → Observation d => dyadicIncrementRawVector (ℓ := ℓ) j x (z i))) ∧
    (∀ i t, IdentDistrib
      (fun z => dyadicIncrementRawVector j x (z i))
      (fun z => dyadicIncrementRawVector (ℓ := ℓ) j x (z t)) (sampleLaw θ n) (sampleLaw θ n)) ∧
    (∀ i a, MemLp (fun z => dyadicIncrementRawVector (ℓ := ℓ) j x (z i) a)
      2 (sampleLaw θ n)) ∧
    (∀ i a, (∫ z, dyadicIncrementRawVector (ℓ := ℓ) j x (z i) a ∂sampleLaw θ n) =
      dyadicIncrementRawMean θ j x a) := by
  let := observationLaw_isProbability C θ hθ
  have hm := dyadicIncrementRawVector_measurable (ℓ := ℓ) j x
  have hp (i : Fin n) : MeasurePreserving (fun z => z i)
      (sampleLaw θ n) (observationLaw θ) := measurePreserving_eval _ i
  refine ⟨iIndepFun_pi (fun _ => hm.aemeasurable),
    fun i => hm.comp (measurable_pi_apply i), ?_, ?_, ?_⟩
  · intro i t
    have ht : IdentDistrib (fun z => z i)
        (fun z => z t) (sampleLaw θ n) (sampleLaw θ n) :=
      ⟨(hp i).aemeasurable, (hp t).aemeasurable, (hp i).map_eq.trans (hp t).map_eq.symm⟩
    exact ht.comp hm
  · intro i a
    exact (dyadicIncrementFeature_memLp_two hθ j hx _).comp_measurePreserving (hp i)
  · intro i a
    exact integral_comp_eval
      ((dyadicIncrementFeature_measurable j x
        ((Fintype.equivFin (incrementVariables (anchoredDimension d ℓ))).symm a)).aestronglyMeasurable)

include hx in
theorem dyadicIncrementRawVector_sample_second_le (i : Fin n) :
    (∫ z, ‖dyadicIncrementRawVector (ℓ := ℓ) j x (z i)‖ ^ 2 ∂sampleLaw θ n) ≤
      Fintype.card (incrementVariables (anchoredDimension d ℓ)) *
        preconditionedPilotMomentConstant C ℓ * dyadicPilotScale d j := by
  let := observationLaw_isProbability C θ hθ
  unfold sampleLaw
  rw [integral_comp_eval (μ := fun _ => observationLaw θ)
    (((dyadicIncrementRawVector_measurable j x).norm.pow_const 2).aestronglyMeasurable)]
  exact dyadicIncrementRawVector_second_le hθ j hx

end NearlyMinimax
