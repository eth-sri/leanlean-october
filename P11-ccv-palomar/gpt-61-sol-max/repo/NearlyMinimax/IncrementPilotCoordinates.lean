module

public import NearlyMinimax.DyadicPilotPointwise


@[expose] public section

/-! One fixed finite original-observation feature vector realizes every
anchor-dependent current/parent pilot input as a continuous linear image.
The deterministic root parent is realized by an explicit constant coordinate. -/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

abbrev DyadicGlobalDimension d ℓ j :=
  Fintype.card (PilotBasisIndex (Fintype.card (DyadicPilotLabelIndex d j)) d (2 * ℓ))

abbrev IncrementGlobalIndex d ℓ j :=
  Unit ⊕ (Fin (DyadicGlobalDimension d ℓ j) ⊕ Fin (DyadicGlobalDimension d ℓ (j - 1)))

section
variable {d ℓ : ℕ}

section
variable (j : ℕ)

def incrementGlobalFeature   (a : IncrementGlobalIndex d ℓ j)
    (z : Observation d)  :=
  match a with
  | Sum.inl _ => 1
  | Sum.inr (Sum.inl i) => pilotRawVector (ℓ := 2 * ℓ) (dyadicPilotLabel j) z i
  | Sum.inr (Sum.inr i) => pilotRawVector (ℓ := 2 * ℓ) (dyadicPilotLabel (j - 1)) z i

def incrementGlobalVector   z  :=
  fun a => incrementGlobalFeature j ((Fintype.equivFin (IncrementGlobalIndex d ℓ j)).symm a) z
end


def incrementGlobalMean  (θ : RegressionParameter d) (j : ℕ) :
    Fin (Fintype.card (IncrementGlobalIndex d ℓ j)) → ℝ :=
  fun a => ∫ z, incrementGlobalVector (ℓ := ℓ) j z a ∂observationLaw θ

section
variable (j : ℕ)

theorem incrementGlobalFeature_measurable  
    (a : IncrementGlobalIndex d ℓ j) : Measurable (incrementGlobalFeature j a) := by
  cases a with
  | inl _ => exact measurable_const
  | inr a =>
    cases a <;> exact pilotBasisFeature_measurable _ (dyadicPilotLabel_measurable _) _

theorem incrementGlobalVector_measurable   :
    Measurable (incrementGlobalVector (d := d) (ℓ := ℓ) j) :=
  measurable_pi_iff.mpr (fun _ => incrementGlobalFeature_measurable j _)
end


theorem incrementGlobalFeature_memLp_two  C
    θ (hθ : Admissible C θ) j
    (a : IncrementGlobalIndex d ℓ j) : MemLp (incrementGlobalFeature j a) 2 (observationLaw θ) := by
  let := observationLaw_isProbability C θ hθ
  cases a with
  | inl _ => exact memLp_const _
  | inr a =>
    cases a <;> exact pilotBasisFeature_memLp_two C θ hθ _ (dyadicPilotLabel_measurable _) _

section
variable (j : ℕ)

def incrementGlobalCurrent   :
    (Fin (Fintype.card (IncrementGlobalIndex d ℓ j)) → ℝ) →L[ℝ]
      (Fin (DyadicGlobalDimension d ℓ j) → ℝ) :=
  ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj
    ((Fintype.equivFin (IncrementGlobalIndex d ℓ j)) (Sum.inr (Sum.inl i))))

def incrementGlobalParent   :
    (Fin (Fintype.card (IncrementGlobalIndex d ℓ j)) → ℝ) →L[ℝ]
      (Fin (DyadicGlobalDimension d ℓ (j - 1)) → ℝ) :=
  ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj
    ((Fintype.equivFin (IncrementGlobalIndex d ℓ j)) (Sum.inr (Sum.inr i))))

def incrementGlobalOne   :
    (Fin (Fintype.card (IncrementGlobalIndex d ℓ j)) → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj ((Fintype.equivFin (IncrementGlobalIndex d ℓ j)) (Sum.inl ()))

section
variable (z : Observation d)

@[simp] theorem incrementGlobalCurrent_raw    :
    incrementGlobalCurrent (ℓ := ℓ) j (incrementGlobalVector j z) =
      pilotRawVector (ℓ := 2 * ℓ) (dyadicPilotLabel j) z := by
  
  simp [incrementGlobalCurrent, incrementGlobalVector, incrementGlobalFeature]

@[simp] theorem incrementGlobalParent_raw    :
    incrementGlobalParent (ℓ := ℓ) j (incrementGlobalVector j z) =
      pilotRawVector (ℓ := 2 * ℓ) (dyadicPilotLabel (j - 1)) z := by
  
  simp [incrementGlobalParent, incrementGlobalVector, incrementGlobalFeature]

@[simp] theorem incrementGlobalOne_raw    :
    incrementGlobalOne (ℓ := ℓ) j (incrementGlobalVector j z) = 1 := by
  simp [incrementGlobalOne, incrementGlobalVector, incrementGlobalFeature]
end


section
variable (x : Covariate d)
include x

section
variable (a : LocalPilotIndex d ℓ)
include a

def preconditionedPilotCoordinate   
     : (Fin (DyadicGlobalDimension d ℓ j) → ℝ) →L[ℝ] ℝ :=
  ∑ β : AnchoredIndex d ℓ, (dyadicKnownGram j x)⁻¹ (localPilotRow a) β •
    dyadicPilotCoordinate j x (localPilotReplaceRow a β)

@[simp] theorem preconditionedPilotCoordinate_raw   
     z :
    preconditionedPilotCoordinate j x a (pilotRawVector (dyadicPilotLabel j) z) =
      preconditionedPilotFeature j x a z := by
  simp [preconditionedPilotCoordinate, preconditionedPilotFeature, smul_eq_mul,
    dyadicPilotCoordinate_raw_apply]
end


def incrementPilotFreeCoordinate   
    (a : incrementVariables (anchoredDimension d ℓ))  :=
  match a with
  | Sum.inl (Sum.inl it) =>
    (preconditionedPilotCoordinate j x (Sum.inl (anchoredFinIndex it.1, anchoredFinIndex it.2))).comp
      (incrementGlobalCurrent j)
  | Sum.inl (Sum.inr it) =>
    if j = 0 then (if it.2.1 = it.2.2 then incrementGlobalOne j else 0) else
      (preconditionedPilotCoordinate (j - 1) x (Sum.inl (anchoredFinIndex it.2.1, anchoredFinIndex it.2.2))).comp
        (incrementGlobalParent j)
  | Sum.inr pri =>
    if pri.1 && (j == 0) then 0 else
      if pri.1 then
        (preconditionedPilotCoordinate (j - 1) x
          (if pri.2.1 then Sum.inr (Sum.inr (anchoredFinIndex pri.2.2))
            else Sum.inr (Sum.inl (anchoredFinIndex pri.2.2)))).comp (incrementGlobalParent j)
      else
        (preconditionedPilotCoordinate j x
          (if pri.2.1 then Sum.inr (Sum.inr (anchoredFinIndex pri.2.2))
            else Sum.inr (Sum.inl (anchoredFinIndex pri.2.2)))).comp (incrementGlobalCurrent j)

def incrementPilotCoordinate    :
    (Fin (Fintype.card (IncrementGlobalIndex d ℓ j)) → ℝ) →L[ℝ]
      (Fin (Fintype.card (incrementVariables (anchoredDimension d ℓ))) → ℝ) :=
  ContinuousLinearMap.pi (fun a => incrementPilotFreeCoordinate j x
    ((Fintype.equivFin (incrementVariables (anchoredDimension d ℓ))).symm a))

theorem incrementPilotFreeCoordinate_raw   
    (a : incrementVariables (anchoredDimension d ℓ)) z :
    incrementPilotFreeCoordinate j x a (incrementGlobalVector j z) = dyadicIncrementFeature j x a z := by
  cases a with
  | inl a =>
    cases a with
    | inl a =>
      
      simp [incrementPilotFreeCoordinate, dyadicIncrementFeature]
    | inr a =>
      by_cases hj : j = 0
      · by_cases hit : a.2.1 = a.2.2 <;> simp [incrementPilotFreeCoordinate, dyadicIncrementFeature, hj, hit]
      · simp [incrementPilotFreeCoordinate, dyadicIncrementFeature, hj]
  | inr a =>
    rcases a with ⟨parent, response, i⟩
    cases parent <;> cases response <;> by_cases hj : j = 0
    all_goals simp [incrementPilotFreeCoordinate, dyadicIncrementFeature, hj]

@[simp] theorem incrementPilotCoordinate_raw   
    z :
    incrementPilotCoordinate j x (incrementGlobalVector j z) = dyadicIncrementRawVector (ℓ := ℓ) j x z := by
  funext a
  exact incrementPilotFreeCoordinate_raw j x _ z
end

end


/-- Actual original-law population integration commutes with the exact
global-coordinate map. This is the common mean needed by field covariance. -/
theorem incrementPilotCoordinate_mean  (C : ModelConstants d)
    θ (hθ : Admissible C θ) j x :
    incrementPilotCoordinate (ℓ := ℓ) j x (incrementGlobalMean θ j) = dyadicIncrementRawMean θ j x := by
  let := observationLaw_isProbability C θ hθ
  have hlp := KernelMomentBounds.vector_memLp_two (incrementGlobalVector (ℓ := ℓ) j)
    (incrementGlobalVector_measurable j) (fun a => incrementGlobalFeature_memLp_two C θ hθ j _)
  have hi := hlp.integrable (by norm_num)
  have hm : (∫ z, incrementGlobalVector (ℓ := ℓ) j z ∂observationLaw θ) = incrementGlobalMean θ j := by
    funext a
    exact ((ContinuousLinearMap.proj a :
      (Fin (Fintype.card (IncrementGlobalIndex d ℓ j)) → ℝ) →L[ℝ] ℝ).integral_comp_comm hi).symm
  rw [← hm, ← (incrementPilotCoordinate (ℓ := ℓ) j x).integral_comp_comm hi]
  
  funext a
  simpa only [ContinuousLinearMap.proj_apply, incrementPilotCoordinate_raw,
    dyadicIncrementRawMean] using ((ContinuousLinearMap.proj a :
    (Fin (Fintype.card (incrementVariables (anchoredDimension d ℓ))) → ℝ) →L[ℝ] ℝ).integral_comp_comm
    ((incrementPilotCoordinate (ℓ := ℓ) j x).integrable_comp hi)).symm
end


theorem incrementGlobalVector_sample_facts {d ℓ n } C
    θ (hθ : Admissible C θ) j :
    iIndepFun (fun i z => incrementGlobalVector (ℓ := ℓ) j (z i)) (sampleLaw θ n) ∧
    (∀ i , Measurable (fun z : Fin n → Observation d => incrementGlobalVector (ℓ := ℓ) j (z i))) ∧
    (∀ i t , IdentDistrib
      (fun z  => incrementGlobalVector (ℓ := ℓ) j (z i))
      (fun z  => incrementGlobalVector (ℓ := ℓ) j (z t)) (sampleLaw θ n) (sampleLaw θ n)) ∧
    (∀ i a, MemLp (fun z  => incrementGlobalVector (ℓ := ℓ) j (z i) a)
      2 (sampleLaw θ n)) ∧
    (∀ i a, (∫ z : Fin n → Observation d, incrementGlobalVector (ℓ := ℓ) j (z i) a ∂sampleLaw θ n) =
      incrementGlobalMean θ j a) := by
  let := observationLaw_isProbability C θ hθ
  have hm := incrementGlobalVector_measurable (d := d) (ℓ := ℓ) j
  have hp (i : Fin n) : MeasurePreserving (fun z : Fin n → Observation d => z i)
      (sampleLaw θ n) (observationLaw θ) := measurePreserving_eval _ i
  refine ⟨iIndepFun_pi (fun _ : Fin n => hm.aemeasurable),
    fun i => hm.comp (measurable_pi_apply i), ?_, ?_, ?_⟩
  · intro i t
    have ht : IdentDistrib (fun z : Fin n → Observation d => z i)
        (fun z : Fin n → Observation d => z t) (sampleLaw θ n) (sampleLaw θ n) :=
      ⟨(hp i).aemeasurable, (hp t).aemeasurable, (hp i).map_eq.trans (hp t).map_eq.symm⟩
    exact ht.comp hm
  · intro i a
    exact (incrementGlobalFeature_memLp_two C θ hθ j _).comp_measurePreserving (hp i)
  · intro i a
    exact integral_comp_eval (μ := fun _ : Fin n => observationLaw θ) (i := i)
      ((incrementGlobalFeature_measurable j
        ((Fintype.equivFin (IncrementGlobalIndex d ℓ j)).symm a)).aestronglyMeasurable)

end NearlyMinimax
