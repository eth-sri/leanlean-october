module

public import HypoellipticAleksandrov.Parabolic.TimeVelocityMultiIndexLeibniz
public import HypoellipticAleksandrov.Parabolic.ParabolicDerivativeIndex
public import Mathlib.Topology.Separation.Regular
public import HypoellipticAleksandrov.Parabolic.SmoothScalarWeakDerivativeFamily

/-!
# Coordinate derivative majorants on precompact neighborhoods

This file bounds a finite-order family of coordinate derivatives on the compact closure of one
common precompact neighborhood.
-/

@[expose] public section


namespace HypoellipticAleksandrov.Parabolic


variable {d M : ℕ}

private theorem continuousOn_coordinateIteratedFDeriv
     {U : Set (TimeVelocity d)}
    (hU : IsOpen U) (f : TimeVelocity d → ℝ) (hf : ContDiffOn ℝ M f U)
    (alpha : ParabolicDerivativeIndex d M) :
    ContinuousOn
      (TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1 f) U := by
  intro z hz
  have horder : alpha.1.order ≤ M :=
    (order_le_parabolicWeight alpha.1).trans alpha.2
  have hdiff  := hf.contDiffAt (hU.mem_nhds hz)
  have hiter := hdiff.iteratedFDeriv_right
    (m := 0) (i := alpha.1.coordinateList.length) (by simpa)
  exact ((contDiffAt_const (c := ContinuousMultilinearMap.apply ℝ _ _
    _)).clm_apply hiter).continuousAt.continuousWithinAt

/-- A compact subset of an open time--velocity set has one precompact open
neighborhood carrying nonnegative finite-order derivative majorants for an
arbitrary indexed scalar family. -/
theorem exists_precompactOpen_coordinateIteratedFDeriv_majorants
     {ι : Type*}
    {U K : Set (TimeVelocity d)}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (q : ι → TimeVelocity d → ℝ)
    (hq : ∀ i, ContDiffOn ℝ M (q i) U) :
    ∃ (V : Set (TimeVelocity d))
      (B : ι → ParabolicDerivativeIndex d M → ℝ),
      IsOpen V ∧
      K ⊆ V ∧
      closure V ⊆ U ∧
      IsCompact (closure V) ∧
      (∀ i alpha, 0 ≤ B i alpha) ∧
      ∀ i alpha z, z ∈ closure V →
        |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1 (q i) z| ≤
          B i alpha := by
  classical
  obtain ⟨V, hVopen, hKV, hVU, hVcompact⟩ :=
    exists_open_between_and_isCompact_closure hK hU hKU
  have hbound : ∀ (i : ι) (alpha : ParabolicDerivativeIndex d M),
      ∃ C : ℝ, ∀ z ∈ closure V,
        ‖TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1 (q i) z‖ ≤ C := by
    intro i alpha
    exact hVcompact.exists_bound_of_continuousOn
      ((continuousOn_coordinateIteratedFDeriv hU _ (hq i) alpha).mono hVU)
  choose C hC using hbound
  refine ⟨V, fun i alpha ↦ max 0 (C i alpha), hVopen, hKV, hVU, hVcompact, ?_, ?_⟩
  · simp
  simp_all

end HypoellipticAleksandrov.Parabolic
