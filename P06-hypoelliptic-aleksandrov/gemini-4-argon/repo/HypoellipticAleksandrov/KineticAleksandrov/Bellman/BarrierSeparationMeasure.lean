module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.BarrierSeparationFunctional
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Tactic
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.ContinuousMap.Compact

/-! # Riesz representation of the normalized positive separator -/

@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace HypoellipticAleksandrov.KineticAleksandrov

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]

/- A normalized positive continuous functional has a probability representing it. -/
theorem exists_bellman_subspace_probability (S : Submodule ℝ C(X, ℝ))
    (hno : Disjoint (bellmanPositiveCone (X := X)) (S : Set C(X, ℝ))) :
    ∃ mu : Measure X, IsProbabilityMeasure mu ∧
      ∀ f ∈ S, ∫ x, f x ∂mu = 0 := by
  obtain ⟨L, h1, hpos, hS⟩ : ∃ L : C(X, ℝ) →L[ℝ] ℝ,
      L 1 = 1 ∧ (∀ f : C(X, ℝ), (∀ x, 0 ≤ f x) → 0 ≤ L f) ∧
      ∀ f ∈ S, L f = 0 := by
    have hd : Disjoint (bellmanPositiveCone (X := X))
        (S.topologicalClosure : Set C(X, ℝ)) :=
      hno.closure_right bellmanPositiveCone_isOpen
    obtain ⟨l, u, hl, hu⟩ := geometric_hahn_banach_open bellmanPositiveCone_convex
      bellmanPositiveCone_isOpen S.topologicalClosure.convex hd
    have hu0 : u ≤ 0 := by simpa only [map_zero] using hu 0 S.topologicalClosure.zero_mem
    have hz : ∀ f ∈ S.topologicalClosure, l f = 0 := by
      intro f hf
      by_contra hn
      have hc := hu (((u - 1) / l f) • f) (S.topologicalClosure.smul_mem _ hf)
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hn] at hc
      linarith only [hc]
    let g := -l
    have hgp : ∀ f ∈ bellmanPositiveCone, 0 < g f := by
      intro f hf
      change 0 < -l f
      linarith only [hl f hf, hu0]
    have hg1 : 0 < g 1 := hgp 1 (fun _ => zero_lt_one)
    have hgn : ∀ f : C(X, ℝ), (∀ x, 0 ≤ f x) → 0 ≤ g f := by
      intro f hf
      by_contra hn
      have hneg := lt_of_not_ge hn
      let c := (g 1 + 1) / (-g f)
      have hc : 0 < c := div_pos (by linarith only [hg1]) (neg_pos.mpr hneg)
      have hp : 1 + c • f ∈ bellmanPositiveCone := by
        intro x
        change 0 < 1 + c * f x
        exact add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hc.le (hf x))
      have h := hgp (1 + c • f) hp
      rw [map_add, map_smul, smul_eq_mul] at h
      have he : c * g f = -(g 1 + 1) := by
        dsimp [c]
        field_simp [hneg.ne]
      rw [he] at h
      linarith only [h]
    refine ⟨(g 1)⁻¹ • g, ?_, ?_, ?_⟩
    · simp only [smul_apply, smul_eq_mul, inv_mul_cancel₀ hg1.ne']
    · intro f hf
      exact mul_nonneg (inv_nonneg.mpr hg1.le) (hgn f hf)
    · intro f hf
      have he := hz f (S.le_topologicalClosure hf)
      simp only [smul_apply, smul_eq_mul, g, neg_apply, he, neg_zero, mul_zero]
  obtain ⟨mu, hmu, ht⟩ : ∃ mu : Measure X, IsProbabilityMeasure mu ∧
      ∀ f : C(X, ℝ), ∫ x, f x ∂mu = L f := by
      let ell : C_c(X, ℝ) →ₚ[ℝ] ℝ :=
        { toFun := fun f => L f.toContinuousMap
          map_add' := fun f g => by
            change L (f.toContinuousMap + g.toContinuousMap) = _
            exact map_add L _ _
          map_smul' := fun c f => by
            change L (c • f.toContinuousMap) = _
            exact map_smul L _ _
          monotone' := fun f g hfg => by
            have hp := hpos (g.toContinuousMap - f.toContinuousMap)
              (fun x => sub_nonneg.mpr (hfg x))
            rw [map_sub] at hp
            exact sub_nonneg.mp hp }
      let mu := RealRMK.rieszMeasure ell
      have ht (f : C(X, ℝ)) : ∫ x, f x ∂mu = L f := by
        let fc : C_c(X, ℝ) := ⟨f, HasCompactSupport.of_compactSpace f⟩
        exact RealRMK.integral_rieszMeasure ell fc
      have hmass : mu.real univ = 1 := by
        simpa only [ContinuousMap.one_apply, integral_const, smul_eq_mul, mul_one] using (ht 1).trans h1
      exact ⟨mu, isProbabilityMeasure_iff_real.mpr hmass, ht⟩

    /- A continuous subspace avoiding strict positivity has an annihilating probability. -/
  exact ⟨mu, hmu, fun f hf => (ht f).trans (hS f hf)⟩

end HypoellipticAleksandrov.KineticAleksandrov
