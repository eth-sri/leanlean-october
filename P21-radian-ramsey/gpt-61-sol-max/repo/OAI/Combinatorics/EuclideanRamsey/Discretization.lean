/-
From openai/math (https://github.com/openai/math), commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, lean/OAI/Combinatorics/EuclideanRamsey/Discretization.lean;
licensed under the Apache License, Version 2.0 (see LICENSES/Apache-2.0.txt and NOTICE).
Modified: ported to the Lean module system for Lean v4.35.0-rc2 / Mathlib v4.35.0-rc2 (this
notice, a `module` header, `public import`, `@[expose] public section`); subsequently
refactored and proof-compressed while preserving the main results.
-/
module

public import OAI.Combinatorics.EuclideanRamsey.LatticeMoments

@[expose] public section

open scoped ContDiff

namespace OAI.EuclideanRamsey


noncomputable section




lemma compact_taylor_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x h : E,
      |f (x+h)-f x-fderiv ℝ f x h-
        (1/2:ℝ)*iteratedFDeriv ℝ 2 f x ![h,h]| ≤ K*‖h‖^3 := by
  obtain ⟨K,hK⟩ := (hf.continuous_iteratedFDeriv (m := 3) (by norm_cast)).bounded_above_of_compact_support
    (hfc.iteratedFDeriv 3)
  have hK0 := (norm_nonneg _).trans (hK 0)
  refine ⟨K,hK0,?_⟩
  intro x h
  have ht := map_add_eq_sum_add_integral_iteratedFDeriv (n := 2) (f := f) (x := x) (y := h)
    (fun t ht => (hf.of_le (by norm_cast)).contDiffAt)
  have hvec : (fun _ : Fin 2 => h) = ![h,h] := by ext i; fin_cases i <;> rfl
  simp [Finset.sum_range_succ,Nat.factorial,hvec] at ht
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := 1)
    (f := fun t : ℝ => (1-t)^2 * iteratedFDeriv ℝ 3 f (x+t • h) (fun _ => h))
    (C := K*‖h‖^3) (fun t ht' => by
      rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      have hm := (iteratedFDeriv ℝ 3 f (x+t • h)).le_opNorm (fun _ => h)
      simp at hm
      exact (mul_le_mul_of_nonneg_left (hm.trans
        (mul_le_mul_of_nonneg_right (hK _) (by positivity))) (sq_nonneg (1-t))).trans
        (mul_le_of_le_one_left (by positivity) (by
          have ht0 : 0 ≤ t := (show 0 < t by simpa using ht'.1).le
          have ht1 : t ≤ 1 := by simpa using ht'.2
          nlinarith)))
  simp only [Real.norm_eq_abs,sub_zero,abs_one] at hi
  rw [abs_le] at hi ⊢
  constructor <;> nlinarith [mul_nonneg hK0 (pow_nonneg (norm_nonneg h) 3)]



lemma bilinear_moment_contract {ι : Type*} {k : ℕ}
    (S : Finset ι) (q : ι → ℝ) (v : ι → (Fin k → ℝ))
    (L : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ) →L[ℝ] ℝ) :
    ∑ γ ∈ S,q γ*L (v γ) (v γ) =
      ∑ j,∑ l,(∑ γ ∈ S,q γ*v γ j*v γ l)*L (Pi.single j 1) (Pi.single l 1) := by
  classical
  let M : Matrix (Fin k) S ℝ := fun j γ => v γ j
  have h := bilinear_matrix_pushforward L M (Matrix.diagonal (fun γ : S => q γ))
  simp only [Matrix.mul_apply,Matrix.transpose_apply] at h
  simp only [← Finset.sum_coe_sort S]
  simpa [M,Matrix.diagonal_apply,mul_assoc,mul_comm,mul_left_comm] using h.symm

open scoped Pointwise Topology
open MeasureTheory Filter

abbrev realLattice (k : ℕ) := Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin k)))
def latticeSample {k : ℕ} (n : ℕ) (γ : Fin k → ℤ) : Fin k → ℝ := fun j => (γ j : ℝ)/n

lemma latticeSample_injective {k n : ℕ} (hn : n ≠ 0) :
    Function.Injective (@latticeSample k n) := by
  simp [Function.Injective, latticeSample, funext_iff, hn]

lemma latticeSample_mem_grid {k n : ℕ} (hn : n ≠ 0) (γ : Fin k → ℤ) :
    latticeSample n γ ∈ (n:ℝ)⁻¹ • (realLattice k : Set (Fin k → ℝ)) := by
  let : NeZero n := ⟨hn⟩
  rw [← Submodule.coe_pointwise_smul]
  apply BoxIntegral.unitPartition.mem_smul_span_iff.mpr
  intro j
  refine ⟨γ j,?_⟩
  simp [latticeSample,← mul_div_assoc,hn]

lemma lattice_tsum_eq_grid {k n : ℕ} (hn : n ≠ 0) (s : Set (Fin k → ℝ))
    (f : (Fin k → ℝ) → ℝ) (hf : Function.support f ⊆ s) :
    (∑' γ : Fin k → ℤ, f (latticeSample n γ)) =
      ∑' x : ↑(s ∩ (n:ℝ)⁻¹ • realLattice k), f x := by
  let e : {γ : Fin k → ℤ // latticeSample n γ ∈ s} ≃
      ↑(s ∩ (n:ℝ)⁻¹ • realLattice k) := Equiv.ofBijective
    (fun γ => ⟨latticeSample n γ,γ.property,latticeSample_mem_grid hn γ.val⟩) (by
      constructor
      · intro x y h
        grind [latticeSample_injective]
      · intro x
        let : NeZero n := ⟨hn⟩
        have hx := x.property.2
        simp only [← Submodule.coe_pointwise_smul] at hx
        choose γ hγ using BoxIntegral.unitPartition.mem_smul_span_iff.mp hx
        have he : latticeSample n γ = x := by ext; simp_all [latticeSample]
        exact ⟨⟨γ,he.symm ▸ x.property.1⟩,Subtype.ext he⟩)
  rw [← tsum_subtype_eq_of_support_subset (s := {γ | latticeSample n γ ∈ s})
    (f := fun γ => f (latticeSample n γ)) (fun γ hγ => hf hγ)]
  exact e.tsum_eq (fun x => f x)

theorem lattice_riemann {k : ℕ} {f : (Fin k → ℝ) → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    Tendsto (fun n : ℕ => (∑' γ : Fin k → ℤ, f (latticeSample n γ))/(n:ℝ)^k)
      atTop (𝓝 (∫ x, f x)) := by
  obtain ⟨R,hR,hfR⟩ := hfc.isCompact.isBounded.exists_pos_norm_lt
  let s := Metric.closedBall (0 : Fin k → ℝ) R
  have hs : Function.support f ⊆ s := by
    intro x hx
    simpa [s, Metric.mem_closedBall, dist_zero_right] using (hfR x (subset_tsupport f hx)).le
  have hfront : volume (frontier s) = 0 :=
    measure_mono_null Metric.frontier_closedBall_subset_sphere
      (volume.addHaar_sphere_of_ne_zero 0 hR.ne')
  have h := tendsto_tsum_div_pow_atTop_integral s f hf Metric.isBounded_closedBall
    measurableSet_closedBall hfront
  have hi : (∫ x in s,f x) = ∫ x,f x := by
    rw [← integral_indicator measurableSet_closedBall, Set.indicator_eq_self.mpr hs]
  simp [hi] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [lattice_tsum_eq_grid (by omega) s f hs]

lemma bounded_grid_finite {k n : ℕ} (hn : n ≠ 0) {s : Set (Fin k → ℝ)}
    (hs : Bornology.IsBounded s) :
    (s ∩ (n:ℝ)⁻¹ • (realLattice k : Set (Fin k → ℝ))).Finite := by
  rw [← Submodule.coe_pointwise_smul, ZSpan.smul _ (inv_ne_zero (by exact_mod_cast hn))]
  exact ZSpan.setFinite_inter _ hs

lemma latticeSample_finite_support {k n : ℕ} (hn : n ≠ 0)
    {f : (Fin k → ℝ) → ℝ} (hf : HasCompactSupport f) :
    Function.HasFiniteSupport (fun γ : Fin k → ℤ => f (latticeSample n γ)) := by
  apply ((bounded_grid_finite hn hf.isCompact.isBounded).preimage
    (latticeSample_injective hn).injOn).subset
  intro γ hγ
  exact ⟨subset_tsupport f hγ, latticeSample_mem_grid hn γ⟩

end

end OAI.EuclideanRamsey
