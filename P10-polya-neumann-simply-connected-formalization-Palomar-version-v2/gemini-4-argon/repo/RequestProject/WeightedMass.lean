module

public import RequestProject.Approximation

/-!
# Weighted masses (Lemma 10.11 for the mass form)

For uniformly bounded weights `ρ_n` on `Ω` converging almost everywhere to `1`, the weighted
masses `m_n[u,u] = ∫_Ω ρ_n |u|²` converge to `1` uniformly on the unit sphere of every
finite-dimensional subspace of `L²(Ω)` (`tendstoUniformlyOn_weightedMass`). This is the mass part of
Lemma 10.11 of the paper; the proof is the paper's: dominated convergence for the matrix entries
in a basis, then uniformity on bounded sets of a finite-dimensional space
(`tendstoUniformlyOn_sesq_of_basis`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace PolyaNeumann

variable {Ω : Set ℂ}

variable {C : ℝ}

/-- The weighted mass `m[u,u] = ∫_Ω ρ |u|²`. -/
def weightedMass (Ω : Set ℂ) (ρ : ℂ → ℝ) (u : L2 Ω) : ℝ :=
  ∫ w in Ω, ρ w * ‖(u : ℂ → ℂ) w‖ ^ 2

/-- Integrability of `ρ ⟨u, v⟩` for a bounded weight `ρ`. -/
local notation "Φ0" => L2 Ω

lemma integrable_weight_inner {ρ : ℂ → ℝ} 
    (hρm : AEStronglyMeasurable ρ (volume.restrict Ω))
    (hρb : ∀ᵐ w ∂(volume.restrict Ω), |ρ w| ≤ C) (u v : Φ0) :
    Integrable (fun w => (ρ w : ℂ) * inner ℂ ((u : ℂ → ℂ) w) ((v : ℂ → ℂ) w))
      (volume.restrict Ω) :=
  (L2.integrable_inner u v).bdd_mul (Complex.continuous_ofReal.comp_aestronglyMeasurable hρm)
    (hρb.mono fun w hw => by simpa [Complex.norm_real] using hw)

/-- The weighted sesquilinear form `(u, v) ↦ ∫_Ω ρ ⟨u, v⟩` on a submodule of `L²(Ω)`. -/
def weightedSesq (S : Submodule ℂ (Φ0)) {ρ : ℂ → ℝ} 
    (hρm : AEStronglyMeasurable ρ (volume.restrict Ω))
    (hρb : ∀ᵐ w ∂(volume.restrict Ω), |ρ w| ≤ C) : S →ₗ⋆[ℂ] S →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ)
    (fun u v => ∫ w in Ω, (ρ w : ℂ) *
      inner ℂ (((u : Φ0) : ℂ → ℂ) w) (((v : Φ0) : ℂ → ℂ) w))
    (fun u₁ u₂ v => by
      rw [← integral_add (integrable_weight_inner hρm hρb _ _)
        (integrable_weight_inner hρm hρb _ _)]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_add (u₁ : Φ0) (u₂ : Φ0)] with w hw
      rw [Submodule.coe_add, hw, Pi.add_apply, inner_add_left, mul_add])
    (fun c u v => by
      rw [smul_eq_mul, ← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_smul c (u : Φ0)] with w hw
      rw [Submodule.coe_smul, hw, Pi.smul_apply, inner_smul_left]
      simp only [starRingEnd_apply]
      ring)
    (fun u v₁ v₂ => by
      rw [← integral_add (integrable_weight_inner hρm hρb _ _)
        (integrable_weight_inner hρm hρb _ _)]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_add (v₁ : Φ0) (v₂ : Φ0)] with w hw
      rw [Submodule.coe_add, hw, Pi.add_apply, inner_add_right, mul_add])
    (fun c u v => by
      rw [smul_eq_mul, ← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_smul c (v : Φ0)] with w hw
      rw [Submodule.coe_smul, hw, Pi.smul_apply, inner_smul_right, RingHom.id_apply]
      ring)

lemma weightedSesq_apply (S : Submodule ℂ (Φ0)) {ρ : ℂ → ℝ} 
    (hρm : AEStronglyMeasurable ρ (volume.restrict Ω))
    (hρb : ∀ᵐ w ∂(volume.restrict Ω), |ρ w| ≤ C) u v :
    weightedSesq S hρm hρb u v = ∫ w in Ω, (ρ w : ℂ) *
      inner ℂ (((u : Φ0) : ℂ → ℂ) w) (((v : Φ0) : ℂ → ℂ) w) := rfl

lemma weightedSesq_self (S : Submodule ℂ (Φ0)) {ρ : ℂ → ℝ} 
    (hρm : AEStronglyMeasurable ρ (volume.restrict Ω))
    (hρb : ∀ᵐ w ∂(volume.restrict Ω), |ρ w| ≤ C) u :
    weightedSesq S hρm hρb u u = (weightedMass Ω ρ u : ℂ) := by
  rw [weightedSesq_apply, weightedMass, ← integral_complex_ofReal]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  simp only [inner_self_eq_norm_sq_to_K]
  rw [Complex.ofReal_mul, Complex.ofReal_pow]
  rfl

/-- Mass part of Lemma 10.11: for weights `ρ_n` on `Ω`, uniformly bounded and converging to `1`
almost everywhere, `∫_Ω ρ_n |u|² → 1` uniformly on the unit sphere of every finite-dimensional
subspace of `L²(Ω)`. -/
theorem tendstoUniformlyOn_weightedMass (ρ : ℕ → ℂ → ℝ) (C : ℝ)
    (hρm : ∀ n, AEStronglyMeasurable (ρ n) (volume.restrict Ω))
    (hρb : ∀ n, ∀ᵐ w ∂(volume.restrict Ω), |ρ n w| ≤ C)
    (hρt : ∀ᵐ w ∂(volume.restrict Ω), Tendsto (fun n => ρ n w) atTop (𝓝 1))
    (S : Submodule ℂ (Φ0)) (hS : FiniteDimensional ℂ S) :
    TendstoUniformlyOn (fun n u => weightedMass Ω (ρ n) u) (fun _ => 1) atTop
      ((S : Set (Φ0)) ∩ Metric.sphere 0 1) := by
  set b := Module.finBasis ℂ S
  set Bn : ℕ → S →ₗ⋆[ℂ] S →ₗ[ℂ] ℂ := fun n => weightedSesq S (hρm n) (hρb n)
  set B : S →ₗ⋆[ℂ] S →ₗ[ℂ] ℂ := innerₛₗ ℂ
  have hK : Bornology.IsBounded {u : S | ‖u‖ = 1} :=
    (Metric.isBounded_closedBall (x := 0) (r := 1)).subset fun u hu => by
      simp at hu
      simp [hu]
  have hU' := Complex.uniformContinuous_re.comp_tendstoUniformlyOn (tendstoUniformlyOn_sesq_of_basis b Bn B (by
    intro r s
    rw [show B (b r) (b s) = ∫ w in Ω, inner ℂ (((b r : S) : Φ0) w) (((b s : S) : Φ0) w) by
      simp [B, innerₛₗ_apply_apply, L2.inner_def]]
    refine tendsto_integral_of_dominated_convergence
      (fun w => C * ‖inner ℂ (((b r : S) : Φ0) w) (((b s : S) : Φ0) w)‖)
      (fun n => (integrable_weight_inner (hρm n) (hρb n) _ _).aestronglyMeasurable)
      ((L2.integrable_inner _ _).norm.const_mul C) (fun n => ?_) ?_
    · filter_upwards [hρb n] with w hw
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right hw (norm_nonneg _)
    · filter_upwards [hρt] with w hw
      simpa using (((Complex.continuous_ofReal.tendsto 1).comp hw).mul_const (inner ℂ (((b r : S) : Φ0) w) (((b s : S) : Φ0) w)))) hK)
  intro t ht
  filter_upwards [hU' t ht] with n hn
  rintro u ⟨huS, hu1⟩
  have h1 := hn ⟨u, huS⟩ (by simpa using hu1)
  simp only [Function.comp_apply, Bn, weightedSesq_self, Complex.ofReal_re, B,
    innerₛₗ_apply_apply, inner_self_eq_norm_sq_to_K] at h1
  rw [show ‖(⟨u, huS⟩ : S)‖ = 1 by simpa using hu1] at h1
  simpa using h1

end PolyaNeumann

end
