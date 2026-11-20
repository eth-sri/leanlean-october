module

public import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
public import Mathlib.Analysis.Complex.Tietze
public import RequestProject.ReconBasic

/-!
# Boundary densities orthogonal to all smooth functions

If `h` is continuous on `[0, 2π]` and `∫₀^{2π} h φ(γ) γ' = 0` for every smooth compactly supported
`φ`, then `h = 0` on `[0, 2π]` (`eq_zero_of_integral_comp_mul_deriv`).

The proof approximates continuous functions uniformly by smooth ones, and represents every
continuous closed function of the parameter as `Ψ ∘ γ` (Tietze extension through the quotient
map `[0, 2π] → ∂Ω`).
-/

@[expose] public section

open MeasureTheory Set Filter Metric
open scoped ComplexConjugate Real

noncomputable section

namespace PolyaNeumann

variable {Ω : Set ℂ} {γ : ℝ → ℂ}

/-- A compact smooth cutoff equal to one on an open neighbourhood of a bounded set. -/
lemma exists_cutoff_one_bounded {S : Set ℂ} (hS : Bornology.IsBounded S) :
    ∃ (χ : ℂ → ℂ) (U : Set ℂ), TestFunction univ χ ∧ IsOpen U ∧ S ⊆ U ∧ EqOn χ 1 U := by
  obtain ⟨R, hR⟩ := hS.subset_ball (0 : ℂ)
  let b : ContDiffBump (0 : ℂ) := ⟨max R 1, max R 1 + 1, by positivity, by linarith⟩
  refine ⟨fun z => (b z : ℂ), ball 0 b.rIn, ⟨Complex.ofRealCLM.contDiff.comp b.contDiff,
    b.hasCompactSupport.comp_left Complex.ofReal_zero, subset_univ _⟩, isOpen_ball,
    hR.trans (ball_subset_ball (le_max_left _ _)), ?_⟩
  intro z hz
  simp [b.one_of_mem_closedBall (ball_subset_closedBall hz)]

lemma exists_smooth_test_eqOn_bounded {S : Set ℂ} (hS : Bornology.IsBounded S) {f : ℂ → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : ∃ ψ, TestFunction univ ψ ∧ EqOn ψ f S := by
  obtain ⟨χ, U, hχ, _, hU, hχ1⟩ := exists_cutoff_one_bounded hS
  exact ⟨fun z => χ z * f z, ⟨hχ.1.mul hf, hχ.2.1.mul_right, subset_univ _⟩,
    fun z hz => by simp [hχ1 (hU hz)]⟩

section

variable {K : NNReal} (hK : LipschitzWith K γ) {h : ℝ → ℂ} (hh : ContinuousOn h (Icc 0 (2 * π)))
include K hK h hh

lemma intervalIntegrable_mul_comp_mul_deriv  {F : ℂ → ℂ} (hF : Continuous F) :
    IntervalIntegrable (fun θ => h θ * F (γ θ) * deriv γ θ) volume 0 (2 * π) := by
  refine (intervalIntegrable_lipschitz_deriv hK 0 (2 * π)).continuousOn_mul ?_
  rw [uIcc_of_le (by positivity)]
  exact hh.mul (hF.comp hK.continuous).continuousOn

/-- Orthogonality to smooth functions extends to continuous compactly supported functions. -/
lemma integral_comp_mul_deriv_eq_zero_of_continuous 
    (horth : ∀ φ : ℂ → ℂ, TestFunction univ φ →
      ∫ θ in (0 : ℝ)..(2 * π), h θ * φ (γ θ) * deriv γ θ = 0)
    {Ψ : ℂ → ℂ} (hΨ : Continuous Ψ) (hΨc : HasCompactSupport Ψ) :
    ∫ θ in (0 : ℝ)..(2 * π), h θ * Ψ (γ θ) * deriv γ θ = 0 := by
  obtain ⟨Mh, hMh⟩ := isCompact_Icc.exists_bound_of_continuousOn hh
  have hMh0 := (norm_nonneg _).trans (hMh 0 ⟨le_rfl, by positivity⟩)
  have hu := HasCompactSupport.uniformContinuous_of_continuous hΨc hΨ
  refine norm_le_zero_iff.mp (le_of_forall_pos_le_add fun ε hε => ?_)
  rw [zero_add]
  set C : ℝ := Mh * K * (2 * π) + 1 with hC
  have hCpos : 0 < C := by positivity
  obtain ⟨g, hg, hgΨ⟩ := hu.exists_contDiff_dist_le (div_pos hε hCpos)
  obtain ⟨φ, hφt, hφ⟩ := exists_smooth_test_eqOn_bounded
    (isCompact_Icc.image hK.continuous).isBounded (hg.of_le (by rfl))
  have e := horth φ hφt
  have hiΨ := intervalIntegrable_mul_comp_mul_deriv hK hh hΨ
  have hiφ := intervalIntegrable_mul_comp_mul_deriv hK hh hφt.1.continuous
  have hdiff : ∫ θ in (0 : ℝ)..(2 * π), h θ * Ψ (γ θ) * deriv γ θ =
      ∫ θ in (0 : ℝ)..(2 * π), (h θ * Ψ (γ θ) * deriv γ θ - h θ * φ (γ θ) * deriv γ θ) := by
    simp_all
  rw [hdiff]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := Mh * (ε / C) * K)
    fun θ hθ => ?_).trans ?_
  · rw [uIoc_of_le (by positivity)] at hθ
    have hθ' := Ioc_subset_Icc_self hθ
    rw [← sub_mul, ← mul_sub, hφ (mem_image_of_mem γ hθ'), norm_mul, norm_mul]
    gcongr
    tauto
    · rw [← dist_eq_norm, dist_comm]; grind
    · exact norm_deriv_le_of_lipschitz hK
  · rw [sub_zero, abs_of_pos (by positivity)]
    calc Mh * (ε / C) * K * (2 * π) = ε * (Mh * K * (2 * π) / C) := by ring
      _ ≤ ε * 1 := by
          gcongr
          rw [div_le_one hCpos]; linarith
      _ = ε := mul_one ε

end

/-- A continuous closed function of the parameter is `Ψ ∘ γ` for a continuous compactly
supported `Ψ` on `ℂ`. -/
lemma exists_continuous_comp_eq (hγ : IsBoundaryParam Ω γ) {g : ℝ → ℂ}
    (hg : ContinuousOn g (Icc 0 (2 * π))) (hg0 : g 0 = g (2 * π)) :
    ∃ Ψ : ℂ → ℂ, Continuous Ψ ∧ HasCompactSupport Ψ ∧ ∀ θ ∈ Icc 0 (2 * π), Ψ (γ θ) = g θ := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  have hT : 0 < 2 * π := Real.two_pi_pos
  let I := Icc (0 : ℝ) (2 * π)
  let S := γ '' I
  have hSc : IsCompact S := isCompact_Icc.image hK.continuous
  let q : C(I, S) := ⟨fun t => ⟨γ t, mem_image_of_mem γ t.2⟩,
    (hK.continuous.comp continuous_subtype_val).subtype_mk _⟩
  have hq : Topology.IsQuotientMap q := q.continuous.isClosedMap.isQuotientMap q.continuous (by
    rintro ⟨z, t, ht, rfl⟩
    exact ⟨⟨t, ht⟩, rfl⟩)
  let gI : C(I, ℂ) := ⟨fun t => g t, hg.comp_continuous continuous_subtype_val Subtype.property⟩
  have hγ0 : γ (2 * π) = γ 0 := by simpa using hγ.periodic 0
  have hfib : Function.FactorsThrough gI q := by
    let ρ (t : I) : ℝ := if t.val = 2 * π then 0 else t.val
    have hρ (t : I) : ρ t ∈ Ico 0 (2 * π) ∧ γ (ρ t) = γ t ∧ g (ρ t) = g t := by
      by_cases h : t.val = 2 * π
      · simp [ρ, h, hT, hγ0, hg0]
      · exact ⟨by simpa [ρ, h] using ⟨t.2.1, lt_of_le_of_ne t.2.2 h⟩,
          by simp [ρ, h], by simp [ρ, h]⟩
    intro t u h
    have e : γ t = γ u := congrArg Subtype.val h
    have htu := hγ.injOn (hρ t).1 (hρ u).1 ((hρ t).2.1.trans (e.trans (hρ u).2.1.symm))
    exact (hρ t).2.2.symm.trans ((congrArg g htu).trans (hρ u).2.2)
  let G₀ := hq.lift gI hfib
  obtain ⟨G, hG⟩ := ContinuousMap.exists_restrict_eq hSc.isClosed G₀
  obtain ⟨χ, U, hχ, _, hU, hχ1⟩ := exists_cutoff_one_bounded hSc.isBounded
  refine ⟨fun z => χ z * G z, hχ.1.continuous.mul G.continuous, hχ.2.1.mul_right, fun θ hθ => ?_⟩
  have h := congrArg (fun H : C(S, ℂ) => H (q ⟨θ, hθ⟩)) hG
  have hh := congrArg (fun H : C(I, ℂ) => H ⟨θ, hθ⟩) (hq.lift_comp gI hfib)
  change G (γ θ) = G₀ (q ⟨θ, hθ⟩) at h
  change G₀ (q ⟨θ, hθ⟩) = g θ at hh
  change χ (γ θ) * G (γ θ) = _
  rw [hχ1 (hU (mem_image_of_mem γ hθ)), Pi.one_apply, one_mul, h, hh]

/-- A continuous boundary density orthogonal to `φ ∘ γ · γ'` for every test function `φ`
vanishes. -/
theorem eq_zero_of_integral_comp_mul_deriv (hγ : IsBoundaryParam Ω γ)
    {h : ℝ → ℂ} (hh : ContinuousOn h (Icc 0 (2 * π)))
    (horth : ∀ φ : ℂ → ℂ, TestFunction univ φ →
      ∫ θ in (0 : ℝ)..(2 * π), h θ * φ (γ θ) * deriv γ θ = 0) :
    ∀ θ ∈ Icc 0 (2 * π), h θ = 0 := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  obtain ⟨c, hc, hspeed⟩ := hγ.const_speed
  have h2π : (0 : ℝ) < 2 * π := by positivity
  -- `h γ' = 0` a.e. on `(0, 2π)`
  have hloc : LocallyIntegrableOn (fun θ => h θ * deriv γ θ) (Ioo 0 (2 * π)) volume := by
    have hi : IntegrableOn (fun θ => h θ * deriv γ θ) (Ioc 0 (2 * π)) volume := by
      have := intervalIntegrable_mul_comp_mul_deriv hK hh (F := fun _ => (1 : ℂ))
        continuous_const
      simp   at this
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le h2π.le).mp this
    exact (hi.mono_set Ioo_subset_Ioc_self).locallyIntegrableOn
  have hae := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc
    (fun g hg hgc hgs => by
      obtain ⟨Ψ, hΨ, hΨc, hΨγ⟩ := exists_continuous_comp_eq hγ (g := fun θ => (g θ : ℂ))
        (Complex.continuous_ofReal.comp hg.continuous).continuousOn (by
          have h0 := image_eq_zero_of_notMem_tsupport (fun h' => (hgs h').1.false)
          have h1 :=
            image_eq_zero_of_notMem_tsupport (fun h' => (hgs h').2.false)
          simp_all)
      have e := integral_comp_mul_deriv_eq_zero_of_continuous hK hh horth hΨ hΨc
      rw [intervalIntegral.integral_of_le h2π.le] at e
      rw [← e, ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioc 0 (2 * π))]
      · refine setIntegral_congr_fun measurableSet_Ioc fun θ hθ => ?_
        simp  [hΨγ θ (Ioc_subset_Icc_self hθ)]
        ring
      · intro θ hθ
        have := fun h' => hθ (Ioo_subset_Ioc_self (hgs h'))
        simp [image_eq_zero_of_notMem_tsupport this])
  -- `h = 0` a.e. on `(0, 2π)`
  have hae' : ∀ᵐ θ, θ ∈ Ioo 0 (2 * π) → h θ = 0 := by
    filter_upwards [hae, hspeed] with x; aesop
  -- by continuity, `h = 0` on `(0, 2π)`
  have hIoo : ∀ θ ∈ Ioo (0 : ℝ) (2 * π), h θ = 0 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨θ₀, hθ₀, hne⟩ := hcon
    have hopen : IsOpen (Ioo (0 : ℝ) (2 * π) ∩ h ⁻¹' {0}ᶜ) :=
      (hh.mono Ioo_subset_Icc_self).isOpen_inter_preimage isOpen_Ioo isOpen_compl_singleton
    have hzero : volume (Ioo (0 : ℝ) (2 * π) ∩ h ⁻¹' {0}ᶜ) = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      grind
    have := hopen.measure_eq_zero_iff (μ := volume) |>.mp hzero
    exact (this ▸ (show θ₀ ∈ Ioo (0 : ℝ) (2 * π) ∩ h ⁻¹' {0}ᶜ from ⟨hθ₀, hne⟩) :
      θ₀ ∈ (∅ : Set ℝ))
  -- and on the closed interval
  have heq :=
    EqOn.of_subset_closure (s := Ioo 0 (2 * π)) hIoo hh continuousOn_const
      Ioo_subset_Icc_self (by simp)
  assumption

end PolyaNeumann
