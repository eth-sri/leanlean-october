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
open scoped ComplexConjugate Real ContDiff

noncomputable section

namespace PolyaNeumann

variable {Ω : Set ℂ} {γ : ℝ → ℂ}

/-- A smooth real cutoff equal to `1` on a ball. -/
lemma exists_cutoff_one_on_ball R (hR : 0 < R) :
    ∃ χ : ℂ → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ ∀ z ∈ closedBall 0 R, χ z = 1 := by
  let b : ContDiffBump (0 : ℂ) := ⟨R, R + 1, hR, by linarith⟩
  exact ⟨b, b.contDiff, b.hasCompactSupport, fun z hz => b.one_of_mem_closedBall hz⟩

local notation "Φ0" => Icc 0

lemma intervalIntegrable_mul_comp_mul_deriv  (hK : LipschitzWith K γ) 
    (hh : ContinuousOn h (Φ0 (2 * π)))  (hF : Continuous F) :
    IntervalIntegrable (fun θ => h θ * F (γ θ) * deriv γ θ) volume 0 (2 * π) := by
  refine (show IntervalIntegrable (deriv γ) volume 0 (2 * π) by
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).mpr ?_
    exact Measure.integrableOn_of_bounded (M := K) measure_Ioc_lt_top.ne
      (measurable_deriv γ).aestronglyMeasurable
      (Eventually.of_forall fun θ => norm_deriv_le_of_lipschitz hK)).continuousOn_mul ?_
  rw [uIcc_of_le (by positivity)]
  exact hh.mul (hF.comp hK.continuous).continuousOn

/-- Orthogonality to smooth functions extends to continuous compactly supported functions. -/
lemma exists_continuous_comp_eq (hγ : IsBoundaryParam Ω γ) 
    (hg : ContinuousOn g (Φ0 (2 * π))) (hg0 : g 0 = g (2 * π)) :
    ∃ Ψ : ℂ → ℂ, Continuous Ψ ∧ HasCompactSupport Ψ ∧ ∀ θ ∈ Φ0 (2 * π), Ψ (γ θ) = g θ := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  set S := γ '' Φ0 (2 * π) with hS
  have hSc : IsCompact S := isCompact_Icc.image hK.continuous
  -- well-definedness on `S`
  choose! θof hθof using fun p (hp : p ∈ S) => hp
  set Ψ₀ : S → ℂ := fun p => g (θof p) with hΨ₀
  have hΨ₀q : ∀ θ hθ, Ψ₀ ⟨γ θ, mem_image_of_mem γ hθ⟩ = g θ := by
    intro θ hθ
    have hm := mem_image_of_mem γ hθ
    exact (show ∀ θ ∈ Φ0 (2 * π), ∀ θ' ∈ Φ0 (2 * π), γ θ = γ θ' → g θ = g θ' by
      have key : ∀ θ ∈ Φ0 (2 * π), θ < 2 * π → ∀ θ' ∈ Φ0 (2 * π),
          γ θ = γ θ' → g θ = g θ' := by
        intro θ hθ hlt θ' hθ' he
        rcases lt_or_eq_of_le hθ'.2 with h' | h'
        · rw [hγ.injOn ⟨hθ.1, hlt⟩ ⟨hθ'.1, h'⟩ he]
        · subst h'
          rw [show γ (2 * π) = γ 0 by simpa using hγ.periodic 0] at he
          rw [hγ.injOn ⟨hθ.1, hlt⟩ ⟨le_rfl, (show 0 < 2 * π by positivity)⟩ he, hg0]
      intro θ hθ θ' hθ' he
      rcases lt_or_eq_of_le hθ.2 with h | h
      · exact key θ hθ h θ' hθ' he
      · rcases lt_or_eq_of_le hθ'.2 with h' | h'
        · exact (key θ' hθ' h' θ hθ he.symm).symm
        · rw [h, h']) _ (hθof _ hm).1 _ hθ (hθof _ hm).2
  set q : Φ0 (2 * π) → S := fun θ => ⟨γ θ, mem_image_of_mem γ θ.2⟩ with hq
  have hqc : Continuous q := (hK.continuous.comp continuous_subtype_val).subtype_mk _
  obtain ⟨G, hG⟩ := ContinuousMap.exists_restrict_eq hSc.isClosed ⟨Ψ₀, (show Continuous Ψ₀ by
    rw [(hqc.isClosedMap.isQuotientMap hqc (by
      rintro ⟨p, θ, hθ, rfl⟩
      exact ⟨⟨θ, hθ⟩, rfl⟩)).continuous_iff, (funext fun θ => hΨ₀q θ θ.2 : Ψ₀ ∘ q = fun θ : Φ0 (2 * π) => g θ)]
    exact hg.comp_continuous continuous_subtype_val (fun θ => θ.2))⟩
  obtain ⟨R, hR0, hR⟩ : ∃ R, 0 < R ∧ S ⊆ closedBall 0 R := by
    obtain ⟨R, hR⟩ := hSc.isBounded.subset_closedBall 0
    exact ⟨max R 1, by positivity, hR.trans (closedBall_subset_closedBall (le_max_left _ _))⟩
  obtain ⟨χ, hχ, hχc, hχ1⟩ := exists_cutoff_one_on_ball R hR0
  refine ⟨fun z => (χ z : ℂ) * G z, (Complex.continuous_ofReal.comp hχ.continuous).mul
    G.continuous, (hχc.comp_left (g := fun x : ℝ => (x : ℂ)) Complex.ofReal_zero).mul_right,
    fun θ hθ => ?_⟩
  have hm := mem_image_of_mem γ hθ
  simp [hχ1 _ (hR hm), show G (γ θ) = Ψ₀ ⟨γ θ, hm⟩ by
    simpa using congrArg (fun F : C(S, ℂ) => F ⟨γ θ, hm⟩) hG]
  exact hΨ₀q θ hθ

/-- A continuous boundary density orthogonal to `φ ∘ γ · γ'` for every test function `φ`
vanishes. -/
theorem eq_zero_of_integral_comp_mul_deriv (hγ : IsBoundaryParam Ω γ)
     (hh : ContinuousOn h (Φ0 (2 * π)))
    (horth : ∀ φ : ℂ → ℂ, TestFunction univ φ →
      ∫ θ in 0..(2 * π), h θ * φ (γ θ) * deriv γ θ = 0) :
    ∀ θ ∈ Φ0 (2 * π), h θ = 0 := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  obtain ⟨c, hc, hspeed⟩ := hγ.const_speed
  have h2π : (0 : ℝ) < 2 * π := by positivity
  -- `h γ' = 0` a.e. on `(0, 2π)`
  have hae := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero (by
    exact ((show IntegrableOn (fun θ => h θ * deriv γ θ) (Ioc 0 (2 * π)) volume by
      have := intervalIntegrable_mul_comp_mul_deriv hK hh (F := fun _ => (1 : ℂ))
        continuous_const
      simp at this
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le h2π.le).mp this).mono_set Ioo_subset_Ioc_self).locallyIntegrableOn)
    (fun g hg hgc hgs => by
      obtain ⟨Ψ, hΨ, hΨc, hΨγ⟩ := exists_continuous_comp_eq hγ (g := fun θ => (g θ))
        (Complex.continuous_ofReal.comp hg.continuous).continuousOn (by
          have h0 := image_eq_zero_of_notMem_tsupport (fun h' => (hgs h').1.false)
          have h1 :=
            image_eq_zero_of_notMem_tsupport (fun h' => (hgs h').2.false)
          simp [h0, h1])
      have e : ∫ θ in 0..(2 * π), h θ * Ψ (γ θ) * deriv γ θ = 0 := by
        obtain ⟨Mh, hMh⟩ := isCompact_Icc.exists_bound_of_continuousOn hh
        have hMh0 : 0 ≤ Mh := (norm_nonneg _).trans (hMh 0 ⟨le_rfl, by positivity⟩)
        obtain ⟨R, hR0, hR⟩ : ∃ R, 0 < R ∧ ∀ θ ∈ Φ0 (2 * π), γ θ ∈ closedBall 0 R := by
          obtain ⟨R, hR⟩ := (isCompact_Icc.image hK.continuous).isBounded.subset_closedBall 0
          exact ⟨max R 1, by positivity, fun θ hθ =>
            closedBall_subset_closedBall (le_max_left _ _) (hR (mem_image_of_mem γ hθ))⟩
        obtain ⟨χ, hχ, hχc, hχ1⟩ := exists_cutoff_one_on_ball R hR0
        have hu := HasCompactSupport.uniformContinuous_of_continuous hΨc hΨ
        refine norm_le_zero_iff.mp (le_of_forall_pos_le_add fun ε hε => ?_)
        rw [zero_add]
        set C : ℝ := Mh * K * (2 * π) + 1 with hC
        have hCpos : 0 < C := by positivity
        obtain ⟨g, hg, hgΨ⟩ := hu.exists_contDiff_dist_le (div_pos hε hCpos)
        set φ : ℂ → ℂ := fun z => χ z * g z with hφ
        have hφt : TestFunction univ φ := by
          refine ⟨(Complex.ofRealCLM.contDiff.comp hχ).mul (hg.of_le (by exact_mod_cast le_top)), ?_,
            subset_univ _⟩
          exact (hχc.comp_left (g := fun x : ℝ => (x : ℂ)) Complex.ofReal_zero).mul_right
        have hφγ : ∀ θ ∈ Φ0 (2 * π), φ (γ θ) = g (γ θ) := fun θ hθ => by
          simp [hφ, hχ1 _ (hR θ hθ)]
        have hiΨ := intervalIntegrable_mul_comp_mul_deriv hK hh hΨ
        have hiφ := intervalIntegrable_mul_comp_mul_deriv hK hh hφt.1.continuous
        rw [show ∫ θ in 0..(2 * π), h θ * Ψ (γ θ) * deriv γ θ = ∫ θ in 0..(2 * π), (h θ * Ψ (γ θ) * deriv γ θ - h θ * φ (γ θ) * deriv γ θ) by
          rw [intervalIntegral.integral_sub hiΨ hiφ, horth φ hφt, sub_zero]]
        refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := Mh * (ε / C) * K)
          fun θ hθ => ?_).trans ?_
        · rw [uIoc_of_le (by positivity)] at hθ
          have hθ' := Ioc_subset_Icc_self hθ
          rw [← sub_mul, ← mul_sub, hφγ θ hθ', norm_mul, norm_mul]
          gcongr
          · exact hMh θ hθ'
          · rw [← dist_eq_norm, dist_comm]; exact (hgΨ _).le
          · exact norm_deriv_le_of_lipschitz hK
        · rw [sub_zero, abs_of_pos (by positivity)]
          calc _ = ε * (Mh * K * (2 * π) / C) := by ring
            _ ≤ ε * 1 := by
                gcongr
                rw [div_le_one hCpos, hC]; linarith
            _ = ε := mul_one ε
      rw [intervalIntegral.integral_of_le h2π.le] at e
      rw [← e, ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioc 0 (2 * π))]
      · refine setIntegral_congr_fun measurableSet_Ioc fun θ hθ => ?_
        simp [hΨγ θ (Ioc_subset_Icc_self hθ)]
        ring
      · intro θ hθ
        simp [image_eq_zero_of_notMem_tsupport (fun h' => hθ (Ioo_subset_Ioc_self (hgs h')))])
  -- `h = 0` a.e. on `(0, 2π)`
  -- by continuity, `h = 0` on `(0, 2π)`
  have hIoo : ∀ θ ∈ Ioo (0 : ℝ) (2 * π), h θ = 0 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨θ₀, hθ₀, hne⟩ := hcon
    have := ((hh.mono Ioo_subset_Icc_self).isOpen_inter_preimage isOpen_Ioo isOpen_compl_singleton).measure_eq_zero_iff (μ := volume) |>.mp (by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [show ∀ᵐ θ, θ ∈ Ioo 0 (2 * π) → h θ = 0 by
        filter_upwards [hae, hspeed] with θ h1 h2 hθ
        have hne : deriv γ θ ≠ 0 := by
          intro h0; rw [h0, norm_zero] at h2; exact hc.ne h2
        exact (mul_eq_zero.mp (h1 hθ)).resolve_right hne] with θ hθ hmem
      exact hmem.2 (hθ hmem.1))
    exact (this ▸ (⟨hθ₀, hne⟩) :
      θ₀ ∈ (∅ : Set ℝ))
  -- and on the closed interval
  exact fun θ hθ => (EqOn.of_subset_closure (s := Ioo 0 (2 * π)) hIoo hh continuousOn_const Ioo_subset_Icc_self (by rw [closure_Ioo h2π.ne])) hθ

end PolyaNeumann
