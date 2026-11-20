module

public import RequestProject.CircleAnalysisNotation

public import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
public import Mathlib.Analysis.Complex.Tietze
public import RequestProject.ReconBasic
public import RequestProject.PlanarNotation

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

open scoped ContDiff

namespace PolyaNeumann

variable {Ω : Set ℂ} {γ : ℝ → ℂ}

/-- A smooth real cutoff equal to `1` on a ball. -/
lemma exists_cutoff_one_on_ball (R : ℝ) (hR : 0 < R) :
    ∃ χ : ℂ → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ ∀ z ∈ closedBall (0 : ℂ) R, χ z = 1 := by
  let b : ContDiffBump (0 : ℂ) := ⟨R, R + 1, hR, by linarith⟩
  exact ⟨b, b.contDiff, b.hasCompactSupport, fun z hz => b.one_of_mem_closedBall hz⟩

lemma intervalIntegrable_mul_comp_mul_deriv {K : NNReal} (hK : LipschitzWith K γ) {h : ℝ → ℂ}
    (hh : ContinuousOn h angleInterval) {F : ℂ → ℂ} (hF : Continuous F) :
    IntervalIntegrable (fun θ => h θ * F (γ θ) * deriv γ θ) volume 0 anglePeriod := by
  have hd : IntervalIntegrable (deriv γ) volume 0 anglePeriod := by
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).mpr ?_
    exact Measure.integrableOn_of_bounded  measure_Ioc_lt_top.ne
      (by fun_prop)
      (Eventually.of_forall fun θ => norm_deriv_le_of_lipschitz hK)
  refine hd.continuousOn_mul ?_
  rw [uIcc_of_le (by positivity)]
  exact hh.mul (hF.comp hK.continuous).continuousOn

/-- Orthogonality to smooth functions extends to continuous compactly supported functions. -/
lemma integral_comp_mul_deriv_eq_zero_of_continuous {K : NNReal} (hK : LipschitzWith K γ)
    {h : ℝ → ℂ} (hh : ContinuousOn h angleInterval)
    (horth : ∀ φ : ℂ → ℂ, TestFunction univ φ →
      ∫ₚ θ, h θ * φ (γ θ) * deriv γ θ = 0)
    {Ψ : ℂ → ℂ} (hΨ : Continuous Ψ) (hΨc : HasCompactSupport Ψ) :
    ∫ₚ θ, h θ * Ψ (γ θ) * deriv γ θ = 0 := by
  obtain ⟨Mh, hMh⟩ := isCompact_Icc.exists_bound_of_continuousOn hh
  have hMh0  := (norm_nonneg _).trans (hMh 0 ⟨le_rfl, by positivity⟩)
  obtain ⟨R, hR0, hR⟩ : ∃ R, 0 < R ∧ ∀ θ ∈ angleInterval, γ θ ∈ closedBall 0 R := by
    obtain ⟨R, hR⟩ := (isCompact_Icc.image hK.continuous).isBounded.subset_closedBall 0
    exact ⟨max R 1, by positivity, fun θ hθ =>
      closedBall_subset_closedBall (le_max_left _ _) (hR (mem_image_of_mem γ hθ))⟩
  obtain ⟨χ, hχ, hχc, hχ1⟩ := exists_cutoff_one_on_ball R hR0
  
  refine norm_le_zero_iff.mp (le_of_forall_pos_le_add fun ε hε => ?_)
  rw [zero_add]
  set C  := Mh * K * anglePeriod + 1 
  have hCpos : 0 < C := by positivity
  obtain ⟨g, hg, hgΨ⟩ := (HasCompactSupport.uniformContinuous_of_continuous hΨc hΨ).exists_contDiff_dist_le (div_pos hε hCpos)
  set φ  := fun z => (χ z) * g z with hφ
  have hφt : TestFunction univ φ := by
    refine ⟨(Complex.ofRealCLM.contDiff.comp hχ).mul (hg.of_le (by exact_mod_cast le_top)), ?_,
      subset_univ _⟩
    exact (hχc.comp_left  Complex.ofReal_zero).mul_right
  
  have hφγ : ∀ θ ∈ angleInterval, φ (γ θ) = g (γ θ) := fun θ hθ => by
    simp [*]
  
  
  have hdiff : ∫ θ in 0..anglePeriod, h θ * Ψ (γ θ) * deriv γ θ =
      ∫ θ in 0..anglePeriod, (h θ * Ψ (γ θ) * deriv γ θ - h θ * φ (γ θ) * deriv γ θ) := by
    rw [intervalIntegral.integral_sub (intervalIntegrable_mul_comp_mul_deriv hK hh hΨ) (intervalIntegrable_mul_comp_mul_deriv hK hh hφt.1.continuous), (horth φ hφt), sub_zero]
  rw [hdiff]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := Mh * (ε / C) * K)
    fun θ hθ => ?_).trans ?_
  · rw [uIoc_of_le (by positivity)] at hθ
    have hθ'  := Ioc_subset_Icc_self hθ
    rw [← sub_mul, ← mul_sub, hφγ θ hθ', norm_mul, norm_mul]
    gcongr
    · exact hMh θ hθ'
    · rw [← dist_eq_norm, dist_comm]; exact (hgΨ _).le
    · exact norm_deriv_le_of_lipschitz hK
  · rw [sub_zero, abs_of_pos (by positivity)]
    calc _ = ε * (Mh * K * anglePeriod / C) := by ring
      _ ≤ ε * 1 := by
          bound
      _ = ε := mul_one ε

/-- A continuous closed function of the parameter is `Ψ ∘ γ` for a continuous compactly
supported `Ψ` on `ℂ`. -/
lemma exists_continuous_comp_eq (hγ : IsBoundaryParam Ω γ) {g : ℝ → ℂ}
    (hg : ContinuousOn g angleInterval) (hg0 : g 0 = g anglePeriod) :
    ∃ Ψ : ℂ → ℂ, Continuous Ψ ∧ HasCompactSupport Ψ ∧ ∀ θ ∈ angleInterval, Ψ (γ θ) = g θ := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  
  set S  := γ '' angleInterval 
  have hSc : IsCompact S := isCompact_Icc.image hK.continuous
  -- well-definedness on `S`
  have hwd : ∀ θ ∈ angleInterval, ∀ θ' ∈ angleInterval, γ θ = γ θ' → g θ = g θ' := by
    have hend := hγ.periodic.eq
    have key : ∀ θ ∈ angleInterval, θ < anglePeriod → ∀ θ' ∈ angleInterval,
        γ θ = γ θ' → g θ = g θ' := by
      intro θ hθ hlt θ' hθ' he
      rcases lt_or_eq_of_le hθ'.2 with h' | h'
      · rw [hγ.injOn ⟨hθ.1, hlt⟩ ⟨hθ'.1, h'⟩ he]
      · subst h'
        rw [hend] at he
        rw [hγ.injOn ⟨hθ.1, hlt⟩ ⟨le_rfl, (by positivity)⟩ he, hg0]
    grind
  choose! θof hθof using fun p (hp : p ∈ S) => hp
  set Ψ₀ : S → ℂ := fun p => g (θof p) 
  have hΨ₀q : ∀ θ (hθ : θ ∈ angleInterval), Ψ₀ ⟨γ θ, mem_image_of_mem γ hθ⟩ = g θ := by
    grind
  set q : angleInterval → S := fun θ => ⟨γ θ, mem_image_of_mem γ θ.2⟩ 
  have hqc : Continuous q := (hK.continuous.comp continuous_subtype_val).subtype_mk _
  
  
  have hΨ₀c : Continuous Ψ₀ := by
    rw [(hqc.isClosedMap.isQuotientMap hqc (by
      rintro ⟨p, θ, hθ, rfl⟩
      exact ⟨⟨θ, hθ⟩, rfl⟩)).continuous_iff]
    have : Ψ₀ ∘ q = fun θ : angleInterval => g θ := funext fun θ => hΨ₀q θ θ.2
    rw [this]
    exact hg.comp_continuous continuous_subtype_val (fun θ => θ.2)
  obtain ⟨G, hG⟩ := ContinuousMap.exists_restrict_eq hSc.isClosed ⟨Ψ₀, hΨ₀c⟩
  obtain ⟨R, hR0, hR⟩ : ∃ R, 0 < R ∧ S ⊆ closedBall 0 R := by
    obtain ⟨R, hR⟩ := hSc.isBounded.subset_closedBall 0
    exact ⟨max R 1, by positivity, hR.trans (closedBall_subset_closedBall (le_max_left _ _))⟩
  obtain ⟨χ, hχ, hχc, hχ1⟩ := exists_cutoff_one_on_ball R hR0
  refine ⟨fun z => (χ z) * G z, (by fun_prop), (hχc.comp_left  Complex.ofReal_zero).mul_right,
    fun θ hθ => ?_⟩
  have hm  := mem_image_of_mem γ hθ
  have hGθ : G (γ θ) = Ψ₀ ⟨γ θ, hm⟩ := by
    have := congrArg (fun F : C(S, ℂ) => F ⟨γ θ, hm⟩) hG
    exact this
  simp [hχ1 _ (hR hm), Complex.ofReal_one, hGθ]
  exact hΨ₀q θ hθ

/-- A continuous boundary density orthogonal to `φ ∘ γ · γ'` for every test function `φ`
vanishes. -/
theorem eq_zero_of_integral_comp_mul_deriv (hγ : IsBoundaryParam Ω γ)
    {h : ℝ → ℂ} (hh : ContinuousOn h angleInterval)
    (horth : ∀ φ : ℂ → ℂ, TestFunction univ φ →
      ∫ₚ θ, h θ * φ (γ θ) * deriv γ θ = 0) :
    ∀ θ ∈ angleInterval, h θ = 0 := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  obtain ⟨c, hc, hspeed⟩ := hγ.const_speed
  have h2π : 0 < anglePeriod := by positivity
  -- `h γ' = 0` a.e. on `(0, 2π)`
  
  have hae := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero (by
      have hi : IntegrableOn (fun θ => h θ * deriv γ θ) angleIoc volume := by
        have := intervalIntegrable_mul_comp_mul_deriv hK hh (F := fun _ => (1 : ℂ))
          continuous_const
        simp at this
        exact (intervalIntegrable_iff_integrableOn_Ioc_of_le h2π.le).mp this
      exact (hi.mono_set Ioo_subset_Ioc_self).locallyIntegrableOn)
    (fun g hg hgc hgs => by
      obtain ⟨Ψ, hΨ, hΨc, hΨγ⟩ := exists_continuous_comp_eq hγ 
        (Complex.continuous_ofReal.comp hg.continuous).continuousOn (by
          have h0  := image_eq_zero_of_notMem_tsupport (fun h' => (hgs h').1.false)
          have h1  :=
            image_eq_zero_of_notMem_tsupport (fun h' => (hgs h').2.false)
          simp [*])
      have e := integral_comp_mul_deriv_eq_zero_of_continuous hK hh horth hΨ hΨc
      rw [intervalIntegral.integral_of_le h2π.le] at e
      rw [← e, ← setIntegral_eq_integral_of_forall_compl_eq_zero ]
      · refine setIntegral_congr_fun measurableSet_Ioc fun θ hθ => ?_
        simp [hΨγ θ (Ioc_subset_Icc_self hθ)]
        ring
      · intro θ hθ
        have  := fun h' => hθ (Ioo_subset_Ioc_self (hgs h'))
        simp [image_eq_zero_of_notMem_tsupport this])
  -- `h = 0` a.e. on `(0, 2π)`
  have hae' : ∀ᵐ θ, θ ∈ angleInterior → h θ = 0 := by
    filter_upwards [hae, hspeed] with θ h1 h2 hθ
    have hne : deriv γ θ ≠ 0 := by
      aesop
    grind
  -- by continuity, `h = 0` on `(0, 2π)`
  have hIoo : ∀ θ ∈ angleInterior, h θ = 0 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨θ₀, hθ₀, hne⟩ := hcon
    
    
    have := ((hh.mono Ioo_subset_Icc_self).isOpen_inter_preimage isOpen_Ioo isOpen_compl_singleton).measure_eq_zero_iff (μ := volume) |>.mp (by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [hae'] with θ hθ hmem
      exact hmem.2 (hθ hmem.1))
    exact (this ▸ (show θ₀ ∈ angleInterior ∩ h ⁻¹' {0}ᶜ from ⟨hθ₀, hne⟩) :
      θ₀ ∈ ∅)
  -- and on the closed interval
  have heq  :=
    EqOn.of_subset_closure  hIoo hh continuousOn_const
      Ioo_subset_Icc_self (by simp)
  assumption

end PolyaNeumann
