module

public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.FieldTransform.LogarithmicOriginExpansion
public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.LogarithmicStripDecayAndInversion

@[expose] public section

/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

noncomputable section
open scoped Classical ContDiff Topology
open Filter MeasureTheory

namespace DedekindZetaZeroFree.LargeSieve.Vendor

private theorem exists_posSideSupport (h : ℝ → ℂ) (hhc : HasCompactSupport h) :
    ∃ b : ℝ, 0 < b ∧ PositiveSideSupport b h := by
  obtain ⟨K, hK, hK0⟩ := exists_compact_iff_hasCompactSupport.mpr hhc
  obtain ⟨b, hb⟩ := hK.bddAbove
  refine ⟨max b 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun x hx => hK0 x ?_⟩
  intro hxK
  exact absurd (hb hxK) (not_le.mpr (lt_of_le_of_lt (le_max_left _ _) hx))

section

variable (D : ℝ) (r : ℕ) (h : ℝ → ℂ) (hD : 0 < D) (hr : 1 ≤ r) (hh : ContDiff ℝ ∞ h)
    (hhc : HasCompactSupport h)

include hD hr hh hhc in
private theorem fieldTransform_logMellinPhysical (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    LogMellinPhysical (fieldTransform D r h) δ (originPolynomial D r h) := by
  obtain ⟨b, hb, hb0⟩ := exists_posSideSupport h hhc
  refine ⟨hδ, fieldTransform_contDiffOn D r h hD hr hh hhc, ?_, ?_⟩
  · intro j n
    obtain ⟨C, hC, _, hinf⟩ :=
      fieldTransform_euler_two_ended_bound D r h hD hr hh hhc j n δ hδ
    exact ⟨C, hC.le, hinf⟩
  · intro j
    obtain ⟨N, C, hC, hbound⟩ :=
      fieldTransform_origin_remainder_uniform_bound D r b δ j hD hr hb hδ hδ1
    have hS := S_nonneg b hb N h hh
    refine ⟨C * S b N h, mul_nonneg hC.le hS, fun x hx hx1 => ?_⟩
    exact hbound h hh hhc hb0 x hx hx1

include hD hr hh hhc in
private theorem B_differentiableAt_of_lt_one {δ : ℝ} (hδ1 : δ < 1)
    (s : ℂ) (hs : -δ < s.re) (hs0 : s ≠ 0) :
    DifferentiableAt ℂ (B D r h) s := by
  have hs1 : -1 < s.re := lt_trans (by linarith) hs
  refine (A_div_analyticOnNhd D r h hD hr hh hhc s ⟨hs1, hs0⟩).differentiableAt
    |>.congr_of_eventuallyEq ?_
  filter_upwards [(((isOpen_lt continuous_const Complex.continuous_re).inter isOpen_ne).mem_nhds
    ⟨hs1, hs0⟩)] with s' hs'
  exact B_eq_A_div D r h hD hr hh hhc s' hs'.1 hs'.2

end

private theorem smooth_euler {f : ℝ → ℂ} (hf : ContDiffOn ℝ ∞ f (Set.Ioi 0))
    (j : ℕ) : ContDiffOn ℝ ∞ (EulerIter j f) (Set.Ioi 0) := by apply @LogLocalizedJets.LogLocalizedEulerJets.euler_smooth <;> assumption

private theorem euler_sq {f : ℝ → ℂ} (hf : ContDiffOn ℝ ∞ f (Set.Ioi 0))
    (j : ℕ) : ∀ x : ℝ, 0 < x →
      EulerIter j (fun y => f (y ^ 2)) x = (2 : ℂ) ^ j * EulerIter j f (x ^ 2) := by apply @DedekindZetaZeroFree.LargeSieve.SquareScalingAndOriginExpansion.eulerIter_comp_sq <;> assumption

private theorem euler_congr_pos {f g : ℝ → ℂ} (hfg : ∀ x, 0 < x → f x = g x)
    (j : ℕ) : ∀ x, 0 < x → EulerIter j f x = EulerIter j g x := by
  induction j with
  | zero => exact hfg
  | succ j ih =>
    intro x hx
    have heq : EulerIter j f =ᶠ[𝓝 x] EulerIter j g := by
      filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
      exact ih y hy
    rw [EulerIter_succ_of_pos _ _ _ hx, EulerIter_succ_of_pos _ _ _ hx, heq.deriv_eq]

private alias smooth_log_poly := DedekindZetaZeroFree.LargeSieve.SquareScalingAndOriginExpansion.contDiffOn_eval_log

private theorem physical_sq {f : ℝ → ℂ} {δ : ℝ} {P : Polynomial ℂ}
    (hf : LogMellinPhysical f δ P) :
    LogMellinPhysical (fun x : ℝ => f (x ^ 2)) (2 * δ)
      (P.comp (Polynomial.C (2 : ℂ) * Polynomial.X)) := by
  refine ⟨by linarith [hf.delta_pos], ?_, ?_, ?_⟩
  · exact hf.contDiffOn.comp (((contDiff_id (𝕜 := ℝ) (E := ℝ)).pow 2).contDiffOn)
      (fun x hx => by simpa using pow_pos hx 2)
  · intro j n
    obtain ⟨C, hC, hb⟩ := hf.rapid_decay j n
    refine ⟨(2 : ℝ) ^ j * C, by positivity, fun x hx => ?_⟩
    have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
    have hx2 : 1 ≤ x ^ 2 := one_le_pow₀ hx
    rw [euler_sq hf.contDiffOn j x hx0, norm_mul, norm_pow]
    norm_num only [Complex.norm_ofNat]
    have hp : Real.rpow (x ^ 2) (-(n : ℝ)) ≤ Real.rpow x (-(n : ℝ)) := by
      exact ((congrArg (fun z => Real.rpow z (-(n : ℝ))) (Real.rpow_two x).symm).trans
        (Real.rpow_mul hx0.le 2 (-(n : ℝ))).symm).le.trans (Real.rpow_le_rpow_of_exponent_le hx (by nlinarith))
    calc (2 : ℝ) ^ j * ‖EulerIter j f (x ^ 2)‖
        ≤ (2 : ℝ) ^ j * (C * Real.rpow (x ^ 2) (-(n : ℝ))) :=
          mul_le_mul_of_nonneg_left (hb _ hx2) (by positivity)
      _ ≤ (2 : ℝ) ^ j * (C * Real.rpow x (-(n : ℝ))) := by gcongr
      _ = ((2 : ℝ) ^ j * C) * Real.rpow x (-(n : ℝ)) := by ring
  · intro j
    obtain ⟨C, hC, hb⟩ := hf.origin_remainder j
    refine ⟨(2 : ℝ) ^ j * C, by positivity, fun x hx hx1 => ?_⟩
    have heq : ∀ y : ℝ, 0 < y →
        f (y ^ 2) - (P.comp (Polynomial.C (2 : ℂ) * Polynomial.X)).eval (Real.log y : ℂ) =
          (fun z => f z - P.eval (Real.log z : ℂ)) (y ^ 2) := by
      intro y hy
      simp only [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X, Real.log_pow, Complex.ofReal_mul, Complex.ofReal_natCast]
      norm_num
    rw [euler_congr_pos heq j x hx,
      euler_sq (hf.contDiffOn.sub (smooth_log_poly P)) j x hx, norm_mul, norm_pow]
    norm_num only [Complex.norm_ofNat]
    have hx2 : x ^ 2 ≤ 1 := by nlinarith
    have hp : Real.rpow (x ^ 2) δ = Real.rpow x (2 * δ) := by
      exact (congrArg (fun z => Real.rpow z δ) (Real.rpow_two x).symm).trans
        (Real.rpow_mul hx.le 2 δ).symm
    calc (2 : ℝ) ^ j * ‖EulerIter j (fun z => f z - P.eval (Real.log z : ℂ)) (x ^ 2)‖
        ≤ (2 : ℝ) ^ j * (C * Real.rpow (x ^ 2) δ) :=
          mul_le_mul_of_nonneg_left (hb _ (pow_pos hx 2) hx2) (by positivity)
      _ = ((2 : ℝ) ^ j * C) * Real.rpow x (2 * δ) := by rw [hp]; ring

end DedekindZetaZeroFree.LargeSieve.Vendor

namespace DedekindZetaZeroFree.LargeSieve.Vendor.LogMellinAdmissible

theorem comp_sq {f : ℝ → ℂ} {δ : ℝ} {P : Polynomial ℂ} {H : ℂ → ℂ}
    (hf : DedekindZetaZeroFree.LargeSieve.Vendor.LogMellinAdmissible f δ P H) :
    DedekindZetaZeroFree.LargeSieve.Vendor.LogMellinAdmissible (fun x : ℝ => f (x ^ 2)) (2 * δ)
      (P.comp (Polynomial.C (2 : ℂ) * Polynomial.X))
      (fun s : ℂ => (1 / 2 : ℂ) * H (s / 2)) := by
  have hp := physical_sq hf.physical
  have ha := logMellinContinuation_admissible hp
  have hre : ∀ s : ℂ, (s / 2).re = s.re / 2 := by
    intro s
    rw [Complex.div_re]
    norm_num [Complex.normSq]
    ring
  have hm : ∀ s : ℂ, 0 < s.re →
      (1 / 2 : ℂ) * H (s / 2) = mellin (fun x : ℝ => f (x ^ 2)) s := by
    intro s hs
    have hs2 : 0 < (s / 2).re := by rw [hre]; linarith
    rw [hf.eq_mellin _ hs2]
    have he := mellin_comp_rpow f s 2
    simp only [Real.rpow_two] at he
    simpa using he.symm
  have hd : ∀ s : ℂ, -(2 * δ) < s.re → s ≠ 0 →
      DifferentiableAt ℂ (fun z : ℂ => (1 / 2 : ℂ) * H (z / 2)) s := by
    intro s hs hs0
    have hne : s / 2 ≠ 0 := div_ne_zero hs0 (by norm_num)
    exact (differentiableAt_const _).mul
      ((hf.differentiableAt _ (by rw [hre]; linarith) hne).comp s (by fun_prop))
  have heq :=
    fun s hs hs0 => logMellinContinuation_unique hp _ hm hd s hs hs0
  refine ⟨hp, hm, ?_, ?_⟩
  · obtain ⟨A, hA, hAH⟩ := ha.holomorphic_remainder
    exact ⟨A, hA, fun s hs hs0 => by rw [heq s hs hs0, hAH s hs hs0]⟩
  · intro u v hu huv N
    obtain ⟨C, hC, hb⟩ := ha.rapid_vertical_decay u v hu huv N
    refine ⟨C, hC, fun σ t hσ hσv ht => ?_⟩
    have hs : -(2 * δ) < ((σ : ℂ) + (t : ℂ) * Complex.I).re := by
      simpa using lt_of_lt_of_le hu hσ
    have hs0 : ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
      intro hz
      have hti : ((σ : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
      rw [hz] at hti
      have ht0 : t = 0 := by exact hti.symm
      rw [ht0, abs_zero] at ht
      linarith
    rw [heq _ hs hs0]
    exact hb σ t hσ hσv ht

end DedekindZetaZeroFree.LargeSieve.Vendor.LogMellinAdmissible

namespace DedekindZetaZeroFree.LargeSieve

theorem fieldTransform_logMellinAdmissible
    (D : ℝ) (r : ℕ) (h : ℝ → ℂ)
    (hD : 0 < D) (hr : 1 ≤ r) (hh : ContDiff ℝ ∞ h)
    (hhc : HasCompactSupport h) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    Vendor.LogMellinAdmissible (fieldTransform D r h) δ
      (originPolynomial D r h) (B D r h) := by
  have hphys := Vendor.fieldTransform_logMellinPhysical D r h hD hr hh hhc δ hδ hδ1
  have hadm := Vendor.logMellinContinuation_admissible hphys
  have hM :=
    fun s hs => (mellin_fieldTransform_eq_B D r h hD hr hh hhc s hs).symm
  have hEq :=
    fun s hs hs0 => Vendor.logMellinContinuation_unique hphys (B D r h) hM (fun s hs hs0 => Vendor.B_differentiableAt_of_lt_one D r h hD hr hh hhc hδ1 s hs hs0) s hs hs0
  refine ⟨hphys, hM, ?_, ?_⟩
  · obtain ⟨A, hAdiff, hAeq⟩ := hadm.holomorphic_remainder
    exact ⟨A, hAdiff, fun s hs hs0 => by rw [hEq s hs hs0, hAeq s hs hs0]⟩
  · intro u v hu huv N
    obtain ⟨C, hC, hbound⟩ := hadm.rapid_vertical_decay u v hu huv N
    refine ⟨C, hC, fun σ t hσ hσv ht => ?_⟩
    have hσre : -δ < ((σ : ℂ) + (t : ℂ) * Complex.I).re := by
      simpa using lt_of_lt_of_le hu hσ
    have him : ((σ : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
    have hs0 : ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
      intro hcon
      have ht0 : t = 0 := by rw [hcon] at him; exact him.symm
      rw [ht0] at ht
      simp only [abs_zero] at ht
      exact absurd ht (by norm_num)
    rw [hEq _ hσre hs0]
    exact hbound σ t hσ hσv ht

theorem fieldTransform_comp_sq_logMellinAdmissible
    (D : ℝ) (r : ℕ) (h : ℝ → ℂ)
    (hD : 0 < D) (hr : 1 ≤ r) (hh : ContDiff ℝ ∞ h)
    (hhc : HasCompactSupport h) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    Vendor.LogMellinAdmissible (fun x : ℝ => fieldTransform D r h (x ^ 2)) (2 * δ)
      ((originPolynomial D r h).comp (Polynomial.C (2 : ℂ) * Polynomial.X))
      (fun s : ℂ => (1 / 2 : ℂ) * B D r h (s / 2)) := Vendor.LogMellinAdmissible.comp_sq
    (fieldTransform_logMellinAdmissible D r h hD hr hh hhc δ hδ hδ1)

end DedekindZetaZeroFree.LargeSieve

end
