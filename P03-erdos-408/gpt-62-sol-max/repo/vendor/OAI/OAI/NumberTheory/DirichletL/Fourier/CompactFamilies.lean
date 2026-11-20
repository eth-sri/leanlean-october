module

public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical FourierTransform ContDiff
open MeasureTheory Filter Set
namespace SevenEighths.CompactProfileFamily
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem section_deriv_smooth (F : E → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) :
    ContDiff ℝ ∞ (fun p : E × ℝ => deriv (F p.1) p.2) := by
  have hFp : ContDiff ℝ ∞
      (Function.uncurry (fun p : E × ℝ => F p.1)) :=
    hF.comp (contDiff_fst.fst.prodMk contDiff_snd)
  have hd := hFp.fderiv contDiff_snd (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)
  simpa only [deriv] using hd.clm_apply (contDiff_const (c := (1 : ℝ)))

theorem section_iteratedDeriv_smooth (F : E → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (j : ℕ) :
    ContDiff ℝ ∞ (fun p : E × ℝ => iteratedDeriv j (F p.1) p.2) := by
  induction j with
  | zero => simpa only [iteratedDeriv_zero, Function.uncurry_def] using hF
  | succ j ih =>
    simpa only [iteratedDeriv_succ] using
      section_deriv_smooth (fun σ => iteratedDeriv j (F σ)) ih

theorem tsupport_iteratedDeriv_subset (f : ℝ → ℂ) (j : ℕ) :
    tsupport (iteratedDeriv j f) ⊆ tsupport f := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [iteratedDeriv_succ]
    exact tsupport_deriv_subset.trans ih

theorem compact_family_deriv_integrable (F : E → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (σ : E) (j : ℕ) :
    Integrable (iteratedDeriv j (F σ)) := by
  have hs : ContDiff ℝ ∞ (F σ) := hF.comp (contDiff_const.prodMk contDiff_id)
  have hc : HasCompactSupport (iteratedDeriv j (F σ)) := by
    apply HasCompactSupport.of_support_subset_isCompact hK
    exact (subset_tsupport _).trans ((tsupport_iteratedDeriv_subset (F σ) j).trans
      (closure_minimal (hsupp σ) hK.isClosed))
  exact (hs.continuous_iteratedDeriv j (by simp)).integrable_of_hasCompactSupport hc

theorem compact_family_deriv_L1_bound (F : E → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set E) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ J, (∫ u : ℝ, ‖iteratedDeriv j (F σ) u‖) ≤ C := by
  have hc := (section_iteratedDeriv_smooth F hF j).continuous.norm
  obtain ⟨M, hM⟩ := (hJ.prod hK).bddAbove_image hc.continuousOn
  let C : ℝ := (|M| + 1) * (volume.real K + 1)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro σ hσ
  have hbound : ∀ u ∈ K, ‖iteratedDeriv j (F σ) u‖ ≤ |M| + 1 := by
    intro u hu
    exact (hM (Set.mem_image_of_mem _ (show (σ, u) ∈ J ×ˢ K from ⟨hσ, hu⟩))).trans (by linarith [le_abs_self M])
  have hs : Function.support (iteratedDeriv j (F σ)) ⊆ K :=
    (subset_tsupport _).trans ((tsupport_iteratedDeriv_subset (F σ) j).trans
      (closure_minimal (hsupp σ) hK.isClosed))
  have hzero : ∀ u, u ∉ K → ‖iteratedDeriv j (F σ) u‖ = 0 := by
    intro u hu
    have hz : iteratedDeriv j (F σ) u = 0 := by
      by_contra hn
      exact hu (hs hn)
    simp [hz]
  have hi := norm_setIntegral_le_of_norm_le_const («μ» := volume) (f := fun u => ‖iteratedDeriv j (F σ) u‖)
    hK.measure_lt_top (C := |M| + 1) (fun u hu => by simpa using hbound u hu)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero] at hi
  rw [Real.norm_of_nonneg (integral_nonneg (fun u => norm_nonneg _))] at hi
  exact hi.trans (by dsimp [C]; nlinarith [abs_nonneg M])

/-- A bound on the integral of the derivative gives the homogeneous Fourier weight. -/
lemma fourier_power_le {f : ℝ → ℂ} {j : ℕ} (w : ℝ) (hs : ContDiff ℝ ∞ f)
    (hf : ∀ k, Integrable (iteratedDeriv k f)) {C : ℝ}
    (hC : (∫ u, ‖iteratedDeriv j f u‖) ≤ C) :
    |w| ^ j * ‖𝓕 f w‖ ≤ C / (2 * Real.pi) ^ j := by
  have he : ‖𝓕 (iteratedDeriv j f) w‖ =
      (|w| ^ j * ‖𝓕 f w‖) * (2 * Real.pi) ^ j := by
    rw [Real.fourier_iteratedDeriv (N := (⊤ : ℕ∞)) hs (fun k _ => hf k) (by simp)]
    simp only [norm_smul, norm_pow, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
    ring
  rw [le_div_iff₀ (by positivity), ← he]
  exact (VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _).trans hC

/-- Combine the estimates of order zero and of order `j`. -/
lemma inhomogeneous_weight {w a A B : ℝ} {j : ℕ} (ha : 0 ≤ a)
    (hA : a ≤ A) (hB : |w| ^ j * a ≤ B) :
    (1 + |w|) ^ j * a ≤ 2 ^ j * (A + B) := by
  by_cases hw : |w| ≤ 1
  · have h : 1 + |w| ≤ 2 := by linarith
    have hB₀ : 0 ≤ B := (by positivity : 0 ≤ |w| ^ j * a).trans hB
    gcongr
    linarith
  · have h : 1 + |w| ≤ 2 * |w| := by linarith [lt_of_not_ge hw]
    calc
      _ ≤ (2 * |w|) ^ j * a := by gcongr
      _ = 2 ^ j * (|w| ^ j * a) := by rw [mul_pow, mul_assoc]
      _ ≤ _ := by gcongr; linarith

/-- Transfer the Fourier weight at `t / (2π)` to the Mellin variable `t`. -/
lemma mellin_weight {t a C : ℝ} {j : ℕ} (ha : 0 ≤ a)
    (h : (1 + |t / (2 * Real.pi)|) ^ j * a ≤ C) :
    (1 + |t|) ^ j * a ≤ (1 + 2 * Real.pi) ^ j * C := by
  have ht : |t| = (2 * Real.pi) * |t / (2 * Real.pi)| := by
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    field_simp
  have hb : 1 + |t| ≤ (1 + 2 * Real.pi) * (1 + |t / (2 * Real.pi)|) := by
    rw [ht]
    nlinarith [Real.pi_pos, abs_nonneg (t / (2 * Real.pi))]
  calc
    _ ≤ ((1 + 2 * Real.pi) * (1 + |t / (2 * Real.pi)|)) ^ j * a := by gcongr
    _ = (1 + 2 * Real.pi) ^ j * ((1 + |t / (2 * Real.pi)|) ^ j * a) := by
      rw [mul_pow, mul_assoc]
    _ ≤ _ := by gcongr

theorem compact_family_fourier_power_bound (F : E → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set E) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ J, ∀ w : ℝ,
      |w| ^ j * ‖𝓕 (F σ) w‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := compact_family_deriv_L1_bound F hF K hK hsupp J hJ j
  refine ⟨C / (2 * Real.pi) ^ j, by positivity, ?_⟩
  intro σ hσ w
  exact fourier_power_le w (hF.comp (contDiff_const.prodMk contDiff_id))
    (compact_family_deriv_integrable F hF K hK hsupp σ) (hb σ hσ)

theorem compact_family_fourier_weighted_bound (F : E → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set E) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ J, ∀ w : ℝ,
      (1 + |w|) ^ j * ‖𝓕 (F σ) w‖ ≤ C := by
  obtain ⟨C₀, hC₀, h0⟩ := compact_family_fourier_power_bound F hF K hK hsupp J hJ 0
  obtain ⟨Cj, hCj, hj⟩ := compact_family_fourier_power_bound F hF K hK hsupp J hJ j
  refine ⟨2 ^ j * (C₀ + Cj), by positivity, ?_⟩
  intro σ hσ w
  exact inhomogeneous_weight (norm_nonneg _) (by simpa using h0 σ hσ w) (hj σ hσ w)

end SevenEighths.CompactProfileFamily

end

end OAI
