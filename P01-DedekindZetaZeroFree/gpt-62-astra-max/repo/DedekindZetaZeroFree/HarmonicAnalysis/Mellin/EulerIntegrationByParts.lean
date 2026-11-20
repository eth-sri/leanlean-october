module

public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.LogarithmicEndpointIntegrability

@[expose] public section

/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Classical ContDiff Topology

namespace DedekindZetaZeroFree.LargeSieve.Vendor
namespace LogMellinPhysical

variable {f : ℝ → ℂ} {δ : ℝ} {P : Polynomial ℂ}

private theorem contDiffOn_eulerIter {f : ℝ → ℂ} (hf : ContDiffOn ℝ ∞ f (Set.Ioi 0)) :
    ∀ j : ℕ, ContDiffOn ℝ ∞ (EulerIter j f) (Set.Ioi 0) := by apply @DedekindZetaZeroFree.LargeSieve.Vendor.LogLocalizedJets.LogLocalizedEulerJets.euler_smooth <;> assumption

private theorem cpow_sub_one_mul (s : ℂ) {x : ℝ} (hx : 0 < x) :
    (x : ℂ) ^ (s - 1) * (x : ℂ) = (x : ℂ) ^ s := by
  have h1 : (x : ℂ) ^ s = (x : ℂ) ^ (s - 1) * (x : ℂ) ^ (1 : ℂ) := by
    rw [← Complex.cpow_add (s - 1) 1 (Complex.ofReal_ne_zero.mpr (ne_of_gt hx)), show s - 1 + 1 = s by ring]
  rw [h1, Complex.cpow_one]

theorem euler_succ_mellin_eq (h : LogMellinPhysical f δ P) (j : ℕ)
    (s : ℂ) (hs : 0 < s.re) :
    mellin (EulerIter (j + 1) f) s = -s * mellin (EulerIter j f) s := by
  have hpt : ∀ x : ℝ, 0 < x →
      (x : ℂ) ^ (s - 1) * EulerIter (j + 1) f x = (x : ℂ) ^ s * deriv (EulerIter j f) x := by
    intro x hx
    rw [EulerIter_succ_of_pos j f x hx, ← mul_assoc, cpow_sub_one_mul s hx]
  have hconv := euler_mellinConvergent h (j + 1) s hs
  have huv' : IntegrableOn (fun x : ℝ => (x : ℂ) ^ s * deriv (EulerIter j f) x)
      (Set.Ioi 0) := by
    rw [MellinConvergent] at hconv
    refine hconv.congr_fun (fun x hx => ?_) measurableSet_Ioi
    show (x : ℂ) ^ (s - 1) * EulerIter (j + 1) f x = _
    exact hpt x hx
  have hu'v : IntegrableOn (fun x : ℝ => (s * (x : ℂ) ^ (s - 1)) * EulerIter j f x)
      (Set.Ioi 0) := by
    have h0 : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1) * EulerIter j f x)
        (Set.Ioi 0) := by
      have := euler_mellinConvergent h j s hs
      simpa only [MellinConvergent, smul_eq_mul] using this
    simpa only [mul_assoc, IntegrableOn] using (h0.const_mul s)
  have key := integral_Ioi_mul_deriv_eq_deriv_mul

    (fun x hx => hasDerivAt_ofReal_cpow_const (ne_of_gt hx) (by rintro rfl; simp at hs)) (fun x hx => ((((contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).mp (contDiffOn_eulerIter h.contDiffOn j)).1).differentiableAt (isOpen_Ioi.mem_nhds hx)).hasDerivAt) huv' hu'v (euler_cpow_tendsto_origin h j s hs) (euler_cpow_tendsto_atTop h j s hs)
  let Ioi₀ := Set.Ioi (0 : ℝ)
  have hcongr : (∫ x in Ioi₀, (x : ℂ) ^ (s - 1) * EulerIter (j + 1) f x)
      = ∫ x in Ioi₀, (x : ℂ) ^ s * deriv (EulerIter j f) x := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    exact hpt x hx
  have hkey2 : (∫ x in Ioi₀, (s * (x : ℂ) ^ (s - 1)) * EulerIter j f x)
      = s * ∫ x in Ioi₀, (x : ℂ) ^ (s - 1) * EulerIter j f x := by
    simp only [mul_assoc]
    rw [integral_const_mul]
  simp only [mellin, smul_eq_mul]
  rw [hcongr, key, hkey2]
  ring

theorem euler_mellin_eq (h : LogMellinPhysical f δ P) (n : ℕ)
    (s : ℂ) (hs : 0 < s.re) :
    mellin (EulerIter n f) s = (-s) ^ n * mellin f s := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [euler_succ_mellin_eq h n s hs, ih, pow_succ]
    ring

end LogMellinPhysical
end DedekindZetaZeroFree.LargeSieve.Vendor

end
