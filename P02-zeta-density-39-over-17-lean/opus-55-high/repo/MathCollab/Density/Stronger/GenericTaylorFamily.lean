module
public import MathCollab.Density.DetectorBlockExpansion
public import MathCollab.Density.DetectorFamilyScales
public import MathCollab.Density.FixedDetectorCover
import WeylPort.Analytic.RealLaplace

@[expose] public section

open Complex Set Filter
open scoped Topology
noncomputable section
namespace MathCollab.Density.Stronger

/-- Fixed coefficients depending on the base coefficients and scale, never on a zero. -/
def genericTaylorCoefficient (a : ℕ → ℂ) (N j n : ℕ) : ℂ :=
  a n * (((2*(n : ℝ)/N-3 : ℝ) : ℂ)^j)

def genericTaylorPolynomial (a : ℕ → ℂ) (N j : ℕ) (t : ℝ) : ℂ :=
  detectingPolynomial N (genericTaylorCoefficient a N j) (-t)

def genericBlock (ρ : ℂ) (a : ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ioc N (2*N), a n * (n : ℂ)^(-ρ)

theorem norm_genericTaylorCoefficient_le {a : ℕ → ℂ} {N n : ℕ}
    (ha : ∀ n ∈ Finset.Ioc N (2*N), ‖a n‖ ≤ (n.divisors.card : ℝ)) (hN : 0 < N) (hn : n ∈ Finset.Ioc N (2*N)) (j : ℕ) :
    ‖genericTaylorCoefficient a N j n‖ ≤ (n.divisors.card : ℝ) := by
  pm_74 hNpos N hN
  pm_7142 hlo
  have hhi : (n : ℝ) ≤ 2*N := by exact_mod_cast (Finset.mem_Ioc.mp hn).2
  have hr : |2*(n : ℝ)/N-3| ≤ 1 := by
    apply abs_le.mpr
    have hl : (2 : ℝ) ≤ 2*(n : ℝ)/N := (le_div_iff₀ hNpos).2 (by linarith)
    have hh : 2*(n : ℝ)/N ≤ 4 := (div_le_iff₀ hNpos).2 (by linarith)
    grind
  pm_265 genericTaylorCoefficient norm_mul norm_pow Complex.norm_real Real.norm_eq_abs
  have hp : |2*(n : ℝ)/N-3|^j ≤ 1 := pow_le_one₀ (abs_nonneg _) hr
  exact (mul_le_mul (ha n hn) hp (by positivity) (by positivity)).trans_eq (mul_one _)

/-- Uniform in the Taylor index and ordinate, before any beta approximation. -/
theorem norm_genericTaylorPolynomial_le {a : ℕ → ℂ} {N : ℕ}
    (ha : ∀ n ∈ Finset.Ioc N (2*N), ‖a n‖ ≤ (n.divisors.card : ℝ)) (hN : 0 < N) (j : ℕ) (t : ℝ) :
    ‖genericTaylorPolynomial a N j t‖ ≤ 2*(N : ℝ)^2 := by pm_4330 genericTaylorPolynomial genericTaylorCoefficient a norm_genericTaylorCoefficient_le ha

/-- The tail of the actual fixed polynomial family has geometric decay.
Identifying its full weighted series with the beta-dependent block is separate. -/
theorem norm_genericTaylor_tail_le {a : ℕ → ℂ} {β : ℝ} {N : ℕ}
    (ha : ∀ n ∈ Finset.Ioc N (2*N), ‖a n‖ ≤ (n.divisors.card : ℝ)) (hN : 0 < N) (hβ : 0 ≤ β) (hβ' : β ≤ 1) (J : ℕ) (t : ℝ) :
    ‖∑' j : ℕ, (detectorTaylorWeight β (j+J) : ℂ)*genericTaylorPolynomial a N (j+J) t‖ ≤
      3*(N : ℝ)^2*(1/3 : ℝ)^J := by pm_4425 genericTaylorPolynomial a norm_genericTaylorPolynomial_le ha

def normalizedGenericBlock (ρ : ℂ) (a : ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ioc N (2*N), a n *
    ((((n : ℝ)/N)^(-ρ.re) : ℝ) : ℂ)*dirichletPhase ((n : ℝ)/N) (-ρ.im)

section
variable {N : ℕ} (hN : 0 < N) (ρ : ℂ) (a : ℕ → ℂ)
include N hN ρ a
/-- Exact rescaling, including the unit phase of N; no ordinate is shifted. -/
theorem genericBlock_eq_normalized :
    genericBlock ρ a N = (N : ℂ)^(-ρ)*normalizedGenericBlock ρ a N := by pm_4296 genericBlock normalizedGenericBlock

theorem norm_normalizedGenericBlock :
    ‖normalizedGenericBlock ρ a N‖ = (N : ℝ)^ρ.re*‖genericBlock ρ a N‖ := by
  pm_6167 genericBlock_eq_normalized
  pm_4297

/-- Genuine summation and finite-sum interchange for the fixed Taylor family. -/
theorem hasSum_genericTaylorPolynomial :
    HasSum (fun j : ℕ => (detectorTaylorWeight ρ.re j : ℂ)*genericTaylorPolynomial a N j ρ.im)
      ((((3/2 : ℝ)^ρ.re : ℝ) : ℂ)*normalizedGenericBlock ρ a N) := by
  pm_74 hNpos N hN
  have hterm : ∀ n ∈ Finset.Ioc N (2*N),
      HasSum (fun j : ℕ => (detectorTaylorWeight ρ.re j : ℂ)*
        (a n * (((2*(n : ℝ)/N-3 : ℝ) : ℂ)^j) *
          dirichletPhase ((n : ℝ)/N) (-ρ.im)))
        ((((3/2 : ℝ)^ρ.re : ℝ) : ℂ)*(a n *
          ((((n : ℝ)/N)^(-ρ.re) : ℝ) : ℂ)*dirichletPhase ((n : ℝ)/N) (-ρ.im))) := by
    intro n hn
    have hlo : (1 : ℝ) ≤ (n : ℝ)/N := (le_div_iff₀ hNpos).2 (by simpa using (show (N : ℝ) ≤ n by exact_mod_cast (Finset.mem_Ioc.mp hn).1.le))
    have hhi : (n : ℝ)/N ≤ 2 := (div_le_iff₀ hNpos).2 (by exact_mod_cast (Finset.mem_Ioc.mp hn).2)
    have hs := hasSum_detector_binomial (β := ρ.re) hlo hhi
    have he : (2*((n : ℝ)/N)/3)^(-ρ.re) = (3/2 : ℝ)^ρ.re*((n : ℝ)/N)^(-ρ.re) := by
      rw [show 2*((n : ℝ)/N)/3 = ((n : ℝ)/N)/(3/2) by ring,
        Real.div_rpow (by positivity) (by norm_num), Real.rpow_neg (show (0 : ℝ) ≤ 3/2 by norm_num), div_inv_eq_mul]
      ring
    rw [he] at hs
    have hc := (hs.map Complex.ofRealCLM Complex.continuous_ofReal).mul_left
      (a n*dirichletPhase ((n : ℝ)/N) (-ρ.im))
    convert hc using 1
    · funext j
      simp only [Function.comp_apply, Complex.ofRealCLM_apply, Complex.ofReal_mul, Complex.ofReal_pow]
      push_cast
      ring
    · simp only [Complex.ofRealCLM_apply, Complex.ofReal_mul]
      ring
  have hs := hasSum_sum hterm
  convert hs using 1
  · funext j
    simp [genericTaylorPolynomial, detectingPolynomial, genericTaylorCoefficient, Finset.mul_sum]
  · rw [normalizedGenericBlock, Finset.mul_sum]
end

/-- The full Taylor combination is at least the beta-rescaled original block. -/
theorem norm_genericTaylor_tsum_ge {N : ℕ} (hN : 0 < N) {ρ : ℂ} (hβ : 0 ≤ ρ.re) (a : ℕ → ℂ) :
    (N : ℝ)^ρ.re*‖genericBlock ρ a N‖ ≤
      ‖∑' j : ℕ, (detectorTaylorWeight ρ.re j : ℂ)*genericTaylorPolynomial a N j ρ.im‖ := by
  pm_1458 hasSum_genericTaylorPolynomial a norm_normalizedGenericBlock
  pm_4299
  pm_1079 genericBlock a


section
variable {a : ℕ → ℂ} {T : ℝ} {N : ℕ} {ρ : ℂ} (ha : ∀ n ∈ Finset.Ioc N (2*N), ‖a n‖ ≤ (n.divisors.card : ℝ)) (hT : 1 ≤ T) (hN : 0 < N) (hN' : (N : ℝ) ≤ T^2) (hβ : 0 ≤ ρ.re) (hβ' : ρ.re ≤ 1)
include a T N ρ ha hT hN hN' hβ hβ'
/-- Quantitative tail control at the actual family cutoff. -/
theorem norm_fixedGenericTaylor_tail_le :
    ‖∑' j : ℕ, (detectorTaylorWeight ρ.re (j+(detectorTaylorCutoff T+1)) : ℂ)*
      genericTaylorPolynomial a N (j+(detectorTaylorCutoff T+1)) ρ.im‖ ≤ 3*T^(-1 : ℝ) := by pm_4320 norm_genericTaylor_tail_le ha

/-- The fixed family has the full block height, up to an absolute constant. -/
theorem exists_genericTaylor_component
    {D : ℝ} (hD : 0 < D)
    (hsmall : 3*T^(-1 : ℝ) ≤ 1/(4*D))
    (hblock : 1/(2*D) ≤ ‖genericBlock ρ a N‖) :
    ∃ j ∈ Finset.range (detectorTaylorCutoff T+1),
      (N : ℝ)^ρ.re/(8*D) ≤ ‖genericTaylorPolynomial a N j ρ.im‖ := by
  let J := detectorTaylorCutoff T
  let W := fun j : ℕ => (detectorTaylorWeight ρ.re j : ℂ)*genericTaylorPolynomial a N j ρ.im
  have hp : 1 ≤ (N : ℝ)^ρ.re := Real.one_le_rpow (by exact_mod_cast hN) hβ
  have hfull := norm_genericTaylor_tsum_ge hN hβ a
  have ht := (norm_fixedGenericTaylor_tail_le ha hT hN hN' hβ hβ').trans hsmall
  have hs := (hasSum_genericTaylorPolynomial hN ρ a).summable.sum_add_tsum_nat_add (J+1)
  have hnorm : ‖∑' j, W j‖ ≤ ‖∑ j ∈ Finset.range (J+1), W j‖ + ‖∑' j, W (j+(J+1))‖ := by
    change (∑ j ∈ Finset.range (J+1), W j)+(∑' j, W (j+(J+1))) = (∑' j, W j) at hs
    rw [← hs]
    exact norm_add_le _ _
  have hpartial : (N : ℝ)^ρ.re/(4*D) ≤ ‖∑ j ∈ Finset.range (J+1), W j‖ := by
    have hb := mul_le_mul_of_nonneg_left hblock (Real.rpow_nonneg (Nat.cast_nonneg N) ρ.re)
    have ht' : ‖∑' j, W (j+(J+1))‖ ≤ (N : ℝ)^ρ.re/(4*D) := by
      exact ht.trans ((div_le_div_iff_of_pos_right (by positivity)).mpr hp)
    change (N : ℝ)^ρ.re*‖genericBlock ρ a N‖ ≤ ‖∑' j, W j‖ at hfull
    change (N : ℝ)^ρ.re*(1/(2*D)) ≤ _ at hb
    have halg : (N : ℝ)^ρ.re*(1/(2*D)) = 2*((N : ℝ)^ρ.re/(4*D)) := by ring
    rw [halg] at hb
    linarith
  obtain ⟨j, hj, hlarge⟩ := exists_large_taylor_component hβ hβ' J (genericTaylorPolynomial a N · ρ.im)
  refine ⟨j, hj, ?_⟩
  pm_4290 hh div_le_div_of_nonneg_right hpartial
  change ‖∑ j ∈ Finset.range (J+1), W j‖/2 ≤ _ at hlarge
  exact (show (N : ℝ)^ρ.re/(8*D) = ((N : ℝ)^ρ.re/(4*D))/2 by ring).trans_le (hh.trans hlarge)
end


end MathCollab.Density.Stronger
