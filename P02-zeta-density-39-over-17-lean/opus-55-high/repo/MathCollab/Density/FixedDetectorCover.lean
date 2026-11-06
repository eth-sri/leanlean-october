module
public import MathCollab.Density.DetectorBlockExpansion
public import MathCollab.Density.DetectorFamilyScales
import WeylPort.Analytic.RealLaplace

@[expose] public section

open Complex Filter
open scoped Topology
noncomputable section
namespace MathCollab.Density

/-- This finite set depends on T alone, before any zero is selected. -/
def fixedDetectorIndices (T : ℝ) : Finset (ℕ × ℕ) :=
  (Finset.range (detectorDyadicCount T)).product (Finset.range (detectorTaylorCutoff T+1))

theorem fixedDetectorIndices_card_le {T : ℝ}
    (hlog : 0 ≤ Real.log T)
    (hD : (detectorDyadicCount T : ℝ) ≤ 5*Real.log T)
    (hJ : (detectorTaylorCutoff T+1 : ℝ) ≤ 12*Real.log T) :
    ((fixedDetectorIndices T).card : ℝ) ≤ 60*(Real.log T)^2 := by pm_4319 detectorDyadicCount fixedDetectorIndices

/-- Quantitative tail control at the actual family cutoff. -/
theorem norm_fixedDetector_tail_le {T : ℝ} {N : ℕ} {ρ : ℂ}
    (hT : 1 ≤ T) (hN : 0 < N) (hN' : (N : ℝ) ≤ T^2)
    (hβ : 0 ≤ ρ.re) (hβ' : ρ.re ≤ 1) :
    ‖∑' j : ℕ, (detectorTaylorWeight ρ.re (j+(detectorTaylorCutoff T+1)) : ℂ)*
      detectorTaylorPolynomial T N (j+(detectorTaylorCutoff T+1)) ρ.im‖ ≤ 3*T^(-1 : ℝ) := by pm_4320 norm_detectorTaylor_tail_le hTpos

set_option hygiene false in
macro "pf_40" x1:ident x2:ident x3:ident x4:ident x5:ident x6:term:max x7:ident x8:term:max x9:term:max : tactic => `(tactic| (
  let D : ℝ := $x1:ident T
  let J := detectorTaylorCutoff T
  let W := fun j : ℕ => (detectorTaylorWeight ρ.re j : ℂ)*$x2:ident T N j ρ.im
  have hD : 0 < D := by dsimp [D, $x1:ident]; positivity
  have hp : 1 ≤ (N : ℝ)^ρ.re := Real.one_le_rpow (by exact_mod_cast hN) hβ
  have hfull := $x3:ident hN hβ T
  have ht := ($x4:ident hT hN hN' hβ hβ').trans hsmall
  have hs := ($x5:ident hN ρ T).summable.sum_add_tsum_nat_add (J+1)
  have hnorm : ‖∑' j, W j‖ ≤ ‖∑ j ∈ Finset.range (J+1), W j‖ + ‖∑' j, W (j+(J+1))‖ := by
    change (∑ j ∈ Finset.range (J+1), W j)+(∑' j, W (j+(J+1))) = (∑' j, W j) at hs
    rw [← hs]
    exact norm_add_le _ _
  have hpartial : (N : ℝ)^ρ.re/(($x6:term)*D) ≤ ‖∑ j ∈ Finset.range (J+1), W j‖ := by
    have hb := mul_le_mul_of_nonneg_left hblock (Real.rpow_nonneg (Nat.cast_nonneg N) ρ.re)
    have ht' : ‖∑' j, W (j+(J+1))‖ ≤ (N : ℝ)^ρ.re/(($x6:term)*D) := by
      exact ht.trans ((div_le_div_iff_of_pos_right (by positivity)).mpr hp)
    change (N : ℝ)^ρ.re*‖$x7:ident ρ T N‖ ≤ ‖∑' j, W j‖ at hfull
    change (N : ℝ)^ρ.re*(1/(($x8:term)*D)) ≤ _ at hb
    have halg : (N : ℝ)^ρ.re*(1/(($x8:term)*D)) = 2*((N : ℝ)^ρ.re/(($x6:term)*D)) := by ring
    rw [halg] at hb
    linarith
  obtain ⟨j, hj, hlarge⟩ := exists_large_taylor_component hβ hβ' J ($x2:ident T N · ρ.im)
  refine ⟨j, hj, ?_⟩
  have hh := div_le_div_of_nonneg_right hpartial (by norm_num : (0 : ℝ) ≤ 2)
  change ‖∑ j ∈ Finset.range (J+1), W j‖/2 ≤ _ at hlarge
  exact (show (N : ℝ)^ρ.re/(($x9:term)*D) = ((N : ℝ)^ρ.re/(($x6:term)*D))/2 by ring).trans_le (hh.trans hlarge)))
/-- The fixed family has the full block height, up to an absolute constant. -/
theorem exists_fixedDetector_component {T : ℝ} {N : ℕ} {ρ : ℂ}
    (hT : 1 ≤ T) (hN : 0 < N) (hN' : (N : ℝ) ≤ T^2)
    (hβ : 0 ≤ ρ.re) (hβ' : ρ.re ≤ 1)
    (hsmall : 3*T^(-1 : ℝ) ≤ 1/(4*(detectorDyadicCount T : ℝ)))
    (hblock : 1/(2*(detectorDyadicCount T : ℝ)) ≤ ‖detectorBlock ρ T N‖) :
    ∃ j ∈ Finset.range (detectorTaylorCutoff T+1),
      (N : ℝ)^ρ.re/(8*(detectorDyadicCount T : ℝ)) ≤ ‖detectorTaylorPolynomial T N j ρ.im‖ := by pf_40 detectorDyadicCount detectorTaylorPolynomial norm_detectorTaylor_tsum_ge norm_fixedDetector_tail_le hasSum_detectorTaylorPolynomial 4 detectorBlock 2 8

/-- Complete fixed-family coverage of every actual slab zero, conditional only
on the displayed actual-zeta pointwise bound. The threshold and family precede
both coordinates of the zero; no Type-I restriction or ordinate shift occurs. -/
theorem fixedDetector_cover_of_zeta_bound {η C : ℝ}
    (hη : 0 ≤ η) (hη' : η < 1/48) (hC : 0 ≤ C)
    (hW : ∀ t : ℝ, ‖riemannZeta ((1/2 : ℂ)+(t : ℂ)*I)‖ ≤ C*(1+|t|)^(1/6+η)) :
    ∀ᶠ T : ℝ in atTop, ∀ (σ : ℝ) (ρ : ℂ),
      3/4 ≤ σ → σ ≤ ρ.re → ρ.re < 1 → T ≤ |ρ.im| → |ρ.im| ≤ 2*T →
      riemannZeta ρ = 0 →
      ∃ p ∈ fixedDetectorIndices T,
        firstDetectorX T/2 < ((2^p.1 : ℕ) : ℝ) ∧
        ((2^p.1 : ℕ) : ℝ) < T*(Real.log T)^2 ∧
        ((2^p.1 : ℕ) : ℝ)^σ/(40*Real.log T) ≤ ‖detectorTaylorPolynomial T (2^p.1) p.2 ρ.im‖ := by
  filter_upwards [detector_family_scales_eventually,
    finiteDetector_eventually_large_of_zeta_bound hη hη' hC hW] with T hsc hfin
  pm_6746
  intro σ ρ hσ hσβ hβ' hγ hγ' hzero
  have hβ : 3/4 ≤ ρ.re := hσ.trans hσβ
  have hlarge := hfin ρ hβ hβ' hγ hγ' hzero
  obtain ⟨r, hr, hblock⟩ := exists_detector_dyadic_block (by linarith : 1 ≤ T) (by norm_num : (0 : ℝ) < 1/2) hlarge
  let N : ℕ := 2^r
  pm_64 hN N
  pm_7669 detectorDyadicCount
  have hb : 1/(2*(detectorDyadicCount T : ℝ)) ≤ ‖detectorBlock ρ T N‖ := by convert hblock using 1; ring
  pm_4322 detectorBlock detectorBlock_scale_bounds
  obtain ⟨j, hj, hdetect⟩ := exists_fixedDetector_component (by linarith : 1 ≤ T) hN hN'
    (by linarith) hβ'.le hsmall hb
  pm_4321
  have hden : 8*(detectorDyadicCount T : ℝ) ≤ 40*Real.log T := by linarith
  change (N : ℝ)^σ/(40*Real.log T) ≤ _
  pm_1054

end MathCollab.Density
