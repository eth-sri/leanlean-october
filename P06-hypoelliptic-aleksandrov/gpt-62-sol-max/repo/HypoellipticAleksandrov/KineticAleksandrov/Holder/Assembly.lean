module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.OscillationDecay
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.NeighbourhoodEstimate
import Mathlib.Tactic

/-! # The kinetic Holder theorem from the proved growth and oscillation estimates -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open Set MeasureTheory Holder
open scoped ENNReal MatrixOrder

/-- The kinetic Holder theorem, conditional only on its admissibility predicate. -/
theorem kinetic_holder_of_aleksandrov_aux
    (d : ℕ) (hd : 1 ≤ d) (lam Lam p C_A : ℝ)
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (hp : 1 ≤ p) :
    ∃ alpha C : ℝ, 0 < alpha ∧ alpha ≤ 1 ∧
      ∀ A : FullKineticCoefficient d,
        Measurable (fullKineticCoefficientAt A) →
        (∀ P : KineticPoint d, (fullKineticCoefficientAt A P).IsSymm) →
        (∀ᵐ P ∂(volume : Measure (KineticPoint d)),
          lam • (1 : PDE.Mat d) ≤ fullKineticCoefficientAt A P) →
        (∀ᵐ P ∂(volume : Measure (KineticPoint d)),
          fullKineticCoefficientAt A P ≤ Lam • (1 : PDE.Mat d)) →
      ∀ (Omega : Set (KineticPoint d)), IsOpen Omega →
      ∀ (u : KineticPoint d → ℝ),
        (∃ M : ℝ, ∀ P ∈ Omega, |u P| ≤ M) →
        IsAdmissibleSolution A Omega p C_A u →
      ∀ (K : Set (KineticPoint d)), K ⊆ Omega → IsCompact K →
      ∀ (R₀ : ℝ), 0 < R₀ →
        (∀ P ∈ K, closure (backwardCylinder P (2 * R₀)) ⊆ Omega) →
      ∀ P ∈ K, ∀ P' ∈ K,
        |u P - u P'| ≤ C * oscillationOn u (holderNeighbourhood R₀ K) *
          (quasiDistance P P' / R₀) ^ alpha  := by
  obtain ⟨alpha, D, ha, ha1, hdecay⟩ := oscillation_decay d hd lam Lam p C_A hlam hLam hp
  let C := max D 1
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨alpha, C, ha, ha1, ?_⟩
  intro A hmeas hsym hlo hhi Omega hOmega u _hbounded hu K _hKO hK R0 hR0 hQ
  have hA : FullElliptic lam Lam A := ⟨hmeas, hsym, hlo, hhi⟩
  refine neighbourhood_estimate hK hR0 ha hC.le zero_le_one ?_ hu.1.1 hQ ?_
  · simpa only [Real.one_rpow, mul_one] using le_max_right D (1 : ℝ)
  dsimp only
  intro hab hbb P hP P' hP' ht hdpos hratioNear
  have hnear := (div_lt_iff₀ hR0).mp hratioNear
  rw [one_mul] at hnear
  have hdelta := hdpos.le
  have hR : 0 < 2 * R0 := by positivity
  have hdistR : quasiDistance P P' ≤ 2 * R0 := by linarith only [hnear, hR0]
  obtain ⟨hpcl, hp'cl⟩ := pair_mem_closed_later_cylinder P P' ht hdpos
  have hsmallO : closure (backwardCylinder P' (quasiDistance P P')) ⊆ Omega :=
    (closure_mono (backwardCylinder_radius_mono P' hdpos hdistR)).trans (hQ P' hP')
  have hcsmall := isCompact_closure_backwardCylinder P' _ hdpos
  have hucsmall := hu.1.1.mono hsmallO
  have habsmall := hcsmall.bddAbove_image hucsmall
  have hbbsmall := hcsmall.bddBelow_image hucsmall
  have habdiff := abs_sub_le_oscillationOn habsmall hbbsmall hpcl hp'cl
  rw [oscillationOn_closure (backwardCylinder_nonempty P' hdpos) hcsmall hucsmall]
    at habdiff
  have hd := hdecay A hA Omega hOmega P' (2 * R0) (quasiDistance P P')
    hR hdpos hdistR (hQ P' hP') u hu
  have hbigE := cylinder_subset_holderNeighbourhood hP' R0
  have hbigosc := oscillationOn_nonneg (backwardCylinder_nonempty P' hR)
    (hab.mono (image_mono hbigE)) (hbb.mono (image_mono hbigE))
  have hoscmono := oscillationOn_mono (backwardCylinder_nonempty P' hR) hbigE hab hbb
  have hratio : quasiDistance P P' / (2 * R0) ≤ quasiDistance P P' / R0 :=
    div_le_div_of_nonneg_left hdelta hR0 (by linarith only [hR0])
  have hpower := Real.rpow_le_rpow (div_nonneg hdelta hR.le) hratio ha.le
  have hcoeff : D * (quasiDistance P P' / (2 * R0)) ^ alpha ≤
      C * (quasiDistance P P' / R0) ^ alpha :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg (div_nonneg hdelta hR.le) _)).trans
      (mul_le_mul_of_nonneg_left hpower hC.le)
  have hb := (habdiff.trans hd).trans
    (mul_le_mul_of_nonneg_right hcoeff hbigosc)
  have hb' := hb.trans (mul_le_mul_of_nonneg_left hoscmono
    (mul_nonneg hC.le (Real.rpow_nonneg (div_nonneg hdelta hR0.le) _)))
  exact hb'.trans_eq (by ring)

end HypoellipticAleksandrov.KineticAleksandrov
