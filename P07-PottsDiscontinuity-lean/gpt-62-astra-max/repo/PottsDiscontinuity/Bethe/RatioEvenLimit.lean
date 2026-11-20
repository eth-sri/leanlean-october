module

public import PottsDiscontinuity.Bethe.RatioBulk29
public import PottsDiscontinuity.Bethe.RatioEvenAlgebra

/-! # The complete even-deficit eigenvalue ratio limit -/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace PottsDiscontinuity.Bethe

open BetheAnsatz

section

variable {Δ : ℝ} (hΔ : Δ < -1) (r : ℕ) (N : ℕ → ℕ) (h4 : ∀ i, 4 ∣ N i)
    (hr : ∀ i, r ≤ N i / 2) (hN : ∀ i, 0 < N i) (hn : ∀ i, 0 < N i / 2 - r)
    (p : ∀ i, Fin (N i / 2) → ℝ) (q : ∀ i, Fin (N i / 2 - r) → ℝ)
    (hp : ∀ i, p i ∈ S_n (N i / 2)) (hq : ∀ i, q i ∈ S_n (N i / 2 - r))
    (hpBE : ∀ i, DiscreteBetheEquation Δ (N i) (N i / 2) (p i))
    (hqBE : ∀ i, DiscreteBetheEquation Δ (N i) (N i / 2 - r) (q i))
    (hNlim : Tendsto (fun i => (N i : ℝ)) atTop atTop)
    (hbp : ∀ i, BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α *
        (rootStepDensity (N i) (p i) (half_pos_of_half_sub_pos hn i)
          (kMap (lamOf Δ) α) - rho Δ (kMap (lamOf Δ) α))|))
    (hbq : ∀ i, BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α *
        (rootStepDensity (N i) (q i) (hn i)
          (kMap (lamOf Δ) α) - rho Δ (kMap (lamOf Δ) α))|))
    {K : ℝ} (hK : 0 ≤ K)
    (hrate : ∀ᶠ i in atTop,
      densityNorm Δ (fun x => rootStepDensity (N i) (p i)
        (half_pos_of_half_sub_pos hn i) x - rho Δ x) ≤ K / N i ∧
      densityNorm Δ (fun x => rootStepDensity (N i) (q i)
        (hn i) x - rho Δ x) ≤ K / N i)



include hΔ h4 hr hN hp hq hpBE hqBE hNlim hbp hbq hK hrate

include h4 hN hbp hbq hn hp hpBE hq hqBE hr hΔ in
/-- The requested integral-exponent ratio limit for every even deficit r.
The ratios are the actual regular-branch expressions, not newly defined scalars. -/
theorem ratio_even_eigenvalue_limit (heven : r % 2 = 0) {c : ℝ} (hc : 2 < c)
    (hcΔ : anisotropy c = Δ) :
    Tendsto (fun i => eigenvalueRegular c (q i) / eigenvalueRegular c (p i)) atTop
      (𝓝 ((Real.exp (-(r : ℝ) * Real.log |Δ| +
        (r : ℝ) * ∫ x in (-Real.pi)..Real.pi, ratioEllPrime c x * tauCont Δ x) : ℝ) : ℂ)) := by
  let s := r / 2
  have hcount (i : ℕ) : s + (N i / 2 - r) + s = N i / 2 := by
    grind
  have hbulk := ratio_bulk_product_limit hΔ r N h4 hr hN hn p q hp hq hpBE hqBE hNlim hbp hbq hK hrate hc
  have halign (i : ℕ) (j : Fin (N i / 2 - r)) :
      alignedRoot (N := (N i)) (r := r) (hr i) (p i) j = p i ⟨j.val + s, by omega⟩ := by
    simp [alignedRoot, heven, ite_eq_left, s]
  simp_rw [halign] at hbulk
  have hnormP :=
    ratio_densityNorm_tendsto_of_rate (hΔ := hΔ) (N := N) hNlim (f := _) (hb := hbp) (hrate.mono (fun i hi => hi.1))
  have hnP (i : ℕ) : 0 < N i / 2 := by grind
  have hcountP (i : ℕ) : N i = 2 * (N i / 2 + 0) := by
    grind
  let x : ℕ → Fin s → ℝ := fun i j => p i ⟨j.val, by have := hcount i; omega⟩
  have hx (j : Fin s) :=
    ratio_tendsto_root_left hΔ 0 N (fun i => N i / 2) p hp hnP (hs := (fun i => by omega))
      hcountP hNlim hbp hnormP (j := (fun i => ⟨j.val, by have := hcount i; omega⟩)) s
      (fun i => by grind)
  have hboundary := ratio_even_boundary_tendsto hc s x hx
  have hs2 : s * 2 = r := by omega
  have habs : 0 < |Δ| := abs_pos.mpr (by linarith)
  have hpow : Real.exp ((r : ℝ) * Real.log |Δ|) = |Δ| ^ r := by
    rw [Real.exp_nat_mul, Real.exp_log habs]
  have hboundaryValue : ((|anisotropy c| ^ s) ^ 2)⁻¹ = Real.exp (-(r : ℝ) * Real.log |Δ|) := by
    rw [hcΔ, ← pow_mul, hs2, ← hpow, ← Real.exp_neg]
    congr 1
    ring
  rw [hboundaryValue] at hboundary
  have hreal := hbulk.mul hboundary
  have htarget : Real.exp ((r : ℝ) * ∫ x in (-Real.pi)..Real.pi, ratioEllPrime c x * tauCont Δ x) *
      Real.exp (-(r : ℝ) * Real.log |Δ|) =
      Real.exp (-(r : ℝ) * Real.log |Δ| +
        (r : ℝ) * ∫ x in (-Real.pi)..Real.pi, ratioEllPrime c x * tauCont Δ x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [htarget] at hreal
  have hcomplex := Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
  apply hcomplex.congr
  intro i
  exact (ratio_even_quotient_split (hcount i) hc (hp i) (hq i)).symm

end

end PottsDiscontinuity.Bethe

