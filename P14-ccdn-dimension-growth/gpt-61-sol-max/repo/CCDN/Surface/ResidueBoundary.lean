/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Coordinates

import Mathlib

public import CCDN.Surface.CongruenceFamily
public import CCDN.Surface.CongruencePrimeWindow
public import CCDN.Surface.CurveComponents
import CCDN.AuxiliaryPolynomial.PlaneAuxiliaryCount
import CCDN.Surface.CurveCrossing
import CCDN.Surface.ResidueSubsetBoundary
import CCDN.Surface.SmoothPrimeWindow

/-! A nonsingular point on a large-degree initial curve must cross a
proper auxiliary section along a one-prime deletion edge. This constructs
the residual cover from smooth reductions and auxiliaries. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset

/-- The quantity `1 + log B + (log 4 + 4) c L`, with `c` the constant `scalingPrimeRatio`,
which bounds `1 + log B + ∑ p ∈ R, log p` for every set `R` of primes in the prime window of
logarithmic size `L`. -/
def surfaceResidueLogBudget (B L : ℝ)  :=
  1 + Real.log B + (Real.log 4 + 4) * scalingPrimeRatio * L

/-- The parameters of the residue cover of the surface `f = 0` in the box of radius `B ≥ 1`:
the coefficients of `f` are bounded by `H ≥ 1`; the logarithmic prime window `L ≥ 1` dominates
`4 log(d + 1) + log H + d log B`, which bounds the logarithm of a partial derivative of `f` at
a point of the box, where `d` is the degree of `f`; and the residue-modulus cutoff `X`
satisfies `1 < X`, `B^(1/√d) ≤ X` and `X ≤ e^L`. -/
structure IsSurfaceResidueWindow (f : CCDN.IntegerPolynomial 3) (B H L X : ℝ) : Prop where
  /-- The box radius is at least one. -/
  one_le_radius : 1 ≤ B
  /-- The height bound is at least one. -/
  one_le_height : 1 ≤ H
  /-- The logarithmic size of the prime window is at least one. -/
  one_le_window : 1 ≤ L
  /-- The coefficients of `f` are bounded by `H` in absolute value. -/
  coeff_le : CoefficientHeightLE f H
  /-- The window dominates the logarithmic size of a partial derivative of `f` on the
  box. -/
  log_le_window : 4 * Real.log (↑f.totalDegree + 1) +
    Real.log H + f.totalDegree * Real.log B ≤ L
  /-- The modulus cutoff exceeds one. -/
  one_lt_cutoff : 1 < X
  /-- The modulus cutoff is at least `B^(1/√d)`. -/
  root_le_cutoff : B ^ (1 / Real.sqrt ↑f.totalDegree) ≤ X
  /-- The modulus cutoff is at most `exp L`. -/
  cutoff_le_exp : X ≤ Real.exp L

/-- For a finite set `P` of primes, the exponential of `∑ p ∈ P, log p` is `∏ p ∈ P, p`. -/
lemma exp_sum_log_primes (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    Real.exp (∑ p ∈ P, Real.log p) = ∏ p ∈ P, ↑p := by
  rw [Real.exp_sum]
  apply prod_congr rfl
  intro p hp
  exact Real.exp_log (by exact_mod_cast (hP p hp).pos)

private lemma SurfaceCongruenceFamily.terminal_degree_le
    {f : CCDN.IntegerPolynomial 3} {B A L X : ℝ}
    (F : SurfaceCongruenceFamily f B A) (hB : 1 ≤ B) (hA : 0 ≤ A) (hL : 1 ≤ L)
    (P : Finset ℕ) (hPW : P ⊆ congruencePrimeWindow L)
    (hP : ∀ p ∈ P, p.Prime) (r : SmoothAffineResidueFamily f P)
    (hX : B ^ (1 / Real.sqrt ↑f.totalDegree) ≤ X)
    (hprod : X ≤ ∏ p ∈ P, ↑p) :
    ((F.auxiliary P hP r).totalDegree : ℝ) ≤ 2 * A * surfaceResidueLogBudget B L := by
  have hlogB := Real.log_nonneg hB
  have hlog :=
    (sum_le_sum_of_subset_of_nonneg hPW (fun p _ _ => Real.log_natCast_nonneg p)).trans
      (congruencePrimeWindow_log_upper hL)
  have hden : 0 < ∏ p ∈ P, (p : ℝ) := prod_pos (fun p hp => by exact_mod_cast (hP p hp).pos)
  have hratio : B ^ (1 / Real.sqrt ↑f.totalDegree) /
      Real.exp (∑ p ∈ P, Real.log p) ≤ 1 := by
    rw [exp_sum_log_primes P hP]
    exact (div_le_one hden).mpr (hX.trans hprod)
  have hd := F.degree_le P hP r
  calc
    _ ≤ A * (B ^ (1 / Real.sqrt ↑f.totalDegree) /
        Real.exp (∑ p ∈ P, Real.log p) + 1) *
        (1 + Real.log B + ∑ p ∈ P, Real.log p) := hd
    _ ≤ A * 2 * surfaceResidueLogBudget B L := by
      apply mul_le_mul
      · nlinarith
      · dsimp only [surfaceResidueLogBudget]
        linarith
      · positivity
      · positivity
    _ = _ := by ring

private lemma surface_prime_curve_degree_le
    (f g : CoordinatePolynomial 3) (hf : Irreducible f) (hfg : ¬ f ∣ g)
    (I : CCDN.CoordinateIdeal 3) {d : ℕ} (hI : IsSurfaceCurve f I d) (hgI : g ∈ I) :
    d ≤ f.totalDegree * g.totalDegree := by
  have hh := surface_prime_curve_degree_sum_le f g hf hfg {I} (fun _ => d)
    (fun P hP => by
      simp_all)
  simpa only [sum_singleton] using hh

/-- A one-prime deletion edge `R.erase p ⊂ R` of the congruence family `F`, at the smooth
residues `r`, crossing the curve `I` near the point `x`: the primes of `R` lie in the window of
log-size `L`, the modulus of `R` is less than `c L X` and that of `R.erase p` is less than `X`
(where `c` is `scalingPrimeRatio`), the parent auxiliary lies in `I`, the child auxiliary does
not, and the child vanishes at `x`. -/
structure IsSurfaceResidueEdge {f : CCDN.IntegerPolynomial 3} {A B : ℝ}
    (F : SurfaceCongruenceFamily f B A) (I : CCDN.CoordinateIdeal 3) (L X : ℝ)
    (x : IntPoint 3) (R : Finset ℕ) (hR : ∀ p ∈ R, p.Prime) (p : ℕ)
    (r : SmoothAffineResidueFamily f R) : Prop where
  /-- The primes of `R` lie in the prime window of logarithmic size `L`. -/
  subset_window : R ⊆ congruencePrimeWindow L
  /-- The product of the primes of `R` is less than `c L X`, with `c` the constant
  `scalingPrimeRatio`. -/
  prod_lt : (∏ q ∈ R, ↑q) < scalingPrimeRatio * L * X
  /-- The auxiliary attached to `R.erase p`, over `ℚ`, lies in the ideal `I` of the curve. -/
  parent_mem : CCDN.rationalPolynomial
    (F.auxiliary (R.erase p) (fun q hq => hR q (mem_of_mem_erase hq))
      (r.restrict (erase_subset p R))) ∈ I
  /-- The auxiliary attached to `R`, over `ℚ`, does not lie in the ideal `I`. -/
  child_not_mem : CCDN.rationalPolynomial (F.auxiliary R hR r) ∉ I
  /-- The auxiliary attached to `R` vanishes at `x`. -/
  child_vanishes : eval x (F.auxiliary R hR r) = 0

/-- A point on an initial prime curve above the terminal degree cutoff
lies in a proper section across a bounded-modulus residue edge. -/
theorem surface_residue_boundary_of_large_curve
    (f : CCDN.IntegerPolynomial 3)
    (hir : Irreducible (CCDN.rationalPolynomial f))
    {A B H L X : ℝ} (hA : 0 ≤ A) (hW : IsSurfaceResidueWindow f B H L X)
    (F : SurfaceCongruenceFamily f B A)
    (I : CCDN.CoordinateIdeal 3) {d : ℕ}
    (hI : IsSurfaceCurve (CCDN.rationalPolynomial f) I d)
    (hinitI : CCDN.rationalPolynomial F.initial ∈ I)
    (hlarge : 2 * f.totalDegree * A * surfaceResidueLogBudget B L < d)
    (x : IntPoint 3) (hx : InBox x B) (hxf : eval x f = 0)
    (hsmooth : ∃ j, eval x (pderiv j f) ≠ 0) :
    ∃ R : Finset ℕ, ∃ hR : ∀ p ∈ R, p.Prime,
      ∃ p ∈ R, ∃ r : SmoothAffineResidueFamily f R, IsSurfaceResidueEdge F I L X x R hR p r := by
  classical
  have hL := hW.one_le_window
  obtain ⟨P, hPW, hPprod, hPsmooth⟩ := exists_smooth_prime_window_subset f hW.one_le_height
    hW.one_le_radius hL hW.coeff_le (by norm_num; exact hW.log_le_window) x hx hsmooth
  have hPprime (p : ℕ) (hp : p ∈ P) : p.Prime :=
    ((mem_congruencePrimeWindow hL).mp (hPW hp)).1
  obtain ⟨R₀, hR₀P, hR₀prod, hR₀upper⟩ :=
    exists_minimal_product_subset P hW.one_lt_cutoff
      (fun p hp => by exact_mod_cast (hPprime p hp).pos)
      (fun p hp => ((mem_congruencePrimeWindow hL).mp (hPW hp)).2.2)
      (hW.cutoff_le_exp.trans hPprod)
  have hR₀W := hR₀P.trans hPW
  have hR₀prime (q : ℕ) (hq : q ∈ R₀) : q.Prime := hPprime q (hR₀P hq)
  have hR₀smooth (q : ℕ) (hq : q ∈ R₀) := hPsmooth q (hR₀P hq)
  let aux (T : Finset ℕ) : CCDN.IntegerPolynomial 3 :=
    if hT : T ⊆ R₀ then F.auxiliary T (fun q hq => hR₀prime q (hT hq))
      (smoothResidueFamilyOfPoint x hxf T (fun q hq => hR₀smooth q (hT hq))) else 1
  have haux (T : Finset ℕ) (hT : T ⊆ R₀) :
      aux T = F.auxiliary T (fun q hq => hR₀prime q (hT hq))
        (smoothResidueFamilyOfPoint x hxf T (fun q hq => hR₀smooth q (hT hq))) := by
    simp only [aux, dite_eq_left hT]
  have hterminal : CCDN.rationalPolynomial (aux R₀) ∉ I := by
    intro hmem
    rw [haux R₀ (Subset.refl _)] at hmem
    have hdeg := F.terminal_degree_le hW.one_le_radius hA hL R₀ hR₀W hR₀prime
      (smoothResidueFamilyOfPoint x hxf R₀ hR₀smooth) hW.root_le_cutoff hR₀prod
    have hcurve := surface_prime_curve_degree_le (CCDN.rationalPolynomial f)
      (CCDN.rationalPolynomial (F.auxiliary R₀ hR₀prime
        (smoothResidueFamilyOfPoint x hxf R₀ hR₀smooth))) hir (F.proper _ _ _)
      I hI hmem
    rw [rational_map_totalDegree, rational_map_totalDegree] at hcurve
    have hcurveR : ↑d ≤ (f.totalDegree : ℝ) *
        (F.auxiliary R₀ hR₀prime
          (smoothResidueFamilyOfPoint x hxf R₀ hR₀smooth)).totalDegree := by exact_mod_cast hcurve
    nlinarith
  have hempty : ¬ (CCDN.rationalPolynomial (aux ∅) ∉ I) := by
    rw [haux ∅ (empty_subset _), F.initial_eq]
    exact not_not.mpr hinitI
  obtain ⟨R, hRR₀, p, hp, hchild, hparent⟩ := exists_subset_erase_boundary R₀
    (fun T => CCDN.rationalPolynomial (aux T) ∉ I) hempty hterminal
  have hRprime (q : ℕ) (hq : q ∈ R) : q.Prime := hR₀prime q (hRR₀ hq)
  have hRsmooth (q : ℕ) (hq : q ∈ R) := hR₀smooth q (hRR₀ hq)
  let r := smoothResidueFamilyOfPoint x hxf R hRsmooth
  have hparentSub := (erase_subset p R).trans hRR₀
  have hparentEq : aux (R.erase p) =
      F.auxiliary (R.erase p) (fun q hq => hRprime q (mem_of_mem_erase hq))
        (r.restrict (erase_subset p R)) := by
    rw [haux (R.erase p) hparentSub]
    rfl
  have hchildEq := haux R hRR₀
  refine ⟨R, hRprime, p, hp, r, hRR₀.trans hR₀W, ?_, ?_, ?_, ?_⟩
  · exact lt_of_le_of_lt (Finset.prod_le_prod_of_subset_of_one_le₀ hRR₀
      (fun _ _ => Nat.cast_nonneg _) (fun q hq _ => by exact_mod_cast (hR₀prime q hq).one_lt.le)) hR₀upper
  · grind
  · rwa [← hchildEq]
  · exact F.point_vanishes x hx hxf R hRprime hRsmooth

end
end CCDN
