/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Surface.CongruenceFamily
public import CCDN.Surface.SmoothPrimeWindow
public import CCDN.Surface.CurveComponents
import CCDN.Algebra.IntegerRationalIrreducibility
import CCDN.Surface.CurveCrossing
import CCDN.Surface.CompleteIntersectionDegreeBudget
import CCDN.Analysis.SmallDegreeSurfaceNumerics
import Mathlib.Data.Finset.Max

/-! A nonsingular point on a large-degree initial curve must cross a
proper auxiliary section along a one-prime deletion edge. This constructs
the residual cover from smooth reductions and auxiliaries. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset

/-- A prime window large enough that each nonsingular point retains 18 smooth primes. -/
structure IsSurfaceResidueWindow (f : MvPolynomial (Fin 3) ℤ) (B H : ℝ) (W : Finset ℕ) : Prop where
  one_le_radius : 1 ≤ B
  one_le_height : 1 ≤ H
  five_le_degree : 5 ≤ f.totalDegree
  coeff_le : CoefficientHeightLE f H
  prime : ∀ p ∈ W, p.Prime
  log_lower : ∀ p ∈ W, (Real.log B + 1) / 40 ≤ Real.log p
  derivative_bound : 4 * Real.log ((f.totalDegree : ℝ) + 1) + Real.log H + f.totalDegree * Real.log B ≤
    ((W.card : ℝ) - 18) * ((Real.log B + 1) / 40)

private lemma SurfaceCongruenceFamily.terminal_degree_le
    {f : MvPolynomial (Fin 3) ℤ} {B A : ℝ} {W : Finset ℕ}
    (F : SurfaceCongruenceFamily f B A) (hB : 1 ≤ B) (hA : 0 ≤ A)
    (P : Finset ℕ) (hPW : P ⊆ W) (hP : ∀ p ∈ P, p.Prime) (r : SmoothAffineResidueFamily f P)
    (hprod : B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) ≤ ∏ p ∈ P, (p : ℝ)) :
    ((F.auxiliary P hP r).totalDegree : ℝ) ≤ 2 * A * surfaceResidueLogBudget B W := by
  have hden : 0 < ∏ p ∈ P, (p : ℝ) := prod_pos (fun p hp => by exact_mod_cast (hP p hp).pos)
  apply le_of_mul_le_mul_right _ hden
  linear_combination F.scaled_degree_le hA hB hprod hPW hP r

private lemma surface_prime_curve_degree_le
    (f g : CoordinatePolynomial 3) (hf : Irreducible f) (hfg : ¬ f ∣ g)
    (I : Ideal (CoordinatePolynomial 3)) {d : ℕ} (hI : IsSurfaceCurve f I d) (hgI : g ∈ I) :
    d ≤ f.totalDegree * g.totalDegree := by
  have hh := surface_prime_curve_degree_sum_le f g hf hfg {I} (fun _ => d)
    (fun P hP => by
      simp_all)
  assumption

private theorem exists_subset_erase_boundary {α : Type*} [DecidableEq α] (R : Finset α)
    (W : Finset α → Prop) (hempty : ¬ W ∅) (hR : W R) :
    ∃ T : Finset α, T ⊆ R ∧ ∃ p ∈ T, W T ∧ ¬ W (T.erase p) := by
  classical
  let S := R.powerset.filter W
  have hS : S.Nonempty := ⟨R, mem_filter.mpr ⟨mem_powerset.mpr (Subset.refl _), hR⟩⟩
  obtain ⟨T, hTS, hmin⟩ := S.exists_min_image Finset.card hS
  obtain ⟨hTR, hWT⟩ := mem_filter.mp hTS
  have hTne : T.Nonempty := by
    apply nonempty_iff_ne_empty.mpr
    rintro rfl
    exact hempty hWT
  obtain ⟨p, hp⟩ := hTne
  refine ⟨T, mem_powerset.mp hTR, p, hp, hWT, ?_⟩
  intro he
  have herase : T.erase p ∈ S := mem_filter.mpr
    ⟨mem_powerset.mpr (Subset.trans (erase_subset p T) (mem_powerset.mp hTR)), he⟩
  exact (not_le_of_gt (card_lt_card (erase_ssubset hp))) (hmin _ herase)


open Classical in
/-- For a congruence family `F`, a set `R` of primes, a prime `p` and smooth residues `r`
modulo `R`, the rational points on curves `I ∈ S` whose ideal contains the auxiliary of
`R.erase p` but not the one of `R`, and at which the latter auxiliary vanishes. -/
def surfaceResidueCrossing {f : MvPolynomial (Fin 3) ℤ} {A B : ℝ}
    (F : SurfaceCongruenceFamily f B A)
    (S : Finset (Ideal (CoordinatePolynomial 3)))
    (R : Finset ℕ) (hR : ∀ p ∈ R, p.Prime) (p : ℕ)
    (r : SmoothAffineResidueFamily f R) : Set (RatPoint 3) :=
  let g := map (Int.castRingHom ℚ) (F.eraseAuxiliary hR p r)
  let h := map (Int.castRingHom ℚ) (F.auxiliary R hR r)
  ⋃ I ∈ S.filter (fun I => g ∈ I ∧ h ∉ I), idealZeroLocus I ∩ zeroLocus h

/-- Union over the primes in one residue modulus. -/
def surfaceResidueSubsetLocus {f : MvPolynomial (Fin 3) ℤ} {A B : ℝ}
    (F : SurfaceCongruenceFamily f B A) (S : Finset (Ideal (CoordinatePolynomial 3)))
    (W : Finset ℕ) (hW : ∀ p ∈ W, p.Prime) (R : Finset ℕ) : Set (RatPoint 3) :=
  if hR : R ⊆ W then
    ⋃ p ∈ R, ⋃ r : SmoothAffineResidueFamily f R,
      surfaceResidueCrossing F S R (fun q hq => hW q (hR hq)) p r
  else ∅

/-- The union of crossing loci for moduli of at most 18 primes. -/
def surfaceResidueResidualLocus {f : MvPolynomial (Fin 3) ℤ} {A B : ℝ}
    (F : SurfaceCongruenceFamily f B A) (S : Finset (Ideal (CoordinatePolynomial 3)))
    (W : Finset ℕ) (hW : ∀ p ∈ W, p.Prime) : Set (RatPoint 3) :=
  ⋃ R ∈ W.powerset.filter (fun R => R.card ≤ 18), surfaceResidueSubsetLocus F S W hW R

private theorem mem_surfaceResidueResidualLocus
    {f : MvPolynomial (Fin 3) ℤ} {A B : ℝ} {W : Finset ℕ}
    (F : SurfaceCongruenceFamily f B A) (S : Finset (Ideal (CoordinatePolynomial 3)))
    (hW : ∀ p ∈ W, p.Prime) (R : Finset ℕ) (hRW : R ⊆ W) (hcard : R.card ≤ 18)
    (hR : ∀ p ∈ R, p.Prime) (p : ℕ) (hp : p ∈ R)
    (r : SmoothAffineResidueFamily f R) {x : RatPoint 3}
    (hx : x ∈ surfaceResidueCrossing F S R hR p r) :
    x ∈ surfaceResidueResidualLocus F S W hW := by
  refine Set.mem_iUnion.mpr ⟨R, Set.mem_iUnion.mpr ⟨mem_filter.mpr ⟨mem_powerset.mpr hRW, hcard⟩, ?_⟩⟩
  simp only [surfaceResidueSubsetLocus, dite_eq_left hRW]
  exact Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hp, Set.mem_iUnion.mpr ⟨r, hx⟩⟩⟩

/-- A point on an initial prime curve above the terminal degree cutoff
lies in a proper section across a bounded-modulus residue edge. -/
theorem large_curve_point_mem_surfaceResidueResidualLocus
    (f : MvPolynomial (Fin 3) ℤ)
    (hir : Irreducible (map (Int.castRingHom ℚ) f))
    {A B H : ℝ} {W : Finset ℕ} (hA : 0 ≤ A) (hW : IsSurfaceResidueWindow f B H W)
    (F : SurfaceCongruenceFamily f B A)
    (S : Finset (Ideal (CoordinatePolynomial 3)))
    (I : Ideal (CoordinatePolynomial 3)) (hIS : I ∈ S) {d : ℕ}
    (hI : IsSurfaceCurve (map (Int.castRingHom ℚ) f) I d)
    (hinitI : map (Int.castRingHom ℚ) F.initial ∈ I)
    (hlarge : 2 * f.totalDegree * A * surfaceResidueLogBudget B W < d)
    (x : IntPoint 3) (hx : InBox x B) (hxf : eval x f = 0)
    (hxI : rationalPoint x ∈ idealZeroLocus I)
    (hsmooth : ∃ j, eval x (pderiv j f) ≠ 0) :
    rationalPoint x ∈ surfaceResidueResidualLocus F S W hW.prime := by
  classical
  obtain ⟨R₀, hR₀W, hR₀card, hR₀smooth⟩ := exists_smooth_prime_subset f hW.one_le_height
    hW.one_le_radius hW.coeff_le W hW.prime hW.log_lower (by norm_num; exact hW.derivative_bound)
    x hx hsmooth
  have hR₀prime (p) (hp : p ∈ R₀) : p.Prime := hW.prime p (hR₀W hp)
  have hR₀prod : B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) ≤ ∏ p ∈ R₀, (p : ℝ) := by
    have hlo := sum_le_sum (s := R₀) (fun p hp => hW.log_lower p (hR₀W hp))
    simp only [sum_const, nsmul_eq_mul, hR₀card] at hlo
    have hlog := Real.log_nonneg hW.one_le_radius
    rw [← exp_sum_log_primes R₀ hR₀prime, Real.rpow_def_of_pos (by linarith [hW.one_le_radius])]
    apply Real.exp_le_exp.mpr
    have hroot := surface_inverse_sqrt_le_nine_twentieths hW.five_le_degree
    linarith [mul_le_mul_of_nonneg_left hroot hlog]
  let aux (T : Finset ℕ) (hT : T ⊆ R₀) := F.auxiliary T (fun q hq => hR₀prime q (hT hq))
    (smoothResidueFamilyOfPoint x hxf T (fun q hq => hR₀smooth q (hT hq)))
  have hterminal : map (Int.castRingHom ℚ) (aux R₀ le_rfl) ∉ I := by
    intro hmem
    have hdeg := F.terminal_degree_le hW.one_le_radius hA R₀ hR₀W hR₀prime
      (smoothResidueFamilyOfPoint x hxf R₀ hR₀smooth) hR₀prod
    have hcurve := surface_prime_curve_degree_le _ _ hir (F.proper _ _ _) I hI hmem
    rw [rational_map_totalDegree, rational_map_totalDegree] at hcurve
    have hc : (d : ℝ) ≤ f.totalDegree * (aux R₀ le_rfl).totalDegree := by exact_mod_cast hcurve
    apply (not_le_of_gt hlarge) (hc.trans ((mul_le_mul_of_nonneg_left hdeg (Nat.cast_nonneg _)).trans_eq (by ring)))
  let bad (T : Finset ℕ) := ∃ hT : T ⊆ R₀, map (Int.castRingHom ℚ) (aux T hT) ∉ I
  have hempty : ¬ bad ∅ := by
    rintro ⟨hT, hbad⟩
    exact hbad (by simpa only [aux, F.initial_eq] using hinitI)
  obtain ⟨R, hRR₀, p, hp, ⟨hR, hchild⟩, hparent⟩ :=
    exists_subset_erase_boundary R₀ bad hempty ⟨le_rfl, hterminal⟩
  have hRprime (q : ℕ) (hq : q ∈ R) : q.Prime := hR₀prime q (hRR₀ hq)
  have hRsmooth (q : ℕ) (hq : q ∈ R) := hR₀smooth q (hRR₀ hq)
  let r := smoothResidueFamilyOfPoint x hxf R hRsmooth
  refine mem_surfaceResidueResidualLocus F S hW.prime R (hRR₀.trans hR₀W)
    ((card_le_card hRR₀).trans hR₀card.le) hRprime p hp r ?_
  simp only [surfaceResidueCrossing, Set.mem_iUnion, mem_filter, Set.mem_inter_iff]
  exact ⟨I, ⟨hIS, not_not.mp (fun hn => hparent ⟨(erase_subset p R).trans hRR₀, hn⟩), hchild⟩,
    hxI, (eval_rationalPoint_map_eq_zero x _).mpr (F.point_vanishes x hx hxf R hRprime hRsmooth)⟩

end
end CCDN
