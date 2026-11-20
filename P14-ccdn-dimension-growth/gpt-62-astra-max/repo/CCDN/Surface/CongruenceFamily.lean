/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Equations
public import CCDN.Determinant.SmoothAffineResidueClasses
public import CCDN.Surface.CongruenceCutoff
public import CCDN.Surface.CompleteIntersectionDegreeBudget
import CCDN.ForMathlib.MvPolynomial

/-! A coherent choice of proper auxiliaries for every finite
smooth residue family. The structure stores conclusions of the determinant
theorem; its existence is proved from the equation. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset

section

variable (f : IntegerPolynomial 3) {n : ℕ}

/-- The restriction of a family of smooth residues, indexed by the primes of `P`, to a subset
`Q ⊆ P`. -/
def SmoothAffineResidueFamily.restrict {f : IntegerPolynomial n}
    {P Q : Finset ℕ} (r : SmoothAffineResidueFamily f P) (hQP : Q ⊆ P) :
    SmoothAffineResidueFamily f Q := fun q => r ⟨q.val, hQP q.property⟩

/-- The unique family of smooth residues indexed by the empty set of primes. -/
def emptySmoothAffineResidueFamily (f : IntegerPolynomial n) :
    SmoothAffineResidueFamily f ∅ := fun p => False.elim (notMem_empty p.val p.property)

include f in
/-- A choice, for every finite set `P` of primes and every family `r` of smooth residues of `f`
modulo the primes of `P`, of a nonzero integer polynomial that is not divisible by `f` over `ℚ`,
has degree at most `A (B^(1/√d) / ∏ p + 1)(1 + log B + ∑ log p)` (with `d` the degree of `f`
and `p` ranging over `P`) and vanishes at every integer zero of `f` in the box of radius `B`
lying in the residue classes `r`. -/
structure SurfaceCongruenceFamily (B A : ℝ) where
  /-- The auxiliary polynomial attached to a set `P` of primes and smooth residues modulo
  `P`. -/
  auxiliary : (P : Finset ℕ) → (∀ p ∈ P, p.Prime) →
    SmoothAffineResidueFamily f P → IntegerPolynomial 3
  /-- No auxiliary is divisible by `f` over `ℚ`. -/
  proper : ∀ P hP r, ¬ rationalEquation f ∣
    rationalEquation (auxiliary P hP r)
  /-- The degree of the auxiliary attached to `P` is at most
  `A (B^(1/√d) / ∏ p + 1)(1 + log B + ∑ log p)`. -/
  degree_le : ∀ P hP r, ((auxiliary P hP r).totalDegree : ℝ) ≤
    A * (B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) /
      Real.exp (∑ p ∈ P, Real.log p) + 1) * (1 + Real.log B + ∑ p ∈ P, Real.log p)
  /-- The auxiliary attached to `P` and `r` vanishes at the integer zeros of `f` in the box
  that lie in the residue classes `r`. -/
  vanishes : ∀ P hP r x, x ∈ affineCongruencePoints f B P (smoothResidueIntegerLift r) →
    eval x (auxiliary P hP r) = 0

/-- An absolutely irreducible integer surface equation `f` of positive degree, whose
coefficient height `H` satisfies `log H ≤ K (log B + 1)`, admits a congruence family of
auxiliaries with degree constant `surfaceCongruenceDegreeConstant d K`, where `d` is the degree
of `f`. -/
theorem exists_surface_congruence_family
    (hprim : PrimitiveIntegerPolynomial f) (hir : AbsolutelyIrreducible f)
    (hd : 0 < f.totalDegree) {K H B : ℝ} (hK : 0 ≤ K) (hH : 1 ≤ H) (hB : 1 ≤ B)
    (hcoeff : CoefficientHeightLE f H)
    (hheight : Real.log H ≤ K * (Real.log B + 1)) :
    Nonempty (SurfaceCongruenceFamily f B (surfaceCongruenceDegreeConstant f.totalDegree K)) := by
  classical
  have hex (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (r : SmoothAffineResidueFamily f P) :=
    exists_surface_congruence_auxiliary f hprim hir hd hK hH hB hcoeff hheight P hP
      (smoothResidueIntegerLift r)
      (fun p hp => by
        let : NeZero p := ⟨(hP p hp).ne_zero⟩
        exact smoothResidueIntegerLift_zero r p hp)
      (fun p hp => by
        let : NeZero p := ⟨(hP p hp).ne_zero⟩
        exact smoothResidueIntegerLift_smooth r p hp)
  choose g _ hgproper hgdegree hgzero using hex
  exact ⟨⟨g, hgproper, hgdegree, hgzero⟩⟩

end

variable {f : IntegerPolynomial 3} {B A : ℝ} (F : SurfaceCongruenceFamily f B A)
    (x : IntPoint 3) (hx : InBox x B) (hxf : eval x f = 0)

/-- The auxiliary polynomial of a congruence family attached to the empty set of primes: it
vanishes at every integer zero of `f` in the box. -/
def SurfaceCongruenceFamily.initial : IntegerPolynomial 3 :=
  F.auxiliary ∅ (by simp) (emptySmoothAffineResidueFamily f)

/-- The auxiliary attached to the empty set of primes is `F.initial`, whatever the (unique)
residue family and primality proof. -/
lemma SurfaceCongruenceFamily.initial_eq (r : SmoothAffineResidueFamily f ∅)
    (hP : ∀ p ∈ (∅ : Finset ℕ), p.Prime) :
    F.auxiliary ∅ hP r = F.initial := by
  have he : r = emptySmoothAffineResidueFamily f := by
    funext p
    exact False.elim (notMem_empty p.val p.property)
  rw [he]
  rfl

include hx hxf in
/-- The initial auxiliary `F.initial` vanishes at every integer zero of `f` in the box of
radius `B`. -/
lemma SurfaceCongruenceFamily.initial_vanishes :
    eval x F.initial = 0 :=
  F.vanishes ∅ (by simp) (emptySmoothAffineResidueFamily f) x
    (mem_affineCongruencePoints.mpr ⟨hx, hxf, by simp⟩)

include hx in
/-- If an integer zero `x` of `f` in the box is a smooth point of `f` modulo every prime of `P`,
then the auxiliary attached to `P` and to the residues of `x` vanishes at `x`. -/
lemma SurfaceCongruenceFamily.point_vanishes
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hs : ∀ p ∈ P, ∃ j, eval (fun i => (x i : ZMod p))
      (pderiv j (residueEquation p f)) ≠ 0) :
    eval x (F.auxiliary P hP (smoothResidueFamilyOfPoint x hxf P hs)) = 0 := by
  apply F.vanishes
  apply mem_affineCongruencePoints.mpr
  refine ⟨hx, hxf, ?_⟩
  intro p hp j
  let : NeZero p := ⟨(hP p hp).ne_zero⟩
  exact smoothResidueFamilyOfPoint_congruence x hxf P hs p hp j

/-- The curve components cut out on the surface `f = 0` by the initial auxiliary of a
congruence family: height-two primes containing `f` and the auxiliary, whose zero loci cover
the common zero locus and whose total degree is at most `d A (B^(1/√d) + 1)(1 + log B)`. -/
theorem exists_surface_initial_curve_components (f : IntegerPolynomial 3)
    (hirQ : Irreducible (rationalEquation f)) {A B : ℝ}
    (F : SurfaceCongruenceFamily f B A) :
    ∃ S : Finset (Ideal (CoordinatePolynomial 3)),
      ∃ δ : Ideal (CoordinatePolynomial 3) → ℕ,
        (∀ I ∈ S, IsSectionCurve (rationalEquation f)
          (rationalEquation F.initial) I (δ I)) ∧
        (∀ x : IntPoint 3, InBox x B → eval x f = 0 → rationalPoint x ∈ ⋃ I ∈ S, idealZeroLocus I) ∧
        (∑ I ∈ S, (δ I : ℝ)) ≤ (f.totalDegree : ℝ) * A *
          (B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) + 1) * (1 + Real.log B) := by
  obtain ⟨S, δ, hS, hcover, hb⟩ :=
    integer_surface_section (g:=F.initial) hirQ
      (F.proper ∅ (by simp) (emptySmoothAffineResidueFamily f)) F.initial_vanishes
  refine ⟨S, δ, hS, hcover, ?_⟩
  have hinitial : (F.initial.totalDegree : ℝ) ≤
      A * (B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) + 1) * (1 + Real.log B) := by
    have hh := F.degree_le ∅ (by simp) (emptySmoothAffineResidueFamily f)
    simpa only [SurfaceCongruenceFamily.initial, sum_empty, Real.exp_zero, div_one, add_zero]
      using hh
  have hm := mul_le_mul_of_nonneg_left hinitial (Nat.cast_nonneg (α := ℝ) f.totalDegree)
  exact hb.trans (by simpa only [mul_assoc] using hm)

end
end CCDN
