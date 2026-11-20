/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Determinant.SmoothAffineResidueClasses
public import CCDN.Surface.CongruenceCutoff

/-! A coherent choice of proper auxiliaries for every finite
smooth residue family. The structure stores conclusions of the determinant
theorem; its existence is proved from the equation. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset

/-- The restriction of a family of smooth residues, indexed by the primes of `P`, to a subset
`Q ⊆ P`. -/
def SmoothAffineResidueFamily.restrict {n : ℕ} {f : MvPolynomial (Fin n) ℤ}
    {P Q : Finset ℕ} (r : SmoothAffineResidueFamily f P) (hQP : Q ⊆ P) :
    SmoothAffineResidueFamily f Q := fun q => r ⟨q.val, hQP q.property⟩

/-- The unique family of smooth residues indexed by the empty set of primes. -/
def emptySmoothAffineResidueFamily {n : ℕ} (f : MvPolynomial (Fin n) ℤ) :
    SmoothAffineResidueFamily f ∅ := fun p => False.elim (notMem_empty p.val p.property)

/-- A common upper bound on the logarithmic budgets of all submoduli. -/
def surfaceResidueLogBudget (B : ℝ) (W : Finset ℕ) : ℝ :=
  1 + Real.log B + ∑ p ∈ W, Real.log p

lemma exp_sum_log_primes (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    Real.exp (∑ p ∈ P, Real.log p) = ∏ p ∈ P, (p : ℝ) := by
  rw [Real.exp_sum]
  apply prod_congr rfl
  intro p hp
  exact Real.exp_log (by exact_mod_cast (hP p hp).pos)

/-- A choice, for every finite set `P` of primes and every family `r` of smooth residues of `f`
modulo the primes of `P`, of a nonzero integer polynomial that is not divisible by `f` over `ℚ`,
has degree at most `A (B^(1/√d) / ∏ p + 1)(1 + log B + ∑ log p)` (with `d` the degree of `f`
and `p` ranging over `P`) and vanishes at every integer zero of `f` in the box of radius `B`
lying in the residue classes `r`. -/
structure SurfaceCongruenceFamily (f : MvPolynomial (Fin 3) ℤ) (B A : ℝ) where
  /-- The auxiliary polynomial attached to a set `P` of primes and smooth residues modulo
  `P`. -/
  auxiliary : (P : Finset ℕ) → (∀ p ∈ P, p.Prime) →
    SmoothAffineResidueFamily f P → MvPolynomial (Fin 3) ℤ
  /-- No auxiliary is divisible by `f` over `ℚ`. -/
  proper : ∀ P hP r, ¬ map (Int.castRingHom ℚ) f ∣
    map (Int.castRingHom ℚ) (auxiliary P hP r)
  /-- The bound for the auxiliary degree multiplied by the modulus. -/
  degree_le : ∀ P hP r,
    ((auxiliary P hP r).totalDegree : ℝ) * (∏ p ∈ P, (p : ℝ)) ≤
      A * (B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) + ∏ p ∈ P, (p : ℝ)) *
        surfaceResidueLogBudget B P
  /-- The auxiliary attached to `P` and `r` vanishes at the integer zeros of `f` in the box
  that lie in the residue classes `r`. -/
  vanishes : ∀ P hP r x, x ∈ affineCongruencePoints f B P (smoothResidueIntegerLift r) →
    eval x (auxiliary P hP r) = 0

/-- An absolutely irreducible integer surface equation `f` of positive degree, whose
coefficient height `H` satisfies `log H ≤ K (log B + 1)`, admits a congruence family of
auxiliaries with degree constant `surfaceCongruenceDegreeConstant d K`, where `d` is the degree
of `f`. -/
theorem exists_surface_congruence_family
    (f : MvPolynomial (Fin 3) ℤ)
    (hir : AbsolutelyIrreducible f)
    (hd : 0 < f.totalDegree) {K H B : ℝ} (hK : 0 ≤ K) (hH : 1 ≤ H) (hB : 1 ≤ B)
    (hcoeff : CoefficientHeightLE f H)
    (hheight : Real.log H ≤ K * (Real.log B + 1)) :
    Nonempty (SurfaceCongruenceFamily f B (surfaceCongruenceDegreeConstant f.totalDegree K)) := by
  classical
  have hex (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (r : SmoothAffineResidueFamily f P) :=
    exists_surface_congruence_auxiliary f hir hd hK hH hB hcoeff hheight P hP
      (smoothResidueIntegerLift r)
      (fun p hp => by
        let : NeZero p := ⟨(hP p hp).ne_zero⟩
        exact smoothResidueIntegerLift_zero r p hp)
      (fun p hp => by
        let : NeZero p := ⟨(hP p hp).ne_zero⟩
        exact smoothResidueIntegerLift_smooth r p hp)
  choose g hg0 hgproper hgdegree hgzero using hex
  refine ⟨⟨g, hgproper, fun P hP r => ?_, hgzero⟩⟩
  have h := hgdegree P hP r
  let q := ∏ p ∈ P, (p : ℝ)
  rw [exp_sum_log_primes P hP, ← show q = ∏ p ∈ P, (p : ℝ) from rfl] at h
  have hq : 0 < q := prod_pos (fun p hp => by exact_mod_cast (hP p hp).pos)
  refine (mul_le_mul_of_nonneg_right h hq.le).trans_eq ?_
  change _ * q = _ * (_ + q) * _
  unfold surfaceResidueLogBudget
  field_simp

/-- The auxiliary after deleting one prime and restricting the residues. -/
def SurfaceCongruenceFamily.eraseAuxiliary {f : MvPolynomial (Fin 3) ℤ} {A B : ℝ}
    (F : SurfaceCongruenceFamily f B A) {R : Finset ℕ} (hR : ∀ p ∈ R, p.Prime)
    (p : ℕ) (r : SmoothAffineResidueFamily f R) : MvPolynomial (Fin 3) ℤ :=
  F.auxiliary (R.erase p) (fun q hq => hR q (mem_of_mem_erase hq)) (r.restrict (erase_subset p R))

/-- The auxiliary polynomial of a congruence family attached to the empty set of primes: it
vanishes at every integer zero of `f` in the box. -/
def SurfaceCongruenceFamily.initial {f : MvPolynomial (Fin 3) ℤ} {B A : ℝ}
    (F : SurfaceCongruenceFamily f B A) : MvPolynomial (Fin 3) ℤ :=
  F.auxiliary ∅ (by simp) (emptySmoothAffineResidueFamily f)

section

variable {f : MvPolynomial (Fin 3) ℤ} {B A : ℝ}
  (F : SurfaceCongruenceFamily f B A)
include f B A F

/-- Use the whole window's logarithmic budget and a common upper bound on the box power. -/
lemma SurfaceCongruenceFamily.scaled_degree_le
    (hA : 0 ≤ A) (hB : 1 ≤ B) {X : ℝ} (hX : B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) ≤ X)
    {W R : Finset ℕ} (hRW : R ⊆ W) (hR : ∀ p ∈ R, p.Prime) (r : SmoothAffineResidueFamily f R) :
    ((F.auxiliary R hR r).totalDegree : ℝ) * (∏ p ∈ R, (p : ℝ)) ≤
      A * (X + ∏ p ∈ R, (p : ℝ)) * surfaceResidueLogBudget B W := by
  have hb := Real.log_nonneg hB
  refine (F.degree_le R hR r).trans ?_
  unfold surfaceResidueLogBudget
  have hlog (S : Finset ℕ) : 0 ≤ ∑ p ∈ S, Real.log (p : ℝ) :=
    sum_nonneg (fun p _ => Real.log_natCast_nonneg p)
  have hsub := sum_le_sum_of_subset_of_nonneg hRW (fun p _ _ => Real.log_natCast_nonneg p)
  have hr : 0 ≤ ∏ p ∈ R, (p : ℝ) := prod_nonneg (fun _ _ => by positivity)
  have hx : 0 ≤ X := (by positivity : 0 ≤ B ^ (1 / Real.sqrt (f.totalDegree : ℝ))).trans hX
  gcongr

/-- The auxiliary attached to the empty set of primes is `F.initial`, whatever the (unique)
residue family and primality proof. -/
lemma SurfaceCongruenceFamily.initial_eq (r : SmoothAffineResidueFamily f ∅)
    (hP : ∀ p ∈ (∅ : Finset ℕ), p.Prime) :
    F.auxiliary ∅ hP r = F.initial := by
  have he : r = emptySmoothAffineResidueFamily f := by
    funext p
    grind
  tauto

/-- The initial auxiliary `F.initial` vanishes at every integer zero of `f` in the box of
radius `B`. -/
lemma SurfaceCongruenceFamily.initial_vanishes (x : IntPoint 3)
    (hx : InBox x B) (hxf : eval x f = 0) :
    eval x F.initial = 0 :=
  F.vanishes ∅ (by simp) (emptySmoothAffineResidueFamily f) x
    (mem_affineCongruencePoints.mpr ⟨hx, hxf, by simp⟩)

/-- If an integer zero `x` of `f` in the box is a smooth point of `f` modulo every prime of `P`,
then the auxiliary attached to `P` and to the residues of `x` vanishes at `x`. -/
lemma SurfaceCongruenceFamily.point_vanishes (x : IntPoint 3)
    (hx : InBox x B) (hxf : eval x f = 0)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hs : ∀ p ∈ P, ∃ j, eval (fun i => (x i : ZMod p))
      (pderiv j (map (Int.castRingHom (ZMod p)) f)) ≠ 0) :
    eval x (F.auxiliary P hP (smoothResidueFamilyOfPoint x hxf P hs)) = 0 := by
  apply F.vanishes
  apply mem_affineCongruencePoints.mpr
  refine ⟨hx, hxf, ?_⟩
  intro p hp j
  let : NeZero p := ⟨(hP p hp).ne_zero⟩
  exact smoothResidueFamilyOfPoint_congruence x hxf P hs p hp j

end

end
end CCDN
