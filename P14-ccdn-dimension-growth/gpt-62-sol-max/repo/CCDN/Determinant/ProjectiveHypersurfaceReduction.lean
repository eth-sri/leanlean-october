/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Determinant.ProjectiveHypersurfaceLocal
public import CCDN.Determinant.ProjectiveReduction
public import CCDN.Algebra.ProjectiveAffineChart

/-! Projective residue points determine unit charts and integral lifts
in arbitrary dimension. Their reduced affine equations vanish at those lifts. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- A coordinate index at which the chosen representative of a point of `ℙⁿ⁺²(𝔽_p)` is nonzero. -/
def hypersurfaceResiduePivot {n p : ℕ} [Fact p.Prime] (r : ProjectiveResidueSpace (n + 2) p) :
    Fin (n + 3) := Classical.choose (Function.ne_iff.mp r.rep_nonzero)

/-- The representative of `r` is nonzero at the coordinate `hypersurfaceResiduePivot r`. -/
lemma hypersurfaceResiduePivot_ne_zero {n p : ℕ} [Fact p.Prime]
    (r : ProjectiveResidueSpace (n + 2) p) : r.rep (hypersurfaceResiduePivot r) ≠ 0 :=
  Classical.choose_spec (Function.ne_iff.mp r.rep_nonzero)

/-- The affine coordinates in the chosen pivot chart of the residue point. -/
def hypersurfaceResidueChart {n p : ℕ} [Fact p.Prime] (r : ProjectiveResidueSpace (n + 2) p) :=
  projectiveAffineCoordinatesAt (hypersurfaceResiduePivot r) r

/-- The integer lifts of these coordinates. -/
def hypersurfaceResidueChartLift {n p : ℕ} [Fact p.Prime] (r : ProjectiveResidueSpace (n + 2) p) :
    Fin (n + 2) → ℤ := fun j => (hypersurfaceResidueChart r j).val

@[simp] lemma cast_hypersurfaceResidueChartLift {n p : ℕ} [Fact p.Prime]
    (r : ProjectiveResidueSpace (n + 2) p) (j : Fin (n + 2)) :
    (hypersurfaceResidueChartLift r j : ZMod p) = hypersurfaceResidueChart r j := by
  simp [hypersurfaceResidueChartLift]

/-- Reduction determines both a unit coordinate and all affine congruences;
these are derived from equality of projective residue points. -/
theorem primitiveProjectiveReduction_hypersurface_chart {n p : ℕ} [Fact p.Prime]
    (z : IntPoint (n + 3)) (hz : Finset.univ.gcd z = 1)
    (r : ProjectiveResidueSpace (n + 2) p) (he : primitiveProjectiveReduction z hz = r) :
    IsCoprime (p : ℤ) (z (hypersurfaceResiduePivot r)) ∧
      ∀ j : Fin (n + 2), (p : ℤ) ∣ z (Equiv.swap 0 (hypersurfaceResiduePivot r) j.succ) -
        hypersurfaceResidueChartLift r j * z (hypersurfaceResiduePivot r) := by
  obtain ⟨u, hu⟩ := (Projectivization.mk_eq_mk_iff _ _ _ _ _).mp (he.trans r.mk_rep.symm)
  have hcoord (j : Fin (n + 3)) : (z j : ZMod p) = (u : ZMod p) * r.rep j :=
    (congrFun hu j).symm
  constructor
  · apply (Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)).irreducible.coprime_iff_not_dvd.mpr
    intro hd
    have hh := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hd
    rw [hcoord] at hh
    exact (mul_ne_zero u.ne_zero (hypersurfaceResiduePivot_ne_zero r)) hh
  · intro j
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    rw [Int.cast_sub, Int.cast_mul, cast_hypersurfaceResidueChartLift, hcoord, hcoord]
    unfold hypersurfaceResidueChart projectiveAffineCoordinatesAt
    field_simp [hypersurfaceResiduePivot_ne_zero]
    ring

/-- The integer chart representative of a projective residue zero satisfies
the reduced affine equation. -/
theorem hypersurfaceResidueChartLift_zero {n p d : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin (n + 3)) ℤ) (hf : f.IsHomogeneous d)
    (r : ProjectiveResidueSpace (n + 2) p)
    (hr : eval r.rep (map (Int.castRingHom (ZMod p)) f) = 0) :
    eval₂ (Int.castRingHom (ZMod p))
      (fun j => (hypersurfaceResidueChartLift r j : ZMod p))
      (affineChartAt (hypersurfaceResiduePivot r) f) = 0 := by
  rw [← eval_map, map_affineChartAt]
  simp only [cast_hypersurfaceResidueChartLift, affineChartAt_eval, hypersurfaceResidueChart,
    projectiveAffineCoordinatesAt_normalization r (hypersurfaceResiduePivot_ne_zero r),
    homogeneous_eval_smul (hf.map _), hr, mul_zero]

end
end CCDN
