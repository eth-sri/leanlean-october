/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.HomogeneousChart
public import CCDN.AuxiliaryPolynomial.PlaneBadPrimes
public import CCDN.Determinant.HeightDeterminant
public import CCDN.Height.CountingHypotheses
import CCDN.Algebra.HomogeneousChartIrreducible
import CCDN.Determinant.ProjectivePrimeDeterminant

/-! Coefficient-controlled bad primes for homogeneous projective evaluation
matrices. Good reduction of a full-degree affine chart implies good reduction
of the entire projective equation. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset

/-- The global projective determinant lower bound, with the bad-prime charge
controlled by the coefficient height `H` of the affine chart. -/
theorem projective_determinant_log_lower_height
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {s N d M : ℕ} (hs : 0 < s)
    (f : MvPolynomial (Fin 3) ℤ) (hf : f.IsHomogeneous d) (hd : 2 ≤ d)
    {H : ℝ} (hchart : IsBoundedPlaneCurve K (affineChart 2 f) d H)
    {F : Fin N → MvPolynomial (Fin 3) ℤ} {z : Fin s → IntPoint 3}
    (hev : IsIndependentEvaluation f M F z) :
    (s : ℝ) ^ 2 / 2 * (Real.log s - 4 * Real.log d -
      Real.log (1 + Real.log H / (d : ℝ) ^ 2) -
        heightDeterminantError projectivePlaneDeterminantConstant) ≤
        Real.log (Int.Matrix.minorGcd (Matrix.of fun i j => eval (z i) (F j))) := by
  have hdeg := hchart.totalDegree_eq
  obtain ⟨bad, hmem, hcharge⟩ := exists_plane_bad_prime_set (affineChart 2 f)
    (by omega) hchart.irreducible H hchart.one_le_height hchart.coeff_le
  rw [hdeg] at hmem hcharge
  have hred (p : ℕ) (hp : p ∈ ((Ioc 0 s).filter Nat.Prime) \ bad)
      (hlo : stepanovThreshold (d : ℝ) < p) :
      Irreducible (map (Int.castRingHom (ZMod p)) f) := by
    let : Fact p.Prime := ⟨(mem_filter.mp (mem_sdiff.mp hp).1).2⟩
    let L := AlgebraicClosure (ZMod p)
    obtain ⟨hdegree, hir⟩ := (not_hypersurfaceBadReduction_iff (affineChart 2 f) p).mp
      fun hbad => (mem_sdiff.mp hp).2 ((hmem p).mpr ⟨hlo, hbad⟩)
    have hc : affineChart 2 (map (Int.castRingHom L) f) =
        map (Int.castRingHom L) (affineChart 2 f) := affineChart_map _ f
    have hf0 : map (Int.castRingHom L) f ≠ 0 :=
      fun h => hir.ne_zero (by rw [← hc, h, map_zero])
    have hi : Irreducible (map (Int.castRingHom L) f) :=
      irreducible_of_affineChart_irreducible _
        (by rw [hc, hdegree, hdeg, (hf.map (Int.castRingHom L)).totalDegree hf0]) (hc ▸ hir)
    apply mvPolynomial_irreducible_of_field_map (algebraMap (ZMod p) L)
    simpa only [MvPolynomial.map_map,
      show (algebraMap (ZMod p) L).comp (Int.castRingHom (ZMod p)) = Int.castRingHom L by ext; simp]
      using hi
  have hlower := projective_determinant_log_lower_at_rank hs f hf hd hev bad hred
  have hh := mul_le_mul_of_nonneg_left hcharge (show 0 ≤ (s : ℝ) ^ 2 / 2 by positivity)
  dsimp only [heightDeterminantError]
  nlinarith

end
end CCDN
