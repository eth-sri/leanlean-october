/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.IdealZeroLocus
public import CCDN.Hilbert.FilteredIntersection
import CCDN.Algebra.PointSeparation
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-! A sharp affine curve intersection bound from the Hilbert function.
Bounds intersections with arbitrary section polynomials. No projective intersection theorem or
point-counting axiom is used. -/

@[expose] public section
namespace CCDN
noncomputable section

/-- A proper polynomial section of a prime curve contains at most the product
of the curve's affine Hilbert degree and the section degree many distinct points. -/
theorem polynomial_section_card_le_degree {K σ ι : Type*} [Field K] [Fintype σ]
    [Fintype ι] [DecidableEq ι]
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime] (d : ℕ)
    (hdegree : HasFilteredCurveDegree p d)
    (l : MvPolynomial σ K) (hl : l ∉ p) (m : ℕ) (hld : l.totalDegree ≤ m)
    (z : ι → σ → K) (hz : Function.Injective z)
    (hzp : ∀ i, z i ∈ idealZeroLocus p) (hzl : ∀ i, MvPolynomial.eval (z i) l = 0) :
    Fintype.card ι ≤ d * m := by
  classical
  rcases eq_or_ne m 0 with rfl | hm
  · have hlC := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (by omega : l.totalDegree = 0)
    let : IsEmpty ι := ⟨fun i => hl <| by
      have he := hzl i; rw [hlC, MvPolynomial.eval_C] at he
      rw [hlC, he, map_zero]; exact p.zero_mem⟩
    simp
  obtain ⟨h, hsep⟩ := exists_point_separators z hz
  let φ : ι → (MvPolynomial σ K ⧸ p) →ₐ[K] K :=
    fun i => Ideal.Quotient.liftₐ p (MvPolynomial.aeval (z i)) fun f hf => by
      simpa only [MvPolynomial.aeval_eq_eval] using hzp i f hf
  have hφ (i : ι) (f : MvPolynomial σ K) :
      φ i ((Ideal.Quotient.mk p) f) = MvPolynomial.eval (z i) f := by
    simp [φ, Ideal.Quotient.liftₐ_apply]
  let D := Finset.univ.sup fun i => (h i).totalDegree
  obtain ⟨N₀, c, hN₀⟩ := hdegree
  by_contra hlt
  have hcard : d * m + 1 ≤ Fintype.card ι := by omega
  let N := d * D + c.natAbs + N₀ + 1
  have hlin := separator_powers_independent φ (fun i => (Ideal.Quotient.mk p) (h i))
    ((Ideal.Quotient.mk p) l) (fun hzero => hl (Ideal.Quotient.eq_zero_iff_mem.mp hzero))
    (fun i => by rw [hφ]; exact hzl i)
    (fun i j => by rw [hφ]; exact hsep i j) (N + 1)
  let v : ι × Fin (N + 1) → filteredCoordinateSpace p (D + m * N) :=
    fun t => ⟨(Ideal.Quotient.mk p) (h t.1) * ((Ideal.Quotient.mk p) l) ^ t.2.val,
      Submodule.mem_map.mpr ⟨h t.1 * l ^ t.2.val, (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr
        ((MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add
          (Finset.le_sup (f := fun i => (h i).totalDegree) (Finset.mem_univ t.1))
          ((MvPolynomial.totalDegree_pow _ _).trans
            ((Nat.mul_le_mul_left _ hld).trans (by nlinarith [t.2.isLt]))))), by simp⟩⟩
  have hv : LinearIndependent K v :=
    LinearIndependent.of_comp (filteredCoordinateSpace p (D + m * N)).subtype hlin
  have hlow : Fintype.card ι * (N + 1) ≤
      Module.finrank K (filteredCoordinateSpace p (D + m * N)) := by
    simpa using hv.fintype_card_le_finrank
  have he := hN₀ (D + m * N) (by
    have hN : N₀ ≤ N := by dsimp [N]; omega
    have hm1 : 1 ≤ m := by omega
    nlinarith)
  push_cast at he
  have hlo : ((Fintype.card ι : ℕ) : ℤ) * (N + 1) ≤ (d : ℤ) * (D + m * N) + c := by
    rw [← he]; exact_mod_cast hlow
  have hmul : ((d : ℤ) * m + 1) * (N + 1) ≤ (Fintype.card ι : ℤ) * (N + 1) :=
    mod_cast Nat.mul_le_mul_right (N + 1) hcard
  have habs : c ≤ (c.natAbs : ℤ) := Int.le_natAbs
  have hNeq : (N : ℤ) = d * D + c.natAbs + N₀ + 1 := by simp [N]
  nlinarith

end
end CCDN
