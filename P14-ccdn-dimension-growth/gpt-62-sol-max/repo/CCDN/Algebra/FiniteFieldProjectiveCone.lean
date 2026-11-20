/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Height.ProjectiveZeroLocus
import Mathlib.LinearAlgebra.Projectivization.Cardinality

/-! The exact relation between a homogeneous affine cone and its projective
zero locus. The origin is counted once and each projective zero contributes
exactly one nonzero vector for every unit in the field. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

section

variable {K : Type*} [Field K] [Fintype K] {n d : ℕ}
include K n d

private theorem homogeneous_affine_cone_card
    (f : MvPolynomial (Fin (n + 1)) K) (hf : f.IsHomogeneous d) (hd : 0 < d) :
    Nat.card {v : Fin (n + 1) → K // eval v f = 0} =
      Nat.card (projectiveZeroLocus f) * (Fintype.card K - 1) + 1 := by
  classical
  let A := {v : Fin (n + 1) → K // eval v f = 0}
  have hzero : eval (0 : Fin (n + 1) → K) f = 0 := by
    rw [MvPolynomial.eval_zero, constantCoeff_eq]
    exact hf.coeff_eq_zero (by simpa using hd.ne)
  let zeroA : A := ⟨0, hzero⟩
  let e := Projectivization.nonZeroEquivProjectivizationProdUnits K (Fin (n + 1) → K)
  let a : {v : A // v ≠ zeroA} ≃ {v : {v : Fin (n + 1) → K // v ≠ 0} // eval v.val f = 0} :=
    ⟨fun v => ⟨⟨v.val.val, fun h => v.property (Subtype.ext h)⟩, v.val.property⟩,
      fun v => ⟨⟨v.val.val, v.property⟩, fun h => v.val.property (congrArg Subtype.val h)⟩,
      fun _ => rfl, fun _ => rfl⟩
  let b := e.subtypeEquiv (q := fun x => x.1 ∈ projectiveZeroLocus f) (fun v => by
    change eval v.val f = 0 ↔ Projectivization.mk K v.val v.property ∈ projectiveZeroLocus f
    exact (mem_projectiveZeroLocus_mk hf _ _).symm)
  have hc := Nat.card_congr (a.trans (b.trans Equiv.prodSubtypeFstEquivSubtypeProd))
  rw [Nat.card_prod, Nat.card_units, Nat.card_eq_fintype_card (α := K)] at hc
  let : Nonempty A := ⟨zeroA⟩
  have hn : 0 < Nat.card A := Nat.card_pos
  have hleft : Nat.card {v : A // v ≠ zeroA} = Nat.card A - 1 := by
    simp [Nat.card_eq_fintype_card]
  change Nat.card {v : A // v ≠ zeroA} = Nat.card (projectiveZeroLocus f) * (Fintype.card K - 1) at hc
  rw [hleft] at hc
  change Nat.card A = _
  omega

/-- Passing from the affine cone to its projective zero locus preserves the
leading coefficient one, with an explicit lower-order error. -/
theorem homogeneous_projective_count_of_cone_bound (f : MvPolynomial (Fin (n + 3)) K) (hf : f.IsHomogeneous d) (hd : 0 < d)
    {H : ℝ} (hH : 0 ≤ H)
    (hcone : (Nat.card {v : Fin (n + 3) → K // eval v f = 0} : ℝ) ≤
      (Fintype.card K : ℝ) ^ (n + 2) + H * (Fintype.card K : ℝ) ^ (n + 1)) :
    (Nat.card (projectiveZeroLocus f) : ℝ) ≤
      (Fintype.card K : ℝ) ^ (n + 1) + 2 * (H + 1) * (Fintype.card K : ℝ) ^ n := by
  have hqN : 2 ≤ Fintype.card K := Fintype.one_lt_card
  have hq : (2 : ℝ) ≤ Fintype.card K := by exact_mod_cast hqN
  have hc := homogeneous_affine_cone_card f hf hd
  rw [hc] at hcone
  push_cast at hcone
  rw [Nat.cast_sub (by omega : 1 ≤ Fintype.card K), Nat.cast_one] at hcone
  have herror : 0 ≤ (H + 1) * ((Fintype.card K : ℝ) - 2) * (Fintype.card K : ℝ) ^ n :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
  apply (mul_le_mul_iff_left₀ (show (0 : ℝ) < Fintype.card K - 1 by linarith)).mp
  simp only [pow_succ] at hcone ⊢
  linarith only [hcone, herror]

end

end
end CCDN
