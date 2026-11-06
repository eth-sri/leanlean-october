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

/-- Passing from the affine cone to its projective zero locus preserves the
leading coefficient one, with an explicit lower-order error. -/
theorem homogeneous_projective_count_of_cone_bound {K : Type*} [Field K] [Fintype K]
    {n d : ℕ} (f : MvPolynomial (Fin (n + 3)) K) (hf : f.IsHomogeneous d) (hd : 0 < d)
    {H : ℝ} (hH : 0 ≤ H)
    (hcone : (Nat.card {v : Fin (n + 3) → K // eval v f = 0} : ℝ) ≤
      (Fintype.card K : ℝ) ^ (n + 2) + H * (Fintype.card K : ℝ) ^ (n + 1)) :
    (Nat.card (projectiveZeroLocus f) : ℝ) ≤
      (Fintype.card K : ℝ) ^ (n + 1) + 2 * (H + 1) * (Fintype.card K : ℝ) ^ n := by
  classical
  let A := {v : Fin (n + 3) → K // eval v f = 0}
  let P := projectiveZeroLocus f
  let : Fintype A := Fintype.ofFinite _
  let : Fintype P := Fintype.ofFinite _
  have hzero : eval (0 : Fin (n + 3) → K) f = 0 := by
    have h := homogeneous_eval_smul hf (0 : K) (0 : Fin (n + 3) → K)
    simpa [zero_pow (Nat.ne_of_gt hd)] using h
  let zeroA : A := ⟨0, hzero⟩
  let g : P × Kˣ → {v : A // v ≠ zeroA} := fun ru =>
    ⟨⟨(ru.2 : K) • ru.1.val.rep,
      (homogeneous_eval_zero_iff_smul hf ru.2.ne_zero _).mpr ru.1.property⟩,
      fun h => ru.1.val.rep_nonzero ((smul_eq_zero.mp (congrArg Subtype.val h)).resolve_left ru.2.ne_zero)⟩
  have hg : Function.Bijective g := by
    refine ⟨?_, fun v => ?_⟩
    · rintro ⟨r, u⟩ ⟨t, w⟩ h
      have hv : (u : K) • r.val.rep = (w : K) • t.val.rep := congrArg (fun v => v.val.val) h
      have hrt : r = t := Subtype.ext <| by
        rw [← r.val.mk_rep, ← t.val.mk_rep, Projectivization.mk_eq_mk_iff']
        refine ⟨(u : K)⁻¹ * (w : K), ?_⟩
        simpa only [smul_smul, inv_mul_cancel₀ u.ne_zero, one_smul] using
          congrArg (fun v => (u : K)⁻¹ • v) hv.symm
      subst t
      obtain ⟨j, hj⟩ := Function.ne_iff.mp r.val.rep_nonzero
      obtain rfl : u = w := Units.ext (mul_right_cancel₀ hj (congrFun hv j))
      rfl
    · have hv : v.val.val ≠ 0 := fun h => v.property (Subtype.ext h)
      let r : P := ⟨Projectivization.mk K v.val.val hv,
        (mem_projectiveZeroLocus_mk hf _ hv).mpr v.val.property⟩
      obtain ⟨u, hu⟩ := Projectivization.exists_smul_eq_mk_rep K v.val.val hv
      refine ⟨(r, u⁻¹), Subtype.ext (Subtype.ext ?_)⟩
      change (↑u⁻¹ : K) • (Projectivization.mk K v.val.val hv).rep = v.val.val
      rw [← hu]
      change (↑u⁻¹ : K) • (u : K) • v.val.val = v.val.val
      simp [smul_smul]
  have hc : Fintype.card {v : A // v ≠ zeroA} = Fintype.card P * (Fintype.card K - 1) := by
    rw [← Fintype.card_of_bijective hg, Fintype.card_prod, Fintype.card_units]
  have hn : 0 < Fintype.card A := Fintype.card_pos_iff.mpr ⟨zeroA⟩
  rw [show Fintype.card {v : A // v ≠ zeroA} = Fintype.card A - 1 by simp] at hc
  have hcard : Nat.card A = Nat.card P * (Fintype.card K - 1) + 1 := by
    simpa only [Fintype.card_eq_nat_card] using
      (show Fintype.card A = Fintype.card P * (Fintype.card K - 1) + 1 by omega)
  have hqN : 2 ≤ Fintype.card K := Fintype.one_lt_card
  have hq : (2 : ℝ) ≤ Fintype.card K := mod_cast hqN
  rw [hcard] at hcone
  push_cast at hcone
  rw [Nat.cast_sub (by omega : 1 ≤ Fintype.card K), Nat.cast_one] at hcone
  have herror : 0 ≤ (H + 1) * ((Fintype.card K : ℝ) - 2) * (Fintype.card K : ℝ) ^ n :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
  have hmajor :
      (Fintype.card K : ℝ) ^ (n + 2) + H * (Fintype.card K : ℝ) ^ (n + 1) ≤
        ((Fintype.card K : ℝ) ^ (n + 1) + 2 * (H + 1) * (Fintype.card K : ℝ) ^ n) *
          (Fintype.card K - 1) := by
    simp only [pow_succ] at *
    nlinarith only [herror]
  exact (mul_le_mul_iff_left₀ (by linarith : (0 : ℝ) < Fintype.card K - 1)).mp
    (by linarith [hcone.trans hmajor])

end
end CCDN
