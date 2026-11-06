/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.RingTheory.PowerSeries.Basic
import CCDN.ForMathlib.Matrix

/-! Finite linear independence of formal power series survives arbitrary
field extension. A finite nonzero coefficient minor witnesses independence. -/

@[expose] public section
namespace CCDN
noncomputable section
open Matrix

/-- Independence survives coefficient extension even for an infinite family:
each relation involves only a finite subfamily. -/
theorem powerSeries_linearIndependent_map_of_linearIndependent
    {K L ι : Type*} [Field K] [Field L] [Algebra K L]
    (v : ι → PowerSeries K) (hv : LinearIndependent K v) :
    LinearIndependent L (fun i => PowerSeries.map (algebraMap K L) (v i)) := by
  classical
  rw [linearIndependent_iff_finset_linearIndependent]
  intro s
  let v' : s → PowerSeries K := v ∘ Subtype.val
  have hv' : LinearIndependent K v' := hv.comp _ Subtype.val_injective
  let A : Matrix ℕ s K := fun n i => PowerSeries.coeff n (v' i)
  have hcols : LinearIndependent K A.col := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    refine (Fintype.linearIndependent_iff.mp hv') c (PowerSeries.ext fun n => ?_) i
    have h := congrFun hc n
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply] at h
    change (∑ x, c x • PowerSeries.coeff n (v' x)) = 0 at h
    simpa only [map_sum, PowerSeries.coeff_smul, map_zero] using h
  have hrank : A.rank = Fintype.card s :=
    (Matrix.rank_eq_finrank_span_cols A).trans
      (linearIndependent_iff_card_eq_finrank_span.mp hcols).symm
  obtain ⟨a, c, _, _, hdet⟩ :=
    Matrix.exists_det_submatrix_ne_zero_of_le_rank A (Fintype.card s) hrank.ge
  let B : Matrix ℕ s L := A.map (algebraMap K L)
  have hdetB : (B.submatrix a c).det ≠ 0 := by
    rw [show (B.submatrix a c).det = algebraMap K L (A.submatrix a c).det from
      (RingHom.map_det _ _).symm]
    exact (map_ne_zero (algebraMap K L)).mpr hdet
  have hrankB : Fintype.card s ≤ B.rank := B.le_rank_of_det_submatrix_ne_zero a c hdetB
  have hker : B.mulVecLin.ker = ⊥ := by
    apply Submodule.finrank_eq_zero.mp
    have h := B.mulVecLin.finrank_range_add_finrank_ker
    rw [Module.finrank_pi] at h
    change B.rank + Module.finrank L B.mulVecLin.ker = Fintype.card s at h
    omega
  rw [Fintype.linearIndependent_iff]
  intro w hw i
  have hz : w ∈ B.mulVecLin.ker := by
    ext n
    simpa only [B, A, v', Function.comp_apply, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
      Matrix.map, Matrix.of_apply, Pi.zero_apply, map_sum, PowerSeries.coeff_smul,
      PowerSeries.coeff_map, map_zero, smul_eq_mul, mul_comm] using
      congrArg (PowerSeries.coeff n) hw
  rw [hker, Submodule.mem_bot] at hz
  exact congrFun hz i

end
end CCDN
