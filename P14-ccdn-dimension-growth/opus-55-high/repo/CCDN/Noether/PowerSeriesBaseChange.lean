/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.RingTheory.PowerSeries.Basic
import CCDN.ForMathlib.Matrix

/-! Finite linear independence of formal power series survives arbitrary
field extension. A finite nonzero coefficient minor witnesses independence. -/

namespace CCDN
section
open Matrix

variable {K L ι : Type*} [Field K] [Field L] [Algebra K L]

theorem powerSeries_linearIndependent_map
    [Fintype ι]
    (v : ι → PowerSeries K) (hv : LinearIndependent K v) :
    LinearIndependent L (fun i => PowerSeries.map (algebraMap K L) (v i)) := by
  let A : Matrix ℕ ι K := fun n i => PowerSeries.coeff n (v i)
  have hrank : A.rank = Fintype.card ι := by
    rw [Matrix.rank_eq_finrank_span_cols]
    exact (linearIndependent_iff_card_eq_finrank_span.mp (by
      rw [Fintype.linearIndependent_iff]
      intro c hc i
      apply (Fintype.linearIndependent_iff.mp hv) c _ i
      apply PowerSeries.ext
      intro n
      have h := congrFun hc n
      simp at h
      change (∑ x, c x • PowerSeries.coeff n (v x)) = 0 at h
      simp_all)).symm
  obtain ⟨a, c, _, _, hdet⟩ :=
    Matrix.exists_det_submatrix_ne_zero_of_le_rank A (Fintype.card ι) hrank.ge
  let B : Matrix ℕ ι L := A.map (algebraMap K L)
  have hrankB := B.le_rank_of_det_submatrix_ne_zero a c (by
    have hm : (B.submatrix a c).det = algebraMap K L ((A.submatrix a c).det) := by
      rw [RingHom.map_det]
      rfl
    simp_all)
  have hker : B.mulVecLin.ker = ⊥ := by
    apply Submodule.finrank_eq_zero.mp
    have h := B.mulVecLin.finrank_range_add_finrank_ker
    rw [Module.finrank_pi] at h
    change B.rank + Module.finrank L B.mulVecLin.ker = Fintype.card ι at h
    omega
  rw [Fintype.linearIndependent_iff]
  intro w hw i
  have hmem : w ∈ B.mulVecLin.ker := (by
    ext n
    have h := congrArg (PowerSeries.coeff n) hw
    simpa [B, A, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.map,
      Matrix.of_apply, Pi.zero_apply, map_sum, PowerSeries.coeff_smul, PowerSeries.coeff_map,
      map_zero, smul_eq_mul, mul_comm] using h)
  rw [hker, Submodule.mem_bot] at hmem
  exact congrFun hmem i

/-- Independence survives coefficient extension even for an infinite family:
each relation involves only a finite subfamily. -/
theorem powerSeries_linearIndependent_map_of_linearIndependent
    (v : ι → PowerSeries K) (hv : LinearIndependent K v) :
    LinearIndependent L (fun i => PowerSeries.map (algebraMap K L) (v i)) := by
  rw [linearIndependent_iff_finset_linearIndependent]
  intro s
  exact powerSeries_linearIndependent_map (v ∘ Subtype.val)
    (hv.comp _ Subtype.val_injective)

