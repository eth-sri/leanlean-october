module

public import Chazelle.Core.RestoreTIntKey
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics

/-!
# WP-E, the candidate test on the RAM, part 16: dispatching on the model

The model header (register `83021`, `0` for a chain model, `1` for the interior model) selects
the implementation of a model operation.

* `gKey`: `offCmp` (`keyCmp`) for a chain model, `iKey` for the interior model; `gKey_ok`:
  `KeyOK gKey 11010`.
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Machine Machine.Stmt Programs SweepPrim NFLoc SignK

variable {P : Polygon} {W : ℕ} {M : Model} {N : NF} {c₀ c : Config}

/-- **The model kind of a run**: a chain model with header `0`, or the interior model with header
`1` and its orientation bit. -/
theorem TGood.kind (hE : TGood P W M N c₀) :
    (c₀.nmem (c₀.nreg 83000) = 0 ∧ ∃ C : Chain, M = chainModel C) ∨
    (c₀.nmem (c₀.nreg 83000) = 1 ∧ M = interiorModel (Qof P) ∧
      (c₀.nmem (c₀.nreg 83000 + 1) = 1 ↔ Mountain.LeftInside (Qof P))) := by
  rcases hE.hMD with ⟨h0, H, C, -, hM⟩ | ⟨h1, hbit, hM⟩
  · exact Or.inl ⟨h0, C, hM⟩
  · exact Or.inr ⟨h1, hM, hbit⟩

/-- The walk of the interior model has `n` vertices. -/
theorem interior_n : (interiorModel (Qof P)).W.n = P.n := by
  simp [interiorModel]; rw [interiorWalk_n]; exact shear_n _ _

theorem Bik_band (r : ℕ) (h : Bik r = true) : bandOf r ∈ primBands ∧ r ≠ ALLOC := by
  unfold Bik at h
  simp [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ((((h | h) | h) | h) | h) | h
  · have := Bdir_band r h
    refine ⟨?_, this.2⟩
    have h1 := this.1
    simp [Finset.mem_insert, Finset.mem_singleton] at h1
    simp [primBands, Finset.mem_insert, Finset.mem_singleton]
    tauto
  all_goals first
    | (subst h; exact ⟨by simp [primBands, bandOf, bLocate], by ufo ALLOC⟩)
    | exact ⟨by simp [primBands, bandOf, bLocate, bSign, Finset.mem_insert,
        Finset.mem_singleton]; omega, by ufo ALLOC⟩

/-- **The key comparison of both models.** -/
def gKey (a b d e : ℕ) : Stmt := .ifLtN 83021 83023 (keyCmp a b d e) (iKey a b d e)

theorem gKey_ok : KeyOK gKey 11010 := by
  intro a b d e ha hb hd he P W M N c₀ c hE hI hx hy hroom
  have h21 := hI.h21
  have h23 := hI.h23
  have i0 := hI.hin 83000 (by norm_num) (by norm_num)
  unfold InR at ha hb hd he
  rcases hE.kind with ⟨h0, C, hM⟩ | ⟨h1, hMi, hbit⟩
  · -- a chain model
    obtain ⟨H, C', hC, hM', hwf⟩ := hI.chain hE hM
    have hx' : PosOK C' (Qof P) P.n ⟨c.nreg a, c.nreg b⟩ := by
      subst hM'; exact ⟨hx.1, hx.2.1, hx.2.2 C' rfl⟩
    have hy' : PosOK C' (Qof P) P.n ⟨c.nreg d, c.nreg e⟩ := by
      subst hM'; exact ⟨hy.1, hy.2.1, hy.2.2 C' rfl⟩
    obtain ⟨c', k, ex, hk, b1, b2, hf⟩ := keyCmp_exec (by ufo InR) (by ufo InR)
      (by ufo InR) (by ufo InR) hI.hw hE.hG hE.hW hwf hC hI.h22 hx' hy'
      (hE.hWm C' hM') (by omega)
    obtain ⟨hI', hrf, h8⟩ := hI.prim ex.wb_right hf
    refine ⟨c', k + 1, .ifLtN_true (by rwo [h21, h23, h0]) ex, by omega, ?_, ?_,
      hI', hrf.mono subset_rfl (by omega), h8⟩
    · rwx [hM']
    · rwx [hM']
  · -- the interior model
    subst hMi
    have hn := interior_n (P := P)
    obtain ⟨hMD, hwf⟩ := hI.modelDesc hE
    have hD : c.nreg 83000 + 1 ≤ W := by have := hwf.1; have := hI.hw.1 ALLOC; omega
    have hmd : c.nmem (c.nreg 83000 + 1) = c₀.nmem (c₀.nreg 83000 + 1) := by
      rw [i0, hI.hm _ (by have := hE.hwfMD.1; omega)]
    obtain ⟨c', k, ex, hk, b1, b2⟩ := iKey_exec (P := P) (a := a) (b := b) (d := d) (e := e)
      hE.hG (by have := hE.hW; ufo hostWords at this) hI.hw hbit hmd hD
      (by intro r hr; simp [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl <;> omega)
      hx.2.1 hy.2.1 (by rw [← hn]; exact hx.1) (by rw [← hn]; exact hy.1)
    have hfr : FrameB Bik c c' := exec_frameB ex (wr_iKey a b d e)
    obtain ⟨hI', hrf, h8⟩ := hI.prim ex.wb_right (frame_of_frameB hfr Bik_band k)
    refine ⟨c', k + 2, .ifLtN_false (by rwo [h21, h23, h1]) ex, by omega, b1, b2,
      hI', hrf.mono subset_rfl (by omega), h8⟩

end

end Restore

end Chazelle.Core
