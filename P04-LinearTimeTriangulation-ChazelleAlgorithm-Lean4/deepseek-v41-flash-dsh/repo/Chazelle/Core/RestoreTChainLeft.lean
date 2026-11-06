module

public import Chazelle.Golf

public import Chazelle.Core.RestoreTOps

/-!
# WP-E, the candidate test on the RAM, part 19: the sector test in a chain model

`tLeft`: the chain primitive `leftSec` at the candidate (the candidate point lies on the chain,
strictly inside the height band of the box).
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Machine Machine.Stmt Programs SweepPrim

variable {P : Polygon} {W : ℕ} {M : Model} {N : NF} {c₀ c : Config}

/-- The copies of the sector test. -/
def lsL : List (ℕ × ℕ) := [(50200, 83020), (50201, 83005), (50202, 83006), (50203, 83008)]

/-- **The sector test at the candidate** (chain model). -/
def tLeft : Stmt := .seq (block (copies lsL)) leftSec

theorem tLeft_exec (hE : TGood P W M N c₀) (hI : TInv W c₀ c) {C : Chain}
    (hM : M = chainModel C) (hroom : c.nreg ALLOC + 17400 ≤ W) :
    ∃ c' k, Exec P W tLeft c c' k ∧ k ≤ 17404 ∧
      BitIs c' 50210 (LeftB M P (xOf c₀) (c₀.nreg 83008)) ∧ TStep W c₀ c c' k := by
  obtain ⟨H, C', hC, hM', hwf⟩ := hI.chain hE hM
  have i5 := hI.hin 83005 (by norm_num) (by norm_num)
  have i6 := hI.hin 83006 (by norm_num) (by norm_num)
  have i8 := hI.hin 83008 (by norm_num) (by norm_num)
  have hxe : c₀.nreg 83005 < (chainModel C').W.n := by rw [← hM']; exact hE.hxe
  have hxp : ProperPos (chainModel C') (Qof P) P.n ⟨c₀.nreg 83005, c₀.nreg 83006⟩ := by
    rw [← hM']; exact hE.hxp
  have hy : |((chainModel C').pos (Qof P) ⟨c₀.nreg 83005, c₀.nreg 83006⟩).2| < C'.radius := by
    have hx := hE.hxC C' hM'
    rw [hM'] at hx
    exact lt_of_le_of_lt (C'.abs_le_coordBound_of_mem_set hx).2 C'.coordBound_lt_radius
  obtain ⟨c₁, c', k, h1, -, -, ex, hk, hout, hf⟩ := callPrim leftSec_meets lsL
    (by simp only [lsL, List.mem_cons, List.not_mem_nil, or_false]
        rintro q (rfl | rfl | rfl | rfl) r (rfl | rfl | rfl | rfl) <;> simp)
    (by simp [lsL]) (by simp [lsL]) (src := 83020) (by simp [lsL]) hI.hw hE.hG hE.hW
    hwf hC (fun c₁ h1 _ _ => by
      have q1 := h1 (50201, 83005) (by simp [lsL])
      have q2 := h1 (50202, 83006) (by simp [lsL])
      simp only at q1 q2
      refine ⟨by rw [q1, i5]; exact hxe, by rw [q1, q2, i5, i6]; exact hxp, ?_⟩
      rw [q1, q2, i5, i6]; exact hy) hroom
  have q1 := h1 (50201, 83005) (by simp [lsL])
  have q2 := h1 (50202, 83006) (by simp [lsL])
  have q3 := h1 (50203, 83008) (by simp [lsL])
  simp only at q1 q2 q3
  refine ⟨c', k, ex, by simp [lsL] at hk; omega, ?_, hI.prim ex.wb_right hf⟩
  have := hout
  unfold LeftOut at this
  rw [q1, q2, q3, i5, i6, i8] at this
  rw [hM']
  exact this

end

end Restore

end Chazelle.Core
