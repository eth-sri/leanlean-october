/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CappedDonorReadback

@[expose] public section

namespace VaughtConjecture.Knight.CappedDonor.Ref

open Transform Value ExtOrd

noncomputable section

variable {I : Type*} [Fintype I] {nP N J : ℕ} {P : SemScheme (nP + 1)} {C : SemScheme J}
  {R : Ref I nP N J P C}

/-- The source cap is positive once its image is the actual cap. -/
theorem capC_ne_bot_of_read {j : ℕ} (hj : N ≤ j) {st : R.State j} {σ : ExtOrd → ExtOrd}
    (hbot : σ ⊥ = ⊥) (hcap : σ (st.v (R.capC hj)) = R.vact R.cap) : st.v (R.capC hj) ≠ ⊥ := by
  intro hz
  rw [hz, hbot] at hcap
  exact (ne_bot_of_gt R.cap_pos) hcap.symm

/-- **One-chart capped readback.**  For an admissible source `st` at cutoff `j ≥ N` with positive
gate, a witness `σ` through `N` reading its donor section as `u` capped at `m ≥ vact cap`, and
the actual cap and reference labels literally:
`min (u d) (cut vactL) = min (p d) (cut vactL)` at every present donor cell. -/
theorem capped_readback {j : ℕ} (hj : N ≤ j) {st : R.State j} (hst : R.Admissible st)
    {Kσ : ℕ} (hK : N ≤ Kσ) {σ : ExtOrd → ExtOrd} (hσ : Witness (gTop Kσ) σ)
    {m : ExtOrd} (hm : R.vact R.cap ≤ m) {u : P.scheme.below (effP nP j) → ExtOrd}
    (hu : ∀ d, σ (st.u d) = min (u d) m)
    (hcap : σ (st.v (R.capC hj)) = R.vact R.cap)
    (href : ∀ i, σ (st.v (CellScheme.below.mono (R.capLe hj) (R.lowRef i))) = R.vact (R.ref i))
    (hg : st.gate ≠ ⊥) (d : P.scheme.below (effP nP j)) :
    min (u d) (R.cut R.vactL) = min (R.p d.1) (R.cut R.vactL) := by
  have hvcap : st.v (R.capC hj) ≠ ⊥ := capC_ne_bot_of_read hj hσ.bot hcap
  have hrel := hst.relation hj hg hvcap d
  -- the cut and the selector of the source's image are the actual ones: they depend only on the
  -- cap and the references, which are read literally
  have hcut : σ (R.cut (R.lowC hj st.v)) = R.cut R.vactL := by
    rw [← cut_map hσ hK]
    exact cut_congr hcap href
  have hsel : σ (R.sel (R.lowC hj st.v) d.1) = min (R.p d.1) (R.cut R.vactL) := by
    rw [← sel_map hσ hK,
      sel_congr (v₁ := fun e => σ (R.lowC hj st.v e)) (v₂ := R.vactL) hcap href, sel_actual]
  have h := congrArg σ hrel
  rw [hσ.mono.map_min, hu, hcut, hsel] at h
  have hβm : R.cut R.vactL ≤ m := (cut_actual_lt_cap (R := R)).le.trans hm
  grind

end

end VaughtConjecture.Knight.CappedDonor.Ref
