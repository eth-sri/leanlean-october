module

public import Chazelle.Core.SpecMerge

/-!
# WP-J, part 4: the descriptor of a merged chain

For a junction `J` (chains `C₁ = J.left`, `C₂ = J.right`, union `C = J.whole`):

* `whole_topIdx`: the top of `C` is the top of `C₁` if `C₂`'s top is not higher, else the top of
  `C₂` shifted by `m₁` (one height comparison);
* `whole_sideBeta`: the orientation bit of `C` is the bit of the part holding the top (no sign
  test: when the top comes from `C₂` it is not the shared vertex).
-/

namespace Chazelle.Core.L41

open Chazelle Chazelle.Merge

@[expose] public section

variable (J : Junction)

theorem left_vertex (k : ℕ) : J.left.vertex k = J.whole.vertex k := rfl

theorem right_vertex (k : ℕ) : J.right.vertex k = J.whole.vertex (J.m₁ + k) := by
  simp only [Chain.vertex, Chain.edgeIdx, Junction.right, Junction.whole,
    Nat.add_assoc]

/-- **The top index of the union.** -/
theorem whole_topIdx : J.whole.topIdx =
    if (J.right.top).2 ≤ (J.left.top).2 then J.left.topIdx else J.m₁ + J.right.topIdx := by
  have hm1 : J.left.m = J.m₁ := rfl
  have hm2 : J.right.m = J.m₂ := rfl
  have hm : J.whole.m = J.m₁ + J.m₂ := rfl
  have hLt := J.left.topIdx_le; have hRt := J.right.topIdx_le
  have hWt := J.whole.topIdx_le
  -- every vertex of the union is a vertex of a part
  have hsplit : ∀ i, i ≤ J.whole.m → (i ≤ J.m₁ ∧ J.whole.vertex i = J.left.vertex i) ∨
      (∃ t, t ≤ J.m₂ ∧ i = J.m₁ + t ∧ J.whole.vertex i = J.right.vertex t) := by
    intro i hi
    rcases le_or_gt i J.m₁ with h | h
    · exact Or.inl ⟨h, rfl⟩
    · refine Or.inr ⟨i - J.m₁, by omega, by omega, ?_⟩
      rw [right_vertex]; congr 1; omega
  split_ifs with hc
  · apply le_antisymm
    · apply J.whole.topIdx_min (by omega)
      intro i hi
      show (J.whole.vertex i).2 ≤ (J.left.vertex J.left.topIdx).2
      rcases hsplit i hi with ⟨h1, e⟩ | ⟨t, ht, rfl, e⟩
      · rw [e]; exact J.left.vertex_snd_le_top (by omega)
      · rw [e]; exact (J.right.vertex_snd_le_top (by omega)).trans hc
    · by_contra hlt
      push Not at hlt
      have := J.left.topIdx_min (j := J.whole.topIdx) (by omega) (fun i hi => by
        rw [left_vertex, left_vertex]; exact J.whole.vertex_snd_le_top (by omega))
      omega
  · push Not at hc
    apply le_antisymm
    · apply J.whole.topIdx_min (by omega)
      intro i hi
      rw [← right_vertex]
      show (J.whole.vertex i).2 ≤ (J.right.vertex J.right.topIdx).2
      rcases hsplit i hi with ⟨h1, e⟩ | ⟨t, ht, rfl, e⟩
      · rw [e]; exact (J.left.vertex_snd_le_top (by omega)).trans hc.le
      · rw [e]; exact J.right.vertex_snd_le_top (by omega)
    · have hT : J.m₁ + J.right.topIdx ≤ J.whole.m := by omega
      have hge : (J.right.top).2 ≤ (J.whole.top).2 := by
        show (J.right.vertex J.right.topIdx).2 ≤ _
        rw [right_vertex]; exact J.whole.vertex_snd_le_top hT
      rcases hsplit _ hWt with ⟨h1, e⟩ | ⟨t, ht, e1, e⟩
      · exfalso
        have := J.left.vertex_snd_le_top (j := J.whole.topIdx) (by omega)
        have e' : (J.whole.top).2 = (J.left.vertex J.whole.topIdx).2 := by
          show (J.whole.vertex J.whole.topIdx).2 = _; rw [e]
        linarith
      · rw [e1]
        have := J.right.topIdx_min (j := t) ht (fun i hi => by
          rw [right_vertex, ← e]
          exact J.whole.vertex_snd_le_top (by omega))
        omega

/-- **The orientation bit of the union** is the bit of the part holding the top. -/
theorem whole_sideBeta : J.whole.sideBeta =
    if (J.right.top).2 ≤ (J.left.top).2 then J.left.sideBeta else J.right.sideBeta := by
  have hT := whole_topIdx J
  split_ifs at hT ⊢ with hc
  · unfold Chain.sideBeta Chain.slitTop Chain.top Chain.radius
    rw [hT]; rfl
  · push Not at hc
    -- the top of `C₂` is not its first vertex (the shared vertex is a vertex of `C₁`)
    have h0 : 0 < J.right.topIdx := by
      by_contra h
      have e : J.right.topIdx = 0 := by omega
      have : (J.right.top).2 ≤ (J.left.top).2 := by
        show (J.right.vertex J.right.topIdx).2 ≤ _
        rw [e, right_vertex, Nat.add_zero, ← left_vertex]
        exact J.left.vertex_snd_le_top (le_refl _)
      linarith
    unfold Chain.sideBeta Chain.slitTop Chain.top Chain.radius
    rw [hT, right_vertex, right_vertex, right_vertex]
    have e1 : J.m₁ + J.right.topIdx + 1 = J.m₁ + (J.right.topIdx + 1) := by omega
    have e2 : J.m₁ + J.right.topIdx - 1 = J.m₁ + (J.right.topIdx - 1) := by omega
    rw [e1, e2]; rfl

end

end Chazelle.Core.L41
