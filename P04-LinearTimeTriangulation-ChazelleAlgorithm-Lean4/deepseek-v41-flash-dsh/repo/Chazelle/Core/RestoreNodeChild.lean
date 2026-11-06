module

public import Chazelle.Golf

public import Chazelle.Core.RestoreNodeEnd
public import Chazelle.Core.RestoreTree

/-!
# WP-E, the search: choosing the child of a node

`child_side`: in a valid normal form of a good model, a target region `r` faced just after the
walk vertex `p` (not an end of the chord `k`) is on the low side of `k` iff `p` is on the same
side of the chord's attachments as the reference key just after the start `ks` of an arc of the
region `dn` below `k`: `sideInArc ka kb p ↔ (ks = ka ∨ sideInArc ka kb ks)` (`decide_side`).
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Set Filter Topology
open Chazelle.Chain (sidePt SideAttach sideLeft sideInArc)

theorem after_ne (k a : ℝ) : ∀ᶠ ε in 𝓝[>] (0 : ℝ), k + ε ≠ a := by
  filter_upwards [lt_after a k, after_lt a k, self_mem_nhdsWithin] with ε h1 h2 h3 h
  have : (0 : ℝ) < ε := h3
  by_cases hak : a ≤ k
  · linarith
  · push Not at hak; have := h2.2 hak; linarith

theorem small_lt (b : ℝ) (hb : 0 < b) : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < b := by
  filter_upwards [Ioo_mem_nhdsGT hb] with ε hε using hε.2

/-- **The child of a node on the side of the target.** -/
theorem child_side {M : Model} {Q : Polygon} {N : NF} {reg : ℕ → Set Point} {D : ℕ}
    (hGM : GoodModel M) (hN : IsNF M Q N) (hT : Dec.RecTree N D) (hregs : NFRegs M Q N reg)
    {k : ℕ} (hk : k < N.nChords) {pa pb : ℕ} {ta tb : ℝ}
    (hA : SideAttach M.W ((N.chord k).toSet M Q) pa ta)
    (hB : SideAttach M.W ((N.chord k).toSet M Q) pb tb)
    (hAB : sidePt M.W pa ta ≠ sidePt M.W pb tb)
    {r : ℕ} (hr : r < N.nRegions) {p : ℕ} (hp : p < M.W.n)
    (hf : ∀ᶠ ε in 𝓝[>] (0 : ℝ), M.Faces p ε (reg r))
    (hpa : (p : ℝ) ≠ pa + ta) (_hpb : (p : ℝ) ≠ pb + tb)
    {j : ℕ} (hj : j < N.arcs.length) (hjr : (N.arc j).reg = (N.chord k).dn) :
    ((sideInArc (pa + ta) (pb + tb) p ↔
        (M.key Q (N.arc j).s = pa + ta ∨ sideInArc (pa + ta) (pb + tb) (M.key Q (N.arc j).s))) →
      r ∈ N.lowSide k) ∧
    (¬ (sideInArc (pa + ta) (pb + tb) p ↔
        (M.key Q (N.arc j).s = pa + ta ∨ sideInArc (pa + ta) (pb + tb) (M.key Q (N.arc j).s))) →
      r ∈ N.highSide k) := by
  have hM := walkAx_of_goodModel hGM
  set ka : ℝ := pa + ta
  set kb : ℝ := pb + tb
  have hab : ka ≠ kb := WalkAx.key_ne_of_pt_ne hA hB hAB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hprop⟩ := id hN
  obtain ⟨hτ0, hτ1, -⟩ := (hprop j hj).1
  have harc := (hregs.2.2.1.1 j hj).2
  rw [hjr] at harc
  set s := (N.arc j).s with hs
  set τ := M.param Q s with hτ
  have hks : M.key Q s = s.edge + τ := rfl
  set ks := M.key Q s
  set ke := M.key Q (N.arc j).e
  obtain ⟨ε, hε⟩ := (hf.and ((side_after hab p).and ((side_after hab ks).and
    ((after_start ks ke).and ((after_ne p ka).and ((after_ne p kb).and ((after_ne ks ka).and
      ((after_ne ks kb).and ((small_lt 1 one_pos).and ((small_lt (1 - τ) (⟡)).and
        self_mem_nhdsWithin)))))))))).exists
  obtain ⟨hfp, hsp, hss, hst, n1, n2, n3, n4, hε1, hετ, hε0⟩ := hε
  have hε0' := hε0
  have hsedge : s.edge < M.W.n := by
    obtain ⟨-, h, -⟩ := harc
    have := hτ0
    have h' : (s.edge : ℝ) < M.W.n := by
      have : ks = s.edge + τ := hks
      linarith
    exact_mod_cast h'
  have hf₀ : M.Faces s.edge (τ + ε) (reg (N.chord k).dn) :=
    harc.2.2.2.2.2.2 s.edge (τ + ε) hsedge (⟡) (⟡)
      (by rw [← add_assoc, ← hks]; exact hst)
  have hd := decide_side hGM hN hT hregs.1 hregs.2.1 hk hA hB hAB hr hp hε0' hε1 hfp hsedge
    (⟡) (⟡) hf₀
  have sw : ∀ v, v ≠ ka → v ≠ kb → (sideInArc kb ka v ↔ ¬ sideInArc ka kb v) := fun v h1 h2 =>
    Chazelle.Chain.sideInArc_swap (Ne.symm hab) h2 h1
  have ex : sideInArc ka kb (p + ε) ↔ sideInArc ka kb p := by
    rw [hsp]; exact ⟨fun h => h.resolve_left hpa, Or.inr⟩
  have er : sideInArc ka kb (s.edge + (τ + ε)) ↔ (ks = ka ∨ sideInArc ka kb ks) := by
    rw [← add_assoc, ← hks]; exact hss
  rw [sw _ n1 n2, sw _ (by rw [← add_assoc, ← hks]; exact n3)
    (by rw [← add_assoc, ← hks]; exact n4), ex, er] at hd
  refine ⟨fun h => hd.1 ?_, fun h => hd.2 ?_⟩
  · by_cases h' : sideInArc ka kb p
    · exact Or.inl ⟨h', h.1 h'⟩
    · exact Or.inr ⟨h', fun h'' => h' (h.2 h'')⟩
  · by_cases h' : sideInArc ka kb p
    · exact Or.inl ⟨h', fun h'' => h ⟨fun _ => h'', fun _ => h'⟩⟩
    · exact Or.inr ⟨h', by_contra fun h'' => h ⟨fun h3 => absurd h3 h', fun h3 => absurd h3 h''⟩⟩

end

end Restore

end Chazelle.Core
