module

public import Chazelle.Golf

public import Chazelle.Core.SweepIoLab0A

/-!
# The sweep RAM (WP-D), answers: the label candidates of a side-0 query, the labels in memory

* `label_valid`: a label of a log record (place below its count) is a region index of `N₂`;
* `label_mem`: a region of the label set of a log entry is the region of such a label;
* `slotPairs_cover`: every log entry register and label place has a slot.
-/

namespace Chazelle.Core

namespace SweepIo

namespace Lab0

open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep

@[expose] public section

variable {P : Polygon} {W : ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop} {J : Merge.Junction}
  {H : Host} {N₁ N₂ : NF} {E : ℕ} {c₀ : Config}

/-- The label words of a log record. -/
theorem logRec_labels {m : ℕ → ℕ} {AL : ℕ} {ls : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)}
    (hls : LogRecsAt m AL ls) {i : ℕ} (hi : i < ls.length) :
    m (AL + 7 * i + 2) = (ls.getD i (0, 0, 0, 0, 0, 0, 0)).2.2.1 ∧
    ∀ k, k ≤ 3 → m (AL + 7 * i + 3 + k) =
      [(ls.getD i (0, 0, 0, 0, 0, 0, 0)).2.2.2.1, (ls.getD i (0, 0, 0, 0, 0, 0, 0)).2.2.2.2.1,
        (ls.getD i (0, 0, 0, 0, 0, 0, 0)).2.2.2.2.2.1,
        (ls.getD i (0, 0, 0, 0, 0, 0, 0)).2.2.2.2.2.2].getD k 0 := by
  obtain ⟨-, -, a2, a3, a4, a5, a6⟩ := hls i hi
  refine ⟨a2, fun k hk => ?_⟩
  interval_cases k
  · simpa using a3
  · simpa [show AL + 7 * i + 3 + 1 = AL + 7 * i + 4 by ring] using a4
  · simpa [show AL + 7 * i + 3 + 2 = AL + 7 * i + 5 by ring] using a5
  · simpa [show AL + 7 * i + 3 + 3 = AL + 7 * i + 6 by ring] using a6

/-- **A label of a log record** (place below its count) is a region index of `N₂`. -/
theorem label_valid (hA : AEnv P W X Ok J H N₁ N₂ E c₀) {e k : ℕ} (he : e < rd c₀ bSweep 301)
    (hk : k < c₀.nmem (rd c₀ bSweep 300 + 7 * e + 2)) (hk3 : k ≤ 3) :
    c₀.nmem (rd c₀ bSweep 300 + 7 * e + 3 + k) < N₂.nRegions := by
  obtain ⟨rs, ls, -, -, -, -, hlsl, hls, -, hlsW, -, -⟩ := hA.hout
  have he' : e < ls.length := ⋄
  obtain ⟨n2, hlab⟩ := logRec_labels hls he'
  Ξ hlab k hk3
  rw [n2] at hk
  have hmem : ls.getD e (0, 0, 0, 0, 0, 0, 0) ∈ ls := by
    rw [List.getD_eq_getElem _ _ he']; exact List.getElem_mem _
  obtain ⟨-, -, b0, b1, b2, b3⟩ := hlsW _ hmem
  interval_cases k
  · exact b0 (⋄)
  · exact b1 (by simpa using hk)
  · exact b2 (by simpa using hk)
  · exact b3 (by simpa using hk)

/-- The label set of a log entry. -/
theorem logLab_eq {Q : Polygon} {N : NF} {ls : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)} {i : ℕ}
    (hi : i < ls.length) :
    logLab J Q N ls i = labSet J Q N (ls.getD i (0, 0, 0, 0, 0, 0, 0)).2.2.1
      (ls.getD i (0, 0, 0, 0, 0, 0, 0)).2.2.2.1 (ls.getD i (0, 0, 0, 0, 0, 0, 0)).2.2.2.2.1
      (ls.getD i (0, 0, 0, 0, 0, 0, 0)).2.2.2.2.2.1
      (ls.getD i (0, 0, 0, 0, 0, 0, 0)).2.2.2.2.2.2 := by
  unfold logLab logOf
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi,
    List.getD_eq_getElem _ _ hi]
  simp

/-- **A region of the label set of a log entry** is the region of a label in memory. -/
theorem label_mem {ls : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)} {m : ℕ → ℕ} {AL : ℕ}
    (hls : LogRecsAt m AL ls) {i : ℕ} (hi : i < ls.length) {V : Set Point}
    (hV : V ∈ logLab J (Qof P) N₂ ls i) :
    ∃ k, k ≤ 3 ∧ k < m (AL + 7 * i + 2) ∧
      regOf (chainModel J.right) (Qof P) N₂ (m (AL + 7 * i + 3 + k)) = V := by
  rw [logLab_eq hi] at hV
  obtain ⟨n2, hlab⟩ := logRec_labels hls hi
  obtain ⟨l, hl, rfl⟩ := hV
  rcases hl with ⟨h0, rfl⟩ | ⟨h1, rfl⟩ | ⟨h2, rfl⟩ | ⟨h3, rfl⟩
  · exact ⟨0, ⊛, ⋄, by rw [hlab 0 (⊛)]; rfl⟩
  · exact ⟨1, ⊛, ⋄, by rw [hlab 1 (⊛)]; rfl⟩
  · exact ⟨2, ⊛, ⋄, by rw [hlab 2 (⊛)]; rfl⟩
  · exact ⟨3, le_rfl, ⋄, by rw [hlab 3 le_rfl]; rfl⟩

/-- **Every entry register and label place has a slot.** -/
theorem slotPairs_cover {e k : ℕ} (he : e = eR0 ∨ e = eR1 ∨ e = eR2) (hk : k ≤ 3) :
    ∃ idx, idx < 12 ∧ (slotPairs.getD idx (0, 0)).1 = e ∧
      ∀ c : Config, Consts c → c.nreg (slotPairs.getD idx (0, 0)).2 = k := by
  rcases he with rfl | rfl | rfl <;> interval_cases k
  · exact ⟨0, ⊛, rfl, fun c h => h.1⟩
  · exact ⟨1, ⊛, rfl, fun c h => h.2.1⟩
  · exact ⟨2, ⊛, rfl, fun c h => h.2.2.2.2.2.1⟩
  · exact ⟨3, ⊛, rfl, fun c h => h.2.2.2.2.2.2⟩
  · exact ⟨4, ⊛, rfl, fun c h => h.1⟩
  · exact ⟨5, ⊛, rfl, fun c h => h.2.1⟩
  · exact ⟨6, ⊛, rfl, fun c h => h.2.2.2.2.2.1⟩
  · exact ⟨7, ⊛, rfl, fun c h => h.2.2.2.2.2.2⟩
  · exact ⟨8, ⊛, rfl, fun c h => h.1⟩
  · exact ⟨9, ⊛, rfl, fun c h => h.2.1⟩
  · exact ⟨10, ⊛, rfl, fun c h => h.2.2.2.2.2.1⟩
  · exact ⟨11, ⊛, rfl, fun c h => h.2.2.2.2.2.2⟩

/-- The slot pairs: entry registers and constant registers. -/
theorem slotPairs_facts : ∀ p ∈ slotPairs,
    (p.1 = eR0 ∨ p.1 = eR1 ∨ p.1 = eR2) ∧
      (p.2 = K0 ∨ p.2 = K1 ∨ p.2 = K2 ∨ p.2 = K3) := by
  intro p hp
  simp only [slotPairs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end

end Lab0

end SweepIo

end Chazelle.Core
