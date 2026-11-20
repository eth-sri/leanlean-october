module

public import RequestProject.SurfaceRegular
public import RequestProject.GenusLoops

@[expose] public section

/-! Incidence data of the polygon for the genus `q` block. -/


namespace FiniteChains
namespace Davis

open Cell ASC Genus

section GenusSurface

variable (q : ℕ) [NeZero q]

/-! ### Reading the labels -/

omit [NeZero q] in
/-- Two positions of the boundary carry the same edge of the surface exactly when they agree on
the commutator, on the letter, and on the half of the side. -/
theorem gec_eq_iff' (m n : Fin (8 * q)) :
    gec q m = gec q n ↔
      (m.val / 2 / 4 = n.val / 2 / 4 ∧
        m.val / 2 % 4 % 2 = n.val / 2 % 4 % 2 ∧
        (m.val % 2 + (if 2 ≤ m.val / 2 % 4 then 1 else 0)) % 2
          = (n.val % 2 + (if 2 ≤ n.val / 2 % 4 then 1 else 0)) % 2) := by
  have hm2 : m.val % 2 = 0 ∨ m.val % 2 = 1 := by omega
  have hn2 : n.val % 2 = 0 ∨ n.val % 2 = 1 := by omega
  by_cases h2 : 2 ≤ m.val / 2 % 4 <;> by_cases h4 : 2 ≤ n.val / 2 % 4 <;>
    rcases hm2 with h1 | h1 <;> rcases hn2 with h3 | h3 <;>
    simp [gec, Prod.ext_iff, Fin.ext_iff, decide_eq_decide, h1, h2, h3, h4] <;> omega

/-! ### The polygon data of the surface of genus `q` -/

theorem genus_pairs : EdgePairs (gec q) := by
  intro i
  have hq := Nat.pos_of_neZero q
  have hi := i.isLt
  have hh : i.val / 2 / 4 < q := by omega
  have hmlt : 8 * (i.val / 2 / 4) + 2 * (if i.val / 2 % 4 < 2 then i.val / 2 % 4 + 2
      else i.val / 2 % 4 - 2) + (1 - i.val % 2) < 8 * q := by
    split_ifs <;> omega
  refine ⟨⟨_, hmlt⟩, ?_, ?_, ?_⟩
  · rw [Ne, Fin.ext_iff]
    simp only []
    split_ifs <;> omega
  · rw [gec_eq_iff']
    refine ⟨?_, ?_, ?_⟩ <;> simp only [] <;> split_ifs <;> omega
  · grind [gec_eq_iff']

theorem genus_noLoop : NoLoopSide (gvc q) := by
  intro p
  have hq := Nat.pos_of_neZero q
  have hp := p.isLt
  have hs  := fin_succ_val p
  have hpar : (p + 1).val % 2 = (p.val + 1) % 2 := by
    rw [hs]
    rcases Nat.lt_or_ge (p.val + 1) (8 * q) with h | h
    · rw [Nat.mod_eq_of_lt h]
    · have he : p.val + 1 = 8 * q := by omega
      rw [he, Nat.mod_self]
      omega
  grind [gvc]

theorem genus_vc_surj : Function.Surjective (gvc q) := by
  have hq := Nat.pos_of_neZero q
  rintro (_ | ⟨h, i⟩)
  · exact ⟨⟨0, by omega⟩, rfl⟩
  · have hh := h.isLt
    refine ⟨⟨2 * (4 * h.val + (if i then 1 else 0)) + 1, by split_ifs <;> omega⟩, ?_⟩
    have hval : (⟨2 * (4 * h.val + (if i then 1 else 0)) + 1, by split_ifs <;> omega⟩ :
        Fin (8 * q)).val = 2 * (4 * h.val + (if i then 1 else 0)) + 1 := rfl
    rw [gvc, if_neg (by simp)]
    simp only [Option.some.injEq, Prod.mk.injEq]
    constructor
    · apply Fin.ext
      grind
    · have e2 : (2 * (4 * h.val + (if i then 1 else 0)) + 1) / 2 % 4 % 2
          = (if i then 1 else 0) := by
        split_ifs <;> omega
      show decide ((2 * (4 * h.val + (if i then 1 else 0)) + 1) / 2 % 4 % 2 = 1) = i
      rw [e2]
      simp

theorem genus_ec_surj : Function.Surjective (gec q) := by
  have hq := Nat.pos_of_neZero q
  rintro ⟨h, i, b⟩
  have hh := h.isLt
  refine ⟨⟨2 * (4 * h.val + (if i then 1 else 0)) + (if b then 1 else 0), by
    split_ifs <;> omega⟩, ?_⟩
  have e1 : (2 * (4 * h.val + (if i then 1 else 0)) + (if b then 1 else 0)) / 2 / 4 = h.val := by
    split_ifs <;> omega
  have e2 : (2 * (4 * h.val + (if i then 1 else 0)) + (if b then 1 else 0)) / 2 % 4 =
      (if i then 1 else 0) := by
    split_ifs <;> omega
  have e3 : (2 * (4 * h.val + (if i then 1 else 0)) + (if b then 1 else 0)) % 2 =
      (if b then 1 else 0) := by
    split_ifs <;> omega
  simp only [gec, Prod.mk.injEq]
  refine ⟨Fin.ext ?_, ?_, ?_⟩
  · assumption
  · show decide ((2 * (4 * h.val + (if i then 1 else 0)) + (if b then 1 else 0)) / 2 % 4 % 2 = 1)
      = i
    rw [e2]
    cases i <;> simp
  · show (decide ((2 * (4 * h.val + (if i then 1 else 0)) + (if b then 1 else 0)) % 2 = 1) ^^
      decide (2 ≤ (2 * (4 * h.val + (if i then 1 else 0)) + (if b then 1 else 0)) / 2 % 4)) = b
    rw [e2, e3]
    cases i <;> cases b <;> simp

/-- **The identification of the boundary of the `4q`-gon is a polygon gluing**: the sides are
glued in pairs, no side becomes a loop, and every vertex and every edge occurs. -/
theorem genus_polygonData : PolygonData (gvc q) (gec q) where
  three_le := by have := Nat.pos_of_neZero q; omega
  pairs := genus_pairs q
  noLoop := genus_noLoop q
  vc_surj := genus_vc_surj q
  ec_surj := genus_ec_surj q

theorem genus_chain_card_le_three {s : Finset (SCell (gvc q) (gec q) (gc q))}
    (hs : s ∈ (orderComplex (SCell (gvc q) (gec q) (gc q))).faces) : s.card ≤ 3 :=
  (surfaceRank_SCell (gc q) (genus_polygonData q)).chain_card_le_three hs

end GenusSurface

end Davis
end FiniteChains
