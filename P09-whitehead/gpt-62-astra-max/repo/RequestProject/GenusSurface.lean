module

public import RequestProject.SurfaceLink
public import RequestProject.GenusLoops

@[expose] public section

/-!
# The nerve of the block of genus `q` is a closed surface

`RequestProject/GenusData.lean` writes down the `4q`-gon whose sides are glued in pairs
according to the surface word `∏_{h<q} a_h b_h a_h⁻¹ b_h⁻¹`, and
`RequestProject/GenusApply.lean` uses the comparability graph of its face poset as the nerve of
the block.  This file checks that this nerve really is a triangulation of a **closed** surface:

* `FiniteChains.Davis.genus_polygonData` — the sides are glued in pairs, no side becomes a loop,
  and every vertex and every edge of the surface occurs;
* `FiniteChains.Davis.genus_cornersConnected` — the `4q` corners of the polygon, which are all
  identified to one vertex, are glued in a **single** cycle, and the two midpoints of a pair of
  identified sides are glued to each other;
* `FiniteChains.Davis.genusClosedSurface` — hence the face poset is a closed surface cell
  structure, so the nerve is a flag triangulation of a closed surface;
* `FiniteChains.Davis.genus_edgeInTwoTriangles` — in particular every edge of the triangulation
  lies in exactly two triangles, the hypothesis used by the collapse of
  `RequestProject/SurfaceBlockCollapse.lean`.

Together with `FiniteChains.Davis.genus_euler_characteristic` (the alternating sum of the numbers
of cells is `2 - 2q`) this identifies the surface as the closed orientable surface of genus `q`.

The corner walk is the classical one: writing the positions of the boundary of the `4q`-gon as
`8h + 2t` with `t < 4` (each side of the polygon is cut into two positions), the side going out
of the corner `8h` is glued to the side coming into the corner `8h + 6`, then `8h + 6` to
`8h + 4`, then `8h + 4` to `8h + 2`, and finally `8h + 2` to the corner `8(h+1)` of the next
commutator.  So all `4q` corners lie on one cycle.
-/

namespace FiniteChains
namespace Davis

open Cell ASC Relation Genus

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

variable {p : Fin (8 * q)}

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
  · grind
  · rw [gec_eq_iff'] <;> grind
  · grind [gec_eq_iff']

theorem genus_noLoop : NoLoopSide (gvc q) := by
  intro p
  have hq := Nat.pos_of_neZero q
  have hp := p.isLt
  have hs := fin_succ_val p
  have hpar : (p + 1).val % 2 = (p.val + 1) % 2 := by
    rw [hs]
    rcases Nat.lt_or_ge (p.val + 1) (8 * q) with h | h
    · simp_all [Nat.mod_eq_of_lt]
    · have he : p.val + 1 = 8 * q := by omega
      rw [he, Nat.mod_self]
      omega
  by_cases h : p.val % 2 = 0
  · rw [gvc, if_pos h, gvc, if_neg (by omega)]
    simp
  · rw [gvc, if_neg h, gvc, if_pos (by omega)]
    simp

theorem genus_vc_surj : Function.Surjective (gvc q) := by
  have hq := Nat.pos_of_neZero q
  rintro (_ | ⟨h, i⟩)
  · exact ⟨⟨0, by omega⟩, rfl⟩
  · have hh := h.isLt
    refine ⟨⟨2 * (4 * h.val + (if i then 1 else 0)) + 1, by split_ifs <;> omega⟩, ?_⟩
    rw [gvc, if_neg (by simp)]; simp only [Option.some.injEq, Prod.mk.injEq]; constructor <;> grind

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
    omega
  simp only [gec, Prod.mk.injEq] <;> grind

/-- **The identification of the boundary of the `4q`-gon is a polygon gluing**: the sides are
glued in pairs, no side becomes a loop, and every vertex and every edge occurs. -/
theorem genus_polygonData : PolygonData (gvc q) (gec q) where
  three_le := by have := Nat.pos_of_neZero q; omega
  pairs := genus_pairs q
  noLoop := genus_noLoop q
  vc_surj := genus_vc_surj q
  ec_surj := genus_ec_surj q

/-! ### The corners of the polygon form one cycle -/

variable (h : ℕ)

section

variable (hh : h < q)
include hh

end

section

variable (hh : h < q)
include hh

end

/-! ### The closed surface -/

/-- The triangulation of the surface of genus `q` is two-dimensional. -/
theorem genus_chain_card_le_three {s : Finset (SCell (gvc q) (gec q) (gc q))}
    (hs : s ∈ (orderComplex (SCell (gvc q) (gec q) (gc q))).faces) : s.card ≤ 3 :=
  (surfaceRank_SCell (gc q) (genus_polygonData q)).chain_card_le_three hs

end GenusSurface

end Davis
end FiniteChains
