module

public import RequestProject.PresPosetPartialOrder
public import RequestProject.StrictOrderChains

@[expose] public section

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (w : J → List (α × Bool))

/-- Valid attaching-circle positions are downward closed in the actual circle order. -/
theorem tCirc_valid_down {x y : TCirc w} (hxy : x ≤ y)
    (hy : y.2.1 < (w y.1).length) :
    x.1 = y.1 ∧ x.2.1 < (w y.1).length := by
  rcases hxy with rfl | hxy
  · simp_all
  obtain ⟨j, k, t⟩ := x
  obtain ⟨j', k', t'⟩ := y
  obtain ⟨hj, hk', htags⟩ := hxy
  subst j'
  refine ⟨rfl, ?_⟩
  rcases htags with ⟨_, _, hk⟩ | ⟨_, _, hk⟩ | ⟨_, _, hk⟩ | ⟨_, _, hk⟩
  · exact hk ▸ hk'
  · exact hk ▸ hk'
  · exact hk ▸ hk'
  · rw [hk]
    exact Nat.mod_lt _ (by omega)

variable (j : J) (p : PresPos w)

/-- The strict old interval below a relator apex consists exactly of its genuine
valid attaching-circle cells; no rose cell lies in that interval. -/
theorem presPos_le_apex_iff :
    p ≤ apexOf w j ↔ p = apexOf w j ∨
      ∃ k t, k < (w j).length ∧ p = iCirc w (TCirc.pt w j k t) := by
  constructor
  · intro h
    cases p with
    | inr j' => solve_by_elim
    | inl p =>
      obtain ⟨r, ⟨k, t, hk, rfl⟩, hpr⟩ := h
      cases p with
      | inl r => exact hpr.elim
      | inr c =>
        have hc := tCirc_valid_down w hpr hk
        obtain ⟨j', k', t'⟩ := c
        obtain ⟨rfl, hc⟩ := hc; exact Or.inr ⟨k', t', hc, rfl⟩
  · grind [iCirc_le_apexOf]

theorem presPos_lt_apex_iff :
    p < apexOf w j ↔ ∃ k t, k < (w j).length ∧ p = iCirc w (TCirc.pt w j k t) := by
  constructor
  · intro h
    rcases (presPos_le_apex_iff w j p).mp h.le with he | he <;> simp_all
  · rintro ⟨k, t, hk, rfl⟩
    solve_by_elim [iCirc_le_apexOf]

theorem iCirc_strictMono : StrictMono (iCirc w) := by
  solve_by_elim

/-- The only strict circle edges are the four incidences for a valid letter position. -/
theorem tCirc_strict_edge_cases (e : StrictOrdEdge (TCirc w)) :
    ∃ j k, k < (w j).length ∧
      (e.1 = (TCirc.pt w j k CPos.cor, TCirc.pt w j k CPos.cedgL) ∨
       e.1 = (TCirc.pt w j k CPos.cmid, TCirc.pt w j k CPos.cedgL) ∨
       e.1 = (TCirc.pt w j k CPos.cmid, TCirc.pt w j k CPos.cedgR) ∨
       e.1 = (TCirc.pt w j (TCirc.csucc w j k) CPos.cor, TCirc.pt w j k CPos.cedgR)) := by
  rcases e with ⟨⟨⟨j, k, s⟩, ⟨j', k', s'⟩⟩, h⟩
  have hn := ne_of_lt h
  have hl := h.le
  rcases hl with he | hl
  · solve_by_elim
  obtain ⟨hj, hk', htags⟩ := hl
  refine ⟨j, k', hk', ?_⟩ <;> aesop

end FiniteChains.PresModel
