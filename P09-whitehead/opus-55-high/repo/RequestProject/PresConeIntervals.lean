import RequestProject.PresPosetPartialOrder
import RequestProject.StrictOrderChains


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
  obtain ⟨j', k', t'⟩ := y
  obtain ⟨hj, hk', htags⟩ := hxy
  subst j'
  refine ⟨rfl, ?_⟩
  rcases htags with ⟨_, _, hk⟩ | ⟨_, _, hk⟩ | ⟨_, _, hk⟩ | ⟨_, _, hk⟩
  · simp_all
  · simp_all
  · simp_all
  · rw [hk]
    exact Nat.mod_lt _ (by omega)

/-- The strict old interval below a relator apex consists exactly of its genuine
valid attaching-circle cells; no rose cell lies in that interval. -/
theorem presPos_le_apex_iff j p :
    p ≤ apexOf w j ↔ p = apexOf w j ∨
      ∃ k t, k < (w j).length ∧ p = iCirc w (TCirc.pt w j k t) := by
  constructor
  · intro h
    cases p with
    | inr j' => tauto
    | inl p =>
      obtain ⟨r, ⟨k, t, hk, rfl⟩, hpr⟩ := h
      cases p with
      | inl r => exact hpr.elim
      | inr c =>
        have hc := tCirc_valid_down w hpr hk
        aesop
  · rintro (rfl | ⟨k, t, hk, rfl⟩)
    · rfl
    · exact iCirc_le_apexOf w t hk

theorem presPos_lt_apex_iff j p :
    p < apexOf w j ↔ ∃ k t, k < (w j).length ∧ p = iCirc w (TCirc.pt w j k t) := by
  constructor
  · intro h
    rcases (presPos_le_apex_iff w j p).mp h.le with he | he
    · simp_all
    · exact he
  · rintro ⟨k, t, hk, rfl⟩
    apply lt_of_le_of_ne (iCirc_le_apexOf w t hk)
    exact Sum.inl_ne_inr


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
  · tauto
  obtain ⟨hj, hk', htags⟩ := hl
  subst j'
  refine ⟨j, k', hk', ?_⟩
  aesop
