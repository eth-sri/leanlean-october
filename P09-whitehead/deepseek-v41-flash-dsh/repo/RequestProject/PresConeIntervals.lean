module

public import RequestProject.PresPosetPartialOrder
public import RequestProject.StrictOrderChains

@[expose] public section

namespace FiniteChains.PresModel
open Comb
variable {α J : Type u} (w : J → List (α × Bool))

/-- Valid attaching-circle positions are downward closed in the actual circle order. -/
theorem tCirc_valid_down {x y : TCirc w} (hxy : x ≤ y)
    (hy : y.2.1 < (w y.1).length) :
    x.1 = y.1 ∧ x.2.1 < (w y.1).length := by
  change x = y ∨ TCirc.lt w x y at hxy
  rcases hxy with rfl | hxy
  · exact ⟨rfl, hy⟩
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

/-- The strict old interval below a relator apex consists exactly of its genuine
valid attaching-circle cells; no rose cell lies in that interval. -/
theorem presPos_le_apex_iff (j : J) (p : PresPos w) :
    p ≤ apexOf w j ↔ p = apexOf w j ∨
      ∃ k t, k < (w j).length ∧ p = iCirc w (TCirc.pt w j k t) := by
  constructor
  · intro h
    cases p with
    | inr j' => exact Or.inl (congrArg Sum.inr h)
    | inl p =>
      obtain ⟨r, ⟨k, t, hk, rfl⟩, hpr⟩ := h
      cases p with
      | inl r => exact hpr.elim
      | inr c =>
        have hc := tCirc_valid_down w hpr hk
        obtain ⟨j', k', t'⟩ := c
        change j' = j ∧ k' < (w j).length at hc
        obtain ⟨rfl, hc⟩ := hc
        exact Or.inr ⟨k', t', hc, rfl⟩
  · rintro (rfl | ⟨k, t, hk, rfl⟩)
    · exact le_refl _
    · exact iCirc_le_apexOf w t hk

theorem presPos_lt_apex_iff (j : J) (p : PresPos w) :
    p < apexOf w j ↔ ∃ k t, k < (w j).length ∧ p = iCirc w (TCirc.pt w j k t) := by
  constructor
  · intro h
    rcases (presPos_le_apex_iff w j p).mp h.le with he | he
    · exact ((ne_of_lt h) he).elim
    · exact he
  · rintro ⟨k, t, hk, rfl⟩
    apply lt_of_le_of_ne (iCirc_le_apexOf w t hk)
    exact Sum.inl_ne_inr

theorem iCirc_strictMono : StrictMono (iCirc w) := by
  intro x y h
  apply lt_of_le_of_ne ((iCirc_monotone w) h.le)
  intro he
  exact (ne_of_lt h) (Sum.inr.inj (Sum.inl.inj he))

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
  change (j, k, s) = (j', k', s') ∨ TCirc.lt w (j, k, s) (j', k', s') at hl
  rcases hl with he | hl
  · exact (hn he).elim
  obtain ⟨hj, hk', htags⟩ := hl
  subst j'
  refine ⟨j, k', hk', ?_⟩
  rcases htags with ⟨hs, hs', hk⟩ | ⟨hs, hs', hk⟩ | ⟨hs, hs', hk⟩ | ⟨hs, hs', hk⟩
  · subst s; subst s'; subst k
    exact Or.inl rfl
  · subst s; subst s'; subst k
    exact Or.inr (Or.inl rfl)
  · subst s; subst s'; subst k
    exact Or.inr (Or.inr (Or.inl rfl))
  · subst s; subst s'; subst k
    exact Or.inr (Or.inr (Or.inr rfl))

end FiniteChains.PresModel
