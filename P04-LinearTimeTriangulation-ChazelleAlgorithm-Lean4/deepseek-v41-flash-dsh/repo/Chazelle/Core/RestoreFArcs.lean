module

public import Chazelle.Core.RestoreFStart

/-!
# WP-E, the search on the RAM (`FindOK`), part 30: the arcs of the region

When the region has an exit chord, every arc of it meets `ArcOK` (proper ends on the walk, inside
the box band, normalised ends inner or vertices, weight `≤ γ`).
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Machine Machine.Stmt Programs SweepPrim

variable {E : FEnv} {c₀ : Config}

theorem FGood.kind (hE : FGood E c₀) :
    (∃ C : Chain, C.P.Simple ∧ E.M = chainModel C) ∨ E.M = interiorModel (Qof E.P) := by
  rcases hE.hOkM _ _ hE.hOk with ⟨H, C, -, -, -, hs, hM⟩ | hI
  · exact Or.inl ⟨C, hs, hM⟩
  · exact Or.inr hI

theorem FGood.end_ok (hE : FGood E c₀) {x : WPos}
    (hx : ProperPos E.M (Qof E.P) (Qof E.P).n x) (hk : E.M.key (Qof E.P) x < E.M.W.n)
    (hy : ∀ C : Chain, E.M = chainModel C → |(E.M.pos (Qof E.P) x).2| < C.radius) :
    x.edge < E.M.W.n ∧
      ((normOf E.M (Qof E.P) x).hgt = 0 ∨ E.M.InnerPt (E.M.pos (Qof E.P) x)) := by
  have hQn : (Qof E.P).n = E.P.n := shear_n _ _
  rw [hQn] at hx
  obtain ⟨-, -, hpos, -, hcase⟩ := normOf_facts hx
  have hkey : E.M.key (Qof E.P) x = x.edge + E.M.param (Qof E.P) x := rfl
  have hxe : x.edge < E.M.W.n := by
    have : (x.edge : ℝ) < E.M.W.n := by linarith [hx.1]
    exact_mod_cast this
  refine ⟨hxe, ?_⟩
  rcases hcase with h0 | hp
  · exact Or.inl h0
  right
  have hp' : 0 < E.M.param (Qof E.P) x := by
    unfold normOf at hp; split_ifs at hp with hz
    · simp at hp
    · exact hp
  rcases hE.kind with ⟨C, -, hM⟩ | hM
  · have hy' := hy C hM
    rw [hM] at hxe hx hy' ⊢
    exact innerPt_chain_walk C (Qof E.P) hxe hx.1 hx.2.1.le hy'
  · rw [hM] at hxe hx ⊢
    have hn3 : 3 ≤ (Qof E.P).n := by rw [hQn]; exact hE.hG.1.1
    obtain ⟨e, h⟩ := x
    exact innerPt_mi_edge (ShootCut.goodEnv_distinct hE.hG) hn3
      (by rw [IOrc.mi_n] at hxe; exact hxe) (by rw [hM] at hp'; exact hp') hx.2.1

theorem FGood.arc_abs (hE : FGood E c₀) (hne : (E.N.F E.M (Qof E.P)).Nonempty) {j : ℕ}
    (hj : j < E.N.arcs.length) :
    (∀ C : Chain, E.M = chainModel C → |(E.M.pos (Qof E.P) (E.N.arc j).s).2| < C.radius) ∧
      (∀ C : Chain, E.M = chainModel C → |(E.M.pos (Qof E.P) (E.N.arc j).e).2| < C.radius) := by
  refine ⟨fun C hM => ?_, fun C hM => ?_⟩ <;>
  · obtain ⟨C', hs, hM'⟩ : ∃ C' : Chain, C'.P.Simple ∧ E.M = chainModel C' := by
      rcases hE.kind with h | hI
      · exact h
      · exact absurd (hM.symm.trans hI) (chainModel_ne_interior C (Qof E.P))
    have hNF := hE.hNF
    rw [hM'] at hNF hne
    have := arc_abs_lt hs hNF hne hj
    rw [radius_eq_of_model (hM.symm.trans hM'), hM']
    first | exact this.1 | exact this.2

/-- **The arcs of a region with an exit chord.** -/
theorem FGood.arcOK (hE : FGood E c₀) (hch : (E.N.region E.r).chords ≠ []) {t : ℕ}
    (ht : t < (E.N.region E.r).arcs.length) : ArcOK E t := by
  have hr : E.r < E.N.nRegions := hE.hr
  obtain ⟨-, -, -, reg, hRC, -, hArcs, hRg, -, -, hpp⟩ := hE.hNF
  have hQn : (Qof E.P).n = E.P.n := shear_n _ _
  -- the family is nonempty
  have hne : (E.N.F E.M (Qof E.P)).Nonempty := by
    obtain ⟨i, hi⟩ := List.exists_mem_of_ne_nil _ hch
    obtain ⟨hi', -⟩ := ((hRg E.r hr).1 i).1 hi
    have hmem : E.N.chord i ∈ E.N.chords := by
      unfold NF.chord
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
      exact List.getElem_mem hi'
    exact ⟨_, E.N.chord i, hmem, rfl⟩
  set j := (E.N.region E.r).arcs.getD t 0 with hjdef
  have hjm : j ∈ (E.N.region E.r).arcs := by
    rw [hjdef, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht, Option.getD_some]
    exact List.getElem_mem ht
  obtain ⟨hj, -⟩ := (hArcs.2.2.2 E.r hr j).1 hjm
  obtain ⟨hjr, harc⟩ := hArcs.1 j hj
  have hU := hRC.1 _ hjr
  obtain ⟨-, ha, -, hb, -⟩ := harc
  obtain ⟨sy, ey⟩ := hE.arc_abs hne hj
  have hs := hE.end_ok (hpp j hj).1 ha sy
  have he := hE.end_ok (hpp j hj).2 hb ey
  have hps : ProperPos E.M (Qof E.P) E.P.n (E.N.arc j).s := by rw [← hQn]; exact (hpp j hj).1
  have hpe : ProperPos E.M (Qof E.P) E.P.n (E.N.arc j).e := by rw [← hQn]; exact (hpp j hj).2
  exact ⟨ht, hj, hs.1, he.1, hps, hpe, sy, ey, hs.2, he.2,
    (BoxT.arcWt_le_weight (hArcs.1 j hj).2).trans (hE.hsg _ hU)⟩

end

end Restore

end Chazelle.Core
