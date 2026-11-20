module

public import PottsDiscontinuity.TorusCrossing.Exclusion
public import PottsDiscontinuity.TorusCrossing.Cut
public import PottsDiscontinuity.Duality.FiniteGraphBoundaryParity

/-!
# Existence: a missing primal connection forces a dual connection

If two primal cells joined by a closed edge `m` are not connected (rows wired), the dual
endpoints of `m` are connected in the complementary dual configuration (side columns wired).
The proof applies the handshake lemma to the dual graph of the cut edges of the primal component
of one endpoint.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusCrossing

open PottsDiscontinuity
open scoped Classical

namespace Rect

variable (R : Rect)

/-- Dual graph with the edges carried by `E ⊆ inner`. -/
noncomputable abbrev dualOf (E : Finset Cell) : SimpleGraph R.dcells :=
  endGraph dualEnds R.dcells E

theorem dData_mono {E : Finset Cell} (hE : E ⊆ R.inner) : EndData dualEnds R.dcells E where
  mem m hm := R.dData.mem m (hE hm)
  ne := R.dData.ne
  inj := R.dData.inj

/-- Degree of an odd cell in the dual graph of `E`: the number of corners lying in `E`. -/
theorem dualOf_degree {E : Finset Cell} (hE : E ⊆ R.inner) (z : R.dcells) :
    (R.dualOf E).degree z = (E.filter (fun m => m ∈ corners z.1)).card := by
  have hz : ¬ IsPrimal z.1 := (mem_dcells.1 z.2).2
  rw [degree_eq (R.dData_mono hE)]
  congr 1
  apply Finset.filter_congr
  intro m _
  exact mem_dualEnds_iff z.1 m hz

/-- **Handshake for the dual graph.** -/
theorem dual_reachable_of_odd {E : Finset Cell} (hE : E ⊆ R.inner) (B T : Finset R.dcells)
    (heven : ∀ z : R.dcells, z ∉ B → z ∉ T → Even (E.filter (fun m => m ∈ corners z.1)).card)
    (hodd : Odd (∑ z ∈ B, (E.filter (fun m => m ∈ corners z.1)).card)) :
    ∃ b ∈ B, ∃ t ∈ T, (R.dualOf E).Reachable b t := by
  apply FK.exists_reachable_between_of_odd_degree_sum (R.dualOf E) B T
  · intro v hv
    rw [dualOf_degree R hE]
    grind [Finset.mem_union_left]
  · simpa only [dualOf_degree R hE] using hodd

/-- Reachability in the dual graph of `E` gives actual open connectivity for a larger set. -/
theorem dualOf_actualConnected {E D : Finset Cell} (hED : E ⊆ D) (hD : D ⊆ R.inner)
    {x y : R.dcells} (h : (R.dualOf E).Reachable x y) :
    FK.ActualConnected R.dG (cfgOf R.dData D) x y := by
  have hle : R.dualOf E ≤ FK.openGraph R.dG (cfgOf R.dData D) := by
    intro a b hab
    rw [dualOf, endGraph_adj] at hab
    rw [openGraph_adj_iff R.dData, openMedials_cfgOf R.dData D hD]
    rcases hab.2 with ⟨m, hm, h⟩ | ⟨m, hm, h⟩ <;>
      exact ⟨m, hED hm, by tauto⟩
  exact h.mono hle

/-- Reachability in `dualOf E` implies the component relation of any larger configuration. -/
theorem dualOf_reachable_le {E D : Finset Cell} (hED : E ⊆ D) (hD : D ⊆ R.inner)
    (ξ : FK.BoundaryCondition R.dcells) {x y : R.dcells} (h : (R.dualOf E).Reachable x y) :
    (FK.componentSetoid R.dG ξ (cfgOf R.dData D)).r x y :=
  FK.actualConnected_component _ _ _ (R.dualOf_actualConnected hED hD h)

/-- The cells of the primal component of `u` (as a predicate on all cells). -/
def compPred (A : Finset Cell) (u : R.pcells) (c : Cell) : Prop :=
  ∃ hc : c ∈ R.pcells, (FK.componentSetoid R.pG R.sepBC (cfgOf R.pData A)).r ⟨c, hc⟩ u

private theorem compPred_subtype (A : Finset Cell) (u x : R.pcells) :
    R.compPred A u x.1 ↔ (FK.componentSetoid R.pG R.sepBC (cfgOf R.pData A)).r x u :=
  ⟨fun ⟨_, h⟩ => h, fun h => ⟨x.2, h⟩⟩

/-- The cut edges of the board for a vertex predicate. -/
noncomputable def cutSet (X : Cell → Prop) : Finset Cell := R.inner.filter (IsCut X)

theorem mem_cutSet {X : Cell → Prop} {m : Cell} : m ∈ R.cutSet X ↔ m ∈ R.inner ∧ IsCut X m := by
  unfold cutSet; simp

theorem compPred_iff {A : Finset Cell} {u : R.pcells} {x y : R.pcells}
    (hxy : (FK.componentSetoid R.pG R.sepBC (cfgOf R.pData A)).r x y) :
    R.compPred A u x.1 ↔ R.compPred A u y.1 := by
  rw [compPred_subtype, compPred_subtype]
  exact ⟨fun h => (FK.componentSetoid _ _ _).trans ((FK.componentSetoid _ _ _).symm hxy) h,
    fun h => (FK.componentSetoid _ _ _).trans hxy h⟩

/-- Open edges are never cut by a component predicate. -/
theorem not_cut_of_mem {A : Finset Cell} (hA : A ⊆ R.inner) (u : R.pcells) {m : Cell}
    (hm : m ∈ A) : ¬ IsCut (R.compPred A u) m := by
  intro hcut
  unfold IsCut at hcut
  have hmi := hA hm
  have hmem := R.pData.mem m hmi
  apply hcut
  have hadj : (FK.openGraph R.pG (cfgOf R.pData A)).Adj ⟨(primalEnds m).1, hmem.1⟩
      ⟨(primalEnds m).2, hmem.2⟩ := by
    rw [openGraph_adj_iff R.pData, openMedials_cfgOf R.pData A hA]
    exact ⟨m, hm, Or.inl rfl⟩
  have hrel := FK.actualConnected_component R.pG R.sepBC (cfgOf R.pData A)
    (FK.actualConnected_of_adj R.pG _ hadj)
  exact propext (R.compPred_iff hrel)

/-- Cells of the bottom row are related by the wiring. -/
theorem bottom_related (A : Finset Cell) {x y : R.pcells} (hx : x.1.2 = R.y0) (hy : y.1.2 = R.y0) :
    (FK.componentSetoid R.pG R.sepBC (cfgOf R.pData A)).r x y :=
  FK.boundary_component R.pG R.sepBC _ (Or.inr (Or.inl ⟨hx, hy⟩))

theorem top_related (A : Finset Cell) {x y : R.pcells} (hx : x.1.2 = R.y0 + R.h)
    (hy : y.1.2 = R.y0 + R.h) :
    (FK.componentSetoid R.pG R.sepBC (cfgOf R.pData A)).r x y :=
  FK.boundary_component R.pG R.sepBC _ (Or.inr (Or.inr ⟨hx, hy⟩))


theorem cutSet_filter_corners (X : Cell → Prop) (z : Cell) :
    (R.cutSet X).filter (fun m => m ∈ corners z) =
      (corners z).filter (fun m => m ∈ R.inner ∧ IsCut X m) := by
  ext m
  simp only [mem_cutSet, Finset.mem_filter]
  tauto

theorem outer_pcells (z : R.dcells) (hx1 : R.x0 < z.1.1) (hx2 : z.1.1 < R.x0 + R.w) :
    (z.1.1 - 1, z.1.2) ∈ R.pcells ∧ (z.1.1 + 1, z.1.2) ∈ R.pcells := by
  have hz := mem_dcells.1 z.2
  rw [mem_cells] at hz
  unfold IsPrimal at hz
  constructor <;> rw [mem_pcells, mem_cells] <;> unfold IsPrimal <;> dsimp only <;> omega

theorem compPred_cutSet_even (hh : 0 < R.h) (A : Finset Cell) (u : R.pcells) (z : R.dcells)
    (hx1 : R.x0 < z.1.1) (hx2 : z.1.1 < R.x0 + R.w) :
    Even ((R.cutSet (R.compPred A u)).filter (fun m => m ∈ corners z.1)).card := by
  rw [cutSet_filter_corners]
  have hz := mem_dcells.1 z.2
  have hzc := mem_cells.1 hz.1
  obtain ⟨hW, hE⟩ := R.outer_pcells z hx1 hx2
  apply cut_deg_even R hh _ z.1 hz.2 hx1 hx2 hzc.2.2.1 hzc.2.2.2
  · intro hb
    exact R.compPred_iff (u := u) (x := ⟨_, hW⟩) (y := ⟨_, hE⟩)
      (R.bottom_related A (by exact hb) (by exact hb))
  · intro ht
    exact R.compPred_iff (u := u) (x := ⟨_, hW⟩) (y := ⟨_, hE⟩)
      (R.top_related A (by exact ht) (by exact ht))


/-- **Existence.**  If two primal cells joined by a closed edge `m₀` are not connected (rows
wired), then the dual endpoints of `m₀` are connected in the complementary dual configuration
(side columns wired). -/
theorem existence (hh : 0 < R.h) (A : Finset Cell) (hA : A ⊆ R.inner) (m₀ : Cell)
    (hm₀ : m₀ ∈ R.inner) (u v : R.pcells) (hu : u.1 = (primalEnds m₀).1)
    (hv : v.1 = (primalEnds m₀).2) (u' v' : R.dcells) (hu' : u'.1 = (dualEnds m₀).1)
    (hv' : v'.1 = (dualEnds m₀).2)
    (hnot : ¬ (FK.componentSetoid R.pG R.sepBC (cfgOf R.pData A)).r u v) :
    (FK.componentSetoid R.dG R.dualBC (cfgOf R.dData (R.inner \ insert m₀ A))).r u' v' := by
  let X := R.compPred A u
  let E := R.cutSet X
  let E' := E.erase m₀
  let D := R.inner \ insert m₀ A
  let sD := FK.componentSetoid R.dG R.dualBC (cfgOf R.dData D)
  let Side (a : R.dcells) := a.1.1 = R.x0 ∨ a.1.1 = R.x0 + R.w
  have hmE : m₀ ∈ E := by
    change m₀ ∈ R.cutSet X
    rw [mem_cutSet, IsCut, ← hu, ← hv]
    simp [hm₀, X, compPred_subtype, Setoid.refl]
    exact fun h => hnot ((FK.componentSetoid _ _ _).symm h)
  have hDsub : D ⊆ R.inner := Finset.sdiff_subset
  have hsub : E' ⊆ D := by
    intro m hm
    obtain ⟨hne, hmR, hc⟩ := (Finset.mem_erase.1 hm).imp_right (R.mem_cutSet.1 ·)
    exact Finset.mem_sdiff.2 ⟨hmR, by simp [hne, show m ∉ A from fun h => R.not_cut_of_mem hA u h hc]⟩
  have hpar (z : R.dcells) (hz : ¬Side z) :
      Even (E'.filter (fun m => m ∈ corners z.1)).card ↔ ¬(z = u' ∨ z = v') := by
    have hzc := mem_cells.1 (mem_dcells.1 z.2).1
    dsimp [Side] at hz
    have hev : Even (E.filter (fun m => m ∈ corners z.1)).card :=
      R.compPred_cutSet_even hh A u z (by omega) (by omega)
    have hiff : m₀ ∈ E.filter (fun m => m ∈ corners z.1) ↔ z = u' ∨ z = v' := by
      simp only [Finset.mem_filter, hmE, true_and, ← Subtype.val_inj, hu', hv']
      exact (mem_dualEnds_iff z.1 m₀ (mem_dcells.1 z.2).2).symm
    change Even ((E.erase m₀).filter _).card ↔ _
    rw [Finset.filter_erase]
    by_cases h : m₀ ∈ E.filter (fun m => m ∈ corners z.1)
    · have hp := Finset.card_pos.2 ⟨m₀, h⟩
      rw [Finset.card_erase_of_mem h, ← hiff]
      simp only [h, not_true_eq_false, iff_false, Nat.even_iff] 
      rw [Nat.even_iff] at hev
      omega
    · simp [← hiff, h, hev]
  have escape (a b : R.dcells) (hab : ∀ z, (z = u' ∨ z = v') ↔ (z = a ∨ z = b)) :
      sD.r a b ∨ ∃ t, Side t ∧ sD.r a t := by
    by_cases hs : Side a
    · exact Or.inr ⟨a, hs, sD.refl a⟩
    let T := Finset.univ.filter fun t : R.dcells => Side t ∨ t = b
    obtain ⟨x, hx, t, ht, hr⟩ := R.dual_reachable_of_odd (hsub.trans hDsub) {a} T
      (by
        intro z hz hzt
        simp only [Finset.mem_singleton] at hz
        simp only [T, Finset.mem_filter, Finset.mem_univ, true_and, not_or] at hzt
        exact (hpar z hzt.1).2 ((hab z).not.2 (not_or.2 ⟨hz, hzt.2⟩)))
      (by rw [Finset.sum_singleton, ← Nat.not_even_iff_odd, hpar a hs, hab]; simp)
    rw [Finset.mem_singleton] at hx
    subst x
    have hrt : sD.r a t := R.dualOf_reachable_le hsub hDsub R.dualBC hr
    rcases (show Side t ∨ t = b from (Finset.mem_filter.1 ht).2) with ht | rfl
    · exact Or.inr ⟨t, ht, hrt⟩
    · exact Or.inl hrt
  rcases escape u' v' (fun _ => Iff.rfl) with huv | ⟨t, ht, hrt⟩
  · exact huv
  rcases escape v' u' (fun _ => or_comm) with hvu | ⟨s, hs, hrs⟩
  · exact sD.symm hvu
  exact sD.trans hrt (sD.trans (FK.boundary_component _ _ _ (Or.inr ⟨ht, hs⟩)) (sD.symm hrs))

end Rect

end PottsDiscontinuity.TorusCrossing
