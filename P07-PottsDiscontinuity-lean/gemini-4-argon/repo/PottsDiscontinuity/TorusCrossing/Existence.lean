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

theorem dualOf_degree {E : Finset Cell} (hE : E ⊆ R.inner) (z : R.dcells) :
    (R.dualOf E).degree z = (E.filter (fun m => m ∈ corners z.1)).card := by
  rw [degree_eq (R.dData_mono hE)]
  exact congrArg Finset.card (Finset.filter_congr fun m _ =>
    mem_dualEnds_iff z.1 m (mem_dcells.1 z.2).2)

theorem dual_reachable_of_odd {E : Finset Cell} (hE : E ⊆ R.inner) (B T : Finset R.dcells)
    (hdisj : Disjoint B T)
    (heven : ∀ z : R.dcells, z ∉ B → z ∉ T → Even (E.filter (fun m => m ∈ corners z.1)).card)
    (hodd : Odd (∑ z ∈ B, (E.filter (fun m => m ∈ corners z.1)).card)) :
    ∃ b ∈ B, ∃ t ∈ T, (R.dualOf E).Reachable b t :=
  FK.exists_reachable_between_of_odd_degree_sum (R.dualOf E) B T hdisj
    (fun v hv => by
      rw [dualOf_degree R hE]
      exact heven v (fun h => hv (Finset.mem_union_left _ h)) (fun h => hv (Finset.mem_union_right _ h)))
    (by simpa only [dualOf_degree R hE] using hodd)

theorem dualOf_reachable_le {E D : Finset Cell} (hED : E ⊆ D) (hD : D ⊆ R.inner)
    (ξ : FK.BoundaryCondition R.dcells) {x y : R.dcells} (h : (R.dualOf E).Reachable x y) :
    (FK.componentSetoid R.dG ξ (cfgOf R.dData D)).r x y := by
  have hle : (R.dualOf E).reachableSetoid ≤ FK.componentSetoid R.dG ξ (cfgOf R.dData D) := by
    apply FK.reachableSetoid_le_of_adj
    intro a b hab
    rw [dualOf, endGraph_adj] at hab
    apply FK.actualConnected_component
    apply FK.actualConnected_of_adj
    rw [openGraph_adj_iff R.dData, openMedials_cfgOf R.dData D hD]
    rcases hab.2 with ⟨m, hm, h⟩ | ⟨m, hm, h⟩ <;>
      [exact ⟨m, hED hm, Or.inl h⟩; exact ⟨m, hED hm, Or.inr h⟩]
  exact hle h

def compPred (A : Finset Cell) (u : R.pcells) (c : Cell) : Prop :=
  ∃ hc : c ∈ R.pcells, (FK.componentSetoid R.pG R.sepBC (cfgOf R.pData A)).r ⟨c, hc⟩ u

noncomputable def cutSet (X : Cell → Prop) : Finset Cell := R.inner.filter (IsCut X)

theorem mem_cutSet {X : Cell → Prop} {m : Cell} : m ∈ R.cutSet X ↔ m ∈ R.inner ∧ IsCut X m :=
  Finset.mem_filter

theorem compPred_iff {A : Finset Cell} {u : R.pcells} {x y : R.pcells}
    (hxy : (FK.componentSetoid R.pG R.sepBC (cfgOf R.pData A)).r x y) :
    R.compPred A u x.1 ↔ R.compPred A u y.1 :=
  ⟨fun ⟨_, h⟩ => ⟨y.2, (FK.componentSetoid R.pG R.sepBC _).trans
    ((FK.componentSetoid R.pG R.sepBC _).symm hxy) h⟩,
   fun ⟨_, h⟩ => ⟨x.2, (FK.componentSetoid R.pG R.sepBC _).trans hxy h⟩⟩

theorem not_cut_of_mem {A : Finset Cell} (hA : A ⊆ R.inner) (u : R.pcells) {m : Cell}
    (hm : m ∈ A) : ¬ IsCut (R.compPred A u) m := fun hcut => by
  have hmem := R.pData.mem m (hA hm)
  exact hcut (propext (R.compPred_iff (FK.actualConnected_component R.pG R.sepBC _
    (FK.actualConnected_of_adj R.pG _ (by
      rw [openGraph_adj_iff R.pData (cfgOf R.pData A) ⟨(primalEnds m).1, hmem.1⟩ ⟨(primalEnds m).2, hmem.2⟩,
        openMedials_cfgOf R.pData A hA]
      exact ⟨m, hm, Or.inl rfl⟩)))))

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
  ext m; simp only [mem_cutSet, Finset.mem_filter]; tauto

theorem outer_pcells (z : R.dcells) (hx1 : R.x0 < z.1.1) (hx2 : z.1.1 < R.x0 + R.w) :
    (z.1.1 - 1, z.1.2) ∈ R.pcells ∧ (z.1.1 + 1, z.1.2) ∈ R.pcells := by
  have hz := mem_dcells.1 z.2
  rw [mem_cells] at hz; unfold IsPrimal at hz
  constructor <;> rw [mem_pcells, mem_cells] <;> unfold IsPrimal <;> dsimp only <;> omega

theorem compPred_cutSet_even (hh : 0 < R.h) (A : Finset Cell) (u : R.pcells) (z : R.dcells)
    (hx1 : R.x0 < z.1.1) (hx2 : z.1.1 < R.x0 + R.w) :
    Even ((R.cutSet (R.compPred A u)).filter (fun m => m ∈ corners z.1)).card := by
  rw [cutSet_filter_corners]
  have hz := mem_dcells.1 z.2
  have hzc := mem_cells.1 hz.1
  obtain ⟨hW, hE⟩ := R.outer_pcells z hx1 hx2
  exact cut_deg_even R hh _ z.1 hz.2 hx1 hx2 hzc.2.2.1 hzc.2.2.2
    (fun hb => R.compPred_iff (R.bottom_related A (x := ⟨_, hW⟩) (y := ⟨_, hE⟩) hb hb))
    (fun ht => R.compPred_iff (R.top_related A (x := ⟨_, hW⟩) (y := ⟨_, hE⟩) ht ht))

theorem existence (hh : 0 < R.h) (A : Finset Cell) (hA : A ⊆ R.inner) (m₀ : Cell)
    (hm₀ : m₀ ∈ R.inner) (u v : R.pcells) (hu : u.1 = (primalEnds m₀).1)
    (hv : v.1 = (primalEnds m₀).2) (u' v' : R.dcells) (hu' : u'.1 = (dualEnds m₀).1)
    (hv' : v'.1 = (dualEnds m₀).2)
    (hnot : ¬ (FK.componentSetoid R.pG R.sepBC (cfgOf R.pData A)).r u v) :
    (FK.componentSetoid R.dG R.dualBC (cfgOf R.dData (R.inner \ insert m₀ A))).r u' v' := by
  set X := R.compPred A u
  set E := R.cutSet X
  set E' := E.erase m₀
  set D := R.inner \ insert m₀ A
  set sD := FK.componentSetoid R.dG R.dualBC (cfgOf R.dData D)
  have hm₀E : m₀ ∈ E := R.mem_cutSet.2 ⟨hm₀, fun heq => by
    have h1 : X (primalEnds m₀).1 := ⟨hu ▸ u.2, by
      rw [show (⟨(primalEnds m₀).1, hu ▸ u.2⟩ : R.pcells) = u from Subtype.ext hu.symm]⟩
    obtain ⟨hc, h2⟩ : X (primalEnds m₀).2 := heq ▸ h1
    rw [show (⟨(primalEnds m₀).2, hc⟩ : R.pcells) = v from Subtype.ext hv.symm] at h2
    exact hnot ((FK.componentSetoid R.pG R.sepBC _).symm h2)⟩
  have hE'sub : E' ⊆ D := fun m hm => by
    obtain ⟨hmne, hmE⟩ := Finset.mem_erase.1 hm
    rw [Finset.mem_sdiff, Finset.mem_insert, not_or]
    exact ⟨(R.mem_cutSet.1 hmE).1, hmne, fun hmA => R.not_cut_of_mem hA u hmA (R.mem_cutSet.1 hmE).2⟩
  have hpar (z : R.dcells) (hx1 : R.x0 < z.1.1) (hx2 : z.1.1 < R.x0 + R.w) :
      ((z = u' ∨ z = v') → Odd (E'.filter (fun m => m ∈ corners z.1)).card) ∧
      (¬ (z = u' ∨ z = v') → Even (E'.filter (fun m => m ∈ corners z.1)).card) := by
    have hev : Even (E.filter (fun m => m ∈ corners z.1)).card :=
      R.compPred_cutSet_even hh A u z hx1 hx2
    have hiff : m₀ ∈ corners z.1 ↔ (z = u' ∨ z = v') := by
      rw [← mem_dualEnds_iff z.1 m₀ (mem_dcells.1 z.2).2]
      exact ⟨fun h => h.imp (fun h => Subtype.ext (h.trans hu'.symm))
          (fun h => Subtype.ext (h.trans hv'.symm)),
        fun h => h.imp (fun h => by rw [h, hu']) (fun h => by rw [h, hv'])⟩
    rw [Finset.filter_erase]
    refine ⟨fun hz => ?_, fun hz => ?_⟩
    · have hmem : m₀ ∈ E.filter (fun m => m ∈ corners z.1) := Finset.mem_filter.2 ⟨hm₀E, hiff.2 hz⟩
      have := Finset.card_pos.2 ⟨m₀, hmem⟩
      rw [Finset.card_erase_of_mem hmem]
      obtain ⟨k, hk⟩ := hev; exact ⟨k - 1, by omega⟩
    · rwa [Finset.erase_eq_of_notMem fun hm => hz (hiff.1 (Finset.mem_filter.1 hm).2)]
  have hne' : u' ≠ v' := fun h => dualEnds_ne m₀ (by rw [← hu', ← hv', h])
  have key (a o : R.dcells) (hao : a = u' ∧ o = v' ∨ a = v' ∧ o = u') :
      sD.r u' v' ∨ ∃ t : R.dcells, (t.1.1 = R.x0 ∨ t.1.1 = R.x0 + R.w) ∧ sD.r a t := by
    by_cases ha : a.1.1 = R.x0 ∨ a.1.1 = R.x0 + R.w
    · exact Or.inr ⟨a, ha, sD.refl a⟩
    · have hac := mem_cells.1 (mem_dcells.1 a.2).1
      obtain ⟨b, hb, t, ht, hr⟩ := R.dual_reachable_of_odd (hE'sub.trans Finset.sdiff_subset)
        {a} (Finset.univ.filter fun t : R.dcells => t.1.1 = R.x0 ∨ t.1.1 = R.x0 + R.w ∨ t = o)
        (by
          rw [Finset.disjoint_singleton_left]
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_or]
          exact ⟨fun h => ha (Or.inl h), fun h => ha (Or.inr h),
            by rcases hao with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> [exact hne'; exact hne'.symm]⟩)
        (fun z hz1 hz2 => by
          simp only [Finset.mem_singleton, Finset.mem_filter, Finset.mem_univ, true_and, not_or] at hz1 hz2
          have hzc := mem_cells.1 (mem_dcells.1 z.2).1
          exact (hpar z (by omega) (by omega)).2 fun h => by
            rcases hao with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases h with rfl | rfl <;> tauto)
        (by rw [Finset.sum_singleton]; exact (hpar a (by omega) (by omega)).1 (hao.imp And.left And.left))
      rw [Finset.mem_singleton.1 hb] at hr
      have hrt := R.dualOf_reachable_le hE'sub Finset.sdiff_subset R.dualBC hr
      rcases (Finset.mem_filter.1 ht).2 with h1 | h2 | rfl
      · exact Or.inr ⟨t, Or.inl h1, hrt⟩
      · exact Or.inr ⟨t, Or.inr h2, hrt⟩
      · rcases hao with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl hrt
        · exact Or.inl (sD.symm hrt)
  rcases key u' v' (Or.inl ⟨rfl, rfl⟩) with h | ⟨t₁, ht₁, hr₁⟩
  · exact h
  · rcases key v' u' (Or.inr ⟨rfl, rfl⟩) with h | ⟨t₂, ht₂, hr₂⟩
    · exact h
    · exact sD.trans hr₁ (sD.trans
        (FK.boundary_component R.dG R.dualBC _ (Or.inr ⟨ht₁, ht₂⟩)) (sD.symm hr₂))

end Rect

end PottsDiscontinuity.TorusCrossing
