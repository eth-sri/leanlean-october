module
public import Mathlib

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
noncomputable abbrev dualOf (E : Finset Cell)  :=
  endGraph dualEnds R.dcells E

section

variable {E : Finset Cell} (hE : E ⊆ R.inner)
include hE

theorem dData_mono  : EndData dualEnds R.dcells E where
  mem m hm := R.dData.mem m (hE hm)
  ne := R.dData.ne
  inj := R.dData.inj

/-- Degree of an odd cell in the dual graph of `E`: the number of corners lying in `E`. -/
theorem dualOf_degree  (z : R.dcells) :
    (R.dualOf E).degree z = (E.filter  fun m => m ∈ corners z.1 ).card := by
  
  rw [degree_eq (R.dData_mono hE)]
  congr 1
  apply Finset.filter_congr
  intro m _
  exact mem_dualEnds_iff z.1 m  (mem_dcells.1 z.2).2 

/-- **Handshake for the dual graph.** -/
theorem dual_reachable_of_odd  (B T : Finset R.dcells)
    (hdisj : Disjoint B T)
    (heven : ∀ z : R.dcells, z ∉ B → z ∉ T → Even (E.filter  fun m => m ∈ corners z.1 ).card)
    (hodd : Odd (∑ z ∈ B, (E.filter  fun m => m ∈ corners z.1 ).card)) :
    ∃ b ∈ B, ∃ t ∈ T, (R.dualOf E).Reachable b t := by
  apply FK.exists_reachable_between_of_odd_degree_sum (R.dualOf E) B T hdisj
  · intro v hv
    rw [dualOf_degree R hE]
    grind
  · simpa only [dualOf_degree R hE] using hodd

end

/-- Reachability in `dualOf E` implies the component relation of any larger configuration. -/
theorem dualOf_reachable_le {E D : Finset Cell} (hED : E ⊆ D) (hD : D ⊆ R.inner)
    (ξ : FK.BoundaryCondition R.dcells) {x y : R.dcells} (h : (R.dualOf E).Reachable x y) :
    (FK.componentSetoid R.dG ξ (cfgOf R.dData D)).r x y := by
  have hle : (R.dualOf E).reachableSetoid ≤ FK.componentSetoid R.dG ξ (cfgOf R.dData D) := by
    apply FK.reachableSetoid_le_of_adj
    intro a b hab
    
    apply FK.actualConnected_component
    apply FK.actualConnected_of_adj
    rw [openGraph_adj_iff R.dData, openMedials_cfgOf R.dData D hD]
    rcases hab.2 with ⟨m, hm, h⟩ | ⟨m, hm, h⟩
    · exact ⟨m, hED hm, Or.inl h⟩
    · exact ⟨m, hED hm, Or.inr h⟩
  exact hle h


/-- The cells of the primal component of `u` (as a predicate on all cells). -/
def compPred (A : Finset Cell) (u : R.pcells) (c : Cell)  :=
  ∃ hc : c ∈ R.pcells, (FK.componentSetoid R.pG R.sepBC (cfgOf R.pData A)).r ⟨c, hc⟩ u

/-- The cut edges of the board for a vertex predicate. -/
noncomputable def cutSet (X : Cell → Prop)  := R.inner.filter (IsCut X)

theorem mem_cutSet {X : Cell → Prop} {m : Cell} : m ∈ R.cutSet X ↔ m ∈ R.inner ∧ IsCut X m := by
  unfold cutSet; simp [Finset.mem_filter]

theorem compPred_iff {A : Finset Cell} {u x y : R.pcells}
    (hxy : (FK.componentSetoid R.pG R.sepBC (cfgOf R.pData A)).r x y) :
    R.compPred A u x.1 ↔ R.compPred A u y.1 := by
  constructor
  · rintro ⟨hc, h⟩
    exact ⟨y.2, (FK.componentSetoid R.pG R.sepBC (cfgOf R.pData A)).trans
      ((FK.componentSetoid R.pG R.sepBC (cfgOf R.pData A)).symm hxy) h⟩
  · rintro ⟨hc, h⟩
    exact ⟨x.2, (FK.componentSetoid R.pG R.sepBC (cfgOf R.pData A)).trans hxy h⟩

/-- Open edges are never cut by a component predicate. -/
theorem not_cut_of_mem {A : Finset Cell} (hA : A ⊆ R.inner) (u : R.pcells) {m : Cell}
    (hm : m ∈ A) : ¬ IsCut (R.compPred A u) m := by
  intro hcut
  
  
  have hmem := R.pData.mem m (hA hm)
  apply hcut
  have hadj : (FK.openGraph R.pG (cfgOf R.pData A)).Adj ⟨(primalEnds m).1, hmem.1⟩
      ⟨(primalEnds m).2, hmem.2⟩ := by
    rw [openGraph_adj_iff R.pData, openMedials_cfgOf R.pData A hA]
    exact ⟨m, hm, Or.inl rfl⟩
  
  exact propext (R.compPred_iff (FK.actualConnected_component R.pG R.sepBC (cfgOf R.pData A)
                                   (FK.actualConnected_of_adj R.pG _ hadj)))

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
      (corners z).filter  fun m => m ∈ R.inner ∧ IsCut X m  := by
  grind +locals

theorem outer_pcells (z : R.dcells) (hx1 : R.x0 < z.1.1) (hx2 : z.1.1 < R.x0 + R.w) :
    (z.1.1 - 1, z.1.2) ∈ R.pcells ∧ (z.1.1 + 1, z.1.2) ∈ R.pcells := by
  have hz := mem_dcells.1 z.2
  rw [mem_cells] at hz
  unfold IsPrimal at hz
  constructor <;> rw [mem_pcells, mem_cells] <;> unfold IsPrimal <;> dsimp only <;> omega

section

variable (hh : 0 < R.h) (A : Finset Cell)
include hh A

theorem compPred_cutSet_even  (u : R.pcells) (z : R.dcells)
    (hx1 : R.x0 < z.1.1) (hx2 : z.1.1 < R.x0 + R.w) :
    Even ((R.cutSet (R.compPred A u)).filter  fun m => m ∈ corners z.1 ).card := by
  rw [cutSet_filter_corners]
  have hz := mem_dcells.1 z.2
  have hzc := mem_cells.1 hz.1
  obtain ⟨hW, hE⟩ := R.outer_pcells z hx1 hx2
  apply cut_deg_even R hh _ z.1 hz.2 hx1 hx2 hzc.2.2.1 hzc.2.2.2
  · intro hb
    exact R.compPred_iff (u := u) (x := ⟨_, hW⟩) (y := ⟨_, hE⟩)
      (R.bottom_related A  hb   hb )
  · intro ht
    exact R.compPred_iff (u := u) (x := ⟨_, hW⟩) (y := ⟨_, hE⟩)
      (R.top_related A  ht   ht )


/-- **Existence.**  If two primal cells joined by a closed edge `m₀` are not connected (rows
wired), then the dual endpoints of `m₀` are connected in the complementary dual configuration
(side columns wired). -/
theorem existence  (hA : A ⊆ R.inner) (m₀ : Cell)
    (hm₀ : m₀ ∈ R.inner) (u v : R.pcells) (hu : u.1 = (primalEnds m₀).1)
    (hv : v.1 = (primalEnds m₀).2) (u' v' : R.dcells) (hu' : u'.1 = (dualEnds m₀).1)
    (hv' : v'.1 = (dualEnds m₀).2)
    (hnot : ¬ (FK.componentSetoid R.pG R.sepBC (cfgOf R.pData A)).r u v) :
    (FK.componentSetoid R.dG R.dualBC (cfgOf R.dData (R.inner \ insert m₀ A))).r u' v' := by
  set X := R.compPred A u with hX
  set E := R.cutSet X with hE
  set E' := E.erase m₀ with hE'
  set D := R.inner \ insert m₀ A with hD
  set sD := FK.componentSetoid R.dG R.dualBC (cfgOf R.dData D) with hsD
  
  have hEsub : E ⊆ R.inner := fun m hm => (R.mem_cutSet.1 hm).1
  have hm₀E : m₀ ∈ E := by
    rw [hE, mem_cutSet]
    refine ⟨hm₀, ?_⟩
    
    
    have h2 : ¬ X (primalEnds m₀).2 := by
      rintro ⟨hc, h⟩
      apply hnot
      have :  ⟨(primalEnds m₀).2, hc⟩  = v := Subtype.ext hv.symm
      rw [this] at h
      exact (FK.componentSetoid R.pG R.sepBC _).symm h
    intro heq
    exact h2 (heq ▸  by
                       refine ⟨by rw [← hu]; exact u.2, ?_⟩
                       have :  ⟨(primalEnds m₀).1, by rw [← hu]; exact u.2⟩  = u := Subtype.ext hu.symm
                       rw [this] )
  have hE'sub : E' ⊆ D := by
    intro m hm
    rw [hE', Finset.mem_erase] at hm
    rw [hD, Finset.mem_sdiff, Finset.mem_insert, not_or]
    refine ⟨hEsub hm.2, hm.1, fun hmA => ?_⟩
    exact R.not_cut_of_mem hA u hmA (R.mem_cutSet.1 hm.2).2
  
  -- parity of the remaining cut edges at the interior odd cells
  have hpar : ∀ z , R.x0 < z.1.1 → z.1.1 < R.x0 + R.w →
      ( z = u' ∨ z = v'  → Odd (E'.filter  fun m => m ∈ corners z.1 ).card) ∧
      (¬ (z = u' ∨ z = v') → Even (E'.filter  fun m => m ∈ corners z.1 ).card) := by
    intro z hx1 hx2
    have hev : Even (E.filter  fun m => m ∈ corners z.1 ).card :=
      by
        solve_by_elim [_root_.PottsDiscontinuity.TorusCrossing.Rect.compPred_cutSet_even]
    
    have hiff : m₀ ∈ corners z.1 ↔  z = u' ∨ z = v'  := by
      rw [← mem_dualEnds_iff z.1 m₀  (mem_dcells.1 z.2).2 ]
      constructor
      · aesop
      · rintro (h | h)
        all_goals simp_all
    have hfe : E'.filter (fun m => m ∈ corners z.1) = (E.filter  fun m => m ∈ corners z.1 ).erase m₀ := by
      grind
    rw [hfe]
    constructor
    · grind
    · simp_all
  -- wiring of the side columns
  have hLR : ∀ a b ,  a.1.1 = R.x0 ∨ a.1.1 = R.x0 + R.w  →
       b.1.1 = R.x0 ∨ b.1.1 = R.x0 + R.w  → sD.r a b := fun a b ha hb =>
    FK.boundary_component R.dG R.dualBC _ (Or.inr ⟨ha, hb⟩)
  have hreach : ∀ a b , (R.dualOf E').Reachable a b → sD.r a b := by
                                                                              solve_by_elim [_root_.PottsDiscontinuity.TorusCrossing.Rect.dualOf_reachable_le, _root_.Finset.sdiff_subset]
  have hne' : u' ≠ v' := fun h => dualEnds_ne m₀ (by grind)
  -- the key step: an odd dual endpoint strictly inside reaches the side columns or its partner
  have key : ∀ a o ,  a = u' ∧ o = v' ∨ a = v' ∧ o = u'  → a.1.1 ≠ R.x0 →
      a.1.1 ≠ R.x0 + R.w →
      ∃ t : R.dcells, (t.1.1 = R.x0 ∨ t.1.1 = R.x0 + R.w ∨ t = o) ∧ (R.dualOf E').Reachable a t := by
    intro a o hao ha1 ha2
    have hac := mem_cells.1 (mem_dcells.1 a.2).1
    obtain ⟨hodd, hpo⟩ := hpar a (by omega) (by omega)
    
    
    obtain ⟨b, hb, t, ht, hr⟩ := R.dual_reachable_of_odd (hE'sub.trans  Finset.sdiff_subset )
      {a} (Finset.univ.filter  fun t  => t.1.1 = R.x0 ∨ t.1.1 = R.x0 + R.w ∨ t = o )
      (by
        rw [Finset.disjoint_singleton_left]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_or]
        exact ⟨ha1, ha2,  by
                            grind ⟩)
      (by
        intro z hz1 hz2
        simp only [Finset.mem_singleton, Finset.mem_filter, Finset.mem_univ, true_and, not_or] at hz1 hz2
        have hzc := mem_cells.1 (mem_dcells.1 z.2).1
        refine (hpar z (by omega) (by omega)).2 ?_
        rintro (h | h)
        · grind
        · grind
      )
      (by
        grind)
    rw [Finset.mem_singleton] at hb
    subst hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    exact ⟨t, ht, hr⟩
  -- assemble
  by_cases hu1 : u'.1.1 = R.x0 ∨ u'.1.1 = R.x0 + R.w <;>
    by_cases hv1 : v'.1.1 = R.x0 ∨ v'.1.1 = R.x0 + R.w
  · exact hLR u' v' hu1 hv1
  · obtain ⟨t, ht, hr⟩ := key v' u' (Or.inr ⟨rfl, rfl⟩) (by tauto) (by tauto)
    have hr' := hreach _ _ hr
    rcases ht with ht | ht | ht
    · exact sD.symm (sD.trans hr' (hLR t u' (Or.inl ht) hu1))
    · exact sD.symm (sD.trans hr' (hLR t u' (Or.inr ht) hu1))
    · subst ht; exact sD.symm hr'
  · obtain ⟨t, ht, hr⟩ := key u' v' (Or.inl ⟨rfl, rfl⟩) (by tauto) (by tauto)
    have hr' := hreach _ _ hr
    rcases ht with ht | ht | ht
    · exact sD.trans hr' (hLR t v' (Or.inl ht) hv1)
    · exact sD.trans hr' (hLR t v' (Or.inr ht) hv1)
    · subst ht; exact hr'
  · obtain ⟨t₁, ht₁, hr₁⟩ := key u' v' (Or.inl ⟨rfl, rfl⟩) (by tauto) (by tauto)
    obtain ⟨t₂, ht₂, hr₂⟩ := key v' u' (Or.inr ⟨rfl, rfl⟩) (by tauto) (by tauto)
    have h1 := hreach _ _ hr₁
    have h2 := hreach _ _ hr₂
    by_cases e1 : t₁ = v'
    · subst e1; exact h1
    · by_cases e2 : t₂ = u'
      · subst e2; exact sD.symm h2
      · 
        
        exact sD.trans h1 (sD.trans (hLR _ _ (Or.casesOn ht₁ Or.inl fun h => Or.casesOn h Or.inr fun h => absurd h e1) (Or.casesOn ht₂ Or.inl fun h => Or.casesOn h Or.inr fun h => absurd h e2)) (sD.symm h2))

end

end Rect

end PottsDiscontinuity.TorusCrossing
