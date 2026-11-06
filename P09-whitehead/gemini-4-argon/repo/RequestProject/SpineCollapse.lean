module

public import RequestProject.Collapse
public import RequestProject.BarycentricSurface
public import RequestProject.MomentAngleConnected

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains

open Finset

instance : Fintype CubeCoord :=
  ⟨{CubeCoord.free, CubeCoord.pos, CubeCoord.neg}, fun x => by cases x <;> decide⟩

variable {V : Type} [Fintype V] [DecidableEq V]

open scoped Classical in
noncomputable def topCubes (L : ASC V) : Finset (Cube V) :=
  univ.filter fun f => IsTri L (freeSet f)

open scoped Classical in
@[simp] theorem mem_topCubes {L : ASC V} {f : Cube V} :
    f ∈ topCubes L ↔ IsTri L (freeSet f) := by
  simp [topCubes]

open scoped Classical in
noncomputable def spineInc (L : ASC V) : Cube V ⊕ Finset V → Finset (Cube V)
  | Sum.inl g => if (freeSet g).card = 2 then cofaces L g else ∅
  | Sum.inr σ => if IsTri L σ then {posCube σ} else ∅

open scoped Classical in
theorem exists_spine_collapse_of_surface {L : ASC V} (hsurf : ASC.EdgeInTwoTriangles L)
    (hdual : ∀ σ σ', IsTri L σ → IsTri L σ' → Relation.ReflTransGen (TriAdj L) σ σ')
    (hcover : ∀ v : V, ∃ σ, IsTri L σ ∧ v ∈ σ)
    {σ₀ : Finset V} (hσ₀ : IsTri L σ₀) :
    ∃ l : List (Cube V), Collapse.IsCollapse (spineInc L) l (topCubes L) := by
  classical
  have hedge (e : Finset V) (he : e.card = 2) :
      ((univ.filter fun j => j ∉ e).filter fun j => insert j e ∈ L.faces).card ≤ 2 := by
    by_cases hef : e ∈ L.faces
    · obtain ⟨v₁, v₂, -, -, -, huniq⟩ := hsurf e hef he
      refine le_trans (Finset.card_le_card (?_ : _ ⊆ ({v₁, v₂} : Finset V)))
        (by simpa only [Finset.card_singleton] using Finset.card_insert_le v₁ {v₂})
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      rcases huniq j ⟨hj.1, hj.2⟩ with rfl | rfl <;> simp
    · rw [Finset.filter_eq_empty_iff.2 fun j _ hcon =>
        hef (L.down_closed hcon (Finset.subset_insert _ _))]
      simp
  have hcard : ∀ f : Cube V ⊕ Finset V, (spineInc L f).card ≤ 2
    | .inl g => by
        by_cases hg : (freeSet g).card = 2
        · simp only [spineInc, if_pos hg, card_cofaces]; exact hedge _ hg
        · simp [spineInc, hg]
    | .inr σ => by by_cases hσ : IsTri L σ <;> simp [spineInc, hσ]
  have hmove {f g : Cube V} (h : Move L f g) (hf : f ∈ topCubes L) :
      g ∈ topCubes L ∧ Collapse.Adj (spineInc L) f g := by
    have hg : g ∈ topCubes L := by
      obtain ⟨c, c', hcc, hfc, hfc', hgc, hgc', hagree, -, hgL⟩ := h
      rw [mem_topCubes] at hf ⊢
      refine ⟨hgL, ?_⟩
      have hset : freeSet g = insert c' ((freeSet f).erase c) := by
        ext v; simp only [mem_freeSet, Finset.mem_insert, Finset.mem_erase]
        refine ⟨fun hv => if hvc' : v = c' then .inl hvc' else .inr
            ⟨by rintro rfl; exact hgc hv, by rwa [hagree v (by rintro rfl; exact hgc hv) hvc']⟩,
          by rintro (rfl | ⟨hvc, hv⟩)
             · exact hgc'
             · by_cases hvc' : v = c'
               · subst hvc'; exact absurd hv hfc'
               · rwa [← hagree v hvc hvc']⟩
      rw [hset, Finset.card_insert_of_notMem (by simp [hfc']),
        Finset.card_erase_of_mem (by simpa using hfc), hf.2]
    refine ⟨hg, ?_⟩
    obtain ⟨s, ⟨j, hsj, hfs⟩, ⟨k, hsk, hgs⟩⟩ := h.shares_square
    have hfree : freeSet f = insert j (freeSet s) := by rw [hfs, freeSet_update_free]
    have hcard_s : (freeSet s).card = 2 := by
      have := (mem_topCubes.1 hf).2
      rw [hfree, Finset.card_insert_of_notMem (by simpa using hsj)] at this; omega
    refine ⟨by obtain ⟨_, _, _, hfc, _, hgc, _⟩ := h; rintro rfl; exact hgc hfc,
      Sum.inl s, ?_, ?_⟩
    · simp only [spineInc, if_pos hcard_s]
      exact mem_cofaces.2 ⟨j, hsj, hfree ▸ (mem_topCubes.1 hf).1, hfs⟩
    · simp only [spineInc, if_pos hcard_s]
      exact mem_cofaces.2 ⟨k, hsk, by rw [← freeSet_update_free, ← hgs]; exact (mem_topCubes.1 hg).1, hgs⟩
  have hconn : Collapse.Connected (spineInc L) (topCubes L) := fun f hf g hg => by
    have key : ∀ {a b : Cube V}, Relation.ReflTransGen (Move L) a b → a ∈ topCubes L →
        b ∈ topCubes L ∧ Relation.ReflTransGen
          (fun x y => x ∈ topCubes L ∧ y ∈ topCubes L ∧ Collapse.Adj (spineInc L) x y) a b := by
      intro a b hab ha
      induction hab with
      | refl => exact ⟨ha, Relation.ReflTransGen.refl⟩
      | tail _ hyz ih =>
          obtain ⟨hy, hpath'⟩ := ih
          obtain ⟨hz, hadj⟩ := hmove hyz hy
          exact ⟨hz, hpath'.tail ⟨hy, hz, hadj⟩⟩
    exact (key (reflTransGen_move hdual hcover (mem_topCubes.1 hf) (mem_topCubes.1 hg)) hf).2
  have hmem₀ : posCube σ₀ ∈ topCubes L := by rw [mem_topCubes, freeSet_posCube]; exact hσ₀
  refine Collapse.exists_isCollapse_of_connected hcard hconn hmem₀ ⟨Sum.inr σ₀, ?_⟩
  simp only [Collapse.IsFree, spineInc, if_pos hσ₀]
  ext x; simp only [Finset.mem_inter, Finset.mem_singleton]
  exact ⟨fun ⟨rfl, _⟩ => rfl, by rintro rfl; exact ⟨rfl, hmem₀⟩⟩

end FiniteChains
