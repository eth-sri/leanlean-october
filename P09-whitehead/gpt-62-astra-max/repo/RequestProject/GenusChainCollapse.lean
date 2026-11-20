module

public import RequestProject.GenusCollapse
public import Mathlib.Order.Extension.Linear
public import RequestProject.CutFacetCollapse

@[expose] public section

/-! Integral chain collapse of the actual genus block, chosen independently of a cycle. -/

namespace FiniteChains.Davis.Genus
open ASC
variable (q : ℕ) [NeZero q]

noncomputable instance genusVertexLinearOrder : LinearOrder (GenusVertex q) := by
  classical
  exact LinearOrder.lift' (toLinearExtension : GenusVertex q → LinearExtension (GenusVertex q))
    (fun _ _ h => h)

/-- Choose the free faces of the spine collapse, preferring the cut facet
at each positive corner. Its chain properties follow from its incidences. -/
noncomputable def genusChainCollapse :=
  preferCutFaces (Collapse.exists_pairCollapse (genus_spine_collapse q).choose_spec).choose

theorem genusChainCollapse_isPairCollapse :
    Collapse.IsPairCollapse (spineInc (orderComplex (GenusVertex q))) (genusChainCollapse q)
      (topCubes (orderComplex (GenusVertex q))) :=
  preferCutFaces_isPairCollapse (Finset.Subset.refl _)
    (Collapse.exists_pairCollapse (genus_spine_collapse q).choose_spec).choose_spec

theorem genusChainCollapse_isChainCollapse :
    CollapseChain.IsChainCollapse (cubeBdry (V := GenusVertex q)) (genusChainCollapse q) :=
  spine_pair_chainCollapse (Finset.Subset.refl _) (genusChainCollapse_isPairCollapse q)

theorem genusChainCollapse_cutSurface_eq_zero
    (o : Finset (GenusVertex q) → ℤ) (hcyc : simpBdry o = 0)
    (hsupp : ∀ σ, σ.card ≠ 3 → o σ = 0)
    (hfaces : ∀ σ, σ ∉ (orderComplex (GenusVertex q)).faces → o σ = 0) :
    CollapseChain.cmap (cubeBdry (V := GenusVertex q)) (genusChainCollapse q)
      (Sum.elim 0 (fun τ => -o τ)) = 0 :=
  cutSurface_cmap_eq_zero hcyc hsupp hfaces (genusChainCollapse_isPairCollapse q).map_fst rfl
    (genusChainCollapse_isChainCollapse q)

theorem genusChainCollapse_positive_pair
    (p : Cube (GenusVertex q) × (Cube (GenusVertex q) ⊕ Finset (GenusVertex q)))
    (hp : p ∈ genusChainCollapse q) (hpos : p.1 = posCube (freeSet p.1)) :
    p.2 = Sum.inr (freeSet p.1) :=
  preferCutFaces_positive_pair hp hpos

theorem genusChainCollapse_old_face_nonpositive
    (t g : Cube (GenusVertex q))
    (hp : (t, Sum.inl g) ∈ genusChainCollapse q) : t ≠ posCube (freeSet t) := by
  intro ht
  have hh := genusChainCollapse_positive_pair q (t, Sum.inl g) hp ht
  cases hh

/-- Every cut triangle is removed by its own positive corner cube. -/
theorem genusChainCollapse_removes_cut_triangle (σ : Finset (GenusVertex q))
    (hσ : IsTri (orderComplex (GenusVertex q)) σ) :
    Sum.inr σ ∈ (genusChainCollapse q).map Prod.snd := by
  have ht : posCube σ ∈ topCubes (orderComplex (GenusVertex q)) := by
    apply mem_topCubes.mpr
    simpa using hσ
  obtain ⟨f, hf⟩ := (genusChainCollapse_isPairCollapse q).covers ht
  have he : f = Sum.inr σ := by
    simpa using genusChainCollapse_positive_pair q (posCube σ, f) hf (by simp)
  subst f
  exact List.mem_map.mpr ⟨(posCube σ, Sum.inr σ), hf, rfl⟩

end FiniteChains.Davis.Genus
