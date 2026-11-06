import Mathlib.Tactic

import RequestProject.PresSubcomplex

/-!
# The inclusion of two universal covers, and the chain map it induces

`RequestProject/PresSubcomplex.lean` shows that an inclusion of presentations is a cellular
map `X_r → X_{r+1}` of the presentation complexes.  This file lifts that map to the
universal covers (`FiniteChains.Comb.univCoverInclHom`): on the cover of `X_r` the vertices
are the elements of `π₁(X_r)`, and the lift acts on cells by `(q, c) ↦ (Ψ q, c)`, where
`Ψ : π₁(X_r) → π₁(X_{r+1})` is the induced map of fundamental groups.

A cellular map induces a chain map (`FiniteChains.Comb.chain1`,
`FiniteChains.Comb.chain2`, `FiniteChains.Comb.bdry2_chain2`).  Consequently the
hypothesis `zero_pi2` of `FiniteChains.PresChain` says exactly, and only, this: the chain
map on two-chains induced by the lifted inclusion of universal covers kills every
two-cycle, i.e. the inclusion is zero on `π₂ = ker ∂₂`
(`FiniteChains.PresChain.zero_pi2_chain2`).
-/

namespace FiniteChains.Comb





/-! ### The chain map induced by a cellular map -/

variable {X Y : Complex2.{u}}

variable (p : Hom X Y)
/-- The one-chains carried by the image of an edge path. -/
theorem pathChain_map  (l : List (X.E × Bool)) :
    pathChain (l.map (fun eb => (p.onE eb.1, eb.2)))
      = Finsupp.mapDomain p.onE (pathChain l) := by
  induction l with
  | nil => simp
  | cons e l ih =>
      rw [List.map_cons, pathChain_cons, pathChain_cons, ih, Finsupp.mapDomain_add]
      congr 1
      by_cases hb : e.2
      · simp [*]
      · have hneg : Finsupp.mapDomain p.onE (-Finsupp.single e.1 (1 : ℤ))
            = -Finsupp.mapDomain p.onE (Finsupp.single e.1 (1 : ℤ)) := by
          simpa using (Finsupp.lmapDomain ℤ ℤ p.onE).map_neg (Finsupp.single e.1 (1 : ℤ))
        simp [*]

/-- The map of one-chains induced by a cellular map. -/
noncomputable def chain1   :=
  Finsupp.lmapDomain ℤ ℤ p.onE

/-- The map of two-chains induced by a cellular map. -/
noncomputable def chain2   :=
  Finsupp.lmapDomain ℤ ℤ p.onF

@[simp] theorem chain2_apply  (u : X.F →₀ ℤ) :
    chain2 p u = Finsupp.mapDomain p.onF u := rfl

/-- **A cellular map is a chain map**: it commutes with the second boundary. -/
theorem bdry2_chain2  (u : X.F →₀ ℤ) :
    bdry2 Y (chain2 p u) = chain1 p (bdry2 X u) := by
  classical
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u₁ u₂ h₁ h₂ => grind
  | single f n =>
      classical aesop (add simp [FiniteChains.Comb.bdry2_single, FiniteChains.Comb.Hom.att_onF, FiniteChains.Comb.pathChain_map, bdry2])

/-! ### The lift of an inclusion of presentations to the universal covers -/

variable {α β : Type u} [DecidableEq α] [DecidableEq β] {J K : Type u}

omit [DecidableEq α] [DecidableEq β] in
/-- The lift of an edge path is natural in the generating set. -/
theorem liftPath_map {Nsub : Subgroup (FreeGroup α)} [Nsub.Normal]
    {Msub : Subgroup (FreeGroup β)} [Msub.Normal] (f : α → β)
    (Ψ : (FreeGroup α ⧸ Nsub) →* (FreeGroup β ⧸ Msub))
    (hΨ : ∀ i, Ψ (qof Nsub i) = qof Msub (f i))
    (L : List (α × Bool)) (q : FreeGroup α ⧸ Nsub) :
    liftPath (L.map (fun p => (f p.1, p.2))) (Ψ q)
      = (liftPath L q).map (fun eb => ((Ψ eb.1.1, f eb.1.2), eb.2)) := by
  induction L generalizing q with
  | nil => rfl
  | cons a L ih =>
      obtain ⟨i, b⟩ := a
      cases b
      · grind [liftPath_cons_false]
      · grind [FiniteChains.Comb.liftPath_cons_true]

variable (f : α → β)
/-- The map of fundamental groups induced by an inclusion of presentations. -/
def presInclGroupHom  (ρ : J → FreeGroup α) (σ : K → FreeGroup β) (g : J → K)
    (hg : ∀ j, σ (g j) = FreeGroup.map f (ρ j)) : PresGroup ρ →* PresGroup σ :=
  QuotientGroup.map _ _ (FreeGroup.map f) (by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨j, rfl⟩
    refine Subgroup.mem_comap.2 ?_
    rw [← hg j]
    exact Subgroup.subset_normalClosure (Set.mem_range_self _))

omit [DecidableEq α] [DecidableEq β] in
@[simp] theorem presInclGroupHom_mk  (ρ : J → FreeGroup α) (σ : K → FreeGroup β)
    (g : J → K) (hg : ∀ j, σ (g j) = FreeGroup.map f (ρ j)) (w : FreeGroup α) :
    presInclGroupHom f ρ σ g hg (QuotientGroup.mk w) =
      QuotientGroup.mk (FreeGroup.map f w) := rfl

/-- **The inclusion of presentations lifts to the universal covers**: the cellular map of
the universal covers whose action on cells is `(q, c) ↦ (Ψ q, c)`. -/
def univCoverInclHom  (hf : Function.Injective f) (ρ : J → FreeGroup α)
    (σ : K → FreeGroup β) (g : J → K) (hg : ∀ j, σ (g j) = FreeGroup.map f (ρ j)) :
    Hom (univCover ρ) (univCover σ) where
  onV := presInclGroupHom f ρ σ g hg
  onE := Prod.map (presInclGroupHom f ρ σ g hg) f
  onF := Prod.map (presInclGroupHom f ρ σ g hg) g
  src_onE _ := rfl
  tgt_onE e := by
    aesop
  base_onF _ := rfl
  att_onF c := by
    obtain ⟨q, j⟩ := c
    show liftPath (FreeGroup.toWord (σ (g j))) (presInclGroupHom f ρ σ g hg q)
      = (liftPath (FreeGroup.toWord (ρ j)) q).map
          (fun eb => ((presInclGroupHom f ρ σ g hg eb.1.1, f eb.1.2), eb.2))
    rw [hg j, toWord_map f hf]
    exact liftPath_map f (presInclGroupHom f ρ σ g hg) (fun _ => rfl) _ q

@[simp] theorem univCoverInclHom_onF  (hf : Function.Injective f)
    (ρ : J → FreeGroup α) (σ : K → FreeGroup β) (g : J → K)
    (hg : ∀ j, σ (g j) = FreeGroup.map f (ρ j)) :
    (univCoverInclHom f hf ρ σ g hg).onF = Prod.map (presInclGroupHom f ρ σ g hg) g := rfl

end FiniteChains.Comb









