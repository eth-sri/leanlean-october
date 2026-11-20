module

public import RequestProject.PresSubcomplex

@[expose] public section

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

namespace FiniteChains
namespace Comb

open MonoidAlgebra

universe u

/-! ### The chain map induced by a cellular map -/

variable {X Y : Complex2.{u}}

variable (p : Hom X Y)

/-- The one-chains carried by the image of an edge path. -/
theorem pathChain_map (l : List _) :
    pathChain (l.map (fun eb => (p.onE eb.1, eb.2)))
      = Finsupp.mapDomain p.onE (pathChain l) := by
  induction l with
  | nil => simp
  | cons e l ih =>
      rw [List.map_cons, pathChain_cons, pathChain_cons, ih, Finsupp.mapDomain_add]
      congr 1
      by_cases hb : e.2
      · simp [hb]
      · have hneg : Finsupp.mapDomain p.onE (-Finsupp.single e.1 1)
            = -Finsupp.mapDomain p.onE (Finsupp.single e.1 (1 : ℤ)) := by
          simpa using (Finsupp.lmapDomain ℤ ℤ p.onE).map_neg (Finsupp.single e.1 1)
        simp_all

/-- The map of one-chains induced by a cellular map. -/
noncomputable def chain1 :=
  Finsupp.lmapDomain ℤ ℤ p.onE

/-- The map of two-chains induced by a cellular map. -/
noncomputable def chain2 :=
  Finsupp.lmapDomain ℤ ℤ p.onF

variable (u : X.F →₀ ℤ)

@[simp] theorem chain2_apply :
    chain2 p u = Finsupp.mapDomain p.onF u := rfl

/-- **A cellular map is a chain map**: it commutes with the second boundary. -/
theorem bdry2_chain2 :
    bdry2 Y (chain2 p u) = chain1 p (bdry2 X u) := by
  classical
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u₁ u₂ h₁ h₂ => simp_all [map_add, h₁, h₂]
  | single f n =>
      show bdry2 Y _
        = Finsupp.mapDomain p.onE (bdry2 X _)
      simp [Finsupp.mapDomain_single, bdry2_single, p.att_onF, pathChain_map, Finsupp.mapDomain_smul]

/-! ### The lift of an inclusion of presentations to the universal covers -/

variable {α β : Type u} [DecidableEq α] [DecidableEq β] {J K : Type u}

omit [DecidableEq α] [DecidableEq β] in
/-- The lift of an edge path is natural in the generating set. -/
theorem liftPath_map {Nsub : Subgroup (FreeGroup α)} [Nsub.Normal]
    {Msub : Subgroup (FreeGroup β)} [Msub.Normal] (f : α → β)
    (Ψ : (FreeGroup α ⧸ Nsub) →* (FreeGroup β ⧸ Msub))
    (hΨ : ∀ i, Ψ (qof Nsub i) = qof Msub (f i))
    (L : List _) (q : FreeGroup α ⧸ Nsub) :
    liftPath (L.map (fun p => (f p.1, p.2))) (Ψ q)
      = (liftPath L q).map (fun eb => ((Ψ eb.1.1, f eb.1.2), eb.2)) := by
  induction L generalizing q with
  | nil => rfl
  | cons a L ih =>
      obtain ⟨i, b⟩ := a
      cases b
      · have hq : Ψ (q * (qof Nsub i)⁻¹) = Ψ q * (qof Msub (f i))⁻¹ := by
          simp_all
        simp only [List.map_cons, liftPath_cons_false]
        rw [← hq, ih _]
      · have hq : Ψ (q * qof Nsub i) = Ψ q * qof Msub (f i) := by simp_all
        simp only [List.map_cons, liftPath_cons_true]
        rw [← hq, ih _]

variable (f : α → β)

variable (ρ : J → FreeGroup α)
    (σ : K → FreeGroup β)
    (g : J → K)
    (hg : ∀ j, σ (g j) = FreeGroup.map f (ρ j))

/-- The map of fundamental groups induced by an inclusion of presentations. -/
def presInclGroupHom : PresGroup ρ →* PresGroup σ :=
  QuotientGroup.map _ _ (FreeGroup.map f) (by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨j, rfl⟩
    refine Subgroup.mem_comap.2 ?_
    rw [← hg j]
    exact Subgroup.subset_normalClosure (Set.mem_range_self _))

omit [DecidableEq α] [DecidableEq β] in
@[simp] theorem presInclGroupHom_mk (w : FreeGroup α) :
    presInclGroupHom f ρ σ g hg (QuotientGroup.mk w) =
      QuotientGroup.mk (FreeGroup.map f w) := rfl

variable (hf : Function.Injective f)
    (ρ : J → FreeGroup α)
    (σ : K → FreeGroup β)
    (g : J → K)
    (hg : ∀ j, σ (g j) = FreeGroup.map f (ρ j))

/-- **The inclusion of presentations lifts to the universal covers**: the cellular map of
the universal covers whose action on cells is `(q, c) ↦ (Ψ q, c)`. -/
def univCoverInclHom :
    Hom (univCover ρ) (univCover σ) where
  onV := presInclGroupHom f ρ σ g hg
  onE := Prod.map _ f
  onF := Prod.map _ g
  src_onE _ := rfl
  tgt_onE e := by
    aesop
  base_onF _ := rfl
  att_onF c := by
    obtain ⟨q, j⟩ := c
    show liftPath (FreeGroup.toWord (σ (g j))) (presInclGroupHom f ρ σ g hg q)
      = (liftPath _ q).map
          _
    rw [hg j, toWord_map f hf]
    solve_by_elim [liftPath_map]

@[simp] theorem univCoverInclHom_onF :
    (univCoverInclHom f hf ρ σ g hg).onF = Prod.map (presInclGroupHom f ρ σ g hg) g := rfl

end Comb

end FiniteChains
