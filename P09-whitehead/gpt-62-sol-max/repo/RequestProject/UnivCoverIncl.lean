module

public import RequestProject.FinsuppBasis
public import RequestProject.PresSubcomplex

@[expose] public section

open scoped Classical

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

theorem pathChain_apply_zero_of_edge_absent {E : Type u} (p : List (E × Bool))
    (e : E) (hp : ∀ b ∈ p, b.1 ≠ e) : pathChain p e = 0 := by
  classical
  induction p with
  | nil => simp
  | cons b p ih =>
      have hb  := hp b (List.mem_cons_self ..)
      have ht  := fun c hc => hp c (List.mem_cons_of_mem b hc)
      rw [pathChain_cons, Finsupp.add_apply, ih ht]
      cases b.2 <;> simp [hb]

/-- Pushing forward edge coefficients commutes with taking a path chain. -/
theorem pathChain_map_edges {E F : Type*} (f : E → F) (l : List (E × Bool)) :
    pathChain (l.map (fun e => (f e.1, e.2))) = Finsupp.mapDomain f (pathChain l) := by
  induction l with
  | nil => simp
  | cons e l ih =>
    rcases e with ⟨e, b⟩
    cases b <;> simp [pathChain_cons, ih, Finsupp.mapDomain_add, ← zero_sub, Finsupp.mapDomain_sub]

theorem pathChain_map (p : Hom X Y) (l : List (X.E × Bool)) :
    pathChain (l.map (fun eb => (p.onE eb.1, eb.2))) = Finsupp.mapDomain p.onE (pathChain l) :=
  pathChain_map_edges p.onE l

/-- The map of one-chains induced by a cellular map. -/
noncomputable def chain1 (p : Hom X Y) : (X.E →₀ ℤ) →ₗ[ℤ] (Y.E →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ p.onE

/-- The map of two-chains induced by a cellular map. -/
noncomputable def chain2 (p : Hom X Y) : (X.F →₀ ℤ) →ₗ[ℤ] (Y.F →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ p.onF

theorem chain1_comp_apply (f : Hom X Y) (g : Hom Y Z) (c : X.E →₀ ℤ) :
    chain1 (g.comp f) c = chain1 g (chain1 f c) := by
  change Finsupp.mapDomain (g.onE ∘ f.onE) c =
    Finsupp.mapDomain g.onE (Finsupp.mapDomain f.onE c)
  erw [Finsupp.mapDomain_comp]

theorem chain2_comp_apply (f : Hom X Y) (g : Hom Y Z) (c : X.F →₀ ℤ) :
    chain2 (g.comp f) c = chain2 g (chain2 f c) := by
  change Finsupp.mapDomain (g.onF ∘ f.onF) c =
    Finsupp.mapDomain g.onF (Finsupp.mapDomain f.onF c)
  erw [Finsupp.mapDomain_comp]

@[simp] theorem chain2_apply (p : Hom X Y) (u : X.F →₀ ℤ) :
    chain2 p u = Finsupp.mapDomain p.onF u := rfl

/-- **A cellular map is a chain map**: it commutes with the second boundary. -/
theorem bdry2_chain2 (p : Hom X Y) (u : X.F →₀ ℤ) :
    bdry2 Y (chain2 p u) = chain1 p (bdry2 X u) := by
  finsupp_singles u
  intro f n
  simp [chain1, bdry2_single, p.att_onF, pathChain_map]

/-- A cellular map sends two-cycles to two-cycles. -/
theorem chain2_cycle (f : Hom X Y) {z : X.F →₀ ℤ} (h : bdry2 X z = 0) :
    bdry2 Y (chain2 f z) = 0 := by rw [bdry2_chain2, h, map_zero]

/-- The boundary of an image face uses only image edges. -/
theorem bdry2_single_image_zero (f : Hom X Y) (t : X.F) (e : Y.E)
    (he : e ∉ Set.range f.onE) : bdry2 Y (Finsupp.single (f.onF t) 1) e = 0 := by
  rw [bdry2_single, one_smul, f.att_onF, pathChain_map]
  exact Finsupp.mapDomain_of_notMem_range _ e he

/-! ### The lift of an inclusion of presentations to the universal covers -/

variable {α β : Type u}   {J K : Type u}


/-- The lift of an edge path is natural in the generating set. -/
theorem liftPath_map {Nsub : Subgroup (FreeGroup α)} [Nsub.Normal]
    {Msub : Subgroup (FreeGroup β)} [Msub.Normal] (f : α → β)
    (Ψ : (FreeGroup α ⧸ Nsub) →* (FreeGroup β ⧸ Msub))
    (hΨ : ∀ i, Ψ (qof Nsub i) = qof Msub (f i))
    (L : List (α × Bool)) (q : FreeGroup α ⧸ Nsub) :
    liftPath (L.map (fun p => (f p.1, p.2))) (Ψ q)
      = (liftPath L q).map (fun eb => ((Ψ eb.1.1, f eb.1.2), eb.2)) := by
  refine (PathVoltage.liftPath_map (presentationVoltage Nsub) (presentationVoltage Msub)
    f Ψ ?_ L q).symm
  rintro g ⟨i, b⟩
  cases b
  · change Ψ (g * (qof Nsub i)⁻¹) = Ψ g * (qof Msub (f i))⁻¹
    rw [map_mul, map_inv, hΨ]
  aesop

/-- The map of fundamental groups induced by an inclusion of presentations. -/
def presInclGroupHom (f : α → β) (ρ : J → FreeGroup α) (σ : K → FreeGroup β) (g : J → K)
    (hg : ∀ j, σ (g j) = FreeGroup.map f (ρ j)) : PresGroup ρ →* PresGroup σ :=
  QuotientGroup.map _ _ (FreeGroup.map f) (by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨j, rfl⟩
    simpa [← hg j] using! Subgroup.subset_normalClosure (Set.mem_range_self _))




/-- **The inclusion of presentations lifts to the universal covers**: the cellular map of
the universal covers whose action on cells is `(q, c) ↦ (Ψ q, c)`. -/
def univCoverInclHom (f : α → β) (hf : Function.Injective f) (ρ : J → FreeGroup α)
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


end Comb








end FiniteChains
