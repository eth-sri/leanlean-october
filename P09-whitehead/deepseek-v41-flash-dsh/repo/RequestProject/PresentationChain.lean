module

public import RequestProject.FoxNaturality
public import RequestProject.PresentationDictionary
public import RequestProject.NecessityAlgebraicMod
public import RequestProject.CycleLifting
public import RequestProject.Pi2Dictionary
public import RequestProject.PresentationNecessity

@[expose] public section

/-!
# Chains of presentation complexes

Condition (1) of Theorem A speaks of a chain `K = X₀ ⊂ X₁ ⊂ ⋯ ⊂ Xₙ` of two-complexes whose
inclusions are zero on `π₂`.  For complexes given by presentations, "`X_r ⊂ X_{r+1}`" means
concretely: the generators and the two-cells of `X_r` are generators and two-cells of
`X_{r+1}`, and an old two-cell is attached along the same word.  This is the structure
`FiniteChains.PresChain`.

From such a chain the cell-level data `ChainInput` used throughout Section 2 is *derived*
(`FiniteChains.PresChain.toChainInput`): the fundamental groups `π₁(X_r)` are the presented
groups, the maps between them are induced by the inclusions of the generating sets, and the
Fox boundary matrices restrict correctly — this last point is the naturality of the Fox
derivative proved in `RequestProject/FoxNaturality.lean`.  The only data that is not
derived but assumed is the topological content itself: the inclusion is zero on
`π₂ = ker ∂₂` (field `zero_pi2`).  The lifting of cycles modulo `m`, quoted in the paper
from Hatcher, is here a theorem (`RequestProject/CycleLifting.lean`).

Combining this with `RequestProject/PresentationNecessity.lean` gives
`FiniteChains.presComplex_hasAcyclicRegularCover_of_presChains`: if chains of nested
presentation complexes of every length exist over `K`, then `K` has a connected acyclic
regular cover, constructed as a two-complex.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

open MonoidAlgebra


variable {α J : Type u}

/-- A chain `K = X₀ ⊂ X₁ ⊂ ⋯ ⊂ Xₙ` of presentation complexes over the presentation
`⟨α | ρ⟩`, with finite stages, together with the topological property used in Section 2:
the inclusions are zero on `π₂`. -/
structure PresChain (ρ : J → FreeGroup α) (n : ℕ) where
  /-- The generators of the stage `X_r`. -/
  gen : ℕ → Type u
  /-- The two-cells of the stage `X_r`. -/
  cell : ℕ → Type u
  decGen : ∀ r, DecidableEq (gen r)
  finGen : ∀ r, Fintype (gen r)
  finCell : ∀ r, Fintype (cell r)
  /-- The attaching word of a two-cell of `X_r`. -/
  rel : ∀ r, cell r → FreeGroup (gen r)
  /-- The generators of `X_r` are generators of `X_{r+1}`. -/
  genIncl : ∀ r, gen r → gen (r + 1)
  genIncl_injective : ∀ r, Function.Injective (genIncl r)
  /-- The two-cells of `X_r` are two-cells of `X_{r+1}`. -/
  cellIncl : ∀ r, cell r → cell (r + 1)
  cellIncl_injective : ∀ r, Function.Injective (cellIncl r)
  /-- An old two-cell is attached along the same word. -/
  rel_incl : ∀ r c, rel (r + 1) (cellIncl r c) = FreeGroup.map (genIncl r) (rel r c)
  /-- The generators of `K` are generators of `X₀`. -/
  baseGen : α → gen 0
  baseGen_injective : Function.Injective baseGen
  /-- The two-cells of `K` are two-cells of `X₀`. -/
  baseCell : J → cell 0
  baseCell_injective : Function.Injective baseCell
  /-- The two-cells of `K` are attached along the relators of the presentation. -/
  rel_base : ∀ j, rel 0 (baseCell j) = FreeGroup.map baseGen (ρ j)
  /-- **The inclusion `X_r ⊂ X_{r+1}` is zero on `π₂`.**  In the combinatorial model
  `π₂(X_r)` is the module of cellular two-cycles of the universal cover `X̃_r`, and the
  inclusion lifts to the universal covers as the map of two-cells `(q, c) ↦ (Ψ q, c)`,
  where `Ψ : π₁(X_r) → π₁(X_{r+1})` is the induced map of fundamental groups.  The
  condition is that every cellular two-cycle of `X̃_r` is carried to zero. -/
  zero_pi2 : ∀ r, r < n →
      ∀ u : ((FreeGroup (gen r) ⧸ relSub (rel r)) × cell r) →₀ ℤ,
        Comb.bdry2 (@Comb.univCover _ (decGen r) _ (rel r)) u = 0 →
        Finsupp.mapDomain (Prod.map
          (⇑(QuotientGroup.map (relSub (rel r)) (relSub (rel (r + 1)))
            (FreeGroup.map (genIncl r)) (by
              refine Subgroup.normalClosure_le_normal ?_
              rintro _ ⟨c, rfl⟩
              refine Subgroup.mem_comap.2 ?_
              have : FreeGroup.map (genIncl r) (rel r c) = rel (r + 1) (cellIncl r c) :=
                (rel_incl r c).symm
              rw [this]
              exact Subgroup.subset_normalClosure (Set.mem_range_self _))))
          (cellIncl r)) u = 0

namespace PresChain

variable {ρ : J → FreeGroup α} {n : ℕ} (h : PresChain ρ n)

/-- The inclusion of the generators of `K` into those of `X_r`. -/
def gmap (h : PresChain ρ n) : ∀ r, α → h.gen r
  | 0 => h.baseGen
  | r + 1 => fun i => h.genIncl r (gmap h r i)

@[simp] theorem gmap_zero : h.gmap 0 = h.baseGen := by simp [gmap]

@[simp] theorem gmap_succ (r : ℕ) (i : α) : h.gmap (r + 1) i = h.genIncl r (h.gmap r i) := by
  simp [gmap]

/-- The inclusion of the two-cells of `K` into those of `X_r`. -/
def cmap (h : PresChain ρ n) : ∀ r, J → h.cell r
  | 0 => h.baseCell
  | r + 1 => fun j => h.cellIncl r (cmap h r j)

@[simp] theorem cmap_zero : h.cmap 0 = h.baseCell := by simp [cmap]

@[simp] theorem cmap_succ (r : ℕ) (j : J) : h.cmap (r + 1) j = h.cellIncl r (h.cmap r j) := by
  simp [cmap]

/-- The two-cells of `K` are attached, in `X_r`, along the relators of the presentation. -/
theorem rel_cmap (h : PresChain ρ n) : ∀ (r : ℕ) (j : J),
    h.rel r (h.cmap r j) = FreeGroup.map (h.gmap r) (ρ j)
  | 0, j => h.rel_base j
  | r + 1, j => by
      have hg : h.gmap (r + 1) = h.genIncl r ∘ h.gmap r := funext fun i => gmap_succ h r i
      rw [cmap_succ, h.rel_incl, rel_cmap, FreeGroup.map.comp, hg]

/-- The relators of `X_r` generate its relator subgroup, so an inclusion of generating sets
that carries relators to relators induces a map of the presented groups. -/
theorem relSub_le_comap_step (r : ℕ) :
    relSub (h.rel r) ≤ (relSub (h.rel (r + 1))).comap (FreeGroup.map (h.genIncl r)) := by
  refine Subgroup.normalClosure_le_normal ?_
  rintro _ ⟨c, rfl⟩
  refine Subgroup.mem_comap.2 ?_
  rw [show FreeGroup.map (h.genIncl r) (h.rel r c) = h.rel (r + 1) (h.cellIncl r c) from
    (h.rel_incl r c).symm]
  exact Subgroup.subset_normalClosure (Set.mem_range_self _)

theorem relSub_le_comap_base (r : ℕ) :
    relSub ρ ≤ (relSub (h.rel r)).comap (FreeGroup.map (h.gmap r)) := by
  refine Subgroup.normalClosure_le_normal ?_
  rintro _ ⟨j, rfl⟩
  refine Subgroup.mem_comap.2 ?_
  rw [← h.rel_cmap r j]
  exact Subgroup.subset_normalClosure (Set.mem_range_self _)

/-- The map `π₁(X_r) → π₁(X_{r+1})` induced by the inclusion. -/
def psi (r : ℕ) : PresGroup (h.rel r) →* PresGroup (h.rel (r + 1)) :=
  QuotientGroup.map _ _ (FreeGroup.map (h.genIncl r)) (h.relSub_le_comap_step r)

/-- The map `π₁(K) → π₁(X_r)` induced by the inclusion. -/
def phi (r : ℕ) : PresGroup ρ →* PresGroup (h.rel r) :=
  QuotientGroup.map _ _ (FreeGroup.map (h.gmap r)) (h.relSub_le_comap_base r)

@[simp] theorem phi_mk (r : ℕ) (w : FreeGroup α) :
    h.phi r (QuotientGroup.mk w) = QuotientGroup.mk (FreeGroup.map (h.gmap r) w) := rfl

@[simp] theorem psi_mk (r : ℕ) (w : FreeGroup (h.gen r)) :
    h.psi r (QuotientGroup.mk w) = QuotientGroup.mk (FreeGroup.map (h.genIncl r) w) := rfl

variable [Fintype α] [DecidableEq α] [Fintype J]

end PresChain

end FiniteChains
