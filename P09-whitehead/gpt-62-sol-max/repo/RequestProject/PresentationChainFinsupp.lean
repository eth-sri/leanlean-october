module

public import RequestProject.FoxNaturality
public import RequestProject.PresentationDictionary
public import RequestProject.NecessityAlgebraicMod
public import RequestProject.CycleLifting
public import RequestProject.Pi2Dictionary
public import RequestProject.CoverComplex
public import RequestProject.ChainFormula
public import RequestProject.FinitelyDeterminedInf
public import RequestProject.Pigeonhole
public import RequestProject.CoverChainComplex
public import RequestProject.FoxCommutator
public import RequestProject.TorsionFreeGroupRing
public import RequestProject.ChainFormulaMod
public import RequestProject.Pi2DictionaryFinsupp
public import RequestProject.PresUnivCoverIso

@[expose] public section

/-! Chains of presentation complexes with arbitrary generator and relator sets.
The two-cycle condition is imposed on actual cellular universal-cover chains. -/


namespace FiniteChains

open MonoidAlgebra

universe u

variable {α J : Type u}

/-- A chain `K = X₀ ⊂ X₁ ⊂ ⋯ ⊂ Xₙ` of presentation complexes over the presentation
`⟨α | ρ⟩`, with arbitrary cell sets, together with the topological property used in Section 2:
the inclusions are zero on `π₂`. -/
structure PresChainFS (ρ : J → FreeGroup α) (n : ℕ) where
  /-- The generators of the stage `X_r`. -/
  gen : ℕ → Type u
  /-- The two-cells of the stage `X_r`. -/
  cell : ℕ → Type u
  decGen : ∀ r, DecidableEq (gen r)
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
  /-- The maps of cellular universal covers kill two-cycles. -/
  zero_pi2 : ∀ r, r < n →
    letI := decGen r
    letI := decGen (r + 1)
    Comb.ZeroPi2 (Comb.presInclHom (genIncl r) (genIncl_injective r) (rel r) (rel (r + 1))
      (cellIncl r) (rel_incl r))

namespace PresChainFS

variable {ρ : J → FreeGroup α} {n : ℕ} (h : PresChainFS ρ n)

/-- The inclusion of the generators of `K` into those of `X_r`. -/
def gmap (h : PresChainFS ρ n) : ∀ r, α → h.gen r
  | 0 => h.baseGen
  | r + 1 => fun i => h.genIncl r (gmap h r i)



@[simp] theorem gmap_succ (r : ℕ) (i : α) : h.gmap (r + 1) i = h.genIncl r (h.gmap r i) := rfl

/-- The inclusion of the two-cells of `K` into those of `X_r`. -/
def cmap (h : PresChainFS ρ n) : ∀ r, J → h.cell r
  | 0 => h.baseCell
  | r + 1 => fun j => h.cellIncl r (cmap h r j)



@[simp] theorem cmap_succ (r : ℕ) (j : J) : h.cmap (r + 1) j = h.cellIncl r (h.cmap r j) := rfl

theorem gmap_injective (h : PresChainFS ρ n) : ∀ r, Function.Injective (h.gmap r)
  | 0 => h.baseGen_injective
  | r + 1 => by
      intro i i' hii
      exact gmap_injective h r (h.genIncl_injective r hii)

theorem cmap_injective (h : PresChainFS ρ n) : ∀ r, Function.Injective (h.cmap r)
  | 0 => h.baseCell_injective
  | r + 1 => by
      intro j j' hjj
      exact cmap_injective h r (h.cellIncl_injective r hjj)

/-- The two-cells of `K` are attached, in `X_r`, along the relators of the presentation. -/
theorem rel_cmap (h : PresChainFS ρ n) : ∀ (r : ℕ) (j : J),
    h.rel r (h.cmap r j) = FreeGroup.map (h.gmap r) (ρ j)
  | 0, j => h.rel_base j
  | r + 1, j => by
      have hg : h.gmap (r + 1) = h.genIncl r ∘ h.gmap r := funext fun i => gmap_succ h r i
      rw [cmap_succ, h.rel_incl r (h.cmap r j), rel_cmap h r j, FreeGroup.map.comp, hg]

/-- The map `π₁(X_r) → π₁(X_{r+1})` induced by the inclusion. -/
def psi (r : ℕ) : PresGroup (h.rel r) →* PresGroup (h.rel (r + 1)) :=
  Comb.presInclGroupHom (h.genIncl r) (h.rel r) (h.rel (r + 1)) (h.cellIncl r) (h.rel_incl r)

/-- The map `π₁(K) → π₁(X_r)` induced by the inclusion. -/
def phi (r : ℕ) : PresGroup ρ →* PresGroup (h.rel r) :=
  Comb.presInclGroupHom (h.gmap r) ρ (h.rel r) (h.cmap r) (h.rel_cmap r)





theorem psi_comp_phi (r : ℕ) : (h.psi r).comp (h.phi r) = h.phi (r + 1) := by
  ext w
  rfl

/-- **The `π₂`-condition in Fox coordinates.**  The topological hypothesis of the
chain — the inclusion is zero on `π₂` — says, in the coordinates used throughout
Section 2, that a Fox cycle over `ℤ[π₁(X_r)]` has zero image in the chain module of
`X_{r+1}`.  The two forms are equivalent by
`FiniteChains.Comb.fs_univCover_zero_pi2_iff`. -/
theorem zero_pi2_coords (r : ℕ) (hr : r < n)
    (u : h.cell r →₀ MonoidAlgebra ℤ (PresGroup (h.rel r)))
    (hu : ∀ a : h.gen r, ∑ c ∈ u.support, u c *
        quotRingHom ℤ (relSub (h.rel r)) (fox a (h.rel r c)) = 0) :
    Finsupp.mapDomain (h.cellIncl r)
      (Finsupp.mapRange (MonoidAlgebra.mapDomainRingHom ℤ (h.psi r)) (map_zero _) u) = 0 := by
  letI := h.decGen r
  letI := h.decGen (r + 1)
  exact (Comb.fs_univCover_zero_pi2_iff (h.rel r) (h.psi r) (h.cellIncl r)
    (h.cellIncl_injective r)).1 ((Comb.zeroPi2_presInclHom_iff (h.rel r) (h.genIncl r)
      (h.genIncl_injective r) (h.cellIncl r) (h.rel_incl r)).1 (h.zero_pi2 r hr)) u hu

/-- The Fox boundary matrix of the stage `X_r`. -/
noncomputable def bdry (r : ℕ) (a : h.gen r) (c : h.cell r) :
    MonoidAlgebra ℤ (PresGroup (h.rel r)) :=
  quotRingHom ℤ (relSub (h.rel r)) (fox a (h.rel r c))

/-- Reading a group-ring element of `ℤ[F]` in `ℤ[π₁(X_r)]` through the inclusion of
generating sets agrees with pushing it to `ℤ[π₁(K)]` and then along `π₁(K) → π₁(X_r)`. -/
theorem quot_freeRingMap (r : ℕ) (x : FreeGroupRing α) :
    quotRingHom ℤ (relSub (h.rel r)) (freeRingMap (h.gmap r) x)
      = MonoidAlgebra.mapDomainRingHom ℤ (h.phi r) (quotRingHom ℤ (relSub ρ) x) :=
  (quotRingHom_natural (relSub (h.rel r)) (FreeGroup.map (h.gmap r)) (h.phi r) rfl x).symm

variable [DecidableEq α]

/-- **The cell-level data of the chain.**  Everything except the two topological
properties is computed from the presentations. -/
noncomputable def toChainInput :
    ChainInput (foxMatrixPres ρ) n (fun r => PresGroup (h.rel r)) h.gen h.cell where
  phi := h.phi
  psi := h.psi
  phi_succ := h.psi_comp_phi
  genIncl := h.gmap
  cellIncl := h.cmap
  cellIncl_injective := h.cmap_injective
  cellStep := h.cellIncl
  cellStep_injective := h.cellIncl_injective
  bdry := h.bdry
  bdry_old := by
    intro r i j
    letI := h.decGen r
    show quotRingHom ℤ (relSub (h.rel r)) (fox (h.gmap r i) (h.rel r (h.cmap r j))) = _
    rw [h.rel_cmap r j, fox_map (h.gmap r) (h.gmap_injective r) i (ρ j), h.quot_freeRingMap r]
    rfl
  bdry_new := by
    intro r a ha j
    letI := h.decGen r
    show quotRingHom ℤ (relSub (h.rel r)) (fox a (h.rel r (h.cmap r j))) = 0
    rw [h.rel_cmap r j, fox_map_of_not_mem_range (h.gmap r) ha (ρ j), map_zero]
  zero_pi2 := fun r hr u hu => h.zero_pi2_coords r hr u hu

/-- **Cycles lift modulo `m`**: for a chain of presentation complexes this is not a
hypothesis but a theorem, because `H₁` of the universal cover of a stage vanishes. -/
theorem cycleLiftsMod_toChainInput (m : ℕ) : CycleLiftsMod h.toChainInput m := by
  intro r _ u hu
  letI := h.decGen r
  obtain ⟨v, hv, z, hz⟩ := fs_exists_cycle_of_boundary_nsmul (h.rel r) m u
    (fun i => by simpa only [fs_coverSecondBoundary_apply, toChainInput, bdry, foxMatrixPres] using hu i)
  refine ⟨v, ?_, z, hz⟩
  intro i
  have hi := congrArg (fun c => c i) hv
  simpa only [fs_coverSecondBoundary_apply, toChainInput, bdry, foxMatrixPres, Finsupp.zero_apply] using hi

end PresChainFS

/-- **The cell-level chain hypothesis follows from chains of nested presentation
complexes.** -/
theorem hasCellChainsLift_of_presChainsFS [DecidableEq α]
    (ρ : J → FreeGroup α)
    (hchains : ∀ n : ℕ, Nonempty (PresChainFS ρ n)) :
    HasCellChainsLift (foxMatrixPres ρ) := by
  intro n
  obtain ⟨h⟩ := hchains n
  exact ⟨fun r => PresGroup (h.rel r), fun _ => inferInstance, h.gen, h.cell, h.toChainInput,
    h.cycleLiftsMod_toChainInput⟩

end FiniteChains
