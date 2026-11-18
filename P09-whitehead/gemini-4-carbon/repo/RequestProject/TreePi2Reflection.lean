module

public import RequestProject.GenusLoops
public import RequestProject.CombPi1
public import RequestProject.GenusCollapseIteration
public import RequestProject.TopologicalOrderCoverDeck
public import RequestProject.CylinderPi1Surjective
public import RequestProject.OrderNerveOneDecoding
public import RequestProject.PresWordEmbeddingCombPi2
public import RequestProject.OrderNerveCommonSimplex
public import RequestProject.GenusQuotientRelativeSupport
public import RequestProject.QCubeThreeFaceIndex
public import RequestProject.GenusUniversalPolygonTransport
public import Mathlib.Topology.Homotopy.Lifting
public import RequestProject.Statement
public import RequestProject.PresPosetReading
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Topology.Subpath
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
public import Mathlib.Data.List.OfFn
public import Mathlib.GroupTheory.PushoutI
public import Mathlib
public import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence
public import Mathlib.AlgebraicTopology.DoldKan.Degeneracies

@[expose] public section
noncomputable section
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

namespace PresChainFS

variable {ρ : J → FreeGroup α} {n : ℕ} (h : PresChainFS ρ n)

/-- The inclusion of the generators of `K` into those of `X_r`. -/
def gmap (h : PresChainFS ρ n) : ∀ r, α → h.gen r
  | 0 => h.baseGen
  | r + 1 => fun i => h.genIncl r (gmap h r i)

@[simp] theorem gmap_zero : h.gmap 0 = h.baseGen := by simp [gmap]

@[simp] theorem gmap_succ (r : ℕ) (i : α) : h.gmap (r + 1) i = h.genIncl r (h.gmap r i) := rfl

/-- The inclusion of the two-cells of `K` into those of `X_r`. -/
def cmap (h : PresChainFS ρ n) : ∀ r, J → h.cell r
  | 0 => h.baseCell
  | r + 1 => fun j => h.cellIncl r (cmap h r j)

@[simp] theorem cmap_zero : h.cmap 0 = h.baseCell := by simp [cmap]

@[simp] theorem cmap_succ (r : ℕ) (j : J) : h.cmap (r + 1) j = h.cellIncl r (h.cmap r j) := rfl

theorem gmap_injective (h : PresChainFS ρ n) : ∀ r, Function.Injective (h.gmap r)
  | 0 => by simpa using h.baseGen_injective
  | r + 1 => by
      intro i i' hii
      simp only [gmap_succ] at hii
      exact gmap_injective h r (h.genIncl_injective r hii)

theorem cmap_injective (h : PresChainFS ρ n) : ∀ r, Function.Injective (h.cmap r)
  | 0 => by simpa using h.baseCell_injective
  | r + 1 => by
      intro j j' hjj
      simp only [cmap_succ] at hjj
      exact cmap_injective h r (h.cellIncl_injective r hjj)

/-- The two-cells of `K` are attached, in `X_r`, along the relators of the presentation. -/
theorem rel_cmap (h : PresChainFS ρ n) : ∀ (r : ℕ) (j : J),
    h.rel r (h.cmap r j) = FreeGroup.map (h.gmap r) (ρ j)
  | 0, j => h.rel_base j
  | r + 1, j => by
      have hg : h.gmap (r + 1) = h.genIncl r ∘ h.gmap r := funext fun i => gmap_succ h r i
      rw [cmap_succ, h.rel_incl r (h.cmap r j), rel_cmap h r j, FreeGroup.map.comp, hg]

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

theorem psi_comp_phi (r : ℕ) : (h.psi r).comp (h.phi r) = h.phi (r + 1) := by
  ext w
  simp

/-- **The `π₂`-condition in Fox coordinates.**  The topological hypothesis of the
chain — the inclusion is zero on `π₂` — says, in the coordinates used throughout
Section 2, that a Fox cycle over `ℤ[π₁(X_r)]` has zero image in the chain module of
`X_{r+1}`.  The two forms are equivalent by
`FiniteChains.Comb.fs_univCover_zero_pi2_iff`. -/
theorem zero_pi2_coords (r : ℕ) (hr : r < n)
    (u : h.cell r →₀ MonoidAlgebra ℤ (PresGroup (h.rel r)))
    (hu : ∀ a : h.gen r, ∑ c ∈ u.support, u c *
        quotRingHom ℤ (relSub (h.rel r)) (@fox _ (h.decGen r) a (h.rel r c)) = 0) :
    Finsupp.mapDomain (h.cellIncl r)
      (Finsupp.mapRange (MonoidAlgebra.mapDomainRingHom ℤ (h.psi r)) (map_zero _) u) = 0 := by
  letI := h.decGen r
  letI : DecidableEq (h.cell r) := Classical.decEq _
  exact (Comb.fs_univCover_zero_pi2_iff (h.rel r) (h.psi r) (h.cellIncl r)
    (h.cellIncl_injective r)).1 (h.zero_pi2 r hr) u hu

/-- The Fox boundary matrix of the stage `X_r`. -/
def bdry (r : ℕ) (a : h.gen r) (c : h.cell r) :
    MonoidAlgebra ℤ (PresGroup (h.rel r)) :=
  quotRingHom ℤ (relSub (h.rel r)) (@fox _ (h.decGen r) a (h.rel r c))

/-- Reading a group-ring element of `ℤ[F]` in `ℤ[π₁(X_r)]` through the inclusion of
generating sets agrees with pushing it to `ℤ[π₁(K)]` and then along `π₁(K) → π₁(X_r)`. -/
theorem quot_freeRingMap (r : ℕ) (x : FreeGroupRing α) :
    letI := h.decGen r
    quotRingHom ℤ (relSub (h.rel r)) (freeRingMap (h.gmap r) x)
      = MonoidAlgebra.mapDomainRingHom ℤ (h.phi r) (quotRingHom ℤ (relSub ρ) x) := by
  letI := h.decGen r
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single w m =>
      show quotRingHom ℤ (relSub (h.rel r))
          (MonoidAlgebra.mapDomain (FreeGroup.map (h.gmap r)) (MonoidAlgebra.single w m)) = _
      rw [MonoidAlgebra.mapDomain_single, quotRingHom_single]
      show _ = MonoidAlgebra.mapDomain (h.phi r) (quotRingHom ℤ (relSub ρ) (MonoidAlgebra.single w m))
      rw [quotRingHom_single, MonoidAlgebra.mapDomain_single, phi_mk]

variable [DecidableEq α]

/-- **The cell-level data of the chain.**  Everything except the two topological
properties is computed from the presentations. -/
def toChainInput :
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

namespace FiniteChains

universe u

variable {α J : Type u}

/-- A chain `K = X₀ ⊂ X₁ ⊂ ⋯ ⊂ Xₙ` of presentation complexes over `⟨α | ρ⟩` whose inclusions
are zero on `π₂` in the cellular edge-path sense (`FiniteChains.Comb.ZeroPi2`). -/
structure PresChainTopFS (ρ : J → FreeGroup α) (n : ℕ) where
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
  /-- **The inclusion `X_r ⊂ X_{r+1}` is zero on `π₂`**, in the cellular edge-path model: the
  map of two-chains induced on the universal covers built from homotopy classes of edge paths
  kills every two-cycle. -/
  zero_pi2 : ∀ r, r < n →
      letI := decGen r
      letI := decGen (r + 1)
      Comb.ZeroPi2 (Comb.presInclHom (genIncl r) (genIncl_injective r) (rel r) (rel (r + 1))
        (cellIncl r) (rel_incl r))

namespace PresChainTopFS

variable {ρ : J → FreeGroup α} {n : ℕ} (h : PresChainTopFS ρ n)

/-- **A chain with the cellular hypothesis is a chain in the sense of
`FiniteChains.PresChainFS`**: the two readings of "zero on `π₂`" agree. -/
def toPresChainFS : PresChainFS ρ n where
  gen := h.gen
  cell := h.cell
  decGen := h.decGen
  rel := h.rel
  genIncl := h.genIncl
  genIncl_injective := h.genIncl_injective
  cellIncl := h.cellIncl
  cellIncl_injective := h.cellIncl_injective
  rel_incl := h.rel_incl
  baseGen := h.baseGen
  baseGen_injective := h.baseGen_injective
  baseCell := h.baseCell
  baseCell_injective := h.baseCell_injective
  rel_base := h.rel_base
  zero_pi2 := by
    intro r hr
    letI := h.decGen r
    letI := h.decGen (r + 1)
    exact (Comb.zeroPi2_presInclHom_iff (ρ := h.rel r) (σ := h.rel (r + 1)) (h.genIncl r)
      (h.genIncl_injective r) (h.cellIncl r) (h.rel_incl r)).1 (h.zero_pi2 r hr)

end PresChainTopFS

end FiniteChains

namespace FiniteChains.Comb
universe u

structure TopChainFS (K : Complex2.{u}) (n : ℕ) where
  /-- The stages of the chain. -/
  X : ℕ → Complex2.{u}
  /-- The inclusion of `X r` in `X (r + 1)`. -/
  inc : ∀ r, Hom (X r) (X (r + 1))
  incV : ∀ r, Function.Injective (inc r).onV
  incE : ∀ r, Function.Injective (inc r).onE
  incF : ∀ r, Function.Injective (inc r).onF
  /-- Every stage is connected. -/
  conn : ∀ r, IsConnected (X r)
  /-- The inclusion of `K` in the first stage. -/
  base : Hom K (X 0)
  baseV : Function.Injective base.onV
  baseE : Function.Injective base.onE
  baseF : Function.Injective base.onF
  /-- **The inclusion `X r ⊂ X (r + 1)` is zero on `π₂`.** -/
  zero_pi2 : ∀ r, r < n → ZeroPi2 (inc r)



end FiniteChains.Comb

namespace FiniteChains.PresModel
open Comb
variable {α J : ℕ → Type}

/-- Carry the chosen padding generator along the given generator inclusions. -/
def presentationMarkedGenerator (f : ∀ i, α i ↪ α (i + 1)) (a : α 0) : ∀ i, α i
  | 0 => a
  | i + 1 => f i (presentationMarkedGenerator f a i)

variable [∀ i, DecidableEq (α i)]
  (ρ : ∀ i, J i → FreeGroup (α i))
  (f : ∀ i, α i ↪ α (i + 1)) (g : ∀ i, J i ↪ J (i + 1))
  (hr : ∀ i j, ρ (i + 1) (g i j) = FreeGroup.map (f i) (ρ i j)) (a : α 0)

/-- All nonempty word representatives and their literal compatibility are
derived from the labelled group presentations, simultaneously at every stage. -/
def canonicalPresentationStep (i : ℕ) :
    PresWordEmbedding (presCanonicalWords (ρ i) (presentationMarkedGenerator f a i))
      (presCanonicalWords (ρ (i + 1)) (presentationMarkedGenerator f a (i + 1))) :=
  canonicalPresWordEmbedding (ρ i) (ρ (i + 1)) (f i) (g i) (hr i)
    (presentationMarkedGenerator f a i)

end FiniteChains.PresModel

section
open scoped Classical
namespace FiniteChains.RelatorReindex

universe u
variable {A J K : Type u} [Fintype A] [DecidableEq A] [Fintype J] [Fintype K]
  (ρ : J → FreeGroup A) (τ : K → FreeGroup A) (e : J ≃ K)
  (hrel : ∀ j, τ (e j) = ρ j)

/-- The generators are fixed; only the names of relators change. -/
def groupMap : PresGroup ρ →* PresGroup τ :=
  QuotientGroup.lift _ (QuotientGroup.mk' (relSub τ)) (by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨j, rfl⟩
    apply (QuotientGroup.eq_one_iff _).mpr
    exact Subgroup.subset_normalClosure ⟨e j, hrel j⟩)

def coefficientMap : MonoidAlgebra ℤ (PresGroup ρ) →+* MonoidAlgebra ℤ (PresGroup τ) :=
  MonoidAlgebra.mapDomainRingHom ℤ (groupMap ρ τ e hrel)

omit [Fintype A] [DecidableEq A] [Fintype J] [Fintype K] in
theorem coefficientMap_quot (x : FreeGroupRing A) :
    coefficientMap ρ τ e hrel (quotRingHom ℤ (relSub ρ) x) =
      quotRingHom ℤ (relSub τ) x := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp_all
  | single g n =>
      change MonoidAlgebra.mapDomain _ (MonoidAlgebra.mapDomain _ (MonoidAlgebra.single g n)) =
        MonoidAlgebra.mapDomain _ (MonoidAlgebra.single g n)
      simp
      rfl

omit [Fintype A] [Fintype J] [Fintype K] in
theorem coefficientMap_matrix (a : A) (j : J) :
    coefficientMap ρ τ e hrel (foxMatrixPres ρ a j) = foxMatrixPres τ a (e j) := by
  change coefficientMap ρ τ e hrel (quotRingHom ℤ (relSub ρ) (fox a (ρ j))) =
    quotRingHom ℤ (relSub τ) (fox a (τ (e j)))
  rw [coefficientMap_quot, hrel]

end FiniteChains.RelatorReindex

namespace FiniteChains.RelatorReindex
open BlockFamily

universe u
variable {A J K : Type u} [DecidableEq A]
  (ρ : J → FreeGroup A) (τ : K → FreeGroup A) (e : J ≃ K)
  (hrel : ∀ j, τ (e j) = ρ j)

def cellsFS (v : J →₀ MonoidAlgebra ℤ (PresGroup ρ)) :
    K →₀ MonoidAlgebra ℤ (PresGroup τ) :=
  Finsupp.mapDomain e (v.mapRange (coefficientMap ρ τ e hrel) (map_zero _))

omit [DecidableEq A] in
@[simp] theorem cellsFS_apply_image
    (v : J →₀ MonoidAlgebra ℤ (PresGroup ρ)) (j : J) :
    cellsFS ρ τ e hrel v (e j) = coefficientMap ρ τ e hrel (v j) := by simp_all [cellsFS, Finsupp.mapDomain_apply_of_injective, Finsupp.mapRange_apply]

omit [DecidableEq A] in
theorem cellsFS_apply (v : J →₀ MonoidAlgebra ℤ (PresGroup ρ)) (k : K) :
    cellsFS ρ τ e hrel v k = coefficientMap ρ τ e hrel (v (e.symm k)) := by simp_all [cellsFS]

omit [DecidableEq A] in
@[simp] theorem cellsFS_single (j : J) (a : MonoidAlgebra ℤ (PresGroup ρ)) :
    cellsFS ρ τ e hrel (Finsupp.single j a) =
      Finsupp.single (e j) (coefficientMap ρ τ e hrel a) := by
  simp only [cellsFS, Finsupp.mapRange_single, Finsupp.mapDomain_single]


theorem cellsFS_boundary_apply (v : J →₀ MonoidAlgebra ℤ (PresGroup ρ)) (a : A) :
    coverSecondBoundary (relSub τ) τ (cellsFS ρ τ e hrel v) a =
      coefficientMap ρ τ e hrel (coverSecondBoundary (relSub ρ) ρ v a) := by
  induction v using Finsupp.induction_linear with
  | zero => simp [cellsFS]
  | add v w hv hw =>
      simp only [(show cellsFS ρ τ e hrel (v + w) = cellsFS ρ τ e hrel v + cellsFS ρ τ e hrel w by
        ext k : 1
        simp only [cellsFS_apply, Finsupp.add_apply, map_add]), map_add, Finsupp.add_apply, hv, hw]
  | single j c =>
      simp only [cellsFS_single, fsCoverSecondBoundary_apply, Finsupp.sum_single_index,
        zero_mul, map_mul, coefficientMap_matrix]


omit [DecidableEq A] in
theorem cellsFS_aug (v : J →₀ MonoidAlgebra ℤ (PresGroup ρ)) (k : K) :
    augPres τ (cellsFS ρ τ e hrel v k) = augPres ρ (v (e.symm k)) := by
  rw [cellsFS_apply]
  exact augQ_mapDomain (groupMap ρ τ e hrel) (v (e.symm k))

include hrel in
theorem fsIsCockcroft_of (hτ : FSIsCockcroft τ) : FSIsCockcroft ρ := by
  intro v hv j
  have h := hτ (cellsFS ρ τ e hrel v) (by
    change coverSecondBoundary (relSub ρ) ρ v = 0 at hv
    apply Finsupp.ext
    intro a
    simp only [cellsFS_boundary_apply, hv, Finsupp.zero_apply, map_zero]) (e j)
  simpa only [cellsFS_aug, Equiv.symm_apply_apply] using h

end FiniteChains.RelatorReindex
end

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb
universe u

/-- Paths from a chosen vertex fill every augmented cellular zero-cycle. -/
theorem zeroCycle_filling_of_connected (X : Complex2.{u}) (a : X.V)
    (hX : IsConnected X) (c : X.V →₀ ℤ) (hc : augC X c = 0) :
    ∃ b : X.E →₀ ℤ, bdry1 X b = c := by
  choose p hp using hX a
  let s  :=
    Finsupp.linearCombination ℤ (fun v => pathChain (p v))
  have hs z : bdry1 X (s z) = z - augC X z • Finsupp.single a 1 := by
    induction z using Finsupp.induction_linear with
    | zero => simp
    | add z t hz ht =>
      rw [map_add, map_add, hz, ht, map_add, add_smul]
      abel
    | single v n =>
      rw [Finsupp.linearCombination_single, map_smul, bdry1_pathChain_of_isPath (hp v),
        augC_single, smul_sub]
      simp
  exact ⟨s c, by rw [hs, hc, zero_smul, sub_zero]⟩

/-- Normalizing a weak edge filling gives the required strict cellular filling. -/
theorem strict_order_zeroCycle_filling_of_connected {P : Type u} [PartialOrder P]
    (a : P) (hP : IsConnected (orderCx P)) (c : P →₀ ℤ)
    (hc : augC (strictOrderCx P) c = 0) :
    ∃ b : StrictOrdEdge P →₀ ℤ, bdry1 (strictOrderCx P) b = c := by
  obtain ⟨b, hb⟩ := zeroCycle_filling_of_connected (orderCx P) a hP c hc
  exact ⟨normalizeOrdChain1 b, by rw [bdry1_normalizeOrdChain1, hb]⟩

end FiniteChains.Comb
end

section
open scoped Classical unitInterval
open Set
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.PathReplacement

variable {X : Type} [TopologicalSpace X]

theorem concat_conjugate {n : ℕ} (p a : Fin (n + 1) → X)
    (C : ∀ i, Path (p i) (a i))
    (F : ∀ i : Fin n, Path (p i.castSucc) (p i.succ))
    (G : ∀ i : Fin n, Path (a i.castSucc) (a i.succ))
    (h : ∀ i, Path.Homotopic (((C i.castSucc).symm.trans (F i)).trans (C i.succ)) (G i)) :
    Path.Homotopic (((C 0).symm.trans (Path.concat p F)).trans (C (Fin.last n)))
      (Path.concat a G) := by
  induction n with
  | zero =>
    rw [Path.concat_zero, Path.concat_zero]
    apply Path.Homotopic.Quotient.eq.mp
    simp
  | succ n ih =>
    have hi := Path.Homotopic.Quotient.eq.mpr
      (ih (p ∘ Fin.castSucc) (a ∘ Fin.castSucc) (fun i => C i.castSucc)
        (fun i => F i.castSucc) (fun i => G i.castSucc) (fun i => h i.castSucc))
    have hj := Path.Homotopic.Quotient.eq.mpr (h (Fin.last n))
    apply Path.Homotopic.Quotient.eq.mp
    rw [Path.concat_succ, Path.concat_succ]
    calc
      _ = Path.Homotopic.Quotient.trans
          (Path.Homotopic.Quotient.mk (((C 0).symm.trans
            (Path.concat (p ∘ Fin.castSucc) (fun i => F i.castSucc))).trans
              (C (Fin.castSucc (Fin.last n)))))
          (Path.Homotopic.Quotient.mk (((C (Fin.castSucc (Fin.last n))).symm.trans
            (F (Fin.last n))).trans (C (Fin.last (n + 1))))) := by
        simp
        rw [← Path.Homotopic.Quotient.trans_assoc
            (Path.Homotopic.Quotient.mk (C (Fin.castSucc (Fin.last n))))
            (Path.Homotopic.Quotient.mk (C (Fin.castSucc (Fin.last n)))).symm
            ((Path.Homotopic.Quotient.mk (F (Fin.last n))).trans
              (Path.Homotopic.Quotient.mk (C (Fin.last (n + 1))))),
          Path.Homotopic.Quotient.trans_symm, Path.Homotopic.Quotient.refl_trans]
      _ = Path.Homotopic.Quotient.trans
          (Path.Homotopic.Quotient.mk (Path.concat (a ∘ Fin.castSucc) (fun i => G i.castSucc)))
          (Path.Homotopic.Quotient.mk (G (Fin.last n))) := by
        congr 1
      _ = _ := rfl

theorem concat_range_subset {n : ℕ} (p : Fin (n + 1) → X)
    (F : ∀ i : Fin n, Path (p i.castSucc) (p i.succ)) (A : Set X)
    (hp : p 0 ∈ A) (hF : ∀ i, Set.range (F i) ⊆ A) : Set.range (Path.concat p F) ⊆ A := by
  induction n with
  | zero => simp_all
  | succ n ih =>
    simp only [Path.concat_succ, Path.trans_range]
    exact Set.union_subset (ih _ _ hp (fun i => hF i.castSucc)) (hF (Fin.last n))

/-- Local replacements on an open cover concatenate to a replacement of
the entire path. Connectors are allowed to move subdivision vertices. -/
theorem replace_of_open_cover {ι : Type} (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : Set.univ ⊆ ⋃ i, U i)
    (A : Set X) (a : X → X) (ha : ∀ x, a x ∈ A) (C : ∀ x, Path x (a x))
    (hlocal : ∀ i {x y : X} (p : Path x y), Set.range p ⊆ U i →
      ∃ q : Path (a x) (a y), Set.range q ⊆ A ∧
        Path.Homotopic (((C x).symm.trans p).trans (C y)) q)
    {x y : X} (p : Path x y) :
    ∃ q : Path (a x) (a y), Set.range q ⊆ A ∧
      Path.Homotopic (((C x).symm.trans p).trans (C y)) q := by
  obtain ⟨t, ht0, htm, ⟨n, htn⟩, htU⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
      (c := fun i => p ⁻¹' U i) (fun i => (hU i).preimage p.continuous)
      (by intro s _; obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover (Set.mem_univ (p s)))
          exact Set.mem_iUnion.mpr ⟨i, hi⟩)
  let ts : Fin (n + 1) → I := fun i => t i.val
  let points  := p ∘ ts
  let F : ∀ i : Fin n, Path (points i.castSucc) (points i.succ) :=
    fun i => p.subpath (ts i.castSucc) (ts i.succ)
  have hloc (i : Fin n) : ∃ q : Path (a (points i.castSucc)) (a (points i.succ)),
      Set.range q ⊆ A ∧
      Path.Homotopic (((C (points i.castSucc)).symm.trans (F i)).trans (C (points i.succ))) q := by
    obtain ⟨j, hj⟩ := htU i.val
    apply hlocal j (F i)
    rw [show Set.range (F i) = p '' Set.Icc (t i.val) (t (i.val + 1)) from
      p.range_subpath_of_le _ _ (htm (Nat.le_succ i.val))]
    rintro _ ⟨s, hs, rfl⟩
    exact hj hs
  choose G hGA hG using hloc
  have hcat := concat_conjugate points (a ∘ points) (fun i => C (points i)) F G hG
  have hsub  := Path.Homotopic.concat_subpath p ts
  have hcat'  :=
    ((Path.Homotopic.refl _).hcomp hsub.symm).hcomp (Path.Homotopic.refl _) |>.trans hcat
  have hp0 : points 0 = x := by change p (t 0) = x; rw [ht0, p.source]
  have hp1 : points (Fin.last n) = y := by
    change p (t n) = y
    rw [htn n le_rfl, p.target]
  let q := (Path.concat (a ∘ points) G).cast (congrArg a hp0.symm) (congrArg a hp1.symm)
  refine ⟨q, ?_, ?_⟩
  · exact concat_range_subset (a ∘ points) G A (ha _) hGA
  · have ht0' : ts 0 = 0 := ht0
    have ht1' : ts (Fin.last n) = 1 := htn n le_rfl
    have hc0 : (C (points 0)).cast hp0.symm (congrArg a hp0.symm) = C x := by
      apply Path.ext
      funext s
      change C (points 0) s = C x s
      rw [hp0]
    have hc1 : (C (points (Fin.last n))).cast hp1.symm (congrArg a hp1.symm) = C y := by
      apply Path.ext
      funext s
      change C (points (Fin.last n)) s = C y s
      rw [hp1]
    have hps : (p.subpath (ts 0) (ts (Fin.last n))).cast hp0.symm hp1.symm = p := by
      apply Path.ext
      funext s
      change p (Set.Icc.convexComb (ts 0) (ts (Fin.last n)) s) = p s
      rw [ht0', ht1']
      congr 1
      apply Subtype.ext
      simp [Set.Icc.convexComb]
    have hc := hcat'.pathCast (congrArg a hp0.symm) (congrArg a hp1.symm)
    rw [Path.cast_trans _ _ (congrArg a hp0.symm) hp1.symm (congrArg a hp1.symm),
      Path.cast_trans _ _ (congrArg a hp0.symm) hp0.symm hp1.symm,
      Path.cast_symm, hc0, hps, hc1] at hc
    exact hc

end FiniteChains.PathReplacement
end

section
open scoped Classical unitInterval
open Set
namespace FiniteChains.ContinuousEdgeWords

variable {V E X : Type} [TopologicalSpace X]
  (src tgt : E → V) (v : V → X) (edge : ∀ e, Path (v (src e)) (v (tgt e)))

def germPath (g : E × Bool) : Path (v (Comb.germSrc src tgt g))
    (v (Comb.germTgt src tgt g)) :=
  match g with
  | (e, true) => edge e
  | (e, false) => (edge e).symm

/-- Read a genuinely composable finite list as a continuous path. -/
def realize : (l : List (E × Bool)) → {a b : V} →
    Comb.IsPath src tgt l a b → Path (v a) (v b)
  | [], a, _, h => (Path.refl (v a)).cast rfl (congrArg v h.symm)
  | g :: l, _, _, h =>
      ((germPath src tgt v edge g).cast (congrArg v h.1) rfl).trans
        (realize l h.2)

@[simp] theorem realize_nil (a : V) : realize src tgt v edge [] (a := a) rfl = Path.refl (v a) := rfl

theorem realize_append (l m : List (E × Bool)) {a b c : V}
    (hl : Comb.IsPath src tgt l a b) (hm : Comb.IsPath src tgt m b c) :
    Path.Homotopic
      ((realize src tgt v edge l hl).trans (realize src tgt v edge m hm))
      (realize src tgt v edge (l ++ m) (hl.append hm)) := by
  induction l generalizing a with
  | nil =>
    have hab  := hl
    subst b
    exact Path.Homotopic.refl_trans _
  | cons g l ih =>
    exact (Path.Homotopic.trans_assoc _ _ _).trans
      ((Path.Homotopic.refl _).hcomp (ih hl.2))

def IsWord {a b : V} (p : Path (v a) (v b)) : Prop :=
  ∃ l : List (E × Bool), ∃ hl : Comb.IsPath src tgt l a b,
    Path.Homotopic p (realize src tgt v edge l hl)


variable {src tgt v edge} in
theorem IsWord.trans {a b c : V} {p : Path (v a) (v b)} {q : Path (v b) (v c)}
    (hp : IsWord src tgt v edge p) (hq : IsWord src tgt v edge q) :
    IsWord src tgt v edge (p.trans q) := by
  obtain ⟨l, hl, hpl⟩ := hp
  obtain ⟨m, hm, hqm⟩ := hq
  exact ⟨l ++ m, hl.append hm,
    (hpl.hcomp hqm).trans (realize_append src tgt v edge l m hl hm)⟩

variable {src tgt v edge} in
theorem IsWord.of_homotopic {a b : V} {p q : Path (v a) (v b)}
    (hq : IsWord src tgt v edge q) (hpq : Path.Homotopic p q) :
    IsWord src tgt v edge p := by
  obtain ⟨l, hl, hq⟩ := hq
  exact ⟨l, hl, hpq.trans hq⟩

variable {src tgt v edge} in
theorem IsWord.pathCast {a b a' b' : V} {p : Path (v a) (v b)}
    (hp : IsWord src tgt v edge p) (ha : a' = a) (hb : b' = b) :
    IsWord src tgt v edge (p.cast (congrArg v ha) (congrArg v hb)) := by
  subst a'
  subst b'
  exact hp

theorem isWord_concat {n : ℕ} (a : Fin (n + 1) → V)
    (G : ∀ i : Fin n, Path (v (a i.castSucc)) (v (a i.succ)))
    (hG : ∀ i, IsWord src tgt v edge (G i)) :
    IsWord src tgt v edge (Path.concat (v ∘ a) G) := by
  induction n with
  | zero =>
    rw [Path.concat_zero]
    exact (⟨[], rfl, Path.Homotopic.refl _⟩)
  | succ n ih =>
    rw [Path.concat_succ]
    exact (ih (a ∘ Fin.castSucc) (fun i => G i.castSucc)
      (fun i => hG i.castSucc)).trans (hG (Fin.last n))

/-- An open-cover subdivision yields a finite edge word. Local connectors
may move subdivision points to vertices; no finiteness of the graph is used. -/
theorem isWord_of_open_cover {ι : Type} (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : Set.univ ⊆ ⋃ i, U i)
    (a : X → V) (C : ∀ x, Path x (v (a x)))
    (hlocal : ∀ i {x y : X} (p : Path x y), Set.range p ⊆ U i →
      IsWord src tgt v edge (((C x).symm.trans p).trans (C y)))
    {x y : X} (p : Path x y) :
    IsWord src tgt v edge (((C x).symm.trans p).trans (C y)) := by
  obtain ⟨t, ht0, htm, ⟨n, htn⟩, htU⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
      (fun i => (hU i).preimage p.continuous)
      (by intro s _; obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover (Set.mem_univ (p s)))
          exact Set.mem_iUnion.mpr ⟨i, hi⟩)
  let ts : Fin (n + 1) → I := fun i => t i.val
  let points  := p ∘ ts
  let F : ∀ i : Fin n, Path (points i.castSucc) (points i.succ) :=
    fun i => p.subpath (ts i.castSucc) (ts i.succ)
  let G  :=
    fun i => ((C (points i.castSucc)).symm.trans (F i)).trans (C (points i.succ))
  have hG i : IsWord src tgt v edge (G i) := by
    obtain ⟨j, hj⟩ := htU i.val
    apply hlocal j (F i)
    rw [show Set.range (F i) = p '' Set.Icc (t i.val) (t (i.val + 1)) from
      p.range_subpath_of_le _ _ (htm (Nat.le_succ i.val))]
    rintro _ ⟨s, hs, rfl⟩
    exact hj hs
  have hcat := PathReplacement.concat_conjugate points (v ∘ a ∘ points)
    (fun i => C (points i)) F G (fun _ => Path.Homotopic.refl _)
  have hsub  := Path.Homotopic.concat_subpath p ts
  have hcat'  :=
    (((Path.Homotopic.refl _).hcomp hsub.symm).hcomp (Path.Homotopic.refl _)).trans hcat
  have hp0 : points 0 = x := by change p (t 0) = x; rw [ht0, p.source]
  have hp1 : points (Fin.last n) = y := by
    change p (t n) = y
    rw [htn n le_rfl, p.target]
  have hw := (isWord_concat src tgt v edge (a ∘ points) G hG).pathCast
    (congrArg a hp0.symm) (congrArg a hp1.symm)
  have hc := hcat'.pathCast (congrArg (v ∘ a) hp0.symm) (congrArg (v ∘ a) hp1.symm)
  have hc0 : (C (points 0)).cast hp0.symm (congrArg (v ∘ a) hp0.symm) = C x := by
    apply Path.ext
    funext s
    change C (points 0) s = C x s
    rw [hp0]
  have hc1 : (C (points (Fin.last n))).cast hp1.symm (congrArg (v ∘ a) hp1.symm) = C y := by
    apply Path.ext
    funext s
    change C (points (Fin.last n)) s = C y s
    rw [hp1]
  have hps : (p.subpath (ts 0) (ts (Fin.last n))).cast hp0.symm hp1.symm = p := by
    apply Path.ext
    funext s
    change p (Path.subpathAux (ts 0) (ts (Fin.last n)) s) = p s
    have ht0' : ts 0 = 0 := ht0
    have ht1' : ts (Fin.last n) = 1 := htn n le_rfl
    rw [ht0', ht1']
    congr 1
    ext
    simp [Path.subpathAux]
  rw [Path.cast_trans _ _ (congrArg (v ∘ a) hp0.symm) hp1.symm (congrArg (v ∘ a) hp1.symm),
    Path.cast_trans _ _ (congrArg (v ∘ a) hp0.symm) hp0.symm hp1.symm,
    Path.cast_symm, hc0, hps, hc1] at hc
  exact hw.of_homotopic hc

end FiniteChains.ContinuousEdgeWords
end

section
open scoped Classical unitInterval Topology
namespace FiniteChains.ContinuousEdgeWords

theorem realize_congr_list {V E X : Type} [TopologicalSpace X]
    (src tgt : E → V) (v : V → X) (edge : ∀ e, Path (v (src e)) (v (tgt e)))
    {l m : List (E × Bool)} {a b : V}
    (hl : Comb.IsPath src tgt l a b) (hm : Comb.IsPath src tgt m a b) (he : l = m) :
    realize src tgt v edge l hl = realize src tgt v edge m hm := by simp_all

variable {K : Comb.Complex2} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  (v : K.V → X) (edge : ∀ e, Path (v (K.src e)) (v (K.tgt e)))


theorem realize_revPath (l : List (K.E × Bool)) {a b : K.V}
    (hl : Comb.IsPath K.src K.tgt l a b) :
    (realize K.src K.tgt v edge l hl).symm.Homotopic
      (realize K.src K.tgt v edge (Comb.revPath (X := K) l) (Comb.isPath_revPath hl)) := by
  induction l generalizing a with
  | nil =>
    cases hl
    exact Path.Homotopic.refl _
  | cons g l ih =>
    obtain ⟨rfl, ht⟩ := hl
    rw [realize_congr_list K.src K.tgt v edge
      (Comb.isPath_revPath (p := g :: l) ⟨rfl, ht⟩)
      ((Comb.isPath_revPath ht).append (by simp [Comb.IsPath])) (Comb.revPath_cons g l)]
    change ((germPath K.src K.tgt v edge g).trans
      (realize K.src K.tgt v edge l ht)).symm.Homotopic _
    rw [Path.trans_symm]
    exact ((ih ht).hcomp (by
      rcases g with ⟨e, b⟩
      cases b
      · simpa [Comb.germSrc, Comb.germTgt, germPath, Comb.revGerm, Bool.not, Bool.not_false, realize, Path.cast_rfl_rfl,
          Path.symm_symm] using (Path.Homotopic.trans_refl (edge e)).symm
      · simpa [Comb.germSrc, Comb.germTgt, germPath, Comb.revGerm, Bool.not, Bool.not_true, realize, Path.cast_rfl_rfl]
          using (Path.Homotopic.trans_refl (edge e).symm).symm)).trans
      (realize_append K.src K.tgt v edge (Comb.revPath l) [Comb.revGerm g]
        (Comb.isPath_revPath ht) (by simp [Comb.IsPath]))

end FiniteChains.ContinuousEdgeWords

namespace FiniteChains.Comb

theorem isPath_ofFn {V E : Type} (src tgt : E → V) (n : ℕ)
    (a : Fin (n + 1) → V) (g : Fin n → E × Bool)
    (hs : ∀ i, a i.castSucc = germSrc src tgt (g i))
    (ht : ∀ i, germTgt src tgt (g i) = a i.succ) :
    IsPath src tgt (List.ofFn g) (a 0) (a (Fin.last n)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ', List.concat_eq_append]
    exact (ih (a ∘ Fin.castSucc) (fun i => g i.castSucc)
      (fun i => hs i.castSucc) (fun i => ht i.castSucc)).append
      ⟨hs (Fin.last n), ht (Fin.last n)⟩

end FiniteChains.Comb

namespace FiniteChains.ContinuousEdgeWords

variable {V E X : Type} [TopologicalSpace X]
  (src tgt : E → V) (v : V → X) (edge : ∀ e, Path (v (src e)) (v (tgt e)))

theorem concat_homotopic_realize_ofFn (n : ℕ)
    (a : Fin (n + 1) → V) (g : Fin n → E × Bool)
    (hs : ∀ i, a i.castSucc = Comb.germSrc src tgt (g i))
    (ht : ∀ i, Comb.germTgt src tgt (g i) = a i.succ)
    (F : ∀ i : Fin n, Path (v (a i.castSucc)) (v (a i.succ)))
    (hF : ∀ i, (F i).Homotopic
      (realize src tgt v edge [g i] ⟨hs i, ht i⟩)) :
    (Path.concat (v ∘ a) F).Homotopic
      (realize src tgt v edge (List.ofFn g) (Comb.isPath_ofFn src tgt n a g hs ht)) := by
  induction n with
  | zero =>
    rw [Path.concat_zero]
    have he : List.ofFn g = [] := by simp
    rw [realize_congr_list src tgt v edge (Comb.isPath_ofFn src tgt 0 a g hs ht)
      (show Comb.IsPath src tgt [] (a 0) (a (Fin.last 0)) from rfl) he]
    exact Path.Homotopic.refl _
  | succ n ih =>
    rw [Path.concat_succ]
    have he : List.ofFn g = List.ofFn (fun i : Fin n => g i.castSucc) ++ [g (Fin.last n)] := by
      rw [List.ofFn_succ', List.concat_eq_append]
    rw [realize_congr_list src tgt v edge (Comb.isPath_ofFn src tgt (n + 1) a g hs ht)
      ((Comb.isPath_ofFn src tgt n (a ∘ Fin.castSucc) (fun i => g i.castSucc)
        (fun i => hs i.castSucc) (fun i => ht i.castSucc)).append
          (show Comb.IsPath src tgt [g (Fin.last n)]
            ((a ∘ Fin.castSucc) (Fin.last n)) (a (Fin.last (n + 1))) from
              ⟨hs (Fin.last n), ht (Fin.last n)⟩)) he]
    exact ((ih (a ∘ Fin.castSucc) (fun i => g i.castSucc)
      (fun i => hs i.castSucc) (fun i => ht i.castSucc)
      (fun i => F i.castSucc) (fun i => hF i.castSucc)).hcomp (hF (Fin.last n))).trans
      (realize_append src tgt v edge
        (List.ofFn (fun i : Fin n => g i.castSucc)) [g (Fin.last n)]
        (Comb.isPath_ofFn src tgt n (a ∘ Fin.castSucc) (fun i => g i.castSucc)
          (fun i => hs i.castSucc) (fun i => ht i.castSucc))
        ⟨hs (Fin.last n), ht (Fin.last n)⟩)

end FiniteChains.ContinuousEdgeWords
end

section
open scoped Classical unitInterval Topology
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb
open ContinuousEdgeWords CategoryTheory Simplicial

variable {P : Type} [PartialOrder P]

def affineOrderWordPath (l : List ((orderCx P).E × Bool)) {a b : P}
    (hl : IsPath (orderCx P).src (orderCx P).tgt l a b) :
    Path (orderNerveRealizationVertex a) (orderNerveRealizationVertex b) :=
  realize (orderCx P).src (orderCx P).tgt (orderNerveRealizationVertex (P := P))
    (fun e => orderNerveAffineEdgePath (P := P) e.property) l hl


theorem comparablePath_homotopic_single {a b : P} (h : a ≤ b ∨ b ≤ a)
    (g : (orderCx P).E × Bool)
    (hs : a = germSrc (orderCx P).src (orderCx P).tgt g)
    (ht : germTgt (orderCx P).src (orderCx P).tgt g = b) :
    (orderNerveComparablePath h).Homotopic (affineOrderWordPath [g] ⟨hs, ht⟩) := by
  subst a
  subst b
  have he : orderNerveComparablePath h =
      germPath (orderCx P).src (orderCx P).tgt (orderNerveRealizationVertex (P := P))
        (fun e => orderNerveAffineEdgePath e.property) g := by
    apply Path.ext
    funext t
    apply orderNerveRealizationCoordinates_injective P
    funext p
    erw [orderNerveComparablePath_coordinates, (show orderNerveRealizationCoordinates P
      (germPath (orderCx P).src (orderCx P).tgt (orderNerveRealizationVertex (P := P))
        (fun e => orderNerveAffineEdgePath e.property) g t) p =
      (1 - t) * (if germSrc (orderCx P).src (orderCx P).tgt g = p then 1 else 0) +
        t * (if germTgt (orderCx P).src (orderCx P).tgt g = p then 1 else 0) by
      rcases g with ⟨e, b⟩
      cases b
      · simp only [germPath, Path.symm_apply, Function.comp_apply, orderNerveAffineEdgePath_coordinates,
          unitInterval.coe_symm_eq, germSrc_false, germTgt_false]
        ring
      · exact orderNerveAffineEdgePath_coordinates e.property t p)]
  erw [he]
  exact (Path.Homotopic.trans_refl _).symm



theorem affineOrderWordPath_map {Q : Type} [PartialOrder Q]
    (f : P → Q) (hf : Monotone f) (l : List ((orderCx P).E × Bool)) {a b : P}
    (hl : IsPath (orderCx P).src (orderCx P).tgt l a b) (t : I) :
    orderNerveRealizationMap f hf (affineOrderWordPath l hl t) =
      affineOrderWordPath (mapPath (orderCxMap f hf) l)
        (isPath_mapPath (orderCxMap f hf) hl) t := by
  induction l generalizing a t with
  | nil =>
    cases hl
    exact (by
      exact congrArg (fun k : TopCat.of (SimplexCategory.toTop.obj ⦋0⦌) ⟶
          orderNerveRealization Q => k default)
        (orderNerveRealizationSimplex_natural f hf (ComposableArrows.mk₀ b)))
  | cons g l ih =>
    obtain ⟨rfl, ht⟩ := hl
    simp only [affineOrderWordPath, realize, mapPath, List.map_cons, Path.trans_apply, Path.cast_coe]
    split_ifs with hhalf
    · exact (by
      rcases g with ⟨e, b⟩
      cases b
      · change orderNerveRealizationMap f hf
          (orderNerveAffineEdgePath e.property (unitInterval.symm _)) =
            orderNerveAffineEdgePath (hf e.property) (unitInterval.symm _)
        simpa only [orderNerveComparablePath, dif_pos e.property, dif_pos (hf e.property)] using
          orderNerveComparablePath_natural f hf (Or.inl e.property)
            (Or.inl (hf e.property)) (unitInterval.symm _)
      · change orderNerveRealizationMap f hf (orderNerveAffineEdgePath e.property _) =
          orderNerveAffineEdgePath (hf e.property) _
        simpa only [orderNerveComparablePath, dif_pos e.property, dif_pos (hf e.property)] using
          orderNerveComparablePath_natural f hf (Or.inl e.property) (Or.inl (hf e.property)) _)
    · rcases g with ⟨e, direction⟩
      cases direction <;> simpa only [affineOrderWordPath, mapPath] using
        ih ht ⟨2 * t - 1, by constructor <;> linarith [t.property.1, t.property.2]⟩

end FiniteChains.Comb
end

namespace FiniteChains.PresModel
open Comb
open scoped Classical

variable {A J : Type} (w : J → List (A × Bool)) (j : J)

def circleSegmentGerm (k : Fin (w j).length) (t : Fin 4) :
    (orderCx (TCirc w)).E × Bool :=
  ![ordPos (TCirc.cor_le_cedgL w k.isLt),
    ordNeg (TCirc.cmid_le_cedgL w k.isLt),
    ordPos (TCirc.cmid_le_cedgR w k.isLt),
    ordNeg (TCirc.cor_csucc_le_cedgR w k.isLt)] t

def circleIndexedGerm (i : Fin ((w j).length * 4)) : (orderCx (TCirc w)).E × Bool :=
  circleSegmentGerm w j (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2

@[simp] theorem circleIndexedGerm_pair (k : Fin (w j).length) (t : Fin 4) :
    circleIndexedGerm w j (finProdFinEquiv (k, t)) = circleSegmentGerm w j k t := by
  simp only [circleIndexedGerm, Equiv.symm_apply_apply]

theorem circleIndexedGerm_src (i : Fin ((w j).length * 4)) :
    germSrc (orderCx (TCirc w)).src (orderCx (TCirc w)).tgt (circleIndexedGerm w j i) =
      ((relatorCircleIndexEquiv w j).symm i).val := by
  obtain ⟨⟨k, t⟩, rfl⟩ := finProdFinEquiv.surjective i
  rw [circleIndexedGerm_pair, relatorCircleIndex_symm_pair]
  fin_cases t <;> rfl

theorem circleIndexedGerm_tgt (hn : 0 < (w j).length) (i : Fin ((w j).length * 4)) :
    germTgt (orderCx (TCirc w)).src (orderCx (TCirc w)).tgt (circleIndexedGerm w j i) =
      (relatorCircleSuccessor w j hn ((relatorCircleIndexEquiv w j).symm i)).val := by
  obtain ⟨⟨k, t⟩, rfl⟩ := finProdFinEquiv.surjective i
  rw [circleIndexedGerm_pair, relatorCircleIndex_symm_pair]
  fin_cases t <;> rfl


theorem circleSegments_flatten (m : ℕ) :
    (List.ofFn (fun k : Fin m => segAt w j k.val)).flatten = circPath w j m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.ofFn_succ', List.concat_eq_append, List.flatten_append]
    simpa only [List.flatten_cons, List.flatten_nil, List.append_nil, circPath, Fin.val_castSucc, Fin.val_last] using
      congrArg (fun l => l ++ segAt w j m) ih

theorem circleIndexedGerm_ofFn : List.ofFn (circleIndexedGerm w j) = circLoop w j := by
  rw [List.ofFn_mul]
  have hblock (k : Fin (w j).length) :
      List.ofFn (fun t : Fin 4 => circleIndexedGerm w j
        ⟨k.val * 4 + t.val, by omega⟩) = segAt w j k.val := by
    have he t :
        (⟨k.val * 4 + t.val, by omega⟩ : Fin ((w j).length * 4)) =
          finProdFinEquiv (k, t) := by
      ext
      change k.val * 4 + t.val = t.val + 4 * k.val
      omega
    simp_rw [he, circleIndexedGerm_pair]
    exact (by
      rw [segAt, dif_pos k.isLt]
      simp [circleSegmentGerm, List.ofFn_succ])
  simp_rw [hblock]
  exact circleSegments_flatten w j (w j).length

end FiniteChains.PresModel

section
open scoped Classical unitInterval Topology
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.PresModel
open Comb RelativeAttachment ContinuousEdgeWords

variable {A J : Type} (w : J → List (A × Bool)) (j : J) (hn : 0 < (w j).length)

def circleWordVertex (i : Fin (relatorCircleSize w j + 2)) : TCirc w :=
  (relatorCircleEnumeration w j hn i).val

def circleWordGerm (i : Fin (relatorCircleSize w j + 2)) : (orderCx (TCirc w)).E × Bool :=
  circleIndexedGerm w j (Fin.cast (relatorCircleSize_add_two w j hn) i)

theorem circleWordGerm_src (i : Fin (relatorCircleSize w j + 2)) :
    circleWordVertex w j hn i =
      germSrc (orderCx (TCirc w)).src (orderCx (TCirc w)).tgt (circleWordGerm w j hn i) := by
  rw [circleWordGerm, circleIndexedGerm_src]
  rfl

theorem circleWordGerm_tgt (i : Fin (relatorCircleSize w j + 1)) :
    germTgt (orderCx (TCirc w)).src (orderCx (TCirc w)).tgt
      (circleWordGerm w j hn i.castSucc) = circleWordVertex w j hn i.succ := by
  rw [circleWordGerm, circleIndexedGerm_tgt w j hn]
  exact congrArg Subtype.val (relatorCircleEnumeration_next w j hn i)

theorem circleWordGerm_last_tgt :
    germTgt (orderCx (TCirc w)).src (orderCx (TCirc w)).tgt
      (circleWordGerm w j hn (Fin.last (relatorCircleSize w j + 1))) =
        circleWordVertex w j hn 0 := by
  rw [circleWordGerm, circleIndexedGerm_tgt w j hn]
  exact congrArg Subtype.val (relatorCircleEnumeration_last_next w j hn)

theorem circleWordGerms_eq : List.ofFn (circleWordGerm w j hn) = circLoop w j := by
  rw [List.ofFn_congr (relatorCircleSize_add_two w j hn)]
  have he : (fun i => circleWordGerm w j hn
      (Fin.cast (relatorCircleSize_add_two w j hn).symm i)) = circleIndexedGerm w j := by
    funext i
    rfl
  rw [he, circleIndexedGerm_ofFn]

def circleWordEdge (i : Fin (relatorCircleSize w j + 1)) :
    Path (orderNerveRealizationVertex (circleWordVertex w j hn i.castSucc))
      (orderNerveRealizationVertex (circleWordVertex w j hn i.succ)) :=
  orderNerveComparablePath (P := TCirc w) ((relatorCircleCycle w j hn).consecutive i)

def circleWordLastEdge :
    Path (orderNerveRealizationVertex
      (circleWordVertex w j hn (Fin.last (relatorCircleSize w j + 1))))
        (orderNerveRealizationVertex (circleWordVertex w j hn 0)) :=
  orderNerveComparablePath (P := TCirc w) (relatorCircleCycle w j hn).closing

def circleFullLoop :
    Path (orderNerveRealizationVertex (circleWordVertex w j hn 0))
      (orderNerveRealizationVertex (circleWordVertex w j hn 0)) :=
  (arcConcat (relatorCircleSize w j)
    (orderNerveRealizationVertex ∘ circleWordVertex w j hn) (circleWordEdge w j hn)).trans
      (circleWordLastEdge w j hn)

theorem circleTraversal_to_full (t : I) :
    orderNerveRealizationMap (Subtype.val : RelatorCircle w j → TCirc w) (fun _ _ h => h)
      (relatorCircleTraversal w j hn t) = circleFullLoop w j hn t := by
  have he i s :
      orderNerveRealizationMap Subtype.val (fun _ _ h => h)
        ((relatorCircleCycle w j hn).edge i s) = circleWordEdge w j hn i s :=
    orderNerveComparablePath_natural Subtype.val (fun _ _ h => h)
      ((relatorCircleCycle w j hn).consecutive i)
      ((relatorCircleCycle w j hn).consecutive i) s
  have hp := arcConcat_natural
    (orderNerveRealizationMap Subtype.val (fun _ _ h => h))
    (relatorCircleSize w j)
    (orderNerveRealizationVertex ∘ (relatorCircleCycle w j hn).vertex)
    (orderNerveRealizationVertex ∘ circleWordVertex w j hn)
    (relatorCircleCycle w j hn).edge (circleWordEdge w j hn) he
  change orderNerveRealizationMap Subtype.val (fun _ _ h => h)
    (((relatorCircleCycle w j hn).prefix.trans (relatorCircleCycle w j hn).lastEdge) t) = _
  simp only [circleFullLoop, Path.trans_apply]
  split_ifs
  · exact hp _
  · exact orderNerveComparablePath_natural Subtype.val (fun _ _ h => h)
      (relatorCircleCycle w j hn).closing (relatorCircleCycle w j hn).closing _


def circleWordValid : IsPath (orderCx (TCirc w)).src (orderCx (TCirc w)).tgt
    (circLoop w j) (circleWordVertex w j hn 0) (circleWordVertex w j hn 0) := by
  rw [← circleWordGerms_eq w j hn]
  exact (by
    rw [List.ofFn_succ', List.concat_eq_append]
    exact (isPath_ofFn _ _ (relatorCircleSize w j + 1) (circleWordVertex w j hn)
      (fun i => circleWordGerm w j hn i.castSucc)
      (fun i => circleWordGerm_src w j hn i.castSucc) (circleWordGerm_tgt w j hn)).append
      ⟨circleWordGerm_src w j hn _, circleWordGerm_last_tgt w j hn⟩)

theorem circleFullLoop_homotopic_word :
    (circleFullLoop w j hn).Homotopic
      (affineOrderWordPath (circLoop w j) (circleWordValid w j hn)) := by
  have hp := (arcConcat_homotopic_concat (relatorCircleSize w j)
      (orderNerveRealizationVertex ∘ circleWordVertex w j hn) (circleWordEdge w j hn)).trans
    (concat_homotopic_realize_ofFn (orderCx (TCirc w)).src (orderCx (TCirc w)).tgt
      (orderNerveRealizationVertex (P := TCirc w))
      (fun e => orderNerveAffineEdgePath e.property)
      (relatorCircleSize w j + 1) (circleWordVertex w j hn)
      (fun i => circleWordGerm w j hn i.castSucc)
      (fun i => circleWordGerm_src w j hn i.castSucc) (circleWordGerm_tgt w j hn)
      (circleWordEdge w j hn) (fun i => comparablePath_homotopic_single (P := TCirc w)
        ((relatorCircleCycle w j hn).consecutive i) _
        (circleWordGerm_src w j hn i.castSucc) (circleWordGerm_tgt w j hn i)))
  have hl := comparablePath_homotopic_single (P := TCirc w) (relatorCircleCycle w j hn).closing
    (circleWordGerm w j hn (Fin.last (relatorCircleSize w j + 1)))
    (circleWordGerm_src w j hn _) (circleWordGerm_last_tgt w j hn)
  have H := (hp.hcomp hl).trans
    (realize_append (orderCx (TCirc w)).src (orderCx (TCirc w)).tgt
      (orderNerveRealizationVertex (P := TCirc w))
      (fun e => orderNerveAffineEdgePath (P := TCirc w) e.property)
      (List.ofFn (fun i : Fin (relatorCircleSize w j + 1) => circleWordGerm w j hn i.castSucc))
      [circleWordGerm w j hn (Fin.last (relatorCircleSize w j + 1))]
      (isPath_ofFn _ _ (relatorCircleSize w j + 1) (circleWordVertex w j hn)
        (fun i => circleWordGerm w j hn i.castSucc)
        (fun i => circleWordGerm_src w j hn i.castSucc) (circleWordGerm_tgt w j hn))
      ⟨circleWordGerm_src w j hn _, circleWordGerm_last_tgt w j hn⟩)
  have hw : List.ofFn (fun i => circleWordGerm w j hn i.castSucc) ++
      [circleWordGerm w j hn (Fin.last (relatorCircleSize w j + 1))] = circLoop w j := by
    rw [← List.concat_eq_append, ← List.ofFn_succ', circleWordGerms_eq]
  simpa only [hw, circleFullLoop, circleWordLastEdge, relatorCircleCycle, affineOrderWordPath, Function.comp_apply] using H

end FiniteChains.PresModel
end

section
open scoped Classical unitInterval Topology
namespace FiniteChains.Comb.FinitePosetCycle
open RelativeAttachment ContinuousEdgeWords

variable {P Q : Type} [PartialOrder P] [PartialOrder Q] {n : ℕ}
  (C : FinitePosetCycle P n) (f : P → Q) (hf : Monotone f)

def mappedEdge (i : Fin (n + 1)) :=
  orderNerveComparablePath ((C.consecutive i).imp (fun h => hf h) (fun h => hf h))

def mappedLastEdge := orderNerveComparablePath (C.closing.imp (fun h => hf h) (fun h => hf h))

def mappedLoop : Path (orderNerveRealizationVertex (f (C.vertex 0)))
    (orderNerveRealizationVertex (f (C.vertex 0))) :=
  (arcConcat n (fun i => orderNerveRealizationVertex (f (C.vertex i)))
    (C.mappedEdge f hf)).trans (C.mappedLastEdge f hf)

theorem mappedLoop_apply (t : I) :
    C.mappedLoop f hf t = orderNerveRealizationMap f hf (C.traversal t) := by
  have hp := arcConcat_natural (orderNerveRealizationMap f hf) n
    (orderNerveRealizationVertex ∘ C.vertex)
    (fun i => orderNerveRealizationVertex (f (C.vertex i))) C.edge (C.mappedEdge f hf)
    (fun i s => orderNerveComparablePath_natural f hf
      (C.consecutive i) ((C.consecutive i).imp (fun h => hf h) (fun h => hf h)) s)
  simp only [mappedLoop, traversal, Path.trans_apply]
  split_ifs
  · exact (hp _).symm
  · exact (orderNerveComparablePath_natural f hf C.closing
      (C.closing.imp (fun h => hf h) (fun h => hf h)) _).symm

variable (g : Fin (n + 2) → (orderCx Q).E × Bool)
  (hs : ∀ i, f (C.vertex i) = germSrc (orderCx Q).src (orderCx Q).tgt (g i))
  (ht : ∀ i : Fin (n + 1), germTgt (orderCx Q).src (orderCx Q).tgt (g i.castSucc) =
    f (C.vertex i.succ))
  (hclose : germTgt (orderCx Q).src (orderCx Q).tgt (g (Fin.last (n + 1))) = f (C.vertex 0))

def mappedWordValid : IsPath (orderCx Q).src (orderCx Q).tgt (List.ofFn g)
    (f (C.vertex 0)) (f (C.vertex 0)) := by
  rw [List.ofFn_succ', List.concat_eq_append]
  exact (isPath_ofFn _ _ (n + 1) (f ∘ C.vertex) (fun i => g i.castSucc)
    (fun i => hs i.castSucc) ht).append ⟨hs _, hclose⟩

theorem mappedLoop_homotopic_word :
    (C.mappedLoop f hf).Homotopic
      (affineOrderWordPath (List.ofFn g) (C.mappedWordValid f g hs ht hclose)) := by
  have hp := (arcConcat_homotopic_concat n
      (fun i => orderNerveRealizationVertex (f (C.vertex i))) (C.mappedEdge f hf)).trans
    (concat_homotopic_realize_ofFn (orderCx Q).src (orderCx Q).tgt
      (orderNerveRealizationVertex (P := Q)) (fun e => orderNerveAffineEdgePath e.property)
      (n + 1) (f ∘ C.vertex) (fun i => g i.castSucc) (fun i => hs i.castSucc) ht
      (C.mappedEdge f hf) (fun i => comparablePath_homotopic_single
        ((C.consecutive i).imp (fun h => hf h) (fun h => hf h)) _ (hs i.castSucc) (ht i)))
  have hl := comparablePath_homotopic_single
    (C.closing.imp (fun h => hf h) (fun h => hf h)) (g (Fin.last (n + 1)))
    (hs _) hclose
  have H := (hp.hcomp hl).trans
    (realize_append (orderCx Q).src (orderCx Q).tgt (orderNerveRealizationVertex (P := Q))
      (fun e => orderNerveAffineEdgePath e.property)
      (List.ofFn (fun i : Fin (n + 1) => g i.castSucc)) [g (Fin.last (n + 1))]
      (isPath_ofFn _ _ (n + 1) (f ∘ C.vertex) (fun i => g i.castSucc)
        (fun i => hs i.castSucc) ht) ⟨hs _, hclose⟩)
  have he : List.ofFn (fun i : Fin (n + 1) => g i.castSucc) ++ [g (Fin.last (n + 1))] =
      List.ofFn g := by simpa using (List.ofFn_succ' g).symm
  simpa only [he, mappedLoop, mappedLastEdge, affineOrderWordPath] using H

end FiniteChains.Comb.FinitePosetCycle
end

section
open scoped Classical unitInterval Topology
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.PresModel
open Comb RelativeAttachment ContinuousEdgeWords ClassicalGraphModel

variable {A J : Type}

def roseGeneratorWord (a : A) : List ((orderCx (Rose A)).E × Bool) :=
  [ordPos (Rose.base_le_edg a false), ordNeg (Rose.mid_le_edg a false),
    ordPos (Rose.mid_le_edg a true), ordNeg (Rose.base_le_edg a true)]

theorem roseGeneratorWord_valid (a : A) :
    IsPath (orderCx (Rose A)).src (orderCx (Rose A)).tgt (roseGeneratorWord a) .base .base :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

def roseLetterWord (p : A × Bool) : List ((orderCx (Rose A)).E × Bool) :=
  if p.2 then roseGeneratorWord p.1 else revPath (X := orderCx (Rose A)) (roseGeneratorWord p.1)

def roseWord (l : List (A × Bool)) : List ((orderCx (Rose A)).E × Bool) := l.flatMap roseLetterWord

theorem roseLetterWord_valid (p : A × Bool) :
    IsPath (orderCx (Rose A)).src (orderCx (Rose A)).tgt (roseLetterWord p) .base .base := by grind [isPath_revPath, roseGeneratorWord_valid, roseLetterWord]

theorem roseWord_valid (l : List (A × Bool)) :
    IsPath (orderCx (Rose A)).src (orderCx (Rose A)).tgt (roseWord l) .base .base := by
  induction l with
  | nil => rfl
  | cons p l ih => exact (roseLetterWord_valid p).append ih

def roseGeneratorPath (a : A) : Path (orderRoseBase A) (orderRoseBase A) :=
  roseFourCycle.mappedLoop (roseCopy a) (roseCopy a).monotone

theorem roseGeneratorPath_apply (a : A) (t : I) :
    roseGeneratorPath a t = roseCopyRealization a (orderRoseTraversal t) :=
  roseFourCycle.mappedLoop_apply (roseCopy a) (roseCopy a).monotone t

theorem roseGeneratorPath_homotopic_word (a : A) :
    (roseGeneratorPath a).Homotopic (affineOrderWordPath (roseGeneratorWord a) (roseGeneratorWord_valid a)) := by
  let g  :=
    ![ordPos (Rose.base_le_edg a false), ordNeg (Rose.mid_le_edg a false),
      ordPos (Rose.mid_le_edg a true), ordNeg (Rose.base_le_edg a true)]
  have hs : ∀ i, roseCopy a (roseFourCycle.vertex i) =
      germSrc (orderCx (Rose A)).src (orderCx (Rose A)).tgt (g i) := by
    intro i
    fin_cases i <;> rfl
  have ht : ∀ i : Fin 3, germTgt (orderCx (Rose A)).src (orderCx (Rose A)).tgt (g i.castSucc) =
      roseCopy a (roseFourCycle.vertex i.succ) := by
    intro i
    fin_cases i <;> rfl
  have H := roseFourCycle.mappedLoop_homotopic_word (roseCopy a) (roseCopy a).monotone g hs ht rfl
  have hg : List.ofFn g = roseGeneratorWord a := by simp [g, roseGeneratorWord, List.ofFn_succ]
  simpa only [hg, roseGeneratorPath, roseFourCycle, orderRoseBase] using H

def orderRoseRead : List (A × Bool) → Path (orderRoseBase A) (orderRoseBase A)
  | [] => Path.refl _
  | (a, b) :: l => (if b then roseGeneratorPath a else (roseGeneratorPath a).symm).trans (orderRoseRead l)


theorem roseWord_homotopic_read (l : List (A × Bool)) :
    (affineOrderWordPath (roseWord l) (roseWord_valid l)).Homotopic (orderRoseRead l) := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    exact (realize_append (orderCx (Rose A)).src (orderCx (Rose A)).tgt
      (orderNerveRealizationVertex (P := Rose A))
      (fun e => orderNerveAffineEdgePath e.property)
      (roseLetterWord p) (roseWord l) (roseLetterWord_valid p) (roseWord_valid l)).symm.trans
      ((show (affineOrderWordPath (roseLetterWord p) (roseLetterWord_valid p)).Homotopic
      (if p.2 then roseGeneratorPath p.1 else (roseGeneratorPath p.1).symm) by
        rcases p with ⟨a, b⟩
        cases b
        · exact (realize_revPath (K := orderCx (Rose A)) (orderNerveRealizationVertex (P := Rose A))
            (fun e => orderNerveAffineEdgePath e.property) (roseGeneratorWord a)
            (roseGeneratorWord_valid a)).symm.trans (roseGeneratorPath_homotopic_word a).symm.symm₂
        · exact (roseGeneratorPath_homotopic_word a).symm).hcomp ih)

def classicalRoseRead : List (A × Bool) → Path (roseVertex A) (roseVertex A)
  | [] => Path.refl _
  | (a, b) :: l =>
      (if b then graphEdgePath (roseAttaching A) a else (graphEdgePath (roseAttaching A) a).symm).trans
        (classicalRoseRead l)

theorem orderRoseRead_classical (l : List (A × Bool)) (t : I) :
    orderRoseRealizationHomeomorph A (orderRoseRead l t) = classicalRoseRead l t := by
  induction l generalizing t with
  | nil => exact orderRoseRealizationHomeomorph_base A
  | cons p l ih =>
    rcases p with ⟨a, b⟩
    by_cases ht : (t : ℝ) ≤ 1 / 2
    · simp only [orderRoseRead, classicalRoseRead, Path.trans_apply, dif_pos ht, if_pos ht]
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, Path.symm_apply,
        Function.comp_apply, roseGeneratorPath_apply, orderRoseRealizationHomeomorph_interval]
      all_goals rfl
    · simp only [orderRoseRead, classicalRoseRead, Path.trans_apply, dif_neg ht, if_neg ht]
      exact ih _

theorem classicalRoseRead_eq_realize (l : List (A × Bool))
    (hl : IsPath (graphSrc (roseAttaching A)) (graphTgt (roseAttaching A)) l PUnit.unit PUnit.unit) :
    classicalRoseRead l = realize (graphSrc (roseAttaching A)) (graphTgt (roseAttaching A))
      (old (roseAttaching A) (boundaryFamilyInclusion A (Fin 1 → ℝ)))
      (graphEdgePath (roseAttaching A)) l hl := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    rcases p with ⟨a, b⟩
    cases b <;> simp only [classicalRoseRead, Bool.false_eq_true, ↓reduceIte,
      realize, germPath, Path.cast_rfl_rfl]
    all_goals congr 1; exact ih _

variable (w : J → List (A × Bool))

theorem mapPath_aFun_segAt (j : J) {k : ℕ} (hk : k < (w j).length) :
    mapPath (orderCxMap (aFun w) (aFun_monotone w)) (segAt w j k) = roseLetterWord (w j)[k] := by
  have hp : (w j)[k]? = some (w j)[k] := List.getElem?_eq_getElem hk
  have hmid : aFun w (TCirc.pt w j k CPos.cmid) = Rose.mid (w j)[k].1 := by
    rw [aFun_pt_cmid_of_get w hp]
  have hL : aFun w (TCirc.pt w j k CPos.cedgL) = Rose.edg (w j)[k].1 (!(w j)[k].2) := by
    rw [aFun_pt_cedgL_of_get w hp]
  have hR : aFun w (TCirc.pt w j k CPos.cedgR) = Rose.edg (w j)[k].1 (w j)[k].2 := by
    rw [aFun_pt_cedgR_of_get w hp]
  rw [segAt, dif_pos hk]
  change [ordPos ((aFun_monotone w) (TCirc.cor_le_cedgL w hk)),
    ordNeg ((aFun_monotone w) (TCirc.cmid_le_cedgL w hk)),
    ordPos ((aFun_monotone w) (TCirc.cmid_le_cedgR w hk)),
    ordNeg ((aFun_monotone w) (TCirc.cor_csucc_le_cedgR w hk))] = _
  rcases he : (w j)[k] with ⟨a, b⟩
  rw [he] at hmid hL hR
  cases b
  · change _ = [ordPos (Rose.base_le_edg a true), ordNeg (Rose.mid_le_edg a true),
      ordPos (Rose.mid_le_edg a false), ordNeg (Rose.base_le_edg a false)]
    simp
    exact ⟨ordPos_congr rfl hL _ _, ordNeg_congr hmid hL _ _,
      ordPos_congr hmid hR _ _, ordNeg_congr rfl hR _ _⟩
  · change _ = roseGeneratorWord a
    simp only [roseGeneratorWord, List.cons.injEq, and_true]
    exact ⟨ordPos_congr rfl hL _ _, ordNeg_congr hmid hL _ _,
      ordPos_congr hmid hR _ _, ordNeg_congr rfl hR _ _⟩

theorem mapPath_aFun_circPath (j : J) : ∀ {m : ℕ}, m ≤ (w j).length →
    mapPath (orderCxMap (aFun w) (aFun_monotone w)) (circPath w j m) = roseWord ((w j).take m) := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
    intro hm
    have hlt : m < (w j).length := by omega
    have hsplit : (w j).take (m + 1) = (w j).take m ++ [(w j)[m]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hlt]
      rfl
    change mapPath _ (circPath w j m ++ segAt w j m) = _
    rw [mapPath_append, ih (Nat.le_of_lt hlt), mapPath_aFun_segAt w j hlt, hsplit]
    simp only [roseWord, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem mapPath_aFun_circLoop (j : J) :
    mapPath (orderCxMap (aFun w) (aFun_monotone w)) (circLoop w j) = roseWord (w j) := by
  simpa only [List.take_length, circLoop] using mapPath_aFun_circPath w j (le_refl (w j).length)

end FiniteChains.PresModel
end

section
open scoped Classical unitInterval Topology
namespace FiniteChains.PresModel
open Comb RelativeAttachment ContinuousEdgeWords ClassicalGraphModel

variable {A J : Type} (w : J → List (A × Bool)) (j : J) (hn : 0 < (w j).length)

def presReadTraversal : Path (orderRoseBase A) (orderRoseBase A) where
  toFun t := presCircleWordMap w j (relatorCircleTraversal w j hn t)
  continuous_toFun := (presCircleWordMap w j).continuous.comp
    (relatorCircleTraversal w j hn).continuous
  source' := by
    rw (config := { transparency := .default }) [(relatorCircleTraversal w j hn).source]
    exact realizedMap_vertex (fun c : RelatorCircle w j => aFun w c.val)
      (fun _ _ h => aFun_monotone w h) (relatorCircleEnumeration w j hn 0)
  target' := by
    rw (config := { transparency := .default }) [(relatorCircleTraversal w j hn).target]
    exact realizedMap_vertex (fun c : RelatorCircle w j => aFun w c.val)
      (fun _ _ h => aFun_monotone w h) (relatorCircleEnumeration w j hn 0)

theorem presReadTraversal_homotopic_word :
    (presReadTraversal w j hn).Homotopic (orderRoseRead (w j)) := by
  let f  :=
    (orderNerveRealizationMap (aFun w) (aFun_monotone w)).hom
  have hb  :=
    (realizedMap_vertex (aFun w) (aFun_monotone w) (circleWordVertex w j hn 0)).symm
  have H := ((circleFullLoop_homotopic_word w j hn).map f).pathCast hb hb
  have hleft : ((circleFullLoop w j hn).map f.continuous).cast hb hb =
      presReadTraversal w j hn := by
    apply Path.ext
    funext t
    change orderNerveRealizationMap (aFun w) (aFun_monotone w) (circleFullLoop w j hn t) = _
    erw [← circleTraversal_to_full, orderNerveRealizationMap_comp]
    rfl
  have hright : ((affineOrderWordPath (circLoop w j) (circleWordValid w j hn)).map f.continuous).cast hb hb =
      affineOrderWordPath (roseWord (w j)) (roseWord_valid (w j)) := by
    apply Path.ext
    funext t
    erw [affineOrderWordPath_map]
    have wordEq {l m : List ((orderCx (Rose A)).E × Bool)} {a b : Rose A}
        (hl : IsPath (orderCx (Rose A)).src (orderCx (Rose A)).tgt l a b)
        (hm : IsPath (orderCx (Rose A)).src (orderCx (Rose A)).tgt m a b) (he : l = m) :
        affineOrderWordPath l hl t = affineOrderWordPath m hm t := by
      subst m
      rfl
    exact wordEq _ _ (mapPath_aFun_circLoop w j)
  erw [hleft, hright] at H
  exact H.trans (roseWord_homotopic_read (w j))

def classicalPresReadTraversal : Path (roseVertex A) (roseVertex A) :=
  ((presReadTraversal w j hn).map (orderRoseRealizationHomeomorph A).continuous).cast
    (orderRoseRealizationHomeomorph_base A).symm (orderRoseRealizationHomeomorph_base A).symm


variable (hw : ∀ j, w j ≠ [])

def classicalPresCellBoundary : C(UnitBoundary (Fin 2 → ℝ), ClassicalGraphModel.Rose A) :=
  (classicalPresWordAttaching w hw).comp
    (⟨fun z : UnitBoundary (Fin 2 → ℝ) => ⟨j, z⟩, by
      exact continuous_sigmaMk («σ» := fun _ : J => UnitBoundary (Fin 2 → ℝ)) (i := j)⟩ :
        C(UnitBoundary (Fin 2 → ℝ), BoundaryFamily J (Fin 2 → ℝ)))


/-- The actual canonical disk attaching map reads exactly its word,
up to endpoint-preserving reparametrization of the traversal. -/
theorem classicalPresWordAttaching_homotopic_read :
    (classicalPresCellBoundary w j hw).Homotopic
      ((squareLoopDesc (classicalRoseRead (w j))).comp unitBoundarySquareHomeomorph.toContinuousMap) := by
  have H := squareLoopDesc_homotopic
    (by
      have H := ((presReadTraversal_homotopic_word w j (List.length_pos_of_ne_nil (hw j))).map
        (orderRoseRealizationHomeomorph A).toContinuousMap).pathCast
        (orderRoseRealizationHomeomorph_base A).symm (orderRoseRealizationHomeomorph_base A).symm
      have he : ((orderRoseRead (w j)).map (orderRoseRealizationHomeomorph A).continuous).cast
          (orderRoseRealizationHomeomorph_base A).symm (orderRoseRealizationHomeomorph_base A).symm =
            classicalRoseRead (w j) := by
        apply Path.ext
        funext t
        exact orderRoseRead_classical (w j) t
      rwa [he] at H)
  erw [(show squareLoopDesc (classicalPresReadTraversal w j (List.length_pos_of_ne_nil (hw j))) =
      (classicalPresCellBoundary w j hw).comp unitBoundarySquareHomeomorph.symm.toContinuousMap by
    apply ContinuousMap.ext
    intro z
    obtain ⟨t, rfl⟩ := squareBoundaryTraversal_surjective z
    erw [squareLoopDesc_traversal]
    have hb := (relatorCircleCycle w j (List.length_pos_of_ne_nil (hw j))).boundaryHomeomorph_traversal t
    change orderRoseRealizationHomeomorph A
      (presCircleWordMap w j (relatorCircleTraversal w j (List.length_pos_of_ne_nil (hw j)) t)) =
        classicalPresWordAttaching w hw
          ⟨j, unitBoundarySquareHomeomorph.symm (squareBoundaryTraversal t)⟩
    erw [← hb]
    exact (classicalPresWordAttaching_link w hw j _).symm)] at H
  have H' := H.comp (ContinuousMap.Homotopic.refl unitBoundarySquareHomeomorph.toContinuousMap)
  simp_all

end FiniteChains.PresModel
end

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool))
  (f : P → PresPos w) (hf : IsPosetCover f) (hpos : ∀ j, 0 < (w j).length)


/-- A chain with boundary in the cylinder has exactly one coefficient at each
actual relator apex, just as an absolute two-cycle does. -/
theorem presCover_relative_fan_circle
    (c : StrictOrdTri P →₀ ℤ)
    (b : StrictOrdEdge {p : P // f p ∈ coneAdjBaseSet (S := circSet w)} →₀ ℤ)
    (hb : Comb.bdry2 (strictOrderCx P) c =
      chain1 (strictSubposetIncl {p : P | f p ∈ coneAdjBaseSet (S := circSet w)}) b)
    (p : PresCoverRelator w f) :
    presCoverConeCircleChain w f hf p.1.1 p.1.2 p.2 c =
      presCoverConeCircleChain w f hf p.1.1 p.1.2 p.2
        (presCoverRelatorFanChain w f hf (presCoverRelatorChain w f hf hpos c)) := by
  rw [presCoverRelatorFanChain_circle, presCoverRelatorChain_circle]
  exact relatorCircle_cycle_eq_smul_fundamental w p.1.2 _
    (by
      have hr : strictRayChain p.1.1
          (chain1 (strictSubposetIncl {q : P | f q ∈ coneAdjBaseSet}) b) = 0 := by
        clear hb
        induction b using Finsupp.induction_linear with
        | zero => simp
        | add b d hb hd => simp_all
        | single e n =>
          have hn : e.1.2.val ≠ p.1.1 := by
            intro he
            have hm := e.1.2.property
            erw [he, p.2] at hm
            rcases hm with ⟨a, ha⟩
            cases ha
          simp [chain1, strictSubposetIncl, strictOrderCxMap, strictRayChain, strictRayEdge, hn]
      erw [bdry1_chain1, ← strictTopLink_boundary p.1.1
        (presCover_apex_maximal w f hf p.1.1 p.1.2 p.2), hb, hr, map_zero]) (hpos p.1.2)

/-- Subtracting the actual coordinate fans leaves an actual finite cylinder chain. -/
theorem exists_presCover_relative_cone_cylinder_decomposition
    (c : StrictOrdTri P →₀ ℤ)
    (b : StrictOrdEdge {p : P // f p ∈ coneAdjBaseSet (S := circSet w)} →₀ ℤ)
    (hb : Comb.bdry2 (strictOrderCx P) c =
      chain1 (strictSubposetIncl {p : P | f p ∈ coneAdjBaseSet (S := circSet w)}) b) :
    ∃ d : StrictOrdTri {p : P // f p ∈ coneAdjBaseSet (S := circSet w)} →₀ ℤ,
      chain2 (strictSubposetIncl {p : P | f p ∈ coneAdjBaseSet (S := circSet w)}) d =
        c - presCoverRelatorFanChain w f hf (presCoverRelatorChain w f hf hpos c) := by
  let S  := {p | f p ∈ coneAdjBaseSet}
  let r := c - presCoverRelatorFanChain w f hf (presCoverRelatorChain w f hf hpos c)
  have hs : ∀ t ∈ r.support, t.1.1 ∈ S ∧ t.1.2.1 ∈ S ∧ t.1.2.2 ∈ S := by
    intro t ht
    have hlast : t.1.2.2 ∈ S := by
      by_contra hn
      cases hft : f t.1.2.2 with
      | inl x => exact hn ⟨x, hft.symm⟩
      | inr j =>
        let p : PresCoverRelator w f := ⟨(t.1.2.2, j), hft⟩
        let e : StrictOrdEdge (StrictBelow t.1.2.2) :=
          ⟨(⟨t.1.1, t.2.1.trans t.2.2⟩, ⟨t.1.2.1, t.2.2⟩), t.2.1⟩
        have he := congrArg
          (fun z => z ((presCoverConeCircleHom w f hf p.1.1 p.1.2 p.2).onE e))
          (presCover_relative_fan_circle w f hf hpos c b hb p)
        erw [presCoverConeCircleChain_apply, presCoverConeCircleChain_apply] at he
        exact (Finsupp.mem_support_iff.mp ht) (sub_eq_zero.mpr he)
    exact ⟨coneAdjBaseSet_down_closed hlast (hf.mono (t.2.1.le.trans t.2.2.le)),
      coneAdjBaseSet_down_closed hlast (hf.mono t.2.2.le), hlast⟩
  refine ⟨Finsupp.comapDomain (strictSubposetIncl S).onF r
    (strictSubposetIncl_onF_injective S).injOn, ?_⟩
  exact Finsupp.mapDomain_comapDomain _ (strictSubposetIncl_onF_injective S) r
    (fun t ht => (strictSubposetIncl_onF_range S t).mpr (hs t ht))

/-- Relative fillings recover exactly the collapsed attaching boundary of their
actual relator coefficients. -/
theorem presCover_relative_collapsed_boundary
    (c : StrictOrdTri P →₀ ℤ)
    (b : StrictOrdEdge {p : P // f p ∈ coneAdjBaseSet (S := circSet w)} →₀ ℤ)
    (hb : Comb.bdry2 (strictOrderCx P) c =
      chain1 (strictSubposetIncl {p : P | f p ∈ coneAdjBaseSet (S := circSet w)}) b) :
    normalizedStrictChain1 (presCoverCylinderCollapse w f hf)
      (presCoverCylinderCollapse_monotone w f hf) b =
    normalizedStrictChain1 (presCoverCylinderCollapse w f hf)
      (presCoverCylinderCollapse_monotone w f hf)
      (presCoverCylinderRelatorBoundaryChain w f hf (presCoverRelatorChain w f hf hpos c)) := by
  obtain ⟨d, hd⟩ := exists_presCover_relative_cone_cylinder_decomposition w f hf hpos c b hb
  have he : Comb.bdry2 (strictOrderCx _) d =
      b - presCoverCylinderRelatorBoundaryChain w f hf (presCoverRelatorChain w f hf hpos c) := by
    apply Finsupp.mapDomain_injective (strictSubposetIncl_onE_injective
      {p : P | f p ∈ coneAdjBaseSet})
    change chain1 (strictSubposetIncl {p : P | f p ∈ coneAdjBaseSet})
      (Comb.bdry2 (strictOrderCx {p : P // f p ∈ coneAdjBaseSet}) d) =
      chain1 (strictSubposetIncl {p : P | f p ∈ coneAdjBaseSet}) _
    calc
      _ = Comb.bdry2 (strictOrderCx P)
          (chain2 (strictSubposetIncl {p : P | f p ∈ coneAdjBaseSet}) d) :=
        (bdry2_chain2 (strictSubposetIncl {p : P | f p ∈ coneAdjBaseSet}) d).symm
      _ = _ := by
        rw [hd, map_sub, hb, map_sub, presCoverCylinderRelatorBoundaryChain_inclusion]
  have hz := cylinderCover_collapse_boundary_zero w (coneAdjCoverBaseEnd_isPosetCover f hf) d
  rw [he, map_sub] at hz
  exact sub_eq_zero.mp hz

end FiniteChains.PresModel
end

namespace FiniteChains
open BlockFamily

universe u
variable {C S I R : Type u} [Ring R]

@[simp] theorem fsOldOneIncl_single (c : C) (a : R) :
    fsOldOneIncl (Z := S) (Finsupp.single c a) = Finsupp.single (Sum.inl c) a := by
  classical
  ext i
  cases i <;> simp [Finsupp.single_apply]

/-- The off-diagonal correction has values entirely in the retained core. -/
def coreSlideCorrection (lam : S → C →₀ R) :
    ((C ⊕ S) →₀ R) →ₗ[R] ((C ⊕ S) →₀ R) :=
  Finsupp.linearCombination R
    (Sum.elim (fun _ : C => 0) (fun s => fsOldOneIncl (lam s)))

@[simp] theorem coreSlideCorrection_single_inl (lam : S → C →₀ R) (c : C) (a : R) :
    coreSlideCorrection lam (Finsupp.single (Sum.inl c) a) = 0 := by
  simp [coreSlideCorrection]

@[simp] theorem coreSlideCorrection_single_inr (lam : S → C →₀ R) (s : S) (a : R) :
    coreSlideCorrection lam (Finsupp.single (Sum.inr s) a) = a • fsOldOneIncl (lam s) := by
  simp [coreSlideCorrection]

theorem coreSlideCorrection_core (lam : S → C →₀ R) (x : C →₀ R) :
    coreSlideCorrection lam (fsOldOneIncl x) = 0 := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp_all
  | single c a => simp

theorem coreSlideCorrection_square (lam : S → C →₀ R) (x : (C ⊕ S) →₀ R) :
    coreSlideCorrection lam (coreSlideCorrection lam x) = 0 := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp_all
  | single c a =>
      cases c with
      | inl c => simp
      | inr s =>
          rw [coreSlideCorrection_single_inr, map_smul, coreSlideCorrection_core, smul_zero]

def coreSlideForward (lam : S → C →₀ R) :
    ((C ⊕ S) →₀ R) →ₗ[R] ((C ⊕ S) →₀ R) :=
  LinearMap.id - coreSlideCorrection lam

def coreSlideReverse (lam : S → C →₀ R) :
    ((C ⊕ S) →₀ R) →ₗ[R] ((C ⊕ S) →₀ R) :=
  LinearMap.id + coreSlideCorrection lam

@[simp] theorem coreSlideForward_reverse (lam : S → C →₀ R) (x : (C ⊕ S) →₀ R) :
    coreSlideForward lam (coreSlideReverse lam x) = x := by simp_all [coreSlideForward, coreSlideReverse, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply, map_add, coreSlideCorrection_square]

@[simp] theorem coreSlideReverse_forward (lam : S → C →₀ R) (x : (C ⊕ S) →₀ R) :
    coreSlideReverse lam (coreSlideForward lam x) = x := by simp_all [coreSlideForward, coreSlideReverse, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply, map_sub, coreSlideCorrection_square]

/-- A column calculation suffices for the simultaneous boundary identity. -/
theorem coreSlide_boundary (lam : S → C →₀ R)
    (old new : ((C ⊕ S) →₀ R) →ₗ[R] (I →₀ R))
    (hcore : ∀ c, new (Finsupp.single (Sum.inl c) 1) = old (Finsupp.single (Sum.inl c) 1))
    (hextra : ∀ s, new (Finsupp.single (Sum.inr s) 1) =
      old (Finsupp.single (Sum.inr s) 1) + old (fsOldOneIncl (lam s)))
    (x : (C ⊕ S) →₀ R) : new x = old (coreSlideReverse lam x) := by
  have hm : new = old.comp (coreSlideReverse lam) := by
    apply Finsupp.lhom_ext
    intro k a
    rw [← Finsupp.smul_single_one k a, map_smul, map_smul]
    congr 1
    cases k with
    | inl c => simpa [coreSlideReverse] using hcore c
    | inr s => simpa [coreSlideReverse, map_add] using hextra s
  exact LinearMap.congr_fun hm x

theorem coreSlideForward_aug_zero (lam : S → C →₀ R) (ε : R →+* ℤ)
    (x : (C ⊕ S) →₀ R) (hx : ∀ k, ε (x k) = 0) (j : C ⊕ S) :
    ε (coreSlideForward lam x j) = 0 := by
  have hc : ε (coreSlideCorrection lam x j) = 0 := by
    rw [coreSlideCorrection, Finsupp.linearCombination_apply, Finsupp.sum_apply,
      map_finsuppSum]
    apply Finset.sum_eq_zero
    intro k hk
    change ε (x k * _) = 0
    rw [map_mul, hx k, zero_mul]
  change ε (x j - coreSlideCorrection lam x j) = 0
  grind

end FiniteChains

section
open scoped Classical
namespace FiniteChains.RelativeNormalForm
open Davis Davis.Genus BlockFamily

variable {A C Z S : Type} (core : C → FreeGroup A)
  (hcore : Function.Surjective (expMatrix core))

def pairCorePresentation : C → FreeGroup (PairGen A Z) :=
  fun c => FreeGroup.map Sum.inl (core c)

def pairCorrection (w : FreeGroup (A ⊕ Z)) : FreeGroup (PairGen A Z) :=
  FreeGroup.map Sum.inl (correctionWord core (correctionCoefficients core hcore w))

theorem pairCorrection_mem (w : FreeGroup (A ⊕ Z)) :
    pairCorrection core hcore w ∈ relSub (pairCorePresentation (Z := Z) core) :=
  coreCorrection_mem core (relSub (pairCorePresentation (Z := Z) core))
    (fun c => Subgroup.subset_normalClosure ⟨c, rfl⟩) _

theorem pairCorrection_filling_exists (w : FreeGroup (A ⊕ Z)) :
    ∃ v : C →₀ MonoidAlgebra ℤ (PresGroup (pairCorePresentation (Z := Z) core)),
      coverSecondBoundary (relSub (pairCorePresentation (Z := Z) core))
        (pairCorePresentation core) v =
      coverFoxGradient (relSub (pairCorePresentation (Z := Z) core))
        (pairCorrection core hcore w) := by
  apply (coverFoxGradient_mem_range_iff (relSub (pairCorePresentation core))
    (pairCorePresentation core)
    (fun c => Subgroup.subset_normalClosure ⟨c, rfl⟩)
    (pairCorrection_mem core hcore w)).mpr
  exact (le_sup_left : relSub (pairCorePresentation (Z := Z) core) ≤
    relSub (pairCorePresentation (Z := Z) core) ⊔
      ⁅relSub (pairCorePresentation (Z := Z) core),
        relSub (pairCorePresentation (Z := Z) core)⁆) (pairCorrection_mem core hcore w)

def pairCorrectionFilling (w : FreeGroup (A ⊕ Z)) :
    C →₀ MonoidAlgebra ℤ (PresGroup (pairCorePresentation (Z := Z) core)) :=
  Classical.choose (pairCorrection_filling_exists core hcore w)

theorem pairCorrectionFilling_boundary (w : FreeGroup (A ⊕ Z)) :
    coverSecondBoundary (relSub (pairCorePresentation (Z := Z) core))
      (pairCorePresentation core) (pairCorrectionFilling core hcore w) =
    coverFoxGradient (relSub (pairCorePresentation (Z := Z) core))
      (pairCorrection core hcore w) :=
  Classical.choose_spec (pairCorrection_filling_exists core hcore w)

variable (extra : S → FreeGroup (A ⊕ Z))

def slideGroupHom : PresGroup (beforeCorrection core extra) →*
    PresGroup (normalizedPresentation core hcore extra) :=
  QuotientGroup.map _ _ (MonoidHom.id _) (by
    rw [Subgroup.comap_id, relSub_normalizedPresentation core hcore extra])



def pairCoreToNormalized : PresGroup (pairCorePresentation (Z := Z) core) →*
    PresGroup (normalizedPresentation core hcore extra) :=
  QuotientGroup.map _ _ (MonoidHom.id _) (by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨c, rfl⟩
    exact Subgroup.subset_normalClosure ⟨Sum.inl c, rfl⟩)

theorem ringMap_quotient_word {G H : Subgroup (FreeGroup (PairGen A Z))}
    [G.Normal] [H.Normal] (f : (FreeGroup (PairGen A Z) ⧸ G) →*
      (FreeGroup (PairGen A Z) ⧸ H))
    (hf : ∀ w, f (QuotientGroup.mk w) = QuotientGroup.mk w)
    (x : FreeGroupRing (PairGen A Z)) :
    MonoidAlgebra.mapDomainRingHom ℤ f (proj G x) = proj H x := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => grind
  | single w a => simp_all

theorem gradient_groupMap {G H : Subgroup (FreeGroup (PairGen A Z))}
    [G.Normal] [H.Normal] (f : (FreeGroup (PairGen A Z) ⧸ G) →*
      (FreeGroup (PairGen A Z) ⧸ H))
    (hf : ∀ w, f (QuotientGroup.mk w) = QuotientGroup.mk w)
    (w : FreeGroup (PairGen A Z)) :
    (coverFoxGradient G w).mapRange (MonoidAlgebra.mapDomainRingHom ℤ f) (map_zero _) =
      coverFoxGradient H w := by
  ext i : 1
  exact ringMap_quotient_word f hf (fox i w)

def slideCoefficients := MonoidAlgebra.mapDomainRingHom ℤ (slideGroupHom core hcore extra)

def slideCoreCoefficients :=
  MonoidAlgebra.mapDomainRingHom ℤ (pairCoreToNormalized core hcore extra)

/-- Actual correction columns in the target ring, obtained from fixed
core-only chains. There is no dependence of the choice on the stage group. -/
def slideColumns (s : S) :
    C →₀ MonoidAlgebra ℤ (PresGroup (normalizedPresentation core hcore extra)) :=
  (pairCorrectionFilling core hcore (extra s)).mapRange
    (slideCoreCoefficients core hcore extra) (map_zero _)

def slideOldBoundary :
    ((C ⊕ S) →₀ MonoidAlgebra ℤ (PresGroup (normalizedPresentation core hcore extra))) →ₗ[
      MonoidAlgebra ℤ (PresGroup (normalizedPresentation core hcore extra))]
      (PairGen A Z →₀ MonoidAlgebra ℤ (PresGroup (normalizedPresentation core hcore extra))) :=
  fsRingMapBoundary (slideCoefficients core hcore extra)
    (fun j => coverFoxGradient (relSub (beforeCorrection core extra))
      (beforeCorrection core extra j))

theorem slideOldBoundary_single (k : C ⊕ S)
    (a : MonoidAlgebra ℤ (PresGroup (normalizedPresentation core hcore extra))) :
    slideOldBoundary core hcore extra (Finsupp.single k a) =
      a • coverFoxGradient (relSub (normalizedPresentation core hcore extra))
        (beforeCorrection core extra k) := by
  rw [slideOldBoundary, fsRingMapBoundary, Finsupp.linearCombination_single]
  congr 1
  exact gradient_groupMap (slideGroupHom core hcore extra) (fun _ => rfl) _


/-- The actual normalized Fox boundary is the old boundary after the
explicit triangular correction. -/
theorem normalizationSlide_boundary
    (x : (C ⊕ S) →₀ MonoidAlgebra ℤ (PresGroup (normalizedPresentation core hcore extra))) :
    coverSecondBoundary (relSub (normalizedPresentation core hcore extra))
      (normalizedPresentation core hcore extra) x =
    slideOldBoundary core hcore extra (coreSlideReverse (slideColumns core hcore extra) x) := by
  apply coreSlide_boundary (slideColumns core hcore extra)
    (slideOldBoundary core hcore extra) _ ?_ ?_ x
  · intro c
    rw [coverSecondBoundary_single, slideOldBoundary_single]
    rfl
  · intro s
    rw [coverSecondBoundary_single, one_smul, slideOldBoundary_single, one_smul,
      (show slideOldBoundary core hcore extra (fsOldOneIncl (slideColumns core hcore extra s)) =
      coverFoxGradient (relSub (normalizedPresentation core hcore extra))
        (pairCorrection core hcore (extra s)) by
        have hm : (slideOldBoundary core hcore extra).comp fsOldOneIncl =
            fsRingMapBoundary (slideCoreCoefficients core hcore extra)
              (fun c => coverFoxGradient (relSub (pairCorePresentation (Z := Z) core))
                (pairCorePresentation core c)) := by
          apply Finsupp.lhom_ext
          intro c a
          simp only [LinearMap.comp_apply, fsOldOneIncl_single, slideOldBoundary_single,
            fsRingMapBoundary, Finsupp.linearCombination_single]
          congr 1
          exact (gradient_groupMap (pairCoreToNormalized core hcore extra) (fun _ => rfl) _).symm
        change ((slideOldBoundary core hcore extra).comp fsOldOneIncl)
          ((pairCorrectionFilling core hcore (extra s)).mapRange
            (slideCoreCoefficients core hcore extra) (map_zero _)) = _
        rw [hm, fsRingMapBoundary_mapRange]
        erw [pairCorrectionFilling_boundary]
        exact gradient_groupMap (pairCoreToNormalized core hcore extra) (fun _ => rfl) _)]
    change coverFoxGradient _ (normalizedWord core hcore (extra s)) = _
    rw [normalizedWord_eq]
    exact coverFoxGradient_mul _ (by
      rw [relSub_normalizedPresentation]
      exact Subgroup.subset_normalClosure ⟨Sum.inr s, rfl⟩) _

def normalizationSlideMap : PresMorFS (beforeCorrection core extra)
    (normalizedPresentation core hcore extra) where
  hom := slideGroupHom core hcore extra
  cells := fun x => coreSlideForward (slideColumns core hcore extra)
    (x.mapRange (slideCoefficients core hcore extra) (map_zero _))
  cells_add := by
    intro x y
    rw [Finsupp.mapRange_add, map_add]
    exact map_add _
  cells_smul := by
    intro a x
    have h : (a • x).mapRange (slideCoefficients core hcore extra) (map_zero _) =
        (slideCoefficients core hcore extra a) •
          x.mapRange (slideCoefficients core hcore extra) (map_zero _) := by
      ext k : 1
      simp only [Finsupp.mapRange_apply, Finsupp.smul_apply, smul_eq_mul]
      exact map_mul _ _ _
    rw [h, map_smul]
    rfl
  cells_cycle := by
    intro x hx
    change coverSecondBoundary _ _ _ = 0
    rw [normalizationSlide_boundary, coreSlideReverse_forward]
    change fsRingMapBoundary (slideCoefficients core hcore extra) _
      (x.mapRange _ _) = 0
    rw [fsRingMapBoundary_mapRange]
    erw [hx]
    simp
  cells_aug := by
    intro x hx k
    apply coreSlideForward_aug_zero
    intro j
    change augPres (normalizedPresentation core hcore extra)
      (MonoidAlgebra.mapDomainRingHom ℤ (slideGroupHom core hcore extra) (x j)) = 0
    exact (augQ_mapDomain (slideGroupHom core hcore extra) (x j)).trans (hx j)

/-- Genuine rule-2 generation for arbitrary cores and relator families.
All correction columns and all boundary equations are constructed above. -/
theorem normalizationSlideMap_generates :
    FSGenerates (normalizationSlideMap core hcore extra) := by
  intro x hx
  let y := coreSlideReverse (slideColumns core hcore extra) x
  have hy  :=
    (normalizationSlide_boundary core hcore extra x).symm.trans hx
  have hspan := fs_cycle_mem_span_groupMap_cycles (slideGroupHom core hcore extra)
    (by
      apply Function.LeftInverse.injective (g := (QuotientGroup.map _ _ (MonoidHom.id _) (by
    rw [Subgroup.comap_id, relSub_normalizedPresentation core hcore extra])))
      intro g
      induction g using QuotientGroup.induction_on with
      | H w => rfl)
    (fun j => coverFoxGradient (relSub (beforeCorrection core extra))
      (beforeCorrection core extra j)) y hy
  have he : coreSlideForward (slideColumns core hcore extra) y = x :=
    coreSlideForward_reverse _ _
  rw [← he]
  clear hx hy he
  generalize y = z at hspan ⊢
  clear y x
  induction hspan using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨a, ha, rfl⟩ := hz
      exact Submodule.subset_span ⟨a, ha, rfl⟩
  | zero => simp
  | add z w _ _ hz hw => rw [map_add]; exact Submodule.add_mem _ hz hw
  | smul a z _ hz => rw [map_smul]; exact Submodule.smul_mem _ a hz

end FiniteChains.RelativeNormalForm
end

namespace FiniteChains

open MonoidAlgebra

universe u

variable {α γ : Type u} [DecidableEq γ]
variable {J L : Type u}
variable (ρ : J → FreeGroup α) (τ : L → FreeGroup γ) (f : α → γ) (g : J → L)
variable (r : FreeGroup γ →* FreeGroup α)

/-- The data expressing that the presentation `ρ` is a retract block of the presentation `τ`.
-/
structure IsBlock : Prop where
  /-- the generators of the block are included injectively -/
  gen_injective : Function.Injective f
  /-- the two-cells of the block are included injectively -/
  cell_injective : Function.Injective g
  /-- an old relator is read as the same word -/
  rel_eq : ∀ j, τ (g j) = FreeGroup.map f (ρ j)
  /-- no relator outside the block involves a generator of the block -/
  fox_outside : ∀ (i : α) (l : L), l ∉ Set.range g → @fox γ _ (f i) (τ l) = 0
  /-- the retraction restricts to the identity on the block -/
  retract_map : ∀ w : FreeGroup α, r (FreeGroup.map f w) = w
  /-- the retraction carries relators to relators -/
  retract_rel : ∀ l, r (τ l) ∈ relSub ρ

variable {ρ τ f g r} (hb : IsBlock ρ τ f g r)

include hb


/-- The map of fundamental groups induced by the inclusion of the block. -/
def IsBlock.hom : PresGroup ρ →* PresGroup τ :=
  QuotientGroup.map _ _ (FreeGroup.map f) (by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨j, rfl⟩
    refine Subgroup.mem_comap.2 ?_
    rw [← hb.rel_eq j]
    exact Subgroup.subset_normalClosure (Set.mem_range_self _))

@[simp] theorem IsBlock.hom_mk (w : FreeGroup α) :
    hb.hom (QuotientGroup.mk w) = QuotientGroup.mk (FreeGroup.map f w) := rfl


/-- The retraction of the ambient presented group onto the block. -/
def IsBlock.retract : PresGroup τ →* PresGroup ρ :=
  QuotientGroup.map _ _ r (by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨l, rfl⟩
    exact Subgroup.mem_comap.2 (hb.retract_rel l))

/-- The ring map of group rings induced by the inclusion of the block. -/
def IsBlock.ringHom :
    MonoidAlgebra ℤ (PresGroup ρ) →+* MonoidAlgebra ℤ (PresGroup τ) :=
  MonoidAlgebra.mapDomainRingHom ℤ hb.hom

theorem IsBlock.quot_freeRingMap (x : FreeGroupRing α) :
    quotRingHom ℤ (relSub τ) (freeRingMap f x) = hb.ringHom (quotRingHom ℤ (relSub ρ) x) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp_all
  | single w m =>
      show quotRingHom ℤ (relSub τ)
          (MonoidAlgebra.mapDomain (FreeGroup.map f) (MonoidAlgebra.single w m)) = _
      rw [MonoidAlgebra.mapDomain_single, quotRingHom_single]
      show _ = MonoidAlgebra.mapDomain hb.hom (quotRingHom ℤ (relSub ρ) (MonoidAlgebra.single w m))
      rw [quotRingHom_single, MonoidAlgebra.mapDomain_single, IsBlock.hom_mk]


section FoxMatrix

variable [DecidableEq α]

/-- Inside the block the Fox matrix of `τ` is the image of the Fox matrix of `ρ`. -/
theorem IsBlock.foxMatrix_block (i : α) (j : J) :
    foxMatrixPres τ (f i) (g j) = hb.ringHom (foxMatrixPres ρ i j) := by
  have hfox : @fox γ _ (f i) (τ (g j)) = freeRingMap f (fox i (ρ j)) := by
    rw [hb.rel_eq j]
    exact fox_map f hb.gen_injective i (ρ j)
  show quotRingHom ℤ (relSub τ) (fox (f i) (τ (g j))) = _
  rw [hfox, hb.quot_freeRingMap]
  rfl

variable [Fintype J] [Fintype L]

end FoxMatrix

end FiniteChains

namespace FiniteChains

open MonoidAlgebra

universe u

variable {S : Type u} {α : S → Type u} {J : S → Type u} (ρ : ∀ s, J s → FreeGroup (α s))

/-- The presentation of the wedge of a family of presentations: the generators and the
relators of all the factors, side by side. -/
def sigmaWedgeRel : (Σ s, J s) → FreeGroup (Σ s, α s) :=
  fun p => FreeGroup.map (Sigma.mk p.1) (ρ p.1 p.2)

@[simp] theorem sigmaWedgeRel_mk (s : S) (j : J s) :
    sigmaWedgeRel ρ ⟨s, j⟩ = FreeGroup.map (Sigma.mk s) (ρ s j) := rfl

variable [DecidableEq S]

/-- The retraction of the ambient free group onto the `s`-th factor: it kills the generators
of all the other factors. -/
def killOther (s : S) : FreeGroup (Σ t, α t) →* FreeGroup (α s) :=
  FreeGroup.lift fun p => if h : p.1 = s then FreeGroup.of (h ▸ p.2) else 1

@[simp] theorem killOther_map_self (s : S) (w : FreeGroup (α s)) :
    killOther (α := α) s (FreeGroup.map (Sigma.mk s) w) = w := by
  have h : ((killOther (α := α) s).comp (FreeGroup.map (Sigma.mk s))) = MonoidHom.id _ :=
    FreeGroup.ext_hom _ _ fun a => by
      simp [killOther]
  exact congrArg (fun F : FreeGroup (α s) →* FreeGroup (α s) => F w) h

@[simp] theorem killOther_map_other {s t : S} (hst : t ≠ s) (w : FreeGroup (α t)) :
    killOther (α := α) s (FreeGroup.map (Sigma.mk t) w) = 1 := by
  have h : ((killOther (α := α) s).comp (FreeGroup.map (Sigma.mk t))) = 1 :=
    FreeGroup.ext_hom _ _ fun a => by
      simp [killOther, hst]
  exact congrArg (fun F : FreeGroup (α t) →* FreeGroup (α s) => F w) h

variable [∀ s, DecidableEq (α s)]

/-- **Every factor is a retract block of the wedge.** -/
theorem isBlock_sigmaWedge (s : S) :
    IsBlock (ρ s) (sigmaWedgeRel ρ) (Sigma.mk s) (Sigma.mk s) (killOther s) where
  gen_injective := sigma_mk_injective
  cell_injective := sigma_mk_injective
  rel_eq _ := rfl
  fox_outside i l hl := by
    obtain ⟨t, j⟩ := l
    have hts : t ≠ s := by
      rintro rfl
      exact hl ⟨j, rfl⟩
    rw [sigmaWedgeRel_mk]
    refine fox_map_of_not_mem_range (Sigma.mk t) ?_ (ρ t j)
    intro a hcontra
    exact hts (congrArg Sigma.fst hcontra).symm
  retract_map w := killOther_map_self s w
  retract_rel l := by
    obtain ⟨t, j⟩ := l
    by_cases hts : t = s
    · subst hts
      rw [sigmaWedgeRel_mk, killOther_map_self]
      exact Subgroup.subset_normalClosure (Set.mem_range_self _)
    · rw [sigmaWedgeRel_mk, killOther_map_other hts]
      exact one_mem _

variable [Fintype S] [∀ s, Fintype (α s)] [∀ s, Fintype (J s)]

end FiniteChains

namespace FiniteChains

open MonoidAlgebra

universe u

variable {γ δ Mc Ex : Type u} [Fintype γ] [DecidableEq γ] [Fintype δ] [DecidableEq δ]
  [Fintype Mc] [Fintype Ex]

/-- A presentation containing the core `D`: the relators of the core, read in the free group on
the core and the extra generators, together with the extra relators. -/
def corePres (core : Mc → FreeGroup γ) (extra : Ex → FreeGroup (γ ⊕ δ)) :
    Mc ⊕ Ex → FreeGroup (γ ⊕ δ) :=
  Sum.elim (fun m => FreeGroup.map Sum.inl (core m)) extra

omit [Fintype γ] [DecidableEq γ] [Fintype δ] [DecidableEq δ] [Fintype Mc] [Fintype Ex] in
@[simp] theorem corePres_inl (core : Mc → FreeGroup γ) (extra : Ex → FreeGroup (γ ⊕ δ))
    (m : Mc) : corePres core extra (Sum.inl m) = FreeGroup.map Sum.inl (core m) := rfl

omit [Fintype γ] [DecidableEq γ] [Fintype δ] [DecidableEq δ] [Fintype Mc] [Fintype Ex] in
@[simp] theorem corePres_inr (core : Mc → FreeGroup γ) (extra : Ex → FreeGroup (γ ⊕ δ))
    (e : Ex) : corePres core extra (Sum.inr e) = extra e := rfl

omit [Fintype γ] [Fintype δ] in
/-- The exponent sum of a core generator in a word of the core does not change when the word is
read in the larger free group. -/
theorem expSum_map_inl (i : γ) (w : FreeGroup γ) :
    Multiplicative.toAdd (expSum (Sum.inl i : γ ⊕ δ) (FreeGroup.map (Sum.inl : γ → γ ⊕ δ) w))
      = Multiplicative.toAdd (expSum i w) := by
  have h : (expSum (Sum.inl i)).comp (FreeGroup.map (Sum.inl : γ → γ ⊕ δ))
      = expSum i := by
    refine FreeGroup.ext_hom _ _ fun k => ?_
    have h1 : FreeGroup.map (Sum.inl : γ → γ ⊕ δ) (FreeGroup.of k)
        = FreeGroup.of (Sum.inl k) := by simp
    have h2 : Multiplicative.toAdd (expSum (Sum.inl i : γ ⊕ δ) (FreeGroup.of (Sum.inl k)))
        = Multiplicative.toAdd (expSum i (FreeGroup.of k)) := by
      rw [expSum_of, expSum_of]
      simp
    exact Multiplicative.toAdd.injective (by simp [h1, h2])
  exact congrArg Multiplicative.toAdd (DFunLike.congr_fun h w)

/-! ### The collapse onto the wedge of the blocks -/

section Wedge

variable {S : Type u} {β K : S → Type u} [Fintype S] [DecidableEq S] [∀ s, Fintype (β s)]
  [∀ s, DecidableEq (β s)] [∀ s, Fintype (K s)]

end Wedge

end FiniteChains

section
open scoped Classical
namespace FiniteChains.CoreSignedCollapse

variable {A B M J : Type}

/-- Collapse the core generators and retain each extra generator. -/
def dropCore : FreeGroup (A ⊕ B) →* FreeGroup B :=
  FreeGroup.lift (Sum.elim (fun _ => 1) FreeGroup.of)

@[simp] theorem dropCore_of_inl (a : A) :
    dropCore (B := B) (FreeGroup.of (Sum.inl a)) = 1 := rfl

@[simp] theorem dropCore_of_inr (b : B) :
    dropCore (A := A) (FreeGroup.of (Sum.inr b)) = FreeGroup.of b := rfl

@[simp] theorem dropCore_map_inl (w : FreeGroup A) :
    dropCore (B := B) (FreeGroup.map Sum.inl w) = 1 := by
  have h : (dropCore (A := A) (B := B)).comp (FreeGroup.map Sum.inl) = 1 := by
    apply FreeGroup.ext_hom
    intro a
    simp
  exact DFunLike.congr_fun h w


variable (core : M → FreeGroup A) (extra : J → FreeGroup (A ⊕ B))
  (target : J → FreeGroup B) (rev : J → Bool)
  (hword : ∀ j, dropCore (extra j) = if rev j then (target j)⁻¹ else target j)

/-- The collapse descends because every collapsed attaching word is a target
relator or its inverse. -/
def groupMap : PresGroup (corePres core extra) →* PresGroup target :=
  QuotientGroup.lift _
    ((QuotientGroup.mk' (relSub target)).comp dropCore) (by
      refine Subgroup.normalClosure_le_normal ?_
      rintro _ ⟨m | j, rfl⟩
      · change (QuotientGroup.mk' (relSub target))
          (dropCore (FreeGroup.map Sum.inl (core m))) = 1
        rw [dropCore_map_inl, map_one]
      · change (QuotientGroup.mk' (relSub target)) (dropCore (extra j)) = 1
        have ht : (QuotientGroup.mk (target j) : PresGroup target) = 1 :=
          (QuotientGroup.eq_one_iff _).mpr
            (Subgroup.subset_normalClosure ⟨j, rfl⟩)
        rw [hword j]
        cases rev j <;> simp [ht])

def coefficientMap : MonoidAlgebra ℤ (PresGroup (corePres core extra)) →+*
    MonoidAlgebra ℤ (PresGroup target) :=
  MonoidAlgebra.mapDomainRingHom ℤ (groupMap core extra target rev hword)

theorem coefficientMap_quot (x : FreeGroupRing (A ⊕ B)) :
    coefficientMap core extra target rev hword
      (quotRingHom ℤ (relSub (corePres core extra)) x) =
    quotRingHom ℤ (relSub target)
      (MonoidAlgebra.mapDomainRingHom ℤ dropCore x) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => grind
  | single g n =>
      change MonoidAlgebra.mapDomain _ (MonoidAlgebra.mapDomain _ (MonoidAlgebra.single g n)) =
        MonoidAlgebra.mapDomain _ (MonoidAlgebra.mapDomain _ (MonoidAlgebra.single g n))
      simp
      rfl

variable [DecidableEq A] [DecidableEq B]

theorem coefficientMap_fox (b : B) (w : FreeGroup (A ⊕ B)) :
    coefficientMap core extra target rev hword
      (quotRingHom ℤ (relSub (corePres core extra)) (fox (Sum.inr b) w)) =
    quotRingHom ℤ (relSub target) (fox b (dropCore w)) := by
  rw [coefficientMap_quot]
  congr 1
  symm
  apply fox_subst_coordinate
  simp


theorem matrix_core (b : B) (m : M) :
    foxMatrixPres (corePres core extra) (Sum.inr b) (Sum.inl m) = 0 := by
  change quotRingHom ℤ _ (fox (Sum.inr b) (FreeGroup.map Sum.inl (core m))) = 0
  rw [fox_map_of_not_mem_range Sum.inl (fun _ => Sum.inr_ne_inl), map_zero]

theorem matrix_extra (b : B) (j : J) :
    coefficientMap core extra target rev hword
      (foxMatrixPres (corePres core extra) (Sum.inr b) (Sum.inr j)) =
      if rev j then -foxMatrixPres target b j else foxMatrixPres target b j := by
  change coefficientMap core extra target rev hword
    (quotRingHom ℤ _ (fox (Sum.inr b) (extra j))) = _
  rw [coefficientMap_fox, hword j]
  cases h : rev j
  · rfl
  · exact (show quotRingHom ℤ (relSub target) (fox b (target j)⁻¹) =
      -foxMatrixPres target b j by
    have ht : (QuotientGroup.mk ((target j)⁻¹) : PresGroup target) = 1 := by
      apply (QuotientGroup.eq_one_iff _).mpr
      exact inv_mem (Subgroup.subset_normalClosure ⟨j, rfl⟩)
    have hg : quotRingHom ℤ (relSub target) (grp (target j)⁻¹) = 1 := by
      change quotRingHom ℤ _ (MonoidAlgebra.single _ 1) = _
      rw [quotRingHom_single, ht]
      rfl
    rw [fox_inv, map_neg, map_mul, hg, one_mul]
    rfl)

variable [Fintype M] [Fintype J]

end FiniteChains.CoreSignedCollapse

namespace FiniteChains

open BlockFamily

variable {A B M J : Type} [DecidableEq A] [DecidableEq B]

theorem expMatrix_augmentation (ρ : J → FreeGroup A)
    (v : J →₀ MonoidAlgebra ℤ (PresGroup ρ)) :
    expMatrix ρ (v.mapRange (augPres ρ) (map_zero _)) =
      (coverSecondBoundary (relSub ρ) ρ v).mapRange (augPres ρ) (map_zero _) := by
  have hadd {I : Type} (x y : I →₀ MonoidAlgebra ℤ (PresGroup ρ)) :
      (x + y).mapRange (augPres ρ) (map_zero _) =
        x.mapRange (augPres ρ) (map_zero _) + y.mapRange (augPres ρ) (map_zero _) := by
    ext i : 1
    exact map_add (augPres ρ) _ _
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp_all
  | single j a =>
      simp only [Finsupp.mapRange_single, expMatrix, coverSecondBoundary,
        Finsupp.linearCombination_single]
      ext i : 1
      change augPres ρ a * expVec (ρ j) i =
        augPres ρ (a * foxMatrixPres ρ i j)
      rw [map_mul, augPres_foxMatrixPres, expVec_apply]
      rfl

/-- Core rows of a supported chain on retained core cells are unchanged. -/
theorem corePres_expMatrix_retained (core : M → FreeGroup A)
    (extra : J → FreeGroup (A ⊕ B)) (c : M →₀ ℤ) (a : A) :
    expMatrix (corePres core extra) (Finsupp.mapDomain Sum.inl c) (Sum.inl a) =
      expMatrix core c a := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [Finsupp.mapDomain_add, map_add, Finsupp.add_apply, hc, hd]
  | single m n =>
      simp only [Finsupp.mapDomain_single, expMatrix, Finsupp.linearCombination_single,
        Finsupp.smul_apply, smul_eq_mul, expVec_apply]
      change n * Multiplicative.toAdd (expSum (Sum.inl a)
          (FreeGroup.map Sum.inl (core m))) =
        n * Multiplicative.toAdd (expSum a (core m))
      rw [expSum_map_inl]

/-- Injectivity on supported core chains reflects vanishing when the extra
coordinates vanish.  This is the actual H2 injection used by terminal B3. -/
theorem corePres_expMatrix_kernel_reflect (core : M → FreeGroup A)
    (extra : J → FreeGroup (A ⊕ B)) (hcore : Function.Injective (expMatrix core))
    (c : (M ⊕ J) →₀ ℤ) (hc : expMatrix (corePres core extra) c = 0)
    (hextra : ∀ j, c (Sum.inr j) = 0) : c = 0 := by
  let d := c.comapDomain Sum.inl Sum.inl_injective.injOn
  have he : Finsupp.mapDomain Sum.inl d = c := by
    apply Finsupp.mapDomain_comapDomain Sum.inl Sum.inl_injective c
    rintro (m | j) h
    · simp
    · simp_all
  have hd : expMatrix core d = 0 := by
    ext a
    rw [← corePres_expMatrix_retained core extra d a, he, hc]
    rfl
  simp_all

theorem corePres_fsAugmentation_reflect (core : M → FreeGroup A)
    (extra : J → FreeGroup (A ⊕ B)) (hcore : Function.Injective (expMatrix core))
    (v : (M ⊕ J) →₀ MonoidAlgebra ℤ (PresGroup (corePres core extra)))
    (hv : FSIsFoxCycle (corePres core extra) v)
    (hextra : ∀ j, augPres (corePres core extra) (v (Sum.inr j)) = 0) :
    ∀ j, augPres (corePres core extra) (v j) = 0 := by
  let c := v.mapRange (augPres (corePres core extra)) (map_zero _)
  have hc : expMatrix (corePres core extra) c = 0 := by
    rw [expMatrix_augmentation]
    rw [hv, Finsupp.mapRange_zero]
  have hz := corePres_expMatrix_kernel_reflect core extra hcore c hc hextra
  intro j
  exact congrArg (fun c : (M ⊕ J) →₀ ℤ => c j) hz

namespace CoreSignedCollapse

variable (core : M → FreeGroup A) (extra : J → FreeGroup (A ⊕ B))
  (target : J → FreeGroup B) (rev : J → Bool)
  (hword : ∀ j, dropCore (extra j) = if rev j then (target j)⁻¹ else target j)

/-- The supported signed collapse has support contained in the extra part
of the original chain's support. -/
def cellsFS (v : (M ⊕ J) →₀ MonoidAlgebra ℤ (PresGroup (corePres core extra))) :
    J →₀ MonoidAlgebra ℤ (PresGroup target) :=
  Finsupp.onFinset (v.comapDomain Sum.inr Sum.inr_injective.injOn).support
    (fun j => if rev j then -coefficientMap core extra target rev hword (v (Sum.inr j))
      else coefficientMap core extra target rev hword (v (Sum.inr j))) (by
    intro j hj
    apply Finsupp.mem_support_iff.mpr
    intro hz
    have hz' : v (Sum.inr j) = 0 := hz
    apply hj
    simp only [hz', map_zero, neg_zero, ite_self])

omit [DecidableEq A] [DecidableEq B] in
@[simp] theorem cellsFS_apply
    (v : (M ⊕ J) →₀ MonoidAlgebra ℤ (PresGroup (corePres core extra))) (j : J) :
    cellsFS core extra target rev hword v j =
      if rev j then -coefficientMap core extra target rev hword (v (Sum.inr j))
        else coefficientMap core extra target rev hword (v (Sum.inr j)) := rfl

omit [DecidableEq A] [DecidableEq B] in
@[simp] theorem cellsFS_zero : cellsFS core extra target rev hword 0 = 0 := by
  ext j : 1
  simp [cellsFS_apply]


omit [DecidableEq A] [DecidableEq B] in
@[simp] theorem cellsFS_single_core (m : M)
    (a : MonoidAlgebra ℤ (PresGroup (corePres core extra))) :
    cellsFS core extra target rev hword (Finsupp.single (Sum.inl m) a) = 0 := by
  ext j : 1
  simp [cellsFS_apply]

omit [DecidableEq A] [DecidableEq B] in
@[simp] theorem cellsFS_single_extra (j : J)
    (a : MonoidAlgebra ℤ (PresGroup (corePres core extra))) :
    cellsFS core extra target rev hword (Finsupp.single (Sum.inr j) a) =
      Finsupp.single j (if rev j then -coefficientMap core extra target rev hword a
        else coefficientMap core extra target rev hword a) := by grind [cellsFS]

theorem cellsFS_boundary_apply
    (v : (M ⊕ J) →₀ MonoidAlgebra ℤ (PresGroup (corePres core extra))) (b : B) :
    coverSecondBoundary (relSub target) target (cellsFS core extra target rev hword v) b =
      coefficientMap core extra target rev hword
        (coverSecondBoundary (relSub (corePres core extra)) (corePres core extra) v
          (Sum.inr b)) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [(show cellsFS core extra target rev hword (v + w) =
      cellsFS core extra target rev hword v + cellsFS core extra target rev hword w by
    ext j : 1
    cases h : rev j <;> simp [cellsFS_apply, h, map_add, add_comm]), map_add, Finsupp.add_apply, hv, hw]
  | single j a =>
      cases j with
      | inl m =>
          rw [cellsFS_single_core, map_zero, Finsupp.zero_apply,
            fsCoverSecondBoundary_apply, Finsupp.sum_single_index (zero_mul _),
            matrix_core, mul_zero, map_zero]
      | inr j =>
          simp only [cellsFS_single_extra, fsCoverSecondBoundary_apply,
            Finsupp.sum_single_index, zero_mul, map_mul, matrix_extra]
          cases rev j <;> simp



include hword in
theorem fsIsCockcroft (hcore : Function.Injective (expMatrix core))
    (htarget : FSIsCockcroft target) : FSIsCockcroft (corePres core extra) := by
  intro v hv
  exact (by
    apply corePres_fsAugmentation_reflect core extra hcore v hv
    intro j
    have ha : augPres target
        (coefficientMap core extra target rev hword (v (Sum.inr j))) =
        augPres (corePres core extra) (v (Sum.inr j)) :=
      augQ_mapDomain (groupMap core extra target rev hword) _
    have h := (htarget _ (show FSIsFoxCycle target (cellsFS core extra target rev hword v) by
      ext b : 1
      rw [cellsFS_boundary_apply, hv, Finsupp.zero_apply, map_zero]
      rfl)) j
    cases he : rev j <;> simpa [cellsFS_apply, he, map_neg, ha] using h)

end CoreSignedCollapse
end FiniteChains

namespace FiniteChains

open BlockFamily

variable {A B J L : Type} [DecidableEq A] [DecidableEq B] [Fintype J]
  {ρ : J → FreeGroup A} {τ : L → FreeGroup B}
  {f : A → B} {g : J → L} {r : FreeGroup B →* FreeGroup A}
  (hb : IsBlock ρ τ f g r)

omit [DecidableEq A] [Fintype J] in
theorem IsBlock.retract_hom_apply (x : PresGroup ρ) : hb.retract (hb.hom x) = x := by
  induction x using QuotientGroup.induction_on with
  | H w =>
      change (QuotientGroup.mk (r (FreeGroup.map f w))) = QuotientGroup.mk w
      rw [hb.retract_map]

def IsBlock.retractCoefficient :
    MonoidAlgebra ℤ (PresGroup τ) →+* MonoidAlgebra ℤ (PresGroup ρ) :=
  MonoidAlgebra.mapDomainRingHom ℤ hb.retract

omit [DecidableEq A] [Fintype J] in
theorem IsBlock.retractCoefficient_ringHom (x : MonoidAlgebra ℤ (PresGroup ρ)) :
    hb.retractCoefficient (hb.ringHom x) = x := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp_all
  | single a n =>
      change MonoidAlgebra.mapDomain hb.retract (MonoidAlgebra.mapDomain hb.hom (MonoidAlgebra.single a n)) = _
      rw [MonoidAlgebra.mapDomain_single, MonoidAlgebra.mapDomain_single, hb.retract_hom_apply]

/-- Reading a factor's coefficients through its actual retraction commutes
with the boundary at every generator in that factor. -/
theorem IsBlock.fsRetract_boundary (v : L →₀ MonoidAlgebra ℤ (PresGroup τ)) (a : A) :
    (∑ j : J, hb.retractCoefficient (v (g j)) * foxMatrixPres ρ a j) =
      hb.retractCoefficient (coverSecondBoundary (relSub τ) τ v (f a)) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw =>
      simp only [Finsupp.add_apply, map_add, add_mul, Finset.sum_add_distrib, hv, hw]
  | single l c =>
      by_cases hl : l ∈ Set.range g
      · obtain ⟨j, rfl⟩ := hl
        simp only [Finsupp.single_apply, hb.cell_injective.eq_iff,
          apply_ite hb.retractCoefficient, map_zero, ite_mul, zero_mul]
        rw [Fintype.sum_ite_eq]
        simp only [fsCoverSecondBoundary_apply, Finsupp.sum_single_index, zero_mul,
          map_mul, hb.foxMatrix_block, hb.retractCoefficient_ringHom]
      · have hn j : l ≠ g j := fun he => hl ⟨j, he.symm⟩
        have hz : foxMatrixPres τ (f a) l = 0 := by
          change quotRingHom ℤ _ (fox (f a) (τ l)) = 0
          rw [hb.fox_outside a l hl, map_zero]
        rw [fsCoverSecondBoundary_apply, Finsupp.sum_single_index (zero_mul _), hz,
          mul_zero, map_zero]
        simp [hn]

/-- The actual finitely supported ambient cycle gives a cycle of the finite
factor after applying the actual group retraction. -/
theorem IsBlock.fsRetract_cycle (v : L →₀ MonoidAlgebra ℤ (PresGroup τ))
    (hv : FSIsFoxCycle τ v) :
    IsFoxCycle ρ (fun j => hb.retractCoefficient (v (g j))) := by
  intro a
  rw [hb.fsRetract_boundary, hv, Finsupp.zero_apply, map_zero]

include hb in
theorem IsBlock.fsAugmentation_zero (hρ : IsCockcroft ρ)
    (v : L →₀ MonoidAlgebra ℤ (PresGroup τ)) (hv : FSIsFoxCycle τ v) (j : J) :
    augPres τ (v (g j)) = 0 := by
  have h := hρ _ (hb.fsRetract_cycle v hv) j
  exact (augQ_mapDomain hb.retract (v (g j))).symm.trans h

variable {S : Type} {X C : S → Type} [DecidableEq S]
  [∀ s, DecidableEq (X s)] [∀ s, Fintype (C s)]

/-- The indexing family is arbitrary.  Only each individual block has a
finite cell set, as do the genuine genus spines. -/
theorem fsIsCockcroft_sigmaWedgeRel (rels : ∀ s, C s → FreeGroup (X s))
    (h : ∀ s, IsCockcroft (rels s)) : FSIsCockcroft (sigmaWedgeRel rels) := by
  intro v hv p
  obtain ⟨s, j⟩ := p
  exact (isBlock_sigmaWedge rels s).fsAugmentation_zero (h s) v hv j

end FiniteChains
end

namespace FiniteChains

open MonoidAlgebra

universe u

/-! ### A map which kills the fundamental group is zero on Hurewicz-trivial chains -/

section Trivial

variable {α J α' J' : Type u} [Fintype α] [DecidableEq α] [Fintype J]
  [Fintype α'] [DecidableEq α'] [Fintype J']
variable {ρ : J → FreeGroup α} {ρ' : J' → FreeGroup α'}

omit [Fintype α] [DecidableEq α] [Fintype J] [Fintype α'] [DecidableEq α'] [Fintype J'] in
/-- If a homomorphism of fundamental groups is trivial, then pushing coefficients along it is
the augmentation: the group ring acts on the target through `ℤ`. -/
theorem mapDomainRingHom_eq_single_augPres (h : PresGroup ρ →* PresGroup ρ')
    (htriv : ∀ g, h g = 1) (c : MonoidAlgebra ℤ (PresGroup ρ)) :
    MonoidAlgebra.mapDomainRingHom ℤ h c = MonoidAlgebra.single 1 (augPres ρ c) := by
  induction c using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, MonoidAlgebra.single_add]
  | single g m => simp_all

omit [Fintype α] [DecidableEq α] [Fintype J] [Fintype α'] [DecidableEq α'] [Fintype J'] in
/-- A homomorphism out of a presented group is trivial as soon as it kills the generators. -/
theorem hom_eq_one_of_gens {H : Type u} [Group H] (h : PresGroup ρ →* H)
    (hgen : ∀ a : α, h (QuotientGroup.mk (FreeGroup.of a)) = 1) (x : PresGroup ρ) : h x = 1 := by
  have hcomp : (h.comp (QuotientGroup.mk' (relSub ρ))) = 1 :=
    FreeGroup.ext_hom _ _ fun a => hgen a
  induction x using QuotientGroup.induction_on with
  | H w => exact congrArg (fun F : FreeGroup α →* H => F w) hcomp

end Trivial

/-! ### The terminal extension: adjoining individual relators -/

section AddRels

variable {α J L : Type u} [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J]
  [Fintype L] [DecidableEq L]
variable (ρ : J → FreeGroup α) (ν : L → FreeGroup α)

/-- **The terminal extension on presentations**: the relators `ν` (in the paper the letters
`a_z` and `b_z`) are adjoined as further individual relators, the generators being
unchanged. -/
def addRels : J ⊕ L → FreeGroup α := Sum.elim ρ ν

omit [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J] [Fintype L] [DecidableEq L] in
@[simp] theorem addRels_inl (j : J) : addRels ρ ν (Sum.inl j) = ρ j := rfl

omit [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J] [Fintype L] [DecidableEq L] in
@[simp] theorem addRels_inr (l : L) : addRels ρ ν (Sum.inr l) = ν l := rfl

omit [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J] [Fintype L] [DecidableEq L] in
theorem relSub_le_relSub_addRels : relSub ρ ≤ relSub (addRels ρ ν) := by
  refine Subgroup.normalClosure_le_normal ?_
  rintro _ ⟨j, rfl⟩
  exact Subgroup.subset_normalClosure ⟨Sum.inl j, rfl⟩

/-- The homomorphism of fundamental groups induced by the terminal extension. -/
def addRelsHom : PresGroup ρ →* PresGroup (addRels ρ ν) :=
  QuotientGroup.map _ _ (MonoidHom.id _) (by
    intro w hw
    exact Subgroup.mem_comap.2 (relSub_le_relSub_addRels ρ ν hw))

omit [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J] [Fintype L] [DecidableEq L] in
@[simp] theorem addRelsHom_mk (w : FreeGroup α) :
    addRelsHom ρ ν (QuotientGroup.mk w) = QuotientGroup.mk w := rfl

/-- The induced map of group rings. -/
def addRelsRingHom :
    MonoidAlgebra ℤ (PresGroup ρ) →+* MonoidAlgebra ℤ (PresGroup (addRels ρ ν)) :=
  MonoidAlgebra.mapDomainRingHom ℤ (addRelsHom ρ ν)

omit [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J] [Fintype L] [DecidableEq L] in
/-- Reading an element of `ℤ[F]` in the group ring of the enlarged presentation agrees with
pushing it forward from the group ring of the old one. -/
theorem quot_addRelsRingHom (x : FreeGroupRing α) :
    quotRingHom ℤ (relSub (addRels ρ ν)) x = addRelsRingHom ρ ν (quotRingHom ℤ (relSub ρ) x) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp_all
  | single w m =>
      rw [quotRingHom_single]
      show _ = MonoidAlgebra.mapDomain (addRelsHom ρ ν) (quotRingHom ℤ (relSub ρ) (single w m))
      rw [quotRingHom_single, MonoidAlgebra.mapDomain_single, addRelsHom_mk]

omit [Fintype α] [Fintype J] [DecidableEq J] [Fintype L] [DecidableEq L] in
/-- On the old two-cells the Fox matrix of the enlarged presentation is the image of the old
Fox matrix. -/
theorem foxMatrix_addRels_inl (i : α) (j : J) :
    foxMatrixPres (addRels ρ ν) i (Sum.inl j) = addRelsRingHom ρ ν (foxMatrixPres ρ i j) :=
  quot_addRelsRingHom ρ ν (fox i (ρ j))

omit [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J] [Fintype L] [DecidableEq L] in
/-- The augmentation is unchanged by the terminal extension. -/
theorem augPres_addRelsRingHom (z : MonoidAlgebra ℤ (PresGroup ρ)) :
    augPres (addRels ρ ν) (addRelsRingHom ρ ν z) = augPres ρ z :=
  augQ_mapDomain (addRelsHom ρ ν) z

end AddRels
end FiniteChains

section
open scoped Classical
namespace FiniteChains

open BlockFamily

variable {A B J L I : Type} [DecidableEq A] [DecidableEq B]

theorem PresMorFS.cells_finset_sum {ρ : J → FreeGroup A} {τ : L → FreeGroup B}
    (f : PresMorFS ρ τ) (s : Finset I)
    (v : I → J →₀ MonoidAlgebra ℤ (PresGroup ρ)) :
    f.cells (∑ i ∈ s, v i) = ∑ i ∈ s, f.cells (v i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, f.cells_add, ih, Finset.sum_insert ha]


theorem fsCells_eq_zero_of_isCockcroft_of_hom_trivial
    {ρ : J → FreeGroup A} {τ : L → FreeGroup B}
    (f : PresMorFS ρ τ) (hρ : FSIsCockcroft ρ) (htriv : ∀ g, f.hom g = 1)
    (v : J →₀ MonoidAlgebra ℤ (PresGroup ρ)) (hv : FSIsFoxCycle ρ v) : f.cells v = 0 :=
  (by
    have hdec : v = ∑ j ∈ v.support, Finsupp.single j (v j) := (Finsupp.sum_single v).symm
    have hsingle (j : J) :
        Finsupp.single j (v j) = v j • Finsupp.single j (1 : MonoidAlgebra ℤ (PresGroup ρ)) := by
      ext k : 1
      by_cases h : j = k
      · subst k
        simp
      · simp
    rw [hdec, f.cells_finset_sum]
    apply Finset.sum_eq_zero
    intro j hj
    rw [hsingle, f.cells_smul, mapDomainRingHom_eq_single_augPres f.hom htriv, (hρ v hv) j]
    simp)

variable (ρ : J → FreeGroup A) (ν : L → FreeGroup A)

def addRelsCellsFS (v : J →₀ MonoidAlgebra ℤ (PresGroup ρ)) :
    (J ⊕ L) →₀ MonoidAlgebra ℤ (PresGroup (addRels ρ ν)) :=
  Finsupp.mapDomain Sum.inl (v.mapRange (addRelsRingHom ρ ν) (map_zero _))

omit [DecidableEq A] in
@[simp] theorem addRelsCellsFS_inl (v : J →₀ MonoidAlgebra ℤ (PresGroup ρ)) (j : J) :
    addRelsCellsFS ρ ν v (Sum.inl j) = addRelsRingHom ρ ν (v j) := by
  simp only [addRelsCellsFS, Finsupp.mapDomain_apply_of_injective Sum.inl_injective, Finsupp.mapRange_apply]

omit [DecidableEq A] in
@[simp] theorem addRelsCellsFS_inr (v : J →₀ MonoidAlgebra ℤ (PresGroup ρ)) (l : L) :
    addRelsCellsFS ρ ν v (Sum.inr l) = 0 := by simp_all [Finsupp.mapDomain_notin_range, addRelsCellsFS]

omit [DecidableEq A] in
@[simp] theorem addRelsCellsFS_single (j : J) (a : MonoidAlgebra ℤ (PresGroup ρ)) :
    addRelsCellsFS ρ ν (Finsupp.single j a) =
      Finsupp.single (Sum.inl j) (addRelsRingHom ρ ν a) := by
  simp only [addRelsCellsFS, Finsupp.mapRange_single, Finsupp.mapDomain_single]

omit [DecidableEq A] in
theorem addRelsCellsFS_add (v w : J →₀ MonoidAlgebra ℤ (PresGroup ρ)) :
    addRelsCellsFS ρ ν (v + w) = addRelsCellsFS ρ ν v + addRelsCellsFS ρ ν w := by
  ext j : 1
  cases j <;> simp [map_add]

theorem addRelsCellsFS_boundary (v : J →₀ MonoidAlgebra ℤ (PresGroup ρ)) (a : A) :
    coverSecondBoundary (relSub (addRels ρ ν)) (addRels ρ ν) (addRelsCellsFS ρ ν v) a =
      addRelsRingHom ρ ν (coverSecondBoundary (relSub ρ) ρ v a) := by
  induction v using Finsupp.induction_linear with
  | zero => simp [addRelsCellsFS]
  | add v w hv hw => simp only [addRelsCellsFS_add, map_add, Finsupp.add_apply, hv, hw]
  | single j c =>
      simp only [addRelsCellsFS_single, fsCoverSecondBoundary_apply,
        Finsupp.sum_single_index, zero_mul, foxMatrix_addRels_inl, map_mul]

def addRelsMorFS : PresMorFS ρ (addRels ρ ν) where
  hom := addRelsHom ρ ν
  cells := addRelsCellsFS ρ ν
  cells_add := addRelsCellsFS_add ρ ν
  cells_smul := by
    intro a v
    ext j : 1
    cases j <;>
      simp [Finsupp.smul_apply, smul_eq_mul, map_mul, addRelsRingHom]
  cells_cycle := by
    intro v hv
    change coverSecondBoundary _ _ v = 0 at hv
    ext a : 1
    rw [addRelsCellsFS_boundary, hv, Finsupp.zero_apply, map_zero]
    rfl
  cells_aug := by
    intro v hv j
    cases j with
    | inl j => rw [addRelsCellsFS_inl, augPres_addRelsRingHom, hv]
    | inr l => rw [addRelsCellsFS_inr, map_zero]

end FiniteChains
end

section
open scoped Classical commutatorElement
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.RelativeNormalForm

section Receiver
variable {G : Type} [Group G]

abbrev PairReceiver (z : G) :=
  HNNExtension (Monoid.Coprod G (Multiplicative ℤ))
    (Subgroup.zpowers (freeGen (G := G)))
    (Subgroup.zpowers (Monoid.Coprod.inl z * freeGen))
    (zpowersEquivZpowers not_isOfFinOrder_freeGen (not_isOfFinOrder_mul_freeGen z))

def pairReceiverBase (z : G) : G →* PairReceiver z :=
  (HNNExtension.of : Monoid.Coprod G (Multiplicative ℤ) →* PairReceiver z).comp
    Monoid.Coprod.inl

def pairReceiverA (z : G) : PairReceiver z := HNNExtension.t
def pairReceiverB (z : G) : PairReceiver z := HNNExtension.of freeGen

theorem pairReceiver_commutator (z : G) :
    ⁅pairReceiverA z, pairReceiverB z⁆ = pairReceiverBase z z := by
  have hgen :
      (zpowersEquivZpowers not_isOfFinOrder_freeGen (not_isOfFinOrder_mul_freeGen z))
        ⟨freeGen, Subgroup.mem_zpowers _⟩ =
      ⟨Monoid.Coprod.inl z * freeGen, Subgroup.mem_zpowers _⟩ := by
    have hsymm : (zpowersEquivInt (not_isOfFinOrder_freeGen (G := G))).symm
        ⟨freeGen, Subgroup.mem_zpowers _⟩ = Multiplicative.ofAdd 1 := by
      rw [MulEquiv.symm_apply_eq]
      exact Subtype.ext (by simp [zpowersEquivInt])
    change (zpowersEquivInt (not_isOfFinOrder_mul_freeGen z))
      ((zpowersEquivInt not_isOfFinOrder_freeGen).symm _) = _
    rw [hsymm]
    exact Subtype.ext (by simp [zpowersEquivInt])
  have hconj := HNNExtension.equiv_eq_conj
    (φ := zpowersEquivZpowers not_isOfFinOrder_freeGen (not_isOfFinOrder_mul_freeGen z))
    ⟨freeGen, Subgroup.mem_zpowers _⟩
  rw [hgen] at hconj
  rw [map_mul] at hconj
  change pairReceiverBase z z * pairReceiverB z =
    pairReceiverA z * pairReceiverB z * (pairReceiverA z)⁻¹ at hconj
  rw [commutatorElement_def, ← hconj]
  group


end Receiver

variable {A Z J : Type} (ρ : J → FreeGroup (A ⊕ Z))

def pairRel : J → FreeGroup (PairGen A Z) := fun j => pairSubstitution (ρ j)

def pairSubGroupHom : PresGroup ρ →* PresGroup (pairRel ρ) :=
  QuotientGroup.lift _ ((QuotientGroup.mk' _).comp pairSubstitution) (by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨j, rfl⟩
    exact (QuotientGroup.eq_one_iff _).mpr
      (Subgroup.subset_normalClosure ⟨j, rfl⟩))

def familyPairBase (z : Z) : PresGroup ρ →*
    PairReceiver (QuotientGroup.mk (FreeGroup.of (Sum.inr z)) : PresGroup ρ) :=
  pairReceiverBase _

abbrev PairAmalgam := Monoid.PushoutI (familyPairBase ρ)

def pairReceiverLift : FreeGroup (PairGen A Z) →* PairAmalgam ρ :=
  FreeGroup.lift (Sum.elim
    (fun a => Monoid.PushoutI.base (familyPairBase ρ)
      (QuotientGroup.mk (FreeGroup.of (Sum.inl a))))
    (fun p => Monoid.PushoutI.of p.1
      (if p.2 then pairReceiverB
        (QuotientGroup.mk (FreeGroup.of (Sum.inr p.1)) : PresGroup ρ)
       else pairReceiverA
        (QuotientGroup.mk (FreeGroup.of (Sum.inr p.1)) : PresGroup ρ))))

/-- The prescribed commutator of each pair is the corresponding original
generator in the common amalgamated base group. -/
theorem pairReceiverLift_comp :
    (pairReceiverLift ρ).comp (pairSubstitution (A := A) (Z := Z)) =
      (Monoid.PushoutI.base (familyPairBase ρ)).comp (QuotientGroup.mk' (relSub ρ)) := by
  apply FreeGroup.ext_hom
  intro x
  cases x with
  | inl a => rfl
  | inr z =>
      simp
      change ⁅Monoid.PushoutI.of (φ := familyPairBase ρ) z
          (pairReceiverA (QuotientGroup.mk (FreeGroup.of (Sum.inr z)))),
        Monoid.PushoutI.of (φ := familyPairBase ρ) z
          (pairReceiverB (QuotientGroup.mk (FreeGroup.of (Sum.inr z))))⁆ = _
      rw [← map_commutatorElement, pairReceiver_commutator]
      exact Monoid.PushoutI.of_apply_eq_base (familyPairBase ρ) z _

def pairComparison : PresGroup (pairRel ρ) →* PairAmalgam ρ :=
  QuotientGroup.lift _ (pairReceiverLift ρ) (by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨j, rfl⟩
    change pairReceiverLift ρ (pairSubstitution (ρ j)) = 1
    have h := congrArg (fun f : FreeGroup (A ⊕ Z) →* PairAmalgam ρ => f (ρ j))
      (pairReceiverLift_comp ρ)
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply] at h
    rw [h]
    have hj : (QuotientGroup.mk (ρ j) : PresGroup ρ) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure ⟨j, rfl⟩)
    rw [QuotientGroup.mk'_apply, hj, map_one])

theorem pairComparison_comp : (pairComparison ρ).comp (pairSubGroupHom ρ) =
    Monoid.PushoutI.base (familyPairBase ρ) := by
  apply MonoidHom.ext
  intro g
  induction g using QuotientGroup.induction_on with
  | H w =>
      exact congrArg (fun f : FreeGroup (A ⊕ Z) →* PairAmalgam ρ => f w)
        (pairReceiverLift_comp ρ)

/-- Actual simultaneous generator substitution is injective, including for
an infinite or empty family of extra generators. -/
theorem pairSubGroupHom_injective : Function.Injective (pairSubGroupHom ρ) := by
  intro g h he
  apply Monoid.PushoutI.base_injective (φ := familyPairBase ρ)
    (fun z => (rule_one_embedding _))
  have hc := congrArg (pairComparison ρ) he
  change ((pairComparison ρ).comp (pairSubGroupHom ρ)) g =
    ((pairComparison ρ).comp (pairSubGroupHom ρ)) h at hc
  simpa only [pairComparison_comp] using hc

end FiniteChains.RelativeNormalForm
end

section
open scoped Classical
namespace FiniteChains

theorem fox_subst_weighted_coordinate {I K : Type} [DecidableEq I] [DecidableEq K]
    (φ : FreeGroup I →* FreeGroup K)
    (a : I) (b : K) (d : FreeGroupRing K)
    (h : ∀ i, fox b (φ (FreeGroup.of i)) = if a = i then d else 0)
    (w : FreeGroup I) :
    fox b (φ w) = MonoidAlgebra.mapDomainRingHom ℤ φ (fox a w) * d := by
  induction w using FreeGroup.induction_on with
  | one => simp
  | of i => simp_all
  | inv_of i ih =>
      rw [map_inv, fox_inv, fox_inv, map_neg, map_mul, ih, groupRingMap_grp, map_inv]
      noncomm_ring
  | mul v w hv hw =>
      rw [map_mul, fox_mul, fox_mul, map_add, map_mul, groupRingMap_grp, hv, hw]
      noncomm_ring

namespace RelativeNormalForm
open BlockFamily

variable {A Z J : Type}

def pairOldCoordinate : PairGen A Z → A ⊕ Z :=
  Sum.elim Sum.inl (fun p => Sum.inr p.1)

def pairFoxWeight (i : PairGen A Z) : FreeGroupRing (PairGen A Z) :=
  fox i (pairSubstitution (FreeGroup.of (pairOldCoordinate i)))

theorem pairSubstitution_generator_fox (i : PairGen A Z) (j : A ⊕ Z) :
    fox i (pairSubstitution (FreeGroup.of j)) =
      if pairOldCoordinate i = j then pairFoxWeight i else 0 := by
  by_cases h : pairOldCoordinate i = j
  · subst j
    rw [if_pos rfl]
    rfl
  · rw [if_neg h]
    cases i with
    | inl a =>
        cases j with
        | inl b =>
            have hab : a ≠ b := by simpa [pairOldCoordinate] using h
            simp [fox_of, hab]
        | inr z =>
            simp [commutatorElement_def, fox_mul, fox_inv, fox_of]
    | inr p =>
        cases j with
        | inl a => simp [fox_of]
        | inr z =>
            have hpz : p.1 ≠ z := by simpa [pairOldCoordinate] using h
            obtain ⟨p, b⟩ := p
            simp [commutatorElement_def, fox_mul, fox_inv, fox_of, hpz]

theorem pairSubstitution_fox (i : PairGen A Z) (w : FreeGroup (A ⊕ Z)) :
    fox i (pairSubstitution w) =
      MonoidAlgebra.mapDomainRingHom ℤ pairSubstitution (fox (pairOldCoordinate i) w) *
        pairFoxWeight i :=
  fox_subst_weighted_coordinate (pairSubstitution (A := A) (Z := Z))
    (pairOldCoordinate i) i (pairFoxWeight i) (pairSubstitution_generator_fox i) w

@[simp] theorem pairFoxWeight_core (a : A) : pairFoxWeight (Sum.inl (β := Z × Bool) a) = 1 := by
  simp [pairFoxWeight, pairOldCoordinate, fox_of]

def pairConjugate (z : Z) : FreeGroup (PairGen A Z) :=
  FreeGroup.of (Sum.inr (z, false)) * FreeGroup.of (Sum.inr (z, true)) *
    (FreeGroup.of (Sum.inr (z, false)))⁻¹


variable (ρ : J → FreeGroup (A ⊕ Z))

def pairCoefficients := MonoidAlgebra.mapDomainRingHom ℤ (pairSubGroupHom ρ)

theorem pairCoefficients_proj (x : FreeGroupRing (A ⊕ Z)) :
    pairCoefficients ρ (proj (relSub ρ) x) =
      proj (relSub (pairRel ρ)) (MonoidAlgebra.mapDomainRingHom ℤ pairSubstitution x) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => rfl
  | add x y hx hy => grind
  | single w a =>
      apply MonoidAlgebra.coeff_injective
      change Finsupp.mapDomain (pairSubGroupHom ρ)
        (Finsupp.mapDomain (QuotientGroup.mk' (relSub ρ)) (Finsupp.single w a)) =
        Finsupp.mapDomain (QuotientGroup.mk' (relSub (pairRel ρ)))
          (Finsupp.mapDomain pairSubstitution (Finsupp.single w a))
      simp
      rfl

def pairOldBoundary := fsRingMapBoundary (pairCoefficients ρ)
  (fun j => coverFoxGradient (relSub ρ) (ρ j))

theorem pair_boundary_coordinate
    (x : J →₀ MonoidAlgebra ℤ (PresGroup (pairRel ρ))) (i : PairGen A Z) :
    coverSecondBoundary (relSub (pairRel ρ)) (pairRel ρ) x i =
      pairOldBoundary ρ x (pairOldCoordinate i) *
        proj (relSub (pairRel ρ)) (pairFoxWeight i) := by
  rw [fsCoverSecondBoundary_apply]
  have hcol j : foxMatrixPres (pairRel ρ) i j =
      pairCoefficients ρ (foxMatrixPres ρ (pairOldCoordinate i) j) *
        proj (relSub (pairRel ρ)) (pairFoxWeight i) := by
    change proj _ (fox i (pairSubstitution (ρ j))) = _
    rw [pairSubstitution_fox, map_mul, ← pairCoefficients_proj]
    rfl
  simp_rw [hcol, ← mul_assoc]
  rw [Finsupp.sum, ← Finset.sum_mul]
  congr 1
  simp only [pairOldBoundary, fsRingMapBoundary, Finsupp.linearCombination_apply,
    Finsupp.sum_apply, Finsupp.smul_apply, smul_eq_mul, Finsupp.mapRange_apply]
  rfl

def pairExponent (z : Z) : PresGroup (pairRel ρ) →* Multiplicative ℤ :=
  QuotientGroup.lift _ (expSum (Sum.inr (α := A) (z, true))) (by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨j, rfl⟩
    exact pairSubstitution_exp_pair (ρ j) (z, true))


/-- Every new cycle is an actual old Fox cycle over the enlarged coefficient
ring. This is the content of rule 1, before the injective base-change step. -/

def pairStructuralMap : PresMorFS ρ (pairRel ρ) where
  hom := pairSubGroupHom ρ
  cells := fun x => x.mapRange (pairCoefficients ρ) (map_zero _)
  cells_add := by
    intro x y
    ext j : 1
    simp only [Finsupp.mapRange_apply, Finsupp.add_apply]
    exact map_add _ _ _
  cells_smul := by
    intro a x
    ext j : 1
    simp only [Finsupp.mapRange_apply, Finsupp.smul_apply, smul_eq_mul]
    exact map_mul _ _ _
  cells_cycle := by
    intro x hx
    change coverSecondBoundary _ _ _ = 0
    ext i : 1
    rw [pair_boundary_coordinate]
    change fsRingMapBoundary (pairCoefficients ρ) _ (x.mapRange _ _) _ * _ = 0
    rw [fsRingMapBoundary_mapRange]
    erw [hx]
    simp
  cells_aug := by
    intro x hx j
    change augPres (pairRel ρ) (MonoidAlgebra.mapDomainRingHom ℤ (pairSubGroupHom ρ) (x j)) = 0
    exact (augQ_mapDomain (pairSubGroupHom ρ) (x j)).trans (hx j)

/-- Equation (3.3) for simultaneous rule 1 with every input discharged. -/
theorem pairStructuralMap_generates : FSGenerates (pairStructuralMap ρ) := by
  intro x hx
  exact fs_cycle_mem_span_groupMap_cycles (pairSubGroupHom ρ)
    (pairSubGroupHom_injective ρ)
    (fun j => coverFoxGradient (relSub ρ) (ρ j)) x (show pairOldBoundary ρ x = 0 by
      ext i : 1
      cases i with
      | inl a =>
          have h := congrArg (fun c => c (Sum.inl a)) hx
          simpa only [pair_boundary_coordinate, pairOldCoordinate, Sum.elim_inl, Sum.elim_inr, pairFoxWeight_core,
            map_one, mul_one, Finsupp.zero_apply] using h
      | inr z =>
          apply mul_one_sub_single_eq_zero (by
            apply not_isOfFinOrder_of_map (pairExponent ρ z)
            have he : pairExponent ρ z (QuotientGroup.mk (pairConjugate z)) =
                Multiplicative.ofAdd 1 := by
              change expSum (Sum.inr (z, true)) (pairConjugate z) = _
              simp [pairConjugate, expSum]
            rw [he]
            exact not_isOfFinOrder_ofAdd_one)
          have h := congrArg (fun c => c (Sum.inr (z, false))) hx
          simpa only [pair_boundary_coordinate, pairOldCoordinate, Sum.elim_inl, Sum.elim_inr, (show pairFoxWeight (Sum.inr (z, false)) = 1 - grp (pairConjugate z) by
            simp [pairFoxWeight, pairOldCoordinate, commutatorElement_def, fox_mul,
              fox_inv, fox_of, pairConjugate, grp_mul]
            noncomm_ring),
            map_sub, map_one, proj_grp, qgrp, Finsupp.zero_apply] using h)

end RelativeNormalForm
end FiniteChains
end

section
open scoped Classical
namespace FiniteChains.RelativeNormalForm

variable {A C Z S : Type} (core : C → FreeGroup A)
  (hcore : Function.Surjective (expMatrix core))
  (extra : S → FreeGroup (A ⊕ Z))

def rawPresentation : C ⊕ S → FreeGroup (A ⊕ Z) :=
  Sum.elim (fun c => FreeGroup.map Sum.inl (core c)) extra

theorem pairRel_rawPresentation : pairRel (rawPresentation core extra) =
    beforeCorrection core extra := by
  funext j
  cases j with
  | inl c => exact pairSubstitution_map_core (core c)
  | inr s => rfl

def relativeRuleOneMap : PresMorFS (rawPresentation core extra) (beforeCorrection core extra) :=
  (pairStructuralMap (rawPresentation core extra)).castTarget (pairRel_rawPresentation core extra)

def pairGroupHomTo {B W J : Type} (ρ : J → FreeGroup (B ⊕ W))
    (τ : J → FreeGroup (PairGen B W)) (h : pairRel ρ = τ) : PresGroup ρ →* PresGroup τ :=
  QuotientGroup.lift _ ((QuotientGroup.mk' _).comp pairSubstitution) (by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨j, rfl⟩
    apply (QuotientGroup.eq_one_iff _).mpr
    exact Subgroup.subset_normalClosure ⟨j, (congrFun h j).symm⟩)

theorem pairCast_hom {B W J : Type} (ρ : J → FreeGroup (B ⊕ W))
    (τ : J → FreeGroup (PairGen B W)) (h : pairRel ρ = τ) :
    ((pairStructuralMap ρ).castTarget h).hom = pairGroupHomTo ρ τ h := by
  cases h
  rfl

theorem pairCast_cells {B W J : Type} (ρ : J → FreeGroup (B ⊕ W))
    (τ : J → FreeGroup (PairGen B W)) (h : pairRel ρ = τ)
    (x : J →₀ MonoidAlgebra ℤ (PresGroup ρ)) :
    ((pairStructuralMap ρ).castTarget h).cells x =
      x.mapRange (MonoidAlgebra.mapDomainRingHom ℤ ((pairStructuralMap ρ).castTarget h).hom)
        (map_zero _) := by
  cases h
  rfl

@[simp] theorem relativeRuleOneMap_hom_mk (w : FreeGroup (A ⊕ Z)) :
    (relativeRuleOneMap core extra).hom (QuotientGroup.mk w) =
      QuotientGroup.mk (pairSubstitution w) := by
  rw [relativeRuleOneMap, pairCast_hom]
  rfl

theorem relativeRuleOneMap_cells
    (x : (C ⊕ S) →₀ MonoidAlgebra ℤ (PresGroup (rawPresentation core extra))) :
    (relativeRuleOneMap core extra).cells x =
      x.mapRange (MonoidAlgebra.mapDomainRingHom ℤ (relativeRuleOneMap core extra).hom)
        (map_zero _) := pairCast_cells _ _ _ x

theorem relativeRuleOneMap_generates : FSGenerates (relativeRuleOneMap core extra) :=
  (pairStructuralMap_generates (rawPresentation core extra)).castTarget
    (pairRel_rawPresentation core extra)

/-- Rules 1 and 2 supply the normalized source used by the terminal theorem. -/
def relativeNormalizationMap : PresMorFS (rawPresentation core extra)
    (normalizedPresentation core hcore extra) :=
  (normalizationSlideMap core hcore extra).comp (relativeRuleOneMap core extra)


theorem normalizedPresentation_cockcroft (hP : FSIsCockcroft (rawPresentation core extra)) :
    FSIsCockcroft (normalizedPresentation core hcore extra) :=
  fsIsCockcroft_of_generates (relativeNormalizationMap core hcore extra)
    ((normalizationSlideMap_generates core hcore extra).comp
    (relativeRuleOneMap_generates core extra)) hP

end FiniteChains.RelativeNormalForm

namespace FiniteChains.Davis.Genus

open BlockFamily

variable {A K M S : Type} [Fintype A] [Fintype K] [Fintype M] [Fintype S]
  [DecidableEq A] [DecidableEq K] [DecidableEq S]
  (core : M → FreeGroup A) (q : S → ℕ) [∀ s, NeZero (q s)]
  (u : ∀ s, Fin (q s) × Bool → FreeGroup (A ⊕ K))

/-- The original core together with one disk on each stable generator. -/
def terminalSpineCore : M ⊕ K → FreeGroup (A ⊕ K) :=
  corePres core (fun k => FreeGroup.of (Sum.inr k))

/-- Each new internal generator belongs to exactly one spine. -/
def terminalSpineGen (s : S) (z : SpinePresentationGen (q s)) :
    (A ⊕ K) ⊕ (Σ s, SpinePresentationGen (q s)) := Sum.inr ⟨s, z⟩

/-- Actual substituted relators, written out to retain their orientation. -/
def terminalSpineExtra : (Σ s, NamedSpineRel (q s)) →
    FreeGroup ((A ⊕ K) ⊕ (Σ s, SpinePresentationGen (q s)))
  | ⟨s, .inl f⟩ => FreeGroup.map (terminalSpineGen (A := A) (K := K) q s)
      (spinePresentation (q s) f)
  | ⟨s, .inr x⟩ => FreeGroup.map Sum.inl (u s x) *
      (FreeGroup.map (terminalSpineGen (A := A) (K := K) q s)
        (spinePresentationMarkedWord (q s) x))⁻¹

/-- Q after capping the stable generators, with caps placed next to the core. -/
def terminalSpinePres : (M ⊕ K) ⊕ (Σ s, NamedSpineRel (q s)) →
    FreeGroup ((A ⊕ K) ⊕ (Σ s, SpinePresentationGen (q s))) :=
  corePres (terminalSpineCore (K := K) core) (terminalSpineExtra q u)

def terminalNamedWordMap (s : S) : FreeGroup (NamedSpineGen (q s)) →*
    FreeGroup ((A ⊕ K) ⊕ (Σ s, SpinePresentationGen (q s))) :=
  (FreeGroup.map (genEmb (Zt := fun s => SpinePresentationGen (q s)) s)).comp
    ((blockSubst (Zt := fun _ : PUnit.{1} => SpinePresentationGen (q s))
      (fun _ => u s) PUnit.unit).comp (FreeGroup.map Sum.swap))

omit [Fintype A] [Fintype K] [Fintype S] [DecidableEq A] [DecidableEq K] [DecidableEq S] in
theorem terminalNamedWordMap_old (s : S)
    (w : FreeGroup (SpinePresentationGen (q s))) :
    terminalNamedWordMap q u s (FreeGroup.map Sum.inl w) =
      FreeGroup.map (terminalSpineGen (A := A) (K := K) q s) w := by
  have h : (terminalNamedWordMap q u s).comp (FreeGroup.map Sum.inl) =
      FreeGroup.map (terminalSpineGen q s) := by
    apply FreeGroup.ext_hom
    intro z
    simp [terminalNamedWordMap, terminalSpineGen]
  exact DFunLike.congr_fun h w


omit [Fintype A] [Fintype K] [Fintype M] [Fintype S]
  [DecidableEq A] [DecidableEq K] [DecidableEq S] in
/-- The explicit terminal words are exactly the words used in actual B1/B2,
not a different block presentation. -/
theorem terminalSpineExtra_eq_family (s : S) (m : NamedSpineRel (q s)) :
    terminalSpineExtra q u ⟨s, m⟩ =
      FreeGroup.map (genEmb (Zt := fun s => SpinePresentationGen (q s)) s)
        (familyFiniteSpineWordBlock q u s m) := by
  cases m with
  | inl f =>
      exact (terminalNamedWordMap_old q u s (spinePresentation (q s) f)).symm
  | inr x =>
      change FreeGroup.map Sum.inl (u s x) *
        (FreeGroup.map (terminalSpineGen q s)
          (spinePresentationMarkedWord (q s) x))⁻¹ =
        terminalNamedWordMap q u s (FreeGroup.of (Sum.inr x) *
          (FreeGroup.map Sum.inl (spinePresentationMarkedWord (q s) x))⁻¹)
      rw [map_mul, map_inv, (show terminalNamedWordMap q u s (FreeGroup.of (Sum.inr x)) =
      FreeGroup.map Sum.inl (u s x) by
        change FreeGroup.map (genEmb (Zt := fun s => SpinePresentationGen (q s)) s)
          (blockSubst (Zt := fun _ : PUnit.{1} => SpinePresentationGen (q s))
            (fun _ => u s) PUnit.unit (FreeGroup.map Sum.swap (FreeGroup.of (Sum.inr x)))) = _
        simp
        have h : (FreeGroup.map (genEmb (Zt := fun s => SpinePresentationGen (q s)) s)).comp
            (FreeGroup.map Sum.inl) =
            FreeGroup.map (Sum.inl : A ⊕ K → (A ⊕ K) ⊕ (Σ s, SpinePresentationGen (q s))) := by
          apply FreeGroup.ext_hom
          intro a
          simp
        exact DFunLike.congr_fun h (u s x)), terminalNamedWordMap_old]

/-- The target is the actual wedge of genuine capped-spine presentations. -/
def terminalSpineWedge : (Σ s, NamedSpineRel (q s)) →
    FreeGroup (Σ s, SpinePresentationGen (q s)) :=
  sigmaWedgeRel (fun s => cappedSpinePresentation (q s))

def terminalSpineReverse : (Σ s, NamedSpineRel (q s)) → Bool
  | ⟨_, .inl _⟩ => false
  | ⟨_, .inr _⟩ => true

omit [Fintype A] [Fintype K] [Fintype S] [DecidableEq A] [DecidableEq K] [DecidableEq S] in
theorem terminalSpineGen_drop (s : S)
    (w : FreeGroup (SpinePresentationGen (q s))) :
    CoreSignedCollapse.dropCore
      (FreeGroup.map (terminalSpineGen (A := A) (K := K) q s) w) =
      FreeGroup.map (Sigma.mk s) w := by
  have h : (CoreSignedCollapse.dropCore).comp
      (FreeGroup.map (terminalSpineGen (A := A) (K := K) q s)) =
      FreeGroup.map (Sigma.mk (β := fun s => SpinePresentationGen (q s)) s) := by
    apply FreeGroup.ext_hom
    intro z
    simp [terminalSpineGen]
  exact DFunLike.congr_fun h w

omit [Fintype A] [Fintype K] [Fintype M] [Fintype S]
  [DecidableEq A] [DecidableEq K] [DecidableEq S] in
theorem terminalSpine_collapse_word (p : Σ s, NamedSpineRel (q s)) :
    CoreSignedCollapse.dropCore (terminalSpineExtra q u p) =
      if terminalSpineReverse q p then (terminalSpineWedge q p)⁻¹
        else terminalSpineWedge q p := by
  obtain ⟨s, f | x⟩ := p
  · exact terminalSpineGen_drop q s (spinePresentation (q s) f)
  · change CoreSignedCollapse.dropCore
      (FreeGroup.map Sum.inl (u s x) *
        (FreeGroup.map (terminalSpineGen q s)
          (spinePresentationMarkedWord (q s) x))⁻¹) =
      (FreeGroup.map (Sigma.mk s) (spinePresentationMarkedWord (q s) x))⁻¹
    rw [map_mul, map_inv, CoreSignedCollapse.dropCore_map_inl,
      terminalSpineGen_drop, one_mul]

/-- The presentation just before rule 3: retain the core and replace the
specified products of commutators. -/
def terminalSpineSource : M ⊕ S → FreeGroup (A ⊕ K) :=
  Sum.elim (fun m => FreeGroup.map Sum.inl (core m))
    (fun s => commWord (u s) (finitePairs (q s)))

/-- The actual simultaneous rule-3 target, before the stable generators are capped. -/
def terminalSpineStructural : M ⊕ (Σ s, NamedSpineRel (q s)) →
    FreeGroup ((A ⊕ K) ⊕ (Σ s, SpinePresentationGen (q s))) :=
  substPresF (terminalSpineSource core q u) (familyFiniteSpineWordBlock q u)

/-- The stable loops capped at the terminal step. -/
def terminalSpineCaps (k : K) :
    FreeGroup ((A ⊕ K) ⊕ (Σ s, SpinePresentationGen (q s))) :=
  FreeGroup.of (Sum.inl (Sum.inr k))

/-- The terminal step in the literal `addRels` indexing. -/
def terminalSpineQ : (M ⊕ (Σ s, NamedSpineRel (q s))) ⊕ K →
    FreeGroup ((A ⊕ K) ⊕ (Σ s, SpinePresentationGen (q s))) :=
  addRels (terminalSpineStructural core q u) (terminalSpineCaps (A := A) (K := K) q)

/-- Move the stable cap labels next to the core labels, retaining every label. -/
def terminalCapReindex {J : Type} : (M ⊕ J) ⊕ K ≃ (M ⊕ K) ⊕ J where
  toFun
    | .inl (.inl m) => .inl (.inl m)
    | .inl (.inr j) => .inr j
    | .inr k => .inl (.inr k)
  invFun
    | .inl (.inl m) => .inl (.inl m)
    | .inl (.inr k) => .inr k
    | .inr j => .inl (.inr j)
  left_inv := by rintro ((m | j) | k) <;> rfl
  right_inv := by rintro ((m | k) | j) <;> rfl

omit [Fintype A] [Fintype K] [Fintype M] [Fintype S]
  [DecidableEq A] [DecidableEq K] [DecidableEq S] in
theorem terminalSpineQ_reindex
    (j : (M ⊕ (Σ s, NamedSpineRel (q s))) ⊕ K) :
    terminalSpinePres core q u (terminalCapReindex j) = terminalSpineQ core q u j := by
  rcases j with (m | ⟨s, f⟩) | k
  · rfl
  · exact terminalSpineExtra_eq_family q u s f
  · rfl

omit [Fintype A] [Fintype K] [Fintype M] [Fintype S]
  [DecidableEq A] [DecidableEq K] [DecidableEq S] in
/-- The terminal presentation depends only on retained core relators: the
replaced source entries no longer occur in the result of rule 3. -/
theorem terminalSpineQ_eq_actual
    (ρ : M ⊕ S → FreeGroup (A ⊕ K))
    (hcore : ∀ m, ρ (Sum.inl m) = FreeGroup.map Sum.inl (core m)) :
    terminalSpineQ core q u =
      addRels (substPresF ρ (familyFiniteSpineWordBlock q u))
        (terminalSpineCaps (A := A) (K := K) q) := by
  funext j
  rcases j with (m | p) | k
  · change FreeGroup.map Sum.inl (FreeGroup.map Sum.inl (core m)) =
      FreeGroup.map Sum.inl (ρ (Sum.inl m))
    rw [hcore]
  · rfl
  · rfl

end FiniteChains.Davis.Genus

namespace FiniteChains.Davis.Genus

open BlockFamily

variable {A K M S : Type} [DecidableEq A] [DecidableEq K] [DecidableEq S]
  (core : M → FreeGroup A) (q : S → ℕ) [∀ s, NeZero (q s)]
  (u : ∀ s, Fin (q s) × Bool → FreeGroup (A ⊕ K))

/-- Every stable cap is a distinct unit row in the exponent-sum matrix. -/
theorem terminalSpineCore_expMatrix_cap (c : (M ⊕ K) →₀ ℤ) (k : K) :
    expMatrix (terminalSpineCore (K := K) core) c (Sum.inr k) = c (Sum.inr k) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single j n =>
      cases j with
      | inl m =>
          have hz : expEntry (terminalSpineCore (K := K) core)
              (Sum.inr k) (Sum.inl m) = 0 := by
            rw [← augPres_foxMatrixPres]
            change augPres (corePres core (fun k : K => FreeGroup.of (Sum.inr k)))
              (foxMatrixPres (corePres core (fun k : K => FreeGroup.of (Sum.inr k)))
                (Sum.inr k) (Sum.inl m)) = 0
            rw [CoreSignedCollapse.matrix_core, map_zero]
          simp only [expMatrix, Finsupp.linearCombination_single,
            Finsupp.smul_apply, smul_eq_mul, expVec_apply]
          change n * expEntry (terminalSpineCore core) (Sum.inr k) (Sum.inl m) = _
          simp [hz]
      | inr l =>
          simp [expMatrix, terminalSpineCore, corePres, expVec_apply, expSum_of,
            Finsupp.single_apply, eq_comm, mul_ite]

/-- Adding arbitrarily many stable generator-cap pairs preserves the genuine
supported exponent-sum injection of the original core. -/
theorem terminalSpineCore_expMatrix_injective
    (hcore : Function.Injective (expMatrix core)) :
    Function.Injective (expMatrix (terminalSpineCore (K := K) core)) := by
  intro c d h
  have hz : expMatrix (terminalSpineCore (K := K) core) (c - d) = 0 := by
    rw [map_sub, h, sub_self]
  have hcap (k : K) : (c - d) (Sum.inr k) = 0 := by
    rw [← terminalSpineCore_expMatrix_cap core (c - d) k, hz]
    rfl
  exact sub_eq_zero.mp (corePres_expMatrix_kernel_reflect core
    (fun k : K => FreeGroup.of (Sum.inr k)) hcore (c - d) hz hcap)



/-- Actual addRels ordering, with no finiteness assumptions. -/
theorem terminalSpineQ_fsIsCockcroft (hcore : Function.Injective (expMatrix core)) :
    FSIsCockcroft (terminalSpineQ core q u) :=
  RelatorReindex.fsIsCockcroft_of (terminalSpineQ core q u) (terminalSpinePres core q u)
    terminalCapReindex (terminalSpineQ_reindex core q u)
    (CoreSignedCollapse.fsIsCockcroft (terminalSpineCore (K := K) core) (terminalSpineExtra q u)
    (terminalSpineWedge q) (terminalSpineReverse q) (terminalSpine_collapse_word q u)
    (terminalSpineCore_expMatrix_injective core hcore) (fsIsCockcroft_sigmaWedgeRel (fun s => cappedSpinePresentation (q s))
    (fun s => cappedSpinePresentation_isCockcroft (q s))))


variable (ρ : M ⊕ S → FreeGroup (A ⊕ K))
  (hrho : ∀ s, ρ (Sum.inr s) = commWord (u s) (finitePairs (q s)))

/-- The actual structural map with the equality instances of the terminal presentation. -/
def terminalStructuralMapFS :
    PresMorFS ρ (substPresF ρ (familyFiniteSpineWordBlock q u)) := by
  let dSrc : DecidableEq (A ⊕ K) := inferInstance
  let dTgt : DecidableEq ((A ⊕ K) ⊕ (Σ s, SpinePresentationGen (q s))) := inferInstance
  letI : DecidableEq (A ⊕ K) := Classical.decEq _
  letI : DecidableEq S := Classical.decEq _
  let dFamilyTgt : DecidableEq ((A ⊕ K) ⊕ (Σ s, SpinePresentationGen (q s))) :=
    @instDecidableEqSum _ _ (Classical.decEq _) inferInstance
  exact @PresMorFS.redecide _ _ _ _ (Classical.decEq _) dFamilyTgt _ _
    (finiteSpineFamilyStructuralMap ρ q u hrho) dSrc dTgt


/-- The actual terminal inclusion, with supported chain modules. -/
def actualTerminalSpineMorFS :
    PresMorFS (substPresF ρ (familyFiniteSpineWordBlock q u))
      (addRels (substPresF ρ (familyFiniteSpineWordBlock q u))
        (terminalSpineCaps (A := A) (K := K) q)) :=
  addRelsMorFS (substPresF ρ (familyFiniteSpineWordBlock q u))
    (terminalSpineCaps (A := A) (K := K) q)



include hrho in
/-- The arbitrary-core terminal step of Lemma 3.10.  The only core H2
assumption is injectivity of expMatrix on actual finitely supported chains.
Both the terminal Cockcroft and zero-pi2 conclusions are proved. -/
theorem actualTerminalSpineFS_conclusions
    (hretained : ∀ m, ρ (Sum.inl m) = FreeGroup.map Sum.inl (core m))
    (hcore : Function.Injective (expMatrix core)) (hP : FSIsCockcroft ρ)
    (hcoreTriv : ∀ a : A,
      (QuotientGroup.mk (FreeGroup.of (Sum.inl a)) : PresGroup ρ) = 1) :
    FSIsCockcroft (addRels (substPresF ρ (familyFiniteSpineWordBlock q u))
        (terminalSpineCaps (A := A) (K := K) q)) ∧
    (∀ v, FSIsFoxCycle (substPresF ρ (familyFiniteSpineWordBlock q u)) v →
      (actualTerminalSpineMorFS q u ρ).cells v = 0) :=
  ⟨(by
    rw [← terminalSpineQ_eq_actual core q u ρ hretained]
    exact terminalSpineQ_fsIsCockcroft core q u hcore),
    fun v hv => (by
      apply fsCells_eq_zero_of_generates_comp (terminalStructuralMapFS q u ρ hrho)
        (actualTerminalSpineMorFS q u ρ)
        (by
          let dSrc : DecidableEq (A ⊕ K) := inferInstance
          let dTgt : DecidableEq ((A ⊕ K) ⊕ (Σ s, SpinePresentationGen (q s))) := inferInstance
          letI : DecidableEq (A ⊕ K) := Classical.decEq _
          letI : DecidableEq S := Classical.decEq _
          let dFamilyTgt : DecidableEq ((A ⊕ K) ⊕ (Σ s, SpinePresentationGen (q s))) :=
            @instDecidableEqSum _ _ (Classical.decEq _) inferInstance
          exact @FSGenerates.redecide _ _ _ _ (Classical.decEq _) dFamilyTgt _ _ _
            (finiteSpineFamilyStructuralMap_generates ρ q u hrho) dSrc dTgt) ?_ hv
      intro y hy
      exact fsCells_eq_zero_of_isCockcroft_of_hom_trivial
        ((actualTerminalSpineMorFS q u ρ).comp (terminalStructuralMapFS q u ρ hrho))
        hP (by
          apply hom_eq_one_of_gens
          rintro (a | k)
          · grind
          · change (QuotientGroup.mk (FreeGroup.map Sum.inl (FreeGroup.of (Sum.inr k))) :
              PresGroup (addRels (substPresF ρ (familyFiniteSpineWordBlock q u))
                (terminalSpineCaps (A := A) (K := K) q))) = 1
            rw [FreeGroup.map.of]
            apply (QuotientGroup.eq_one_iff _).mpr
            exact Subgroup.subset_normalClosure ⟨Sum.inr k, rfl⟩) y hy)⟩

end FiniteChains.Davis.Genus

namespace FiniteChains.RelativeNormalForm
open Davis Davis.Genus BlockFamily

variable {A C Z S : Type} (core : C → FreeGroup A)
  (hcore : Function.Surjective (expMatrix core))
  (extra : S → FreeGroup (A ⊕ Z))

/-- The original relative group maps to its actual normalized group by
the prescribed pair substitution. -/
def rawToNormalizedGroup : PresGroup (rawPresentation core extra) →*
    PresGroup (normalizedPresentation core hcore extra) :=
  QuotientGroup.lift _ ((QuotientGroup.mk' _).comp pairSubstitution) (by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨j, rfl⟩
    apply (QuotientGroup.eq_one_iff _).mpr
    rw [relSub_normalizedPresentation]
    cases j with
    | inl c =>
        change pairSubstitution (FreeGroup.map Sum.inl (core c)) ∈ _
        rw [pairSubstitution_map_core]
        exact Subgroup.subset_normalClosure ⟨Sum.inl c, rfl⟩
    | inr s => exact Subgroup.subset_normalClosure ⟨Sum.inr s, rfl⟩)

theorem normalized_core_trivial
    (htriv : ∀ a : A,
      (QuotientGroup.mk (FreeGroup.of (Sum.inl a)) : PresGroup (rawPresentation core extra)) = 1)
    (a : A) :
    (QuotientGroup.mk (FreeGroup.of (Sum.inl a)) :
      PresGroup (normalizedPresentation core hcore extra)) = 1 := by
  have h := congrArg (rawToNormalizedGroup core hcore extra) (htriv a)
  change QuotientGroup.mk (pairSubstitution (FreeGroup.of (Sum.inl a))) =
    rawToNormalizedGroup core hcore extra 1 at h
  simp_all

def terminalPresentation :=
  addRels (blockPresentation core hcore extra)
    (terminalSpineCaps (A := A) (K := Z × Bool) (normalizedGenus core hcore extra))

def relativeTerminalMap : PresMorFS (blockPresentation core hcore extra)
    (terminalPresentation core hcore extra) :=
  actualTerminalSpineMorFS (normalizedGenus core hcore extra)
    (normalizedLoops core hcore extra) (normalizedPresentation core hcore extra)

/-- A genuine fixed-core terminal step for an arbitrary relative source.
The source need only be Cockcroft with trivial core image. -/
theorem relativeTerminal_conclusions
    (hcoreInjective : Function.Injective (expMatrix core))
    (hP : FSIsCockcroft (rawPresentation core extra))
    (htriv : ∀ a : A,
      (QuotientGroup.mk (FreeGroup.of (Sum.inl a)) : PresGroup (rawPresentation core extra)) = 1) :
    FSIsCockcroft (terminalPresentation core hcore extra) ∧
      (∀ v, FSIsFoxCycle (blockPresentation core hcore extra) v →
        (relativeTerminalMap core hcore extra).cells v = 0) :=
  actualTerminalSpineFS_conclusions core (normalizedGenus core hcore extra)
    (normalizedLoops core hcore extra) (normalizedPresentation core hcore extra)
    (normalizedPresentation_surface core hcore extra) (fun _ => rfl)
    hcoreInjective (normalizedPresentation_cockcroft core hcore extra hP)
    (normalized_core_trivial core hcore extra htriv)

end FiniteChains.RelativeNormalForm

namespace FiniteChains
open BlockFamily

namespace FreePadding
variable {A B J : Type} (ρ : J → FreeGroup A) (f : A → B) (hf : Function.Injective f)

def rel : J → FreeGroup B := fun j => FreeGroup.map f (ρ j)

def groupHom : PresGroup ρ →* PresGroup (rel ρ f) :=
  QuotientGroup.map _ _ (FreeGroup.map f) (by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨j, rfl⟩
    exact Subgroup.subset_normalClosure ⟨j, rfl⟩)

def wordRetraction : FreeGroup B →* FreeGroup A :=
  FreeGroup.lift (fun b => if h : ∃ a, f a = b then FreeGroup.of h.choose else 1)

include hf in
theorem wordRetraction_map (w : FreeGroup A) :
    wordRetraction f (FreeGroup.map f w) = w := by
  have hmap : (wordRetraction f).comp (FreeGroup.map f) = MonoidHom.id _ := by
    apply FreeGroup.ext_hom
    intro a
    have he : ∃ a', f a' = f a := ⟨a, rfl⟩
    simp only [MonoidHom.comp_apply, FreeGroup.map.of, wordRetraction,
      FreeGroup.lift_apply_of, dif_pos he, MonoidHom.id_apply]
    exact congrArg FreeGroup.of (hf he.choose_spec)
  exact congrArg (fun h : FreeGroup A →* FreeGroup A => h w) hmap



def coefficients := MonoidAlgebra.mapDomainRingHom ℤ (groupHom ρ f)

theorem coefficients_proj (x : FreeGroupRing A) :
    coefficients ρ f (proj (relSub ρ) x) =
      proj (relSub (rel ρ f)) (freeRingMap f x) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => rfl
  | add x y hx hy => simp_all
  | single w a =>
      apply MonoidAlgebra.coeff_injective
      change Finsupp.mapDomain (groupHom ρ f)
        (Finsupp.mapDomain (QuotientGroup.mk' (relSub ρ)) (Finsupp.single w a)) =
        Finsupp.mapDomain (QuotientGroup.mk' (relSub (rel ρ f)))
          (Finsupp.mapDomain (FreeGroup.map f) (Finsupp.single w a))
      simp
      rfl

variable [DecidableEq A] [DecidableEq B]



def oldBoundary := fsRingMapBoundary (coefficients ρ f)
  (fun j => coverFoxGradient (relSub ρ) (ρ j))

include hf in
theorem boundary_retained
    (x : J →₀ MonoidAlgebra ℤ (PresGroup (rel ρ f))) (a : A) :
    coverSecondBoundary (relSub (rel ρ f)) (rel ρ f) x (f a) = oldBoundary ρ f x a := by
  rw [fsCoverSecondBoundary_apply]
  simp only [oldBoundary, fsRingMapBoundary, Finsupp.linearCombination_apply,
    Finsupp.sum_apply, Finsupp.smul_apply, smul_eq_mul, Finsupp.mapRange_apply]
  apply Finsupp.sum_congr
  intro j hj
  rw [(show foxMatrixPres (rel ρ f) (f a) j = coefficients ρ f (foxMatrixPres ρ a j) by
    change proj _ (fox (f a) (FreeGroup.map f (ρ j))) = _
    rw [fox_map f hf, ← coefficients_proj]
    rfl)]
  rfl

def structuralMap : PresMorFS ρ (rel ρ f) where
  hom := groupHom ρ f
  cells := fun x => x.mapRange (coefficients ρ f) (map_zero _)
  cells_add := by
    intro x y
    ext j : 1
    simp only [Finsupp.mapRange_apply, Finsupp.add_apply]
    exact map_add _ _ _
  cells_smul := by
    intro a x
    ext j : 1
    simp only [Finsupp.mapRange_apply, Finsupp.smul_apply, smul_eq_mul]
    exact map_mul _ _ _
  cells_cycle := by
    intro x hx
    change coverSecondBoundary _ _ _ = 0
    ext b : 1
    by_cases hb : b ∈ Set.range f
    · obtain ⟨a, rfl⟩ := hb
      rw [boundary_retained ρ f hf]
      change fsRingMapBoundary (coefficients ρ f) _ (x.mapRange _ _) a = 0
      rw [fsRingMapBoundary_mapRange]
      erw [hx]
      rfl
    · rw [fsCoverSecondBoundary_apply]
      rw [Finsupp.sum]
      apply Finset.sum_eq_zero
      intro j hj
      rw [(show foxMatrixPres (rel ρ f) b j = 0 by
        change proj _ (fox b (FreeGroup.map f (ρ j))) = 0
        rw [fox_map_of_not_mem_range f (fun a h => hb ⟨a, h.symm⟩), map_zero]), mul_zero]
  cells_aug := by
    intro x hx j
    change augPres (rel ρ f) (MonoidAlgebra.mapDomainRingHom ℤ (groupHom ρ f) (x j)) = 0
    exact (augQ_mapDomain (groupHom ρ f) (x j)).trans (hx j)

theorem structuralMap_generates : FSGenerates (structuralMap ρ f hf) := by
  intro x hx
  have hz : oldBoundary ρ f x = 0 := by
    ext a : 1
    rw [← boundary_retained ρ f hf, hx]
    rfl
  exact fs_cycle_mem_span_groupMap_cycles (groupHom ρ f) (by
    apply Function.LeftInverse.injective (g := (QuotientGroup.lift _ ((QuotientGroup.mk' _).comp (wordRetraction f)) (by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨j, rfl⟩
    change QuotientGroup.mk (wordRetraction f (FreeGroup.map f (ρ j))) = 1
    rw [wordRetraction_map f hf]
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure ⟨j, rfl⟩))))
    intro g
    induction g using QuotientGroup.induction_on with
    | H w =>
        change QuotientGroup.mk (wordRetraction f (FreeGroup.map f w)) = QuotientGroup.mk w
        rw [wordRetraction_map f hf])
    (fun j => coverFoxGradient (relSub ρ) (ρ j)) x hz

end FreePadding
end FiniteChains

namespace FiniteChains.PresInclusionFS
open BlockFamily

variable {A B J K : Type} (ρ : J → FreeGroup A) (τ : K → FreeGroup B)
  (g : A → B) (f : J → K) (hg : Function.Injective g) (hf : Function.Injective f)
  (hrel : ∀ j, τ (f j) = FreeGroup.map g (ρ j))

def groupHom : PresGroup ρ →* PresGroup τ :=
  QuotientGroup.map _ _ (FreeGroup.map g) (by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨j, rfl⟩
    apply Subgroup.mem_comap.mpr
    rw [← hrel j]
    exact Subgroup.subset_normalClosure ⟨f j, rfl⟩)

def coefficients := MonoidAlgebra.mapDomainRingHom ℤ (groupHom ρ τ g f hrel)

theorem coefficients_proj (x : FreeGroupRing A) :
    coefficients ρ τ g f hrel (proj (relSub ρ) x) =
      proj (relSub τ) (freeRingMap g x) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => rfl
  | add x y hx hy => simp_all
  | single w a =>
      apply MonoidAlgebra.coeff_injective
      change Finsupp.mapDomain (groupHom ρ τ g f hrel)
        (Finsupp.mapDomain (QuotientGroup.mk' (relSub ρ)) (Finsupp.single w a)) =
        Finsupp.mapDomain (QuotientGroup.mk' (relSub τ))
          (Finsupp.mapDomain (FreeGroup.map g) (Finsupp.single w a))
      simp
      rfl

variable [DecidableEq A] [DecidableEq B]


def cells (x : J →₀ MonoidAlgebra ℤ (PresGroup ρ)) :
    K →₀ MonoidAlgebra ℤ (PresGroup τ) :=
  Finsupp.mapDomain f (x.mapRange (coefficients ρ τ g f hrel) (map_zero _))

omit [DecidableEq A] [DecidableEq B] in
@[simp] theorem cells_single (j : J) (a : MonoidAlgebra ℤ (PresGroup ρ)) :
    cells ρ τ g f hrel (Finsupp.single j a) =
      Finsupp.single (f j) (coefficients ρ τ g f hrel a) := by
  simp [cells]

include hg in
theorem boundary (x : J →₀ MonoidAlgebra ℤ (PresGroup ρ)) :
    coverSecondBoundary (relSub τ) τ (cells ρ τ g f hrel x) =
      Finsupp.mapDomain g ((coverSecondBoundary (relSub ρ) ρ x).mapRange
        (coefficients ρ τ g f hrel) (map_zero _)) := by
  induction x using Finsupp.induction_linear with
  | zero => simp [cells]
  | add x y hx hy =>
      simp only [cells, Finsupp.mapRange_add', Finsupp.mapDomain_add, map_add] at *
      rw [hx, hy]
  | single j a =>
      rw [cells_single, coverSecondBoundary_single, coverSecondBoundary_single,
        (show coverFoxGradient (relSub τ) (τ (f j)) =
      Finsupp.mapDomain g ((coverFoxGradient (relSub ρ) (ρ j)).mapRange
        (coefficients ρ τ g f hrel) (map_zero _)) by
          ext b : 1
          rw [hrel j]
          by_cases hb : b ∈ Set.range g
          · obtain ⟨a, rfl⟩ := hb
            rw [Finsupp.mapDomain_apply_of_injective hg]
            change proj _ (fox (g a) (FreeGroup.map g (ρ j))) =
              coefficients ρ τ g f hrel (proj _ (fox a (ρ j)))
            rw [fox_map g hg, coefficients_proj]
          · rw [Finsupp.mapDomain_notin_range _ b hb]
            change proj _ (fox b (FreeGroup.map g (ρ j))) = 0
            rw [fox_map_of_not_mem_range g (fun a h => hb ⟨a, h.symm⟩), map_zero])]
      have hmap : (a • coverFoxGradient (relSub ρ) (ρ j)).mapRange
          (coefficients ρ τ g f hrel) (map_zero _) =
        coefficients ρ τ g f hrel a •
          (coverFoxGradient (relSub ρ) (ρ j)).mapRange
            (coefficients ρ τ g f hrel) (map_zero _) := by
        ext i : 1
        simp only [Finsupp.mapRange_apply, Finsupp.smul_apply, smul_eq_mul]
        exact map_mul _ _ _
      rw [hmap, Finsupp.mapDomain_smul]

def mor : PresMorFS ρ τ where
  hom := groupHom ρ τ g f hrel
  cells := cells ρ τ g f hrel
  cells_add := by intro x y; simp [cells, Finsupp.mapRange_add', Finsupp.mapDomain_add]
  cells_smul := by
    intro a x
    have h : (a • x).mapRange (coefficients ρ τ g f hrel) (map_zero _) =
        coefficients ρ τ g f hrel a • x.mapRange (coefficients ρ τ g f hrel) (map_zero _) := by
      ext j : 1
      simp only [Finsupp.mapRange_apply, Finsupp.smul_apply, smul_eq_mul]
      exact map_mul _ _ _
    change Finsupp.mapDomain f _ = _
    rw [h, Finsupp.mapDomain_smul]
    rfl
  cells_cycle := by
    intro x hx
    change coverSecondBoundary _ _ _ = 0
    rw [boundary ρ τ g f hg hrel, hx]
    simp
  cells_aug := by
    intro x hx k
    by_cases hk : k ∈ Set.range f
    · obtain ⟨j, rfl⟩ := hk
      change augPres τ (Finsupp.mapDomain f _ (f j)) = 0
      rw [Finsupp.mapDomain_apply_of_injective hf]
      change augPres τ (MonoidAlgebra.mapDomainRingHom ℤ (groupHom ρ τ g f hrel) (x j)) = 0
      exact (augQ_mapDomain (groupHom ρ τ g f hrel) (x j)).trans (hx j)
    · change augPres τ (Finsupp.mapDomain f _ k) = 0
      rw [Finsupp.mapDomain_notin_range _ k hk, map_zero]

end FiniteChains.PresInclusionFS
end

section
open scoped Classical
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.BlockFamily

variable {A C S : Type} {Z M : S → Type}
  (ρ : C ⊕ S → FreeGroup A) (b : ∀ s, M s → FreeGroup (A ⊕ Z s))
  (hfill : FilledF ρ b)
  (c : ∀ s, M s →₀ MonoidAlgebra ℤ (PresGroup (substPresF ρ b)))

theorem fsCellsF_single_extra (s : S) (a : MonoidAlgebra ℤ (PresGroup ρ)) :
    fsCellsF ρ b hfill c (Finsupp.single (Sum.inr s) a) =
      coeffF ρ b hfill a • fsSurfaceChain c s := by
  rw [fsCellsF, Finsupp.mapRange_single,
    ← Finsupp.smul_single_one (Sum.inr s) (coeffF ρ b hfill a),
    map_smul, fsCellsBase_single_inr]

end FiniteChains.BlockFamily

namespace FiniteChains.RelativeNormalForm
open Davis Davis.Genus BlockFamily

variable {A C Z S : Type} (core : C → FreeGroup A)
  (hcore : Function.Surjective (expMatrix core))
  (extra : S → FreeGroup (A ⊕ Z))
  {p t : S → Prop} (hpt : ∀ s, p s → t s)

def normalizedInclusion : PresMorFS (restrictedPresentation core hcore extra p)
    (restrictedPresentation core hcore extra t) :=
  PresInclusionFS.mor _ _ id (oldCellIncl hpt) Function.injective_id
    (oldCellIncl_injective hpt) (by
      intro j
      simpa only [FreeGroup.map.id] using restrictedPresentation_incl core hcore extra hpt j)

def blockInclusion : PresMorFS (restrictedBlockPresentation core hcore extra p)
    (restrictedBlockPresentation core hcore extra t) :=
  PresInclusionFS.mor _ _ (blockGenIncl core hcore extra hpt)
    (blockCellIncl core hcore extra hpt)
    (blockGenIncl_injective core hcore extra hpt)
    (blockCellIncl_injective core hcore extra hpt)
    (restrictedBlockPresentation_incl core hcore extra hpt)

theorem blockInclusion_structural_group_square :
    (blockInclusion core hcore extra hpt).hom.comp
      (restrictedStructuralMap core hcore extra p).hom =
    (restrictedStructuralMap core hcore extra t).hom.comp
      (normalizedInclusion core hcore extra hpt).hom := by
  ext a
  change QuotientGroup.mk (FreeGroup.map (blockGenIncl core hcore extra hpt)
      (FreeGroup.map Sum.inl (FreeGroup.of a))) =
    QuotientGroup.mk (FreeGroup.map Sum.inl (FreeGroup.map id (FreeGroup.of a)))
  simp [blockGenIncl]


/-- The coefficient choices of a block are carried to the identical choices
in every later stage; no new filling is selected. -/

theorem blockInclusion_surface_chain (s : {s // p s})
    (x : NamedSpineRel (restrictedGenus core hcore extra p s) →₀
      MonoidAlgebra ℤ (PresGroup (restrictedBlockPresentation core hcore extra p))) :
    (blockInclusion core hcore extra hpt).cells
      (Finsupp.mapDomain (fun m => Sum.inr ⟨s, m⟩) x) =
    Finsupp.mapDomain (fun m => Sum.inr ⟨labelIncl hpt s, m⟩)
      (x.mapRange (MonoidAlgebra.mapDomainRingHom ℤ
        (blockInclusion core hcore extra hpt).hom) (map_zero _)) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
      rw [Finsupp.mapDomain_add, PresMorFS.cells_add, hx, hy,
        Finsupp.mapRange_add', Finsupp.mapDomain_add]
  | single m a =>
      simp
      change Finsupp.mapDomain (blockCellIncl core hcore extra hpt)
        ((Finsupp.single (Sum.inr ⟨s, m⟩) a).mapRange _ _) = _
      rw [Finsupp.mapRange_single, Finsupp.mapDomain_single]
      rfl

/-- The actual two-chain square commutes. This supplies the square required
by zero-map propagation in the fixed-core induction. -/
theorem blockInclusion_structural_chain_square
    (x : (C ⊕ {s // p s}) →₀ MonoidAlgebra ℤ
      (PresGroup (restrictedPresentation core hcore extra p))) :
    (blockInclusion core hcore extra hpt).cells
      ((restrictedStructuralMap core hcore extra p).cells x) =
    (restrictedStructuralMap core hcore extra t).cells
      ((normalizedInclusion core hcore extra hpt).cells x) := by
  have hcoeff a :
      MonoidAlgebra.mapDomainRingHom ℤ (blockInclusion core hcore extra hpt).hom
        (MonoidAlgebra.mapDomainRingHom ℤ (restrictedStructuralMap core hcore extra p).hom a) =
      MonoidAlgebra.mapDomainRingHom ℤ (restrictedStructuralMap core hcore extra t).hom
        (MonoidAlgebra.mapDomainRingHom ℤ (normalizedInclusion core hcore extra hpt).hom a) := by
    rw [BlockMor.mapDomainRingHom_comp', BlockMor.mapDomainRingHom_comp',
      blockInclusion_structural_group_square]
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
      rw [PresMorFS.cells_add, PresMorFS.cells_add, PresMorFS.cells_add,
        PresMorFS.cells_add, hx, hy]
  | single k a =>
      have hi := PresInclusionFS.cells_single
        (restrictedPresentation core hcore extra p) (restrictedPresentation core hcore extra t)
        id (oldCellIncl hpt)
        (fun j => by simpa using
          restrictedPresentation_incl core hcore extra hpt j) k a
      change (normalizedInclusion core hcore extra hpt).cells (Finsupp.single k a) = _ at hi
      rw [hi]
      cases k with
      | inl c =>
          dsimp only [oldCellIncl, Sum.map_inl, id]
          rw [show (restrictedStructuralMap core hcore extra p).cells
              (Finsupp.single (Sum.inl c) a) = _ from
            finiteSpineFamilyStructuralMap_core_cell _ _ _
              (restrictedPresentation_surface core hcore extra p) c a]
          rw [show (blockInclusion core hcore extra hpt).cells (Finsupp.single (Sum.inl c) _) =
              Finsupp.single (Sum.inl c) _ from
            PresInclusionFS.cells_single _ _ _ _ _ _ _]
          rw [show (restrictedStructuralMap core hcore extra t).cells
              (Finsupp.single (Sum.inl c) _) = _ from
            finiteSpineFamilyStructuralMap_core_cell _ _ _
              (restrictedPresentation_surface core hcore extra t) c _]
          exact congrArg (Finsupp.single (Sum.inl c)) (hcoeff a)
      | inr s =>
          dsimp only [oldCellIncl, Sum.map_inr]
          change (blockInclusion core hcore extra hpt).cells (fsCellsF _ _ _ _ _) =
            fsCellsF _ _ _ _ _
          rw [fsCellsF_single_extra, fsCellsF_single_extra, PresMorFS.cells_smul]
          change _ • (blockInclusion core hcore extra hpt).cells
            (Finsupp.mapDomain (fun m => Sum.inr ⟨s, m⟩) _) = _
          rw [blockInclusion_surface_chain, (show (finiteSpineFamilyFilling (restrictedPresentation core hcore extra p)
      (restrictedGenus core hcore extra p) (restrictedLoops core hcore extra p) s).mapRange
        (MonoidAlgebra.mapDomainRingHom ℤ (blockInclusion core hcore extra hpt).hom) (map_zero _) =
    finiteSpineFamilyFilling (restrictedPresentation core hcore extra t)
      (restrictedGenus core hcore extra t) (restrictedLoops core hcore extra t)
      (labelIncl hpt s) by
            ext m : 1
            erw [BlockMor.mapDomainRingHom_comp']
            erw [(show (blockInclusion core hcore extra hpt).hom.comp
      (finiteSpineFamilyMarkedHom (restrictedPresentation core hcore extra p)
        (restrictedGenus core hcore extra p) (restrictedLoops core hcore extra p) s) =
    finiteSpineFamilyMarkedHom (restrictedPresentation core hcore extra t)
      (restrictedGenus core hcore extra t) (restrictedLoops core hcore extra t)
      (labelIncl hpt s) by
              apply MonoidHom.ext
              intro g
              induction g using QuotientGroup.induction_on with
              | H w =>
                  exact congrArg QuotientGroup.mk (congrArg
                    (fun f => f (blockSubst
                      (Zt := fun s => SpinePresentationGen (restrictedGenus core hcore extra p s))
                      (restrictedLoops core hcore extra p) s w))
                    (blockGenIncl_genEmb core hcore extra hpt s)))]
            rfl)]
          exact congrArg (fun a => a • _) (hcoeff a)

/-- Actual rule-3 replacement preserves every old zero inclusion. -/
theorem blockInclusion_preserves_zero
    (hzero : ∀ x, FSIsFoxCycle (restrictedPresentation core hcore extra p) x →
      (normalizedInclusion core hcore extra hpt).cells x = 0)
    {x} (hx : FSIsFoxCycle (restrictedBlockPresentation core hcore extra p) x) :
    (blockInclusion core hcore extra hpt).cells x = 0 :=
  fsCells_eq_zero_of_generates (restrictedStructuralMap core hcore extra p)
    (restrictedStructuralMap core hcore extra t)
    (normalizedInclusion core hcore extra hpt) (blockInclusion core hcore extra hpt)
    (blockInclusion_structural_chain_square core hcore extra hpt) hzero
    (restrictedStructuralMap_generates core hcore extra p) hx

end FiniteChains.RelativeNormalForm
end

section
open scoped Classical
namespace FiniteChains.RelativeNormalForm

variable {A C Z S : Type} (core : C → FreeGroup A)
  (extra : S → FreeGroup (A ⊕ Z))
  {p t : S → Prop} (hpt : ∀ s, p s → t s)

def restrictedExtra (p : S → Prop) (s : {s // p s}) := extra s.val

def rawInclusion : PresMorFS (rawPresentation core (restrictedExtra extra p))
    (rawPresentation core (restrictedExtra extra t)) :=
  PresInclusionFS.mor _ _ id (oldCellIncl hpt) Function.injective_id
    (oldCellIncl_injective hpt) (by intro j; cases j <;> simp [rawPresentation, oldCellIncl,
      restrictedExtra, labelIncl])

def pairInclusion : PresMorFS (beforeCorrection core (restrictedExtra extra p))
    (beforeCorrection core (restrictedExtra extra t)) :=
  PresInclusionFS.mor _ _ id (oldCellIncl hpt) Function.injective_id
    (oldCellIncl_injective hpt) (by intro j; cases j <;> simp [beforeCorrection, oldCellIncl,
      restrictedExtra, labelIncl])

theorem ruleOne_group_square :
    (pairInclusion core extra hpt).hom.comp
      (relativeRuleOneMap core (restrictedExtra extra p)).hom =
    (relativeRuleOneMap core (restrictedExtra extra t)).hom.comp
      (rawInclusion core extra hpt).hom := by
  apply MonoidHom.ext
  intro g
  induction g using QuotientGroup.induction_on with
  | H w =>
      simp
      change QuotientGroup.mk (FreeGroup.map id (pairSubstitution w)) =
        (relativeRuleOneMap core (restrictedExtra extra t)).hom
          (QuotientGroup.mk (FreeGroup.map id w))
      simp

theorem ruleOne_chain_square
    (x : (C ⊕ {s // p s}) →₀ MonoidAlgebra ℤ
      (PresGroup (rawPresentation core (restrictedExtra extra p)))) :
    (pairInclusion core extra hpt).cells
      ((relativeRuleOneMap core (restrictedExtra extra p)).cells x) =
    (relativeRuleOneMap core (restrictedExtra extra t)).cells
      ((rawInclusion core extra hpt).cells x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
      rw [PresMorFS.cells_add, PresMorFS.cells_add, PresMorFS.cells_add,
        PresMorFS.cells_add, hx, hy]
  | single j a =>
      rw [relativeRuleOneMap_cells, Finsupp.mapRange_single]
      change Finsupp.mapDomain (oldCellIncl hpt)
        ((Finsupp.single j _).mapRange _ _) = _
      rw [Finsupp.mapRange_single, Finsupp.mapDomain_single]
      rw [relativeRuleOneMap_cells]
      change _ = (Finsupp.mapDomain (oldCellIncl hpt)
        ((Finsupp.single j a).mapRange _ _)).mapRange _ _
      rw [Finsupp.mapRange_single, Finsupp.mapDomain_single, Finsupp.mapRange_single]
      congr 1
      change MonoidAlgebra.mapDomainRingHom ℤ (pairInclusion core extra hpt).hom
          (MonoidAlgebra.mapDomainRingHom ℤ
            (relativeRuleOneMap core (restrictedExtra extra p)).hom a) =
        MonoidAlgebra.mapDomainRingHom ℤ (relativeRuleOneMap core (restrictedExtra extra t)).hom
          (MonoidAlgebra.mapDomainRingHom ℤ (rawInclusion core extra hpt).hom a)
      rw [BlockMor.mapDomainRingHom_comp', BlockMor.mapDomainRingHom_comp',
        ruleOne_group_square]

theorem ruleOne_preserves_zero
    (hzero : ∀ x, FSIsFoxCycle (rawPresentation core (restrictedExtra extra p)) x →
      (rawInclusion core extra hpt).cells x = 0)
    {x} (hx : FSIsFoxCycle (beforeCorrection core (restrictedExtra extra p)) x) :
    (pairInclusion core extra hpt).cells x = 0 :=
  fsCells_eq_zero_of_generates
    (relativeRuleOneMap core (restrictedExtra extra p))
    (relativeRuleOneMap core (restrictedExtra extra t))
    (rawInclusion core extra hpt) (pairInclusion core extra hpt)
    (ruleOne_chain_square core extra hpt) hzero
    (relativeRuleOneMap_generates core (restrictedExtra extra p)) hx

end FiniteChains.RelativeNormalForm
end

section
open scoped Classical
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.RelativeNormalForm
open BlockFamily

variable {A C Z S : Type} (core : C → FreeGroup A)
  (hcore : Function.Surjective (expMatrix core))
  (extra : S → FreeGroup (A ⊕ Z))
  {p t : S → Prop} (hpt : ∀ s, p s → t s)

theorem slide_group_square :
    (normalizedInclusion core hcore extra hpt).hom.comp
      (slideGroupHom core hcore (restrictedExtra extra p)) =
    (slideGroupHom core hcore (restrictedExtra extra t)).comp
      (pairInclusion core extra hpt).hom := by
  apply MonoidHom.ext
  intro g
  induction g using QuotientGroup.induction_on with
  | H w =>
      change (QuotientGroup.mk (FreeGroup.map id w) :
        PresGroup (restrictedPresentation core hcore extra t)) =
          QuotientGroup.mk (FreeGroup.map id w)
      rfl

theorem slide_core_group_square :
    (normalizedInclusion core hcore extra hpt).hom.comp
      (pairCoreToNormalized core hcore (restrictedExtra extra p)) =
    pairCoreToNormalized core hcore (restrictedExtra extra t) := by
  apply MonoidHom.ext
  intro g
  induction g using QuotientGroup.induction_on with
  | H w =>
      change QuotientGroup.mk (FreeGroup.map id w) = QuotientGroup.mk w
      simp


theorem normalizedInclusion_core_chain
    (x : C →₀ MonoidAlgebra ℤ (PresGroup (restrictedPresentation core hcore extra p))) :
    (normalizedInclusion core hcore extra hpt).cells (fsOldOneIncl x) =
      fsOldOneIncl (x.mapRange (MonoidAlgebra.mapDomainRingHom ℤ
        (normalizedInclusion core hcore extra hpt).hom) (map_zero _)) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
      rw [map_add, PresMorFS.cells_add, hx, hy, Finsupp.mapRange_add', map_add]
  | single c a =>
      rw [fsOldOneIncl_single, Finsupp.mapRange_single, fsOldOneIncl_single]
      change Finsupp.mapDomain (oldCellIncl hpt)
        ((Finsupp.single (Sum.inl c) a).mapRange _ _) = _
      rw [Finsupp.mapRange_single, Finsupp.mapDomain_single]
      rfl


theorem slide_forward_natural
    (x : (C ⊕ {s // p s}) →₀ MonoidAlgebra ℤ
      (PresGroup (restrictedPresentation core hcore extra p))) :
    (normalizedInclusion core hcore extra hpt).cells
      (coreSlideForward (slideColumns core hcore (restrictedExtra extra p)) x) =
    coreSlideForward (slideColumns core hcore (restrictedExtra extra t))
      ((normalizedInclusion core hcore extra hpt).cells x) := by
  change (normalizedInclusion core hcore extra hpt).cells (x - _) = _ - _
  rw [PresMorFS.cells_sub, (show (normalizedInclusion core hcore extra hpt).cells
      (coreSlideCorrection (slideColumns core hcore (restrictedExtra extra p)) x) =
    coreSlideCorrection (slideColumns core hcore (restrictedExtra extra t))
      ((normalizedInclusion core hcore extra hpt).cells x) by
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy =>
        rw [map_add, PresMorFS.cells_add, PresMorFS.cells_add, map_add, hx, hy]
    | single k a =>
        have hi : (normalizedInclusion core hcore extra hpt).cells (Finsupp.single k a) =
            Finsupp.single (oldCellIncl hpt k)
              (MonoidAlgebra.mapDomainRingHom ℤ (normalizedInclusion core hcore extra hpt).hom a) := by
          change Finsupp.mapDomain _ ((Finsupp.single k a).mapRange _ _) = _
          rw [Finsupp.mapRange_single, Finsupp.mapDomain_single]
          rfl
        rw [hi]
        cases k with
        | inl c => simp [oldCellIncl]
        | inr s =>
            rw [coreSlideCorrection_single_inr, PresMorFS.cells_smul]
            change _ = coreSlideCorrection _ (Finsupp.single (Sum.inr (labelIncl hpt s)) _)
            rw [coreSlideCorrection_single_inr]
            exact congrArg (fun z => MonoidAlgebra.mapDomainRingHom ℤ
                (normalizedInclusion core hcore extra hpt).hom a • z)
              ((normalizedInclusion_core_chain core hcore extra hpt
                  (slideColumns core hcore (restrictedExtra extra p) s)).trans
                (congrArg (fsOldOneIncl (Z := {s // t s}))
                  (by
                    ext c : 1
                    change MonoidAlgebra.mapDomainRingHom ℤ (normalizedInclusion core hcore extra hpt).hom
                      (MonoidAlgebra.mapDomainRingHom ℤ (pairCoreToNormalized core hcore (restrictedExtra extra p))
                        (pairCorrectionFilling core hcore (extra s.val) c)) = _
                    erw [BlockMor.mapDomainRingHom_comp']
                    erw [slide_core_group_square]
                    rfl))))]
  rfl


theorem slide_chain_square
    (x : (C ⊕ {s // p s}) →₀ MonoidAlgebra ℤ
      (PresGroup (beforeCorrection core (restrictedExtra extra p)))) :
    (normalizedInclusion core hcore extra hpt).cells
      ((normalizationSlideMap core hcore (restrictedExtra extra p)).cells x) =
    (normalizationSlideMap core hcore (restrictedExtra extra t)).cells
      ((pairInclusion core extra hpt).cells x) := by
  change (normalizedInclusion core hcore extra hpt).cells (coreSlideForward _ _) =
    coreSlideForward _ _
  exact (slide_forward_natural core hcore extra hpt
    (x.mapRange (slideCoefficients core hcore (restrictedExtra extra p)) (map_zero _))).trans
      (congrArg (coreSlideForward (slideColumns core hcore (restrictedExtra extra t)))
        (by
          induction x using Finsupp.induction_linear with
          | zero => simp
          | add x y hx hy =>
              have hp := Finsupp.mapRange_add'
                (f := slideCoefficients core hcore (restrictedExtra extra p)) x y
              have ht := Finsupp.mapRange_add'
                (f := slideCoefficients core hcore (restrictedExtra extra t))
                ((pairInclusion core extra hpt).cells x) ((pairInclusion core extra hpt).cells y)
              rw [hp, PresMorFS.cells_add, PresMorFS.cells_add, ht, hx, hy]
          | single j a =>
              rw [Finsupp.mapRange_single]
              change Finsupp.mapDomain (oldCellIncl hpt) ((Finsupp.single j _).mapRange _ _) =
                (Finsupp.mapDomain (oldCellIncl hpt) ((Finsupp.single j a).mapRange _ _)).mapRange _ _
              rw [Finsupp.mapRange_single, Finsupp.mapDomain_single,
                Finsupp.mapRange_single, Finsupp.mapDomain_single, Finsupp.mapRange_single]
              congr 1
              change MonoidAlgebra.mapDomainRingHom ℤ (normalizedInclusion core hcore extra hpt).hom
                  (MonoidAlgebra.mapDomainRingHom ℤ
                    (slideGroupHom core hcore (restrictedExtra extra p)) a) =
                MonoidAlgebra.mapDomainRingHom ℤ (slideGroupHom core hcore (restrictedExtra extra t))
                  (MonoidAlgebra.mapDomainRingHom ℤ (pairInclusion core extra hpt).hom a)
              erw [BlockMor.mapDomainRingHom_comp', BlockMor.mapDomainRingHom_comp', slide_group_square]
              rfl))

theorem slide_preserves_zero
    (hzero : ∀ x, FSIsFoxCycle (beforeCorrection core (restrictedExtra extra p)) x →
      (pairInclusion core extra hpt).cells x = 0)
    {x} (hx : FSIsFoxCycle (restrictedPresentation core hcore extra p) x) :
    (normalizedInclusion core hcore extra hpt).cells x = 0 :=
  fsCells_eq_zero_of_generates
    (normalizationSlideMap core hcore (restrictedExtra extra p))
    (normalizationSlideMap core hcore (restrictedExtra extra t))
    (pairInclusion core extra hpt) (normalizedInclusion core hcore extra hpt)
    (slide_chain_square core hcore extra hpt) hzero
    (normalizationSlideMap_generates core hcore (restrictedExtra extra p)) hx

/-- The full actual replacement preserves every zero inclusion between
positive stages. All three required chain squares have been proved. -/
theorem relativeReplacement_preserves_zero
    (hzero : ∀ x, FSIsFoxCycle (rawPresentation core (restrictedExtra extra p)) x →
      (rawInclusion core extra hpt).cells x = 0)
    {x} (hx : FSIsFoxCycle (restrictedBlockPresentation core hcore extra p) x) :
    (blockInclusion core hcore extra hpt).cells x = 0 := by grind [blockInclusion_preserves_zero, slide_preserves_zero, ruleOne_preserves_zero]

end FiniteChains.RelativeNormalForm
end

section
open scoped Classical
namespace FiniteChains.PresInclusionFS

section Square
variable {A B D E J K L M : Type}
  [DecidableEq A] [DecidableEq B] [DecidableEq D] [DecidableEq E]
  (ρ : J → FreeGroup A) (τ : K → FreeGroup B)
  (σ : L → FreeGroup D) (υ : M → FreeGroup E)
  (g : A → B) (f : J → K) (hg : Function.Injective g) (hf : Function.Injective f)
  (hρτ : ∀ j, τ (f j) = FreeGroup.map g (ρ j))
  (a : A → D) (c : J → L) (ha : Function.Injective a) (hc : Function.Injective c)
  (hρσ : ∀ j, σ (c j) = FreeGroup.map a (ρ j))
  (b : B → E) (d : K → M) (hb : Function.Injective b) (hd : Function.Injective d)
  (hτυ : ∀ k, υ (d k) = FreeGroup.map b (τ k))
  (k : D → E) (l : L → M) (hk : Function.Injective k) (hl : Function.Injective l)
  (hσυ : ∀ z, υ (l z) = FreeGroup.map k (σ z))
  (hgen : ∀ x, k (a x) = b (g x)) (hcell : ∀ j, l (c j) = d (f j))


include hgen hcell in
theorem square_cells (x : J →₀ MonoidAlgebra ℤ (PresGroup ρ)) :
    (mor σ υ k l hk hl hσυ).cells ((mor ρ σ a c ha hc hρσ).cells x) =
    (mor τ υ b d hb hd hτυ).cells ((mor ρ τ g f hg hf hρτ).cells x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
      rw [PresMorFS.cells_add, PresMorFS.cells_add, PresMorFS.cells_add,
        PresMorFS.cells_add, hx, hy]
  | single j r =>
      change cells σ υ k l hσυ (cells ρ σ a c hρσ (Finsupp.single j r)) =
        cells τ υ b d hτυ (cells ρ τ g f hρτ (Finsupp.single j r))
      rw [cells_single, cells_single, cells_single, cells_single, hcell j]
      congr 1
      change MonoidAlgebra.mapDomainRingHom ℤ (groupHom σ υ k l hσυ)
        (MonoidAlgebra.mapDomainRingHom ℤ (groupHom ρ σ a c hρσ) r) =
        MonoidAlgebra.mapDomainRingHom ℤ (groupHom τ υ b d hτυ)
          (MonoidAlgebra.mapDomainRingHom ℤ (groupHom ρ τ g f hρτ) r)
      rw [BlockMor.mapDomainRingHom_comp', BlockMor.mapDomainRingHom_comp',
        (show (groupHom σ υ k l hσυ).comp (groupHom ρ σ a c hρσ) =
    (groupHom τ υ b d hτυ).comp (groupHom ρ τ g f hρτ) by
          apply MonoidHom.ext
          intro z
          induction z using QuotientGroup.induction_on with
          | H w =>
              have hm : (FreeGroup.map k).comp (FreeGroup.map a) =
                  (FreeGroup.map b).comp (FreeGroup.map g) := by
                apply FreeGroup.ext_hom
                intro x
                simp
                exact congrArg FreeGroup.of (hgen x)
              exact congrArg (fun h : FreeGroup A →* FreeGroup E =>
                (QuotientGroup.mk (h w) : PresGroup υ)) hm)]
end Square

section Relabel
variable {A B J K : Type} [DecidableEq A] [DecidableEq B]
  (ρ : J → FreeGroup A) (τ : K → FreeGroup B)
  (g : A ≃ B) (f : J ≃ K)
  (hrel : ∀ j, τ (f j) = FreeGroup.map g (ρ j))

include hrel in
omit [DecidableEq A] [DecidableEq B] in
theorem inverse_rel (k : K) :
    ρ (f.symm k) = FreeGroup.map g.symm (τ k) := by
  have hk : τ k = FreeGroup.map g (ρ (f.symm k)) := by
    simpa using hrel (f.symm k)
  rw [hk]
  have hm : (FreeGroup.map g.symm).comp (FreeGroup.map g) = MonoidHom.id _ := by
    apply FreeGroup.ext_hom
    intro x
    simp
  simpa using (congrArg (fun h : FreeGroup A →* FreeGroup A => h (ρ (f.symm k))) hm).symm

theorem relabel_cells_inverse (x : K →₀ MonoidAlgebra ℤ (PresGroup τ)) :
    (mor ρ τ g f g.injective f.injective hrel).cells
      ((mor τ ρ g.symm f.symm g.symm.injective f.symm.injective
        (inverse_rel ρ τ g f hrel)).cells x) = x := by
  have hm : (groupHom ρ τ g f hrel).comp
      (groupHom τ ρ g.symm f.symm (inverse_rel ρ τ g f hrel)) = MonoidHom.id _ := by
    apply MonoidHom.ext
    intro z
    induction z using QuotientGroup.induction_on with
    | H w =>
        have hw : (FreeGroup.map g).comp (FreeGroup.map g.symm) = MonoidHom.id _ := by
          apply FreeGroup.ext_hom
          intro b
          simp
        exact congrArg (fun h : FreeGroup B →* FreeGroup B =>
          (QuotientGroup.mk (h w) : PresGroup τ)) hw
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [PresMorFS.cells_add, PresMorFS.cells_add, hx, hy]
  | single j r =>
      change cells ρ τ g f hrel (cells τ ρ g.symm f.symm
        (inverse_rel ρ τ g f hrel) (Finsupp.single j r)) = _
      rw [cells_single, cells_single, Equiv.apply_symm_apply]
      congr 1
      change MonoidAlgebra.mapDomainRingHom ℤ (groupHom ρ τ g f hrel)
        (MonoidAlgebra.mapDomainRingHom ℤ
          (groupHom τ ρ g.symm f.symm (inverse_rel ρ τ g f hrel)) r) = r
      rw [BlockMor.mapDomainRingHom_comp', hm]
      simp

theorem relabel_generates : FSGenerates (mor ρ τ g f g.injective f.injective hrel) := by
  intro x hx
  let inv := mor τ ρ g.symm f.symm g.symm.injective f.symm.injective
    (inverse_rel ρ τ g f hrel)
  apply Submodule.subset_span
  exact ⟨inv.cells x, inv.cells_cycle x hx, (relabel_cells_inverse ρ τ g f hrel x).symm⟩
end Relabel

section PaddingRelabel
variable {A B J K : Type} [DecidableEq A] [DecidableEq B]
  (ρ : J → FreeGroup A) (τ : K → FreeGroup B)
  (g : A → B) (hg : Function.Injective g) (f : J ≃ K)
  (hrel : ∀ j, τ (f j) = FreeGroup.map g (ρ j))

theorem paddingRelabel_generates : FSGenerates (mor ρ τ g f hg f.injective hrel) := by
  let σ := FreePadding.rel ρ g
  have hσ : ∀ j, τ (f j) = FreeGroup.map (Equiv.refl B) (σ j) := by
    intro j
    simpa [σ, FreePadding.rel] using hrel j
  let pad := FreePadding.structuralMap ρ g hg
  let relabel := mor σ τ (Equiv.refl B) f (Equiv.refl B).injective f.injective hσ
  have hc : ∀ x, (mor ρ τ g f hg f.injective hrel).cells x = relabel.cells (pad.cells x) := by
    intro x
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy => rw [PresMorFS.cells_add, PresMorFS.cells_add,
        PresMorFS.cells_add, hx, hy]
    | single j r =>
        change cells ρ τ g f hrel (Finsupp.single j r) =
          cells σ τ (Equiv.refl B) f hσ
            ((Finsupp.single j r).mapRange (FreePadding.coefficients ρ g) (map_zero _))
        rw [Finsupp.mapRange_single, cells_single, cells_single]
        congr 1
        have hh : groupHom ρ τ g f hrel =
            (groupHom σ τ (Equiv.refl B) f hσ).comp (FreePadding.groupHom ρ g) := by
          apply MonoidHom.ext
          intro z
          induction z using QuotientGroup.induction_on with
          | H w => change QuotientGroup.mk (FreeGroup.map g w) =
              QuotientGroup.mk (FreeGroup.map (Equiv.refl B) (FreeGroup.map g w)); simp
        change MonoidAlgebra.mapDomainRingHom ℤ (groupHom ρ τ g f hrel) r =
          MonoidAlgebra.mapDomainRingHom ℤ (groupHom σ τ (Equiv.refl B) f hσ)
            (MonoidAlgebra.mapDomainRingHom ℤ (FreePadding.groupHom ρ g) r)
        rw [BlockMor.mapDomainRingHom_comp', ← hh]
  have hgen := (relabel_generates σ τ (Equiv.refl B) f hσ).comp
    (FreePadding.structuralMap_generates ρ g hg)
  intro x hx
  have hs := hgen x hx
  apply Submodule.span_mono _ hs
  rintro z ⟨y, hy, rfl⟩
  exact ⟨y, hy, (hc y).symm⟩
end PaddingRelabel

end FiniteChains.PresInclusionFS

namespace FiniteChains.RelativeNormalForm
open Davis Davis.Genus BlockFamily

variable {A C Z S : Type} (core : C → FreeGroup A)
  (hcore : Function.Surjective (expMatrix core))
  (extra : S → FreeGroup (A ⊕ Z))

def NextExtraGen := (Z × Bool) ⊕
  (Σ s, SpinePresentationGen (normalizedGenus core hcore extra s))

instance nextExtraGenDecidableEq : DecidableEq (NextExtraGen core hcore extra) :=
  Classical.decEq _

instance nextExtraGenFinite [Finite Z] [Finite S] : Finite (NextExtraGen core hcore extra) := by
  unfold NextExtraGen
  infer_instance

abbrev NextExtraCell :=
  (Σ s, NamedSpineRel (normalizedGenus core hcore extra s)) ⊕ (Z × Bool)

def flattenBlockGen :
    (PairGen A Z ⊕ (Σ s, SpinePresentationGen (normalizedGenus core hcore extra s))) ≃
      (A ⊕ NextExtraGen core hcore extra) := Equiv.sumAssoc _ _ _

def nextExtra : NextExtraCell core hcore extra → FreeGroup (A ⊕ NextExtraGen core hcore extra)
  | Sum.inl m => FreeGroup.map (flattenBlockGen core hcore extra)
      (blockPresentation core hcore extra (Sum.inr m))
  | Sum.inr k => FreeGroup.of (Sum.inr (Sum.inl k))

def nextPredicate (p : S → Prop) : NextExtraCell core hcore extra → Prop
  | Sum.inl m => p m.1
  | Sum.inr _ => False

theorem nextPredicate_mono {p t : S → Prop} (h : ∀ s, p s → t s) :
    ∀ s, nextPredicate core hcore extra p s → nextPredicate core hcore extra t s := by simp_all [nextPredicate]

def stageNextGen (p : S → Prop) :
    (PairGen A Z ⊕ (Σ s : {s // p s}, SpinePresentationGen
      (restrictedGenus core hcore extra p s))) → A ⊕ NextExtraGen core hcore extra
  | Sum.inl (Sum.inl a) => Sum.inl a
  | Sum.inl (Sum.inr z) => Sum.inr (Sum.inl z)
  | Sum.inr s => Sum.inr (Sum.inr ⟨s.1.val, s.2⟩)

theorem stageNextGen_injective (p : S → Prop) :
    Function.Injective (stageNextGen core hcore extra p) := by
  rintro (a | ⟨s, x⟩) (b | ⟨t, y⟩) h
  · cases a <;> cases b <;> simp_all [stageNextGen, NextExtraGen]
  · cases a <;> simp [stageNextGen] at h <;> cases h
  · cases b <;> simp [stageNextGen] at h <;> cases h
  · have hh : (⟨s.val, x⟩ : Σ s, SpinePresentationGen
        (normalizedGenus core hcore extra s)) = ⟨t.val, y⟩ := Sum.inr.inj (Sum.inr.inj h)
    have hs : s = t := Subtype.ext (congrArg Sigma.fst hh)
    subst t
    have hx : x = y := eq_of_heq (Sigma.mk.inj hh).2
    subst y
    rfl

def stageNextCell (p : S → Prop) :
    (C ⊕ (Σ s : {s // p s}, NamedSpineRel (restrictedGenus core hcore extra p s))) ≃
      (C ⊕ {s // nextPredicate core hcore extra p s}) where
  toFun
    | Sum.inl c => Sum.inl c
    | Sum.inr ⟨s, m⟩ => Sum.inr ⟨Sum.inl ⟨s.val, m⟩, s.property⟩
  invFun
    | Sum.inl c => Sum.inl c
    | Sum.inr ⟨Sum.inl ⟨s, m⟩, hs⟩ => Sum.inr ⟨⟨s, hs⟩, m⟩
    | Sum.inr ⟨Sum.inr _, hs⟩ => hs.elim
  left_inv := by rintro (c | ⟨⟨s, hs⟩, m⟩) <;> rfl
  right_inv := by
    rintro (c | ⟨⟨s, m⟩ | k, hs⟩)
    · rfl
    · rfl
    · exact hs.elim

def nextStage (p : S → Prop) :=
  rawPresentation core (restrictedExtra (nextExtra core hcore extra)
    (nextPredicate core hcore extra p))

theorem stageNext_rel (p : S → Prop)
    (j : C ⊕ (Σ s : {s // p s}, NamedSpineRel (restrictedGenus core hcore extra p s))) :
    nextStage core hcore extra p (stageNextCell core hcore extra p j) =
      FreeGroup.map (stageNextGen core hcore extra p)
        (restrictedBlockPresentation core hcore extra p j) := by
  cases j with
  | inl c =>
      change FreeGroup.map Sum.inl (core c) =
        FreeGroup.map (stageNextGen core hcore extra p)
          (FreeGroup.map Sum.inl (FreeGroup.map Sum.inl (core c)))
      have hm : ((FreeGroup.map (stageNextGen core hcore extra p)).comp
          (FreeGroup.map Sum.inl)).comp (FreeGroup.map Sum.inl) = FreeGroup.map Sum.inl := by
        apply FreeGroup.ext_hom
        intro a
        rfl
      exact (DFunLike.congr_fun hm (core c)).symm
  | inr m =>
      have hm : (FreeGroup.map (stageNextGen core hcore extra p)).comp
          (FreeGroup.map (genEmb
            m.1)) =
        (FreeGroup.map (flattenBlockGen core hcore extra)).comp
          (FreeGroup.map (genEmb
            m.1.val)) := by
        apply FreeGroup.ext_hom
        intro x
        cases x with
        | inl x => cases x <;> rfl
        | inr x => rfl
      exact (DFunLike.congr_fun hm
        (familyFiniteSpineWordBlock (restrictedGenus core hcore extra p)
          (restrictedLoops core hcore extra p) m.1 m.2)).symm

def stageNextMap (p : S → Prop) :
    PresMorFS (restrictedBlockPresentation core hcore extra p) (nextStage core hcore extra p) :=
  PresInclusionFS.mor _ _ (stageNextGen core hcore extra p) (stageNextCell core hcore extra p)
    (stageNextGen_injective core hcore extra p) (stageNextCell core hcore extra p).injective
    (stageNext_rel core hcore extra p)

theorem stageNextMap_generates (p : S → Prop) : FSGenerates (stageNextMap core hcore extra p) :=
  PresInclusionFS.paddingRelabel_generates _ _ (stageNextGen core hcore extra p)
    (stageNextGen_injective core hcore extra p) (stageNextCell core hcore extra p)
    (stageNext_rel core hcore extra p)

theorem nextStage_cockcroft (p : S → Prop)
    (hp : FSIsCockcroft (rawPresentation core (restrictedExtra extra p))) :
    FSIsCockcroft (nextStage core hcore extra p) := by
  apply fsIsCockcroft_of_generates (stageNextMap core hcore extra p)
    (stageNextMap_generates core hcore extra p)
  apply fsIsCockcroft_of_generates (restrictedStructuralMap core hcore extra p)
    (restrictedStructuralMap_generates core hcore extra p)
  exact normalizedPresentation_cockcroft core hcore (restrictedExtra extra p) hp

variable {p t : S → Prop} (hpt : ∀ s, p s → t s)


theorem nextStage_preserves_zero
    (hzero : ∀ x, FSIsFoxCycle (rawPresentation core (restrictedExtra extra p)) x →
      (rawInclusion core extra hpt).cells x = 0)
    {x} (hx : FSIsFoxCycle (nextStage core hcore extra p) x) :
    (rawInclusion core (nextExtra core hcore extra)
      (nextPredicate_mono core hcore extra hpt)).cells x = 0 := by
  apply fsCells_eq_zero_of_generates (stageNextMap core hcore extra p)
    (stageNextMap core hcore extra t) (blockInclusion core hcore extra hpt)
    (rawInclusion core (nextExtra core hcore extra) (nextPredicate_mono core hcore extra hpt))
    (by
      apply PresInclusionFS.square_cells
      · rintro ((a | z) | s) <;> rfl
      · rintro (c | s) <;> rfl) ?_ (stageNextMap_generates core hcore extra p) hx
  intro y hy
  exact relativeReplacement_preserves_zero core hcore extra hpt hzero hy

theorem nextStage_strict (s : S) (hs : t s) (hsp : ¬ p s) :
    ∃ m, nextPredicate core hcore extra t m ∧ ¬ nextPredicate core hcore extra p m := by
  have hq := (surfaceChoice core hcore (extra s)).genus_ge_two
  let m : NamedSpineRel (normalizedGenus core hcore extra s) :=
    Sum.inr (⟨0, by change 0 < (surfaceChoice core hcore (extra s)).genus; omega⟩, false)
  exact ⟨Sum.inl ⟨s, m⟩, hs, hsp⟩

end FiniteChains.RelativeNormalForm
end

section
open scoped Classical
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.RelativeNormalForm
open Davis Davis.Genus BlockFamily

variable {A C Z S : Type} (core : C → FreeGroup A)
  (hcore : Function.Surjective (expMatrix core))
  (extra : S → FreeGroup (A ⊕ Z))

def fullNextCell :
    (C ⊕ (Σ s, NamedSpineRel (normalizedGenus core hcore extra s))) ≃
      (C ⊕ {s // nextPredicate core hcore extra (fun _ => True) s}) where
  toFun
    | Sum.inl c => Sum.inl c
    | Sum.inr m => Sum.inr ⟨Sum.inl m, trivial⟩
  invFun
    | Sum.inl c => Sum.inl c
    | Sum.inr ⟨Sum.inl m, _⟩ => Sum.inr m
    | Sum.inr ⟨Sum.inr _, h⟩ => h.elim
  left_inv := by rintro (c | m) <;> rfl
  right_inv := by rintro (c | ⟨m | k, h⟩); rfl; rfl; exact h.elim

theorem fullNext_rel (j : C ⊕ (Σ s, NamedSpineRel (normalizedGenus core hcore extra s))) :
    nextStage core hcore extra (fun _ => True) (fullNextCell core hcore extra j) =
      FreeGroup.map (flattenBlockGen core hcore extra) (blockPresentation core hcore extra j) := by
  cases j with
  | inr m => rfl
  | inl c =>
      have h : ((FreeGroup.map (flattenBlockGen core hcore extra)).comp
          (FreeGroup.map Sum.inl)).comp (FreeGroup.map Sum.inl) = FreeGroup.map Sum.inl := by
        apply FreeGroup.ext_hom
        intro a
        rfl
      exact (DFunLike.congr_fun h (core c)).symm

def fullNextMap : PresMorFS (blockPresentation core hcore extra)
    (nextStage core hcore extra (fun _ => True)) :=
  PresInclusionFS.mor _ _ (flattenBlockGen core hcore extra) (fullNextCell core hcore extra)
    (flattenBlockGen core hcore extra).injective (fullNextCell core hcore extra).injective
    (fullNext_rel core hcore extra)


def terminalNextCell :
    ((C ⊕ (Σ s, NamedSpineRel (normalizedGenus core hcore extra s))) ⊕ (Z × Bool)) ≃
      (C ⊕ NextExtraCell core hcore extra) := Equiv.sumAssoc _ _ _

theorem terminalNext_rel
    (j : (C ⊕ (Σ s, NamedSpineRel (normalizedGenus core hcore extra s))) ⊕ (Z × Bool)) :
    rawPresentation core (nextExtra core hcore extra) (terminalNextCell core hcore extra j) =
      FreeGroup.map (flattenBlockGen core hcore extra) (terminalPresentation core hcore extra j) := by
  rcases j with (c | m) | k
  · exact fullNext_rel core hcore extra (Sum.inl c)
  · rfl
  · rfl

def terminalNextMap : PresMorFS (terminalPresentation core hcore extra)
    (rawPresentation core (nextExtra core hcore extra)) :=
  PresInclusionFS.mor _ _ (flattenBlockGen core hcore extra) (terminalNextCell core hcore extra)
    (flattenBlockGen core hcore extra).injective (terminalNextCell core hcore extra).injective
    (terminalNext_rel core hcore extra)


/-- A selected stage includes into the full presentation by forgetting
only the proof attached to its extra-cell labels. -/
def stageIntoFull {B T : Type} (r : T → FreeGroup (A ⊕ B)) (p : T → Prop) :
    PresMorFS (rawPresentation core (restrictedExtra r p)) (rawPresentation core r) :=
  PresInclusionFS.mor _ _ id (Sum.map id Subtype.val) Function.injective_id
    (Function.Injective.sumMap Function.injective_id Subtype.val_injective) (by
      intro j
      cases j <;> simp [rawPresentation, restrictedExtra])

theorem nextTerminal_square
    (x : (C ⊕ (Σ s, NamedSpineRel (normalizedGenus core hcore extra s))) →₀
      MonoidAlgebra ℤ (PresGroup (blockPresentation core hcore extra))) :
    (stageIntoFull core (nextExtra core hcore extra)
      (nextPredicate core hcore extra (fun _ => True))).cells ((fullNextMap core hcore extra).cells x) =
    (terminalNextMap core hcore extra).cells ((relativeTerminalMap core hcore extra).cells x) := by
  have hgroup : (stageIntoFull core (nextExtra core hcore extra)
      (nextPredicate core hcore extra (fun _ => True))).hom.comp (fullNextMap core hcore extra).hom =
    (terminalNextMap core hcore extra).hom.comp (relativeTerminalMap core hcore extra).hom := by
    apply MonoidHom.ext
    intro g
    induction g using QuotientGroup.induction_on with
    | H w =>
        change QuotientGroup.mk (FreeGroup.map id (FreeGroup.map
          (flattenBlockGen core hcore extra) w)) =
          QuotientGroup.mk (FreeGroup.map (flattenBlockGen core hcore extra) w)
        simp
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
      rw [PresMorFS.cells_add, PresMorFS.cells_add, PresMorFS.cells_add,
        PresMorFS.cells_add, hx, hy]
  | single j a =>
      change PresInclusionFS.cells _ _ _ _ _
        (PresInclusionFS.cells _ _ _ _ _ (Finsupp.single j a)) =
        PresInclusionFS.cells _ _ _ _ _ (addRelsCellsFS _ _ (Finsupp.single j a))
      rw [PresInclusionFS.cells_single, PresInclusionFS.cells_single,
        addRelsCellsFS_single, PresInclusionFS.cells_single]
      have hj : Sum.map id Subtype.val (fullNextCell core hcore extra j) =
          terminalNextCell core hcore extra (Sum.inl j) := by cases j <;> rfl
      rw [hj]
      congr 1
      change MonoidAlgebra.mapDomainRingHom ℤ
        (stageIntoFull core (nextExtra core hcore extra)
          (nextPredicate core hcore extra (fun _ => True))).hom
        (MonoidAlgebra.mapDomainRingHom ℤ (fullNextMap core hcore extra).hom a) =
        MonoidAlgebra.mapDomainRingHom ℤ (terminalNextMap core hcore extra).hom
          (MonoidAlgebra.mapDomainRingHom ℤ (relativeTerminalMap core hcore extra).hom a)
      erw [BlockMor.mapDomainRingHom_comp', BlockMor.mapDomainRingHom_comp', hgroup]

/-- The next ambient presentation is Cockcroft and the last replaced
stage maps to it by zero on every actual supported two-cycle. -/
theorem nextTerminal_conclusions
    (hinj : Function.Injective (expMatrix core))
    (hP : FSIsCockcroft (rawPresentation core extra))
    (htriv : ∀ a : A,
      (QuotientGroup.mk (FreeGroup.of (Sum.inl a)) : PresGroup (rawPresentation core extra)) = 1) :
    FSIsCockcroft (rawPresentation core (nextExtra core hcore extra)) ∧
      (∀ x, FSIsFoxCycle (nextStage core hcore extra (fun _ => True)) x →
        (stageIntoFull core (nextExtra core hcore extra)
          (nextPredicate core hcore extra (fun _ => True))).cells x = 0) := by
  obtain ⟨hc, hz⟩ := relativeTerminal_conclusions core hcore extra hinj hP htriv
  refine ⟨fsIsCockcroft_of_generates (terminalNextMap core hcore extra)
    (PresInclusionFS.relabel_generates _ _ (flattenBlockGen core hcore extra)
    (terminalNextCell core hcore extra) (terminalNext_rel core hcore extra)) hc, ?_⟩
  intro x hx
  apply fsCells_eq_zero_of_generates (fullNextMap core hcore extra)
    (terminalNextMap core hcore extra) (relativeTerminalMap core hcore extra)
    (stageIntoFull core (nextExtra core hcore extra)
      (nextPredicate core hcore extra (fun _ => True)))
    (nextTerminal_square core hcore extra) hz (PresInclusionFS.relabel_generates _ _ (flattenBlockGen core hcore extra)
    (fullNextCell core hcore extra) (fullNext_rel core hcore extra)) hx

theorem block_core_trivial
    (htriv : ∀ a : A,
      (QuotientGroup.mk (FreeGroup.of (Sum.inl a)) : PresGroup (rawPresentation core extra)) = 1)
    (a : A) :
    (QuotientGroup.mk (FreeGroup.of (Sum.inl (Sum.inl a))) :
      PresGroup (blockPresentation core hcore extra)) = 1 := by
  have hn := normalized_core_trivial core hcore extra htriv a
  have h := congrArg (blockStructuralMap core hcore extra).hom hn
  change (QuotientGroup.mk (FreeGroup.map Sum.inl (FreeGroup.of (Sum.inl a))) :
      PresGroup (blockPresentation core hcore extra)) =
    (blockStructuralMap core hcore extra).hom 1 at h
  simp_all

theorem nextStage_core_trivial (p : S → Prop)
    (htriv : ∀ a : A,
      (QuotientGroup.mk (FreeGroup.of (Sum.inl a)) :
        PresGroup (rawPresentation core (restrictedExtra extra p))) = 1) (a : A) :
    (QuotientGroup.mk (FreeGroup.of (Sum.inl a)) : PresGroup (nextStage core hcore extra p)) = 1 := by
  have h := congrArg (stageNextMap core hcore extra p).hom
    (block_core_trivial core hcore (restrictedExtra extra p) htriv a)
  change QuotientGroup.mk (FreeGroup.map (stageNextGen core hcore extra p)
    (FreeGroup.of (Sum.inl (Sum.inl a)))) = (stageNextMap core hcore extra p).hom 1 at h
  simpa only [FreeGroup.map.of, stageNextGen, map_one] using h

theorem nextFull_core_trivial
    (htriv : ∀ a : A,
      (QuotientGroup.mk (FreeGroup.of (Sum.inl a)) : PresGroup (rawPresentation core extra)) = 1)
    (a : A) :
    (QuotientGroup.mk (FreeGroup.of (Sum.inl a)) :
      PresGroup (rawPresentation core (nextExtra core hcore extra))) = 1 := by
  have h := congrArg ((terminalNextMap core hcore extra).hom.comp
    (relativeTerminalMap core hcore extra).hom) (block_core_trivial core hcore extra htriv a)
  simp at h
  convert h using 1 <;> rfl

/-- Acyclicity of the core is used through its actual supported exponent
matrix. It does not assert that the core has trivial second homotopy group. -/

def coreIntoRaw : PresMorFS core (rawPresentation core extra) :=
  PresInclusionFS.mor _ _ Sum.inl Sum.inl Sum.inl_injective Sum.inl_injective (fun _ => rfl)

theorem coreIntoRaw_zero (hinj : Function.Injective (expMatrix core))
    (htriv : ∀ a : A,
      (QuotientGroup.mk (FreeGroup.of (Sum.inl a)) : PresGroup (rawPresentation core extra)) = 1)
    (x : C →₀ MonoidAlgebra ℤ (PresGroup core)) (hx : FSIsFoxCycle core x) :
    (coreIntoRaw core extra).cells x = 0 := by
  apply fsCells_eq_zero_of_isCockcroft_of_hom_trivial (coreIntoRaw core extra)
    (by
      intro x hx
      have h : x.mapRange (augPres core) (map_zero _) = 0 := by
        apply hinj
        rw [expMatrix_augmentation, hx, map_zero]
        exact Finsupp.mapRange_zero
      intro c
      exact DFunLike.congr_fun h c) ?_ x hx
  apply hom_eq_one_of_gens
  intro a
  exact htriv a

end FiniteChains.RelativeNormalForm
end

section
open scoped Classical
namespace FiniteChains.RelativeNormalForm
open Davis Davis.Genus BlockFamily

variable {A C : Type} (core : C → FreeGroup A)

def stageCellEquivFull {S : Type} (p : S → Prop) (hall : ∀ s, p s) :
    (C ⊕ {s // p s}) ≃ (C ⊕ S) where
  toFun := Sum.map id Subtype.val
  invFun := Sum.map id (fun s => ⟨s, hall s⟩)
  left_inv := by rintro (c | ⟨s, hs⟩) <;> rfl
  right_inv := by rintro (c | s) <;> rfl


def fullIntoStage {Z S : Type} (extra : S → FreeGroup (A ⊕ Z))
    (p : S → Prop) (hall : ∀ s, p s) :
    PresMorFS (rawPresentation core extra) (rawPresentation core (restrictedExtra extra p)) :=
  PresInclusionFS.mor _ _ id (stageCellEquivFull (C := C) p hall).symm
    Function.injective_id (stageCellEquivFull (C := C) p hall).symm.injective (by
      intro j
      cases j <;> simp [rawPresentation, restrictedExtra, stageCellEquivFull])

theorem fullIntoStage_generates {Z S : Type} (extra : S → FreeGroup (A ⊕ Z))
    (p : S → Prop) (hall : ∀ s, p s) : FSGenerates (fullIntoStage core extra p hall) := by
  exact PresInclusionFS.relabel_generates _ _ (Equiv.refl _)
    (stageCellEquivFull p hall).symm (by
      intro j
      cases j <;> simp [rawPresentation, restrictedExtra, stageCellEquivFull])

theorem rawInclusion_factor_full {Z S : Type} (extra : S → FreeGroup (A ⊕ Z))
    {p t : S → Prop} (hpt : ∀ s, p s → t s) (hall : ∀ s, t s)
    (x : (C ⊕ {s // p s}) →₀ MonoidAlgebra ℤ
      (PresGroup (rawPresentation core (restrictedExtra extra p)))) :
    (rawInclusion core extra hpt).cells x =
      (fullIntoStage core extra t hall).cells ((stageIntoFull core extra p).cells x) := by
  have hg : (rawInclusion core extra hpt).hom =
      (fullIntoStage core extra t hall).hom.comp (stageIntoFull core extra p).hom := by
    apply MonoidHom.ext
    intro z
    induction z using QuotientGroup.induction_on with
    | H w => change QuotientGroup.mk (FreeGroup.map id w) =
        QuotientGroup.mk (FreeGroup.map id (FreeGroup.map id w)); simp
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
      rw [PresMorFS.cells_add, PresMorFS.cells_add, PresMorFS.cells_add, hx, hy]
  | single j a =>
      change PresInclusionFS.cells _ _ _ _ _ (Finsupp.single j a) =
        PresInclusionFS.cells _ _ _ _ _ (PresInclusionFS.cells _ _ _ _ _ (Finsupp.single j a))
      rw [PresInclusionFS.cells_single, PresInclusionFS.cells_single, PresInclusionFS.cells_single]
      have hj : oldCellIncl hpt j = (stageCellEquivFull t hall).symm
          (Sum.map id Subtype.val j) := by cases j <;> rfl
      rw [hj]
      congr 1
      change MonoidAlgebra.mapDomainRingHom ℤ (rawInclusion core extra hpt).hom a =
        MonoidAlgebra.mapDomainRingHom ℤ (fullIntoStage core extra t hall).hom
          (MonoidAlgebra.mapDomainRingHom ℤ (stageIntoFull core extra p).hom a)
      rw [BlockMor.mapDomainRingHom_comp', ← hg]

/-- There are `n+1` positive stages after the unchanged core. The last
stage contains every ambient extra relator. All alphabets may be infinite. -/
structure AmbientChain (n : ℕ) where
  extraGen : Type
  extraCell : Type
  fresh : extraGen
  rel : extraCell → FreeGroup (A ⊕ extraGen)
  stage : ℕ → extraCell → Prop
  saturated : ∀ i, n ≤ i → ∀ s, stage i s
  mono : ∀ i s, stage i s → stage (i + 1) s
  strict : ∀ i, i < n → ∃ s, stage (i + 1) s ∧ ¬ stage i s
  cockcroft : ∀ i, FSIsCockcroft (rawPresentation core (restrictedExtra rel (stage i)))
  core_trivial : ∀ i a,
    (QuotientGroup.mk (FreeGroup.of (Sum.inl a)) :
      PresGroup (rawPresentation core (restrictedExtra rel (stage i)))) = 1
  zero : ∀ i, i < n → ∀ x,
    FSIsFoxCycle (rawPresentation core (restrictedExtra rel (stage i))) x →
      (rawInclusion core rel (mono i)).cells x = 0

namespace AmbientChain
variable {core} {n : ℕ} (c : AmbientChain core n)

theorem full_cockcroft : FSIsCockcroft (rawPresentation core c.rel) :=
  fsIsCockcroft_of_generates (stageIntoFull core c.rel (c.stage n))
    (by
      exact PresInclusionFS.relabel_generates _ _ (Equiv.refl _)
        (stageCellEquivFull (C := C) (c.stage n) (c.saturated n le_rfl)) (by
          intro j
          cases j <;> simp [rawPresentation, restrictedExtra, stageCellEquivFull])) (c.cockcroft n)

theorem full_core_trivial (a : A) :
    (QuotientGroup.mk (FreeGroup.of (Sum.inl a)) : PresGroup (rawPresentation core c.rel)) = 1 := by
  have h := congrArg (stageIntoFull core c.rel (c.stage n)).hom (c.core_trivial n a)
  change QuotientGroup.mk (FreeGroup.map id (FreeGroup.of (Sum.inl a))) =
    (stageIntoFull core c.rel (c.stage n)).hom 1 at h
  simp_all

/-- A literal initial pair, such as the actual FS `relY`, seeds the
induction. No replacement or terminal hypotheses are part of this input. -/
def initial {Z S : Type} (z : Z) (extra : S → FreeGroup (A ⊕ Z))
    (hc : FSIsCockcroft (rawPresentation core extra))
    (ht : ∀ a : A,
      (QuotientGroup.mk (FreeGroup.of (Sum.inl a)) : PresGroup (rawPresentation core extra)) = 1) :
    AmbientChain core 0 where
  extraGen := Z
  extraCell := S
  fresh := z
  rel := extra
  stage := fun _ _ => True
  saturated := by intros; trivial
  mono := by intros; trivial
  strict := by intro i hi; omega
  cockcroft := fun _ => fsIsCockcroft_of_generates (fullIntoStage core extra _ (fun _ => trivial))
    (fullIntoStage_generates core extra _ (fun _ => trivial)) hc
  core_trivial := by
    intro i a
    have h := congrArg (fullIntoStage core extra (fun _ => True) (fun _ => trivial)).hom (ht a)
    change QuotientGroup.mk (FreeGroup.map id (FreeGroup.of (Sum.inl a))) =
      (fullIntoStage core extra (fun _ => True) (fun _ => trivial)).hom 1 at h
    simpa only [FreeGroup.map.id, map_one] using h
  zero := by intro i hi; omega

variable (hcore : Function.Surjective (expMatrix core))

def stepStage (i : ℕ) : NextExtraCell core hcore c.rel → Prop :=
  if i ≤ n then nextPredicate core hcore c.rel (c.stage i) else fun _ => True

theorem stepStage_eq_of_le (i : ℕ) (hi : i ≤ n) :
    c.stepStage hcore i = nextPredicate core hcore c.rel (c.stage i) := if_pos hi

theorem stepStage_eq_of_not_le (i : ℕ) (hi : ¬ i ≤ n) :
    c.stepStage hcore i = fun _ => True := if_neg hi

theorem stepStage_mono (i : ℕ) : ∀ s,
    c.stepStage hcore i s → c.stepStage hcore (i + 1) s := by
  intro s hs
  by_cases hi : i + 1 ≤ n
  · simp only [stepStage, if_pos hi, if_pos (by omega : i ≤ n)] at *
    exact nextPredicate_mono core hcore c.rel (c.mono i) s hs
  · simp only [stepStage, if_neg hi]

theorem stepStage_strict (i : ℕ) (hi : i < n + 1) :
    ∃ s, c.stepStage hcore (i + 1) s ∧ ¬ c.stepStage hcore i s := by
  by_cases hin : i < n
  · obtain ⟨s, hs, hsp⟩ := c.strict i hin
    simpa only [stepStage, if_pos (by omega : i ≤ n), if_pos (by omega : i + 1 ≤ n)] using
      nextStage_strict core hcore c.rel s hs hsp
  · have he : i = n := by omega
    subst i
    refine ⟨Sum.inr (c.fresh, false), ?_, ?_⟩
    · simp [stepStage]
    · simp [stepStage, nextPredicate]


theorem stepStage_zero (hinj : Function.Injective (expMatrix core))
    (i : ℕ) (hi : i < n + 1) (x :
      (C ⊕ {s // c.stepStage hcore i s}) →₀ MonoidAlgebra ℤ
        (PresGroup (rawPresentation core (restrictedExtra
          (nextExtra core hcore c.rel) (c.stepStage hcore i)))))
    (hx : FSIsFoxCycle (rawPresentation core (restrictedExtra
      (nextExtra core hcore c.rel) (c.stepStage hcore i))) x) :
    (rawInclusion core (nextExtra core hcore c.rel) (c.stepStage_mono hcore i)).cells x = 0 := by
  let P (p t : NextExtraCell core hcore c.rel → Prop) : Prop :=
    ∀ (hpt : ∀ s, p s → t s)
      y,
      FSIsFoxCycle (rawPresentation core (restrictedExtra (nextExtra core hcore c.rel) p)) y →
        (rawInclusion core (nextExtra core hcore c.rel) hpt).cells y = 0
  have hz : P (c.stepStage hcore i) (c.stepStage hcore (i + 1)) := by
    by_cases hin : i < n
    · rw [c.stepStage_eq_of_le hcore i (by omega),
        c.stepStage_eq_of_le hcore (i + 1) (by omega)]
      intro hpt y hy
      exact nextStage_preserves_zero core hcore c.rel (c.mono i) (c.zero i hin) hy
    · have he : i = n := by omega
      subst i
      rw [c.stepStage_eq_of_le hcore n le_rfl,
        c.stepStage_eq_of_not_le hcore (n + 1) (by omega), (show c.stage n = fun _ => True by
          funext s
          exact propext ⟨fun _ => trivial, fun _ => c.saturated n le_rfl s⟩)]
      intro hpt y hy
      rw [rawInclusion_factor_full core (nextExtra core hcore c.rel) hpt (fun _ => trivial)]
      have ht := (nextTerminal_conclusions core hcore c.rel hinj c.full_cockcroft
        c.full_core_trivial).2 y hy
      rw [ht, PresMorFS.cells_zero]
  grind

/-- The simultaneous fixed-core step `(D,L₁,…,Lₘ)` to
`(D,T L₁,…,T Lₘ,Q Lₘ)`, in actual repeated-use ambient coordinates. -/
def step (hinj : Function.Injective (expMatrix core)) : AmbientChain core (n + 1) where
  extraGen := NextExtraGen core hcore c.rel
  extraCell := NextExtraCell core hcore c.rel
  fresh := Sum.inl (c.fresh, false)
  rel := nextExtra core hcore c.rel
  stage := c.stepStage hcore
  saturated := by
    intro i hi s
    simp only [stepStage, if_neg (by omega : ¬ i ≤ n)]
  mono := c.stepStage_mono hcore
  strict := c.stepStage_strict hcore
  cockcroft := by
    intro i
    let P (p : NextExtraCell core hcore c.rel → Prop) : Prop :=
      FSIsCockcroft (rawPresentation core (restrictedExtra (nextExtra core hcore c.rel) p))
    change P (c.stepStage hcore i)
    by_cases hi : i ≤ n
    · rw [c.stepStage_eq_of_le hcore i hi]
      exact nextStage_cockcroft core hcore c.rel (c.stage i) (c.cockcroft i)
    · rw [c.stepStage_eq_of_not_le hcore i hi]
      exact fsIsCockcroft_of_generates
        (fullIntoStage core (nextExtra core hcore c.rel) (fun _ => True) (fun _ => trivial))
        (fullIntoStage_generates core (nextExtra core hcore c.rel) (fun _ => True) (fun _ => trivial))
        (nextTerminal_conclusions core hcore c.rel hinj c.full_cockcroft c.full_core_trivial).1
  core_trivial := by
    intro i a
    let P (p : NextExtraCell core hcore c.rel → Prop) : Prop :=
      (QuotientGroup.mk (FreeGroup.of (Sum.inl a)) : PresGroup
        (rawPresentation core (restrictedExtra (nextExtra core hcore c.rel) p))) = 1
    change P (c.stepStage hcore i)
    by_cases hi : i ≤ n
    · rw [c.stepStage_eq_of_le hcore i hi]
      exact nextStage_core_trivial core hcore c.rel (c.stage i) (c.core_trivial i) a
    · rw [c.stepStage_eq_of_not_le hcore i hi]
      have h := congrArg (fullIntoStage core (nextExtra core hcore c.rel)
        (fun _ => True) (fun _ => trivial)).hom
        (nextFull_core_trivial core hcore c.rel c.full_core_trivial a)
      change QuotientGroup.mk (FreeGroup.map id (FreeGroup.of (Sum.inl a))) =
        (fullIntoStage core (nextExtra core hcore c.rel) (fun _ => True) (fun _ => trivial)).hom 1 at h
      exact (show (QuotientGroup.mk (FreeGroup.of (Sum.inl a)) : PresGroup
        (rawPresentation core (restrictedExtra (nextExtra core hcore c.rel) (fun _ => True)))) = 1
        from by simpa only [FreeGroup.map.id, map_one] using h)
  zero := c.stepStage_zero hcore hinj

end AmbientChain

/-- Iterating the actual construction produces all finite chain lengths
over the same core. Only the initial concrete relative presentation is
an argument; all replacement and terminal obligations are discharged. -/
def ambientChains (hcore : Function.Bijective (expMatrix core))
    (initial : AmbientChain core 0) : (n : ℕ) → AmbientChain core n
  | 0 => initial
  | n + 1 => (ambientChains hcore initial n).step hcore.2 hcore.1

end FiniteChains.RelativeNormalForm
end

section
open scoped Classical
namespace FiniteChains.PresInclusionFS
variable {A B J K : Type} [DecidableEq A] [DecidableEq B]
  (ρ : J → FreeGroup A) (τ : K → FreeGroup B)
  (g : A → B) (f : J → K) (hg : Function.Injective g) (hf : Function.Injective f)
  (hrel : ∀ j, τ (f j) = FreeGroup.map g (ρ j))

theorem zero_universal_chains
    (hz : ∀ x, FSIsFoxCycle ρ x → (mor ρ τ g f hg hf hrel).cells x = 0)
    (u : PresGroup ρ × J →₀ ℤ) (hu : Comb.bdry2 (Comb.univCover ρ) u = 0) :
    Finsupp.mapDomain (Prod.map (groupHom ρ τ g f hrel) f) u = 0 := by
  apply (Comb.fs_univCover_zero_pi2_iff ρ (groupHom ρ τ g f hrel) f hf).2 ?_ u hu
  intro v hv
  apply hz v
  ext i : 1
  simpa only [fs_coverSecondBoundary_apply, Finsupp.zero_apply] using hv i
end FiniteChains.PresInclusionFS

namespace FiniteChains.RelativeNormalForm.AmbientChain
variable {A C : Type} {core : C → FreeGroup A} {n : ℕ} (c : AmbientChain core n)

def chainGen : ℕ → Type
  | 0 => A
  | _ + 1 => A ⊕ c.extraGen

instance chainGenDecidableEq : (i : ℕ) → DecidableEq (c.chainGen i)
  | 0 => Classical.decEq _
  | _ + 1 => @instDecidableEqSum A c.extraGen (Classical.decEq _) (Classical.decEq _)

def chainCell : ℕ → Type
  | 0 => C
  | i + 1 => C ⊕ {s // c.stage i s}

def chainRel : ∀ i, c.chainCell i → FreeGroup (c.chainGen i)
  | 0 => core
  | i + 1 => rawPresentation core (restrictedExtra c.rel (c.stage i))

def chainGenIncl : ∀ i, c.chainGen i → c.chainGen (i + 1)
  | 0 => Sum.inl
  | _ + 1 => id

def chainCellIncl : ∀ i, c.chainCell i → c.chainCell (i + 1)
  | 0 => Sum.inl
  | i + 1 => oldCellIncl (c.mono i)

theorem chainGenIncl_injective (i : ℕ) : Function.Injective (c.chainGenIncl i) := by
  cases i
  · exact Sum.inl_injective
  · exact Function.injective_id

theorem chainCellIncl_injective (i : ℕ) : Function.Injective (c.chainCellIncl i) := by
  cases i with
  | zero => exact Sum.inl_injective
  | succ i => exact oldCellIncl_injective (c.mono i)

theorem chainRel_incl (i : ℕ) (j : c.chainCell i) :
    c.chainRel (i + 1) (c.chainCellIncl i j) = FreeGroup.map (c.chainGenIncl i) (c.chainRel i j) := by
  cases i with
  | zero => rfl
  | succ i =>
      cases j with
      | inl j => exact (FreeGroup.map.id (FreeGroup.map Sum.inl (core j))).symm
      | inr j => exact (FreeGroup.map.id (c.rel j.val)).symm

theorem chainMor_zero (hinj : Function.Injective (expMatrix core)) (i : ℕ) (hi : i < n + 1)
    (x : c.chainCell i →₀ MonoidAlgebra ℤ (PresGroup (c.chainRel i)))
    (hx : FSIsFoxCycle (c.chainRel i) x) :
    (PresInclusionFS.mor (c.chainRel i) (c.chainRel (i + 1))
      (c.chainGenIncl i) (c.chainCellIncl i) (c.chainGenIncl_injective i)
      (c.chainCellIncl_injective i) (c.chainRel_incl i)).cells x = 0 := by
  cases i with
  | zero =>
      exact coreIntoRaw_zero core (restrictedExtra c.rel (c.stage 0)) hinj
        (c.core_trivial 0) x hx
  | succ i => exact c.zero i (by omega) x hx

/-- Every hypothesis in the presentation-chain zero field is supplied by
the actual finite-support construction. -/
def toPresChainFS (hinj : Function.Injective (expMatrix core)) : PresChainFS core (n + 1) where
  gen := c.chainGen
  cell := c.chainCell
  decGen := c.chainGenDecidableEq
  rel := c.chainRel
  genIncl := c.chainGenIncl
  genIncl_injective := c.chainGenIncl_injective
  cellIncl := c.chainCellIncl
  cellIncl_injective := c.chainCellIncl_injective
  rel_incl := c.chainRel_incl
  baseGen := id
  baseGen_injective := Function.injective_id
  baseCell := id
  baseCell_injective := Function.injective_id
  rel_base := by intro j; exact (FreeGroup.map.id (core j)).symm
  zero_pi2 := by
    intro i hi u hu
    exact PresInclusionFS.zero_universal_chains (c.chainRel i) (c.chainRel (i + 1))
      (c.chainGenIncl i) (c.chainCellIncl i) (c.chainGenIncl_injective i)
      (c.chainCellIncl_injective i) (c.chainRel_incl i) (c.chainMor_zero hinj i hi) u hu

theorem chain_proper (i : ℕ) (hi : i < n + 1) :
    (∃ a : c.chainGen (i + 1), a ∉ Set.range (c.chainGenIncl i)) ∨
      ∃ j : c.chainCell (i + 1), j ∉ Set.range (c.chainCellIncl i) := by
  cases i with
  | zero =>
      left
      exact ⟨Sum.inr c.fresh, by rintro ⟨a, h⟩; exact Sum.inl_ne_inr h⟩
  | succ i =>
      obtain ⟨s, hs, hsp⟩ := c.strict i (by omega)
      right
      refine ⟨Sum.inr ⟨s, hs⟩, ?_⟩
      rintro ⟨j, hj⟩
      cases j with
      | inl j => exact Sum.inl_ne_inr hj
      | inr j =>
          have he : j.val = s := congrArg Subtype.val (Sum.inr.inj hj)
          exact hsp (he ▸ j.property)

end FiniteChains.RelativeNormalForm.AmbientChain
end

namespace FiniteChains.RelativeAttachment
open scoped Classical
variable {J K E X Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace X] [TopologicalSpace Y]
  (r : C(BoundaryFamily J E, X)) (s : C(BoundaryFamily K E, Y))
  (f : C(X, Y)) (i : J → K)
  (h : ∀ j a, f (r ⟨j, a⟩) = s ⟨i j, a⟩)

def diskFamilyMap : C(DiskAttachment r, DiskAttachment s) :=
  desc r (boundaryFamilyInclusion J E)
    ((⟨old s (boundaryFamilyInclusion K E), old_continuous _ _⟩ : C(Y, DiskAttachment s)).comp f)
    ⟨fun d => cell s (boundaryFamilyInclusion K E) ⟨i d.1, d.2⟩,
      (cell_continuous _ _).comp (continuous_sigma (fun j =>
        continuous_sigmaMk (σ := fun _ : K => ClosedUnitBall E) (i := i j)))⟩
    (fun a => by
      change old s (boundaryFamilyInclusion K E) (f (r a)) =
        cell s (boundaryFamilyInclusion K E) ⟨i a.1, unitBoundaryInclusion E a.2⟩
      rw [h]
      exact (cell_boundary s _ (boundaryFamilyInclusion_isClosedEmbedding K E).injective
        ⟨i a.1, a.2⟩).symm)

omit [NormedSpace ℝ E] in
@[simp] theorem diskFamilyMap_old (x : X) :
    diskFamilyMap r s f i h (old r (boundaryFamilyInclusion J E) x) =
      old s (boundaryFamilyInclusion K E) (f x) := rfl

omit [NormedSpace ℝ E] in
@[simp] theorem diskFamilyMap_cell (j : J) (x : ClosedUnitBall E) :
    diskFamilyMap r s f i h (cell r (boundaryFamilyInclusion J E) ⟨j, x⟩) =
      cell s (boundaryFamilyInclusion K E) ⟨i j, x⟩ := by
  unfold diskFamilyMap
  rw [desc_cell]
  rfl

end FiniteChains.RelativeAttachment

namespace FiniteChains

universe u v

variable {I : Type u} {H : Type v} [Group H]

/-- The vector of exponent sums of a word, as a homomorphism to the free abelian group on
the generators.  Its underlying function is `FiniteChains.expVec`. -/
def expVecHom : FreeGroup I →* Multiplicative (I →₀ ℤ) :=
  FreeGroup.lift fun i => Multiplicative.ofAdd (Finsupp.single i (1 : ℤ))

@[simp] theorem expVecHom_of (i : I) :
    Multiplicative.toAdd (expVecHom (FreeGroup.of i)) = Finsupp.single i (1 : ℤ) := by
  simp [expVecHom, FreeGroup.lift_apply_of]

/-- The column of the exponent-sum matrix belonging to the relator `r j`. -/
def expCol {J : Type*} (r : J → FreeGroup I) (j : J) : I →₀ ℤ :=
  Multiplicative.toAdd (expVecHom (r j))

/-- The two descriptions of the exponent vector of a word agree. -/
theorem expCol_eq_expVec [DecidableEq I] {J : Type*} (r : J → FreeGroup I) (j : J) :
    expCol r j = expVec (r j) := by
  have h : ∀ w : FreeGroup I, Multiplicative.toAdd (expVecHom w) = expVec w := by
    intro w
    induction w using FreeGroup.induction_on with
    | one => rfl
    | of i => rfl
    | inv_of i ih => rfl
    | mul w₁ w₂ h₁ h₂ => rfl
  exact h (r j)

section Commuting

variable (u : I → H) (hu : ∀ i k, Commute (u i) (u k))

include hu in
theorem commClosure_comm : ∀ x ∈ Set.range u, ∀ y ∈ Set.range u, x * y = y * x := by
  rintro _ ⟨i, rfl⟩ _ ⟨k, rfl⟩
  exact hu i k

end Commuting

/-- **The elimination step.**  Let the elements `u i` of a group commute pairwise, let each
word `r j` map to `1`, and let the exponent vectors of the `r j` span `ℤ^{(I)}`.  Then every
`u i` is trivial. -/
theorem eq_one_of_expCol_surjective {J : Type*} (u : I → H) (hu : ∀ i k, Commute (u i) (u k))
    (r : J → FreeGroup I) (hrel : ∀ j, FreeGroup.lift u (r j) = 1)
    (hsurj : Function.Surjective (Finsupp.linearCombination ℤ (expCol r))) :
    ∀ i, u i = 1 := by
  set S : Set H := Set.range u with hS
  letI :=
    Subgroup.closureCommGroupOfComm (fun a ha b hb _ => commClosure_comm u hu a ha b hb)
  set U : I → Subgroup.closure S := fun i => ⟨u i, Subgroup.subset_closure ⟨i, rfl⟩⟩ with hU
  -- the additive homomorphism `ℤ^{(I)} → A` sending `e_i` to `U i`
  set g : (I →₀ ℤ) →+ Additive (Subgroup.closure S) :=
    Finsupp.liftAddHom fun i =>
      zmultiplesHom (Additive (Subgroup.closure S)) (Additive.ofMul (U i)) with hg
  have hg_single : ∀ i n,
      Additive.toMul (g (Finsupp.single i n)) = U i ^ n := by
    intro i n
    rw [hg, Finsupp.liftAddHom_apply_single]
    rfl
  -- the same map, read multiplicatively
  set Gm : Multiplicative (I →₀ ℤ) →* Subgroup.closure S :=
    { toFun := fun m => Additive.toMul (g (Multiplicative.toAdd m))
      map_one' := by simp
      map_mul' := fun m₁ m₂ => by
        show Additive.toMul (g (Multiplicative.toAdd m₁ + Multiplicative.toAdd m₂)) = _
        rw [map_add]
        rfl } with hGm
  -- a word in pairwise commuting elements only depends on its exponent vector
  have key : Gm.comp expVecHom = FreeGroup.lift U := by
    refine FreeGroup.ext_hom _ _ fun i => ?_
    show Additive.toMul (g (Multiplicative.toAdd (expVecHom (FreeGroup.of i)))) = _
    rw [expVecHom_of, FreeGroup.lift_apply_of, hg_single i 1, zpow_one]
  have hsub : ∀ w : FreeGroup I, (FreeGroup.lift U w)
      = FreeGroup.lift u w := by
    intro w
    have : ((Subgroup.closure S).subtype).comp (FreeGroup.lift U) = FreeGroup.lift u := by
      refine FreeGroup.ext_hom _ _ fun i => ?_
      simp [FreeGroup.lift_apply_of, hU]
    exact congrArg (fun f : FreeGroup I →* H => f w) this
  -- hence `g` kills every exponent vector of a relator
  have hcol : ∀ j, g (expCol r j) = 0 := by
    intro j
    have h1 : FreeGroup.lift U (r j) = 1 := by
      ext
      rw [hsub (r j), hrel j]
      rfl
    have h2 : Gm (expVecHom (r j)) = 1 := by
      rw [← MonoidHom.comp_apply, key, h1]
    have : Additive.toMul (g (expCol r j)) = 1 := h2
    simpa [expCol] using this
  -- and therefore the whole image of the exponent matrix
  have hzero : ∀ c : J →₀ ℤ, g (Finsupp.linearCombination ℤ (expCol r) c) = 0 := by
    intro c
    rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [AddMonoidHom.map_zsmul, hcol j, smul_zero]
  intro i
  obtain ⟨c, hc⟩ := hsurj (Finsupp.single i 1)
  have h0 : g (Finsupp.single i 1) = 0 := by rw [← hc]; exact hzero c
  have h1 : U i = 1 := by
    have hval := hg_single i 1
    rw [h0] at hval
    simpa using hval.symm
  exact congrArg Subtype.val h1

end FiniteChains

section
open scoped commutatorElement
namespace FiniteChains

variable {G : Type*} [Group G] {I J : Type*}

/-- The commutator `U i = ⁅a i, b i⁆` of the `i`-th added pair of generators. -/
def pairComm (a b : I → G) (i : I) : G := ⁅a i, b i⁆

/-- The cross-commutator relations of `Y_D`: generators with different indices commute. -/
def CrossCommuting (a b : I → G) : Prop :=
  ∀ i k : I, i ≠ k →
    Commute (a i) (a k) ∧ Commute (a i) (b k) ∧ Commute (b i) (a k) ∧ Commute (b i) (b k)

/-- The cross-commutators make the elements `U_i` commute. -/
theorem commute_pairComm (a b : I → G) (hab : CrossCommuting a b) (i k : I) :
    Commute (pairComm a b i) (pairComm a b k) := by
  by_cases hik : i = k
  · simp_all
  · obtain ⟨haa, hab', hba, hbb⟩ := hab i k hik
    have ha  :=
      ((haa.mul_right hab').mul_right haa.inv_right).mul_right hab'.inv_right
    have hb  :=
      ((hba.mul_right hbb).mul_right hba.inv_right).mul_right hbb.inv_right
    exact ((ha.mul_left hb).mul_left ha.inv_left).mul_left hb.inv_left

end FiniteChains
end

namespace FiniteChains

open MonoidAlgebra
open scoped commutatorElement IsMulCommutative

universe u

variable {I J : Type u}

/-- The generators of `Y_D`: the generators `x_i` of `D` (`Sum.inl i`) and the two added
generators `a_i = y_{i,false}`, `b_i = y_{i,true}` (`Sum.inr (i, s)`). -/
abbrev GenY (I : Type u) : Type u := I ⊕ (I × Bool)

/-- The index set of the cross-commutators `[y_{i,s}, y_{k,t}]`, one for each pair `i < k`
and each pair of signs. -/
abbrev CrossY (I : Type u) [LinearOrder I] : Type u := {p : I × I // p.1 < p.2} × Bool × Bool

/-- The two-cells of `Y_D`: the relators `r_j` of `D`, the new relators `x_i[a_i,b_i]⁻¹`,
and the cross-commutators. -/
abbrev CellY (I J : Type u) [LinearOrder I] : Type u := J ⊕ (I ⊕ CrossY I)

/-- The generator `x_i` of `Y_D`. -/
def xGen (i : I) : FreeGroup (GenY I) := FreeGroup.of (Sum.inl i)

/-- The generator `a_i` (`s = false`) or `b_i` (`s = true`) of `Y_D`. -/
def yGen (i : I) (s : Bool) : FreeGroup (GenY I) := FreeGroup.of (Sum.inr (i, s))

variable [LinearOrder I]

/-- The relators of `Y_D`. -/
def relY (r : J → FreeGroup I) : CellY I J → FreeGroup (GenY I)
  | Sum.inl j => FreeGroup.map Sum.inl (r j)
  | Sum.inr (Sum.inl i) => xGen i * ⁅yGen i false, yGen i true⁆⁻¹
  | Sum.inr (Sum.inr (⟨p, _⟩, s, t)) => ⁅yGen p.1 s, yGen p.2 t⁆

variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] (r : J → FreeGroup I)

/-- The fundamental group `G(Y_D)` of the complex `Y_D`. -/
abbrev GroupY : Type u := PresGroup (relY r)

/-- The image of `x_i` in `G(Y_D)`. -/
def xEl (i : I) : GroupY r := QuotientGroup.mk (xGen i)

/-- The image of `a_i`, `b_i` in `G(Y_D)`. -/
def yEl (i : I) (s : Bool) : GroupY r := QuotientGroup.mk (yGen i s)

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem mk_relY (c : CellY I J) : (QuotientGroup.mk (relY r c) : GroupY r) = 1 := by
  rw [QuotientGroup.eq_one_iff]
  exact Subgroup.subset_normalClosure ⟨c, rfl⟩

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
/-- The cross-commutators: generators with a smaller and a larger index commute. -/
theorem commute_yEl_of_lt {i k : I} (hik : i < k) (s t : Bool) :
    Commute (yEl r i s) (yEl r k t) := by
  have h : (QuotientGroup.mk (relY r (Sum.inr (Sum.inr (⟨(i, k), hik⟩, s, t))))) = 1 :=
    mk_relY r _
  have hrel : relY r (Sum.inr (Sum.inr (⟨(i, k), hik⟩, s, t))) = ⁅yGen i s, yGen k t⁆ := rfl
  rw [hrel] at h
  have hmap : (QuotientGroup.mk ⁅yGen i s, yGen k t⁆)
      = ⁅yEl r i s, yEl r k t⁆ :=
    map_commutatorElement (QuotientGroup.mk' (relSub (relY r))) _ _
  rw [hmap] at h
  exact commutatorElement_eq_one_iff_commute.1 h

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
/-- The cross-commutators: generators with different indices commute in `G(Y_D)`. -/
theorem commute_yEl_of_ne {i k : I} (hik : i ≠ k) (s t : Bool) :
    Commute (yEl r i s) (yEl r k t) := by grind [commute_yEl_of_lt, yEl]

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
/-- The relator `x_i[a_i,b_i]⁻¹`: in `G(Y_D)` one has `x_i = [a_i, b_i]`. -/
theorem xEl_eq_commutator (i : I) : xEl r i = ⁅yEl r i false, yEl r i true⁆ := by
  have h : (QuotientGroup.mk' (relSub (relY r))) (xGen i * ⁅yGen i false, yGen i true⁆⁻¹) = 1 :=
    mk_relY r (Sum.inr (Sum.inl i))
  rw [map_mul, map_inv, map_commutatorElement] at h
  exact mul_inv_eq_one.1 h

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
/-- The homomorphism `π₁(D) → G(Y_D)` induced by the inclusion, on the level of free
groups. -/
theorem lift_xEl (w : FreeGroup I) :
    FreeGroup.lift (fun i => xEl r i) w = (QuotientGroup.mk (FreeGroup.map Sum.inl w) : GroupY r) := by
  have h : FreeGroup.lift (fun i => xEl r i)
      = ((QuotientGroup.mk' (relSub (relY r))).comp (FreeGroup.map Sum.inl)) := by
    refine FreeGroup.ext_hom _ _ fun i => ?_
    simp [FreeGroup.lift_apply_of, xEl, xGen]
  simp_all

/-- Surjectivity of the exponent-sum matrix of `D` — part of the acyclicity of `D`. -/
def ExpSurjective : Prop := Function.Surjective (Finsupp.linearCombination ℤ (expCol r))

variable {r}

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
/-- **The elimination step of Lemma 3.1.**  If the exponent-sum matrix of `D` is surjective,
then `[a_i, b_i] = 1` in `G(Y_D)`. -/
theorem commutator_yEl_eq_one (hM : ExpSurjective r) (i : I) :
    ⁅yEl r i false, yEl r i true⁆ = 1 := by
  have hab : CrossCommuting (fun i => yEl r i false) (fun i => yEl r i true) := by
    intro i k hik
    exact ⟨commute_yEl_of_ne r hik false false, commute_yEl_of_ne r hik false true,
      commute_yEl_of_ne r hik true false, commute_yEl_of_ne r hik true true⟩
  have hu  :=
    fun i k => commute_pairComm _ _ hab i k
  have hlift : FreeGroup.lift (fun i => ⁅yEl r i false, yEl r i true⁆)
      = FreeGroup.lift (fun i => xEl r i) := by
    refine congrArg _ (funext fun i => ?_)
    exact (xEl_eq_commutator r i).symm
  have hrel : ∀ j, FreeGroup.lift (fun i => ⁅yEl r i false, yEl r i true⁆) (r j) = 1 := by
    intro j
    rw [hlift, lift_xEl r]
    exact mk_relY r (Sum.inl j)
  exact eq_one_of_expCol_surjective _ hu r hrel hM i

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
/-- **The inclusion `D ⊂ Y_D` kills `π₁(D)`**: every generator `x_i` of `D` becomes trivial
in `G(Y_D)`. -/
theorem xEl_eq_one (hM : ExpSurjective r) (i : I) : xEl r i = 1 := by
  rw [xEl_eq_commutator, commutator_yEl_eq_one hM]

omit [Fintype I] [Fintype J] [DecidableEq J] in
/-- **All added generators commute** in `G(Y_D)`. -/
theorem commute_yEl (hM : ExpSurjective r) (i k : I) (s t : Bool) :
    Commute (yEl r i s) (yEl r k t) := by
  by_cases hik : i = k
  · subst hik
    have hc := commutatorElement_eq_one_iff_commute.mp (commutator_yEl_eq_one hM i)
    cases s <;> cases t <;>
      first
        | exact Commute.refl _
        | exact hc
        | exact hc.symm
  · exact commute_yEl_of_ne r hik s t

/-! ### The Fox matrix of `Y_D` -/

/-- The image of the group element `y_{i,s}` in the group ring `ℤ[G(Y_D)]`. -/
def yRing (i : I) (s : Bool) : MonoidAlgebra ℤ (GroupY r) :=
  MonoidAlgebra.of ℤ (GroupY r) (yEl r i s)

/-- The Fox derivative of a commutator of two free generators. -/
theorem fox_commutator_free {β : Type*} [DecidableEq β] (A B g : β) :
    fox g ⁅FreeGroup.of A, FreeGroup.of B⁆
      = (if g = A then (1 : FreeGroupRing β)
            - grp (FreeGroup.of A * FreeGroup.of B * (FreeGroup.of A)⁻¹) else 0)
        + (if g = B then grp (FreeGroup.of A)
            - grp ⁅FreeGroup.of A, FreeGroup.of B⁆ else 0) := by
  rcases eq_or_ne A B with rfl | hAB
  · have h1 : ⁅FreeGroup.of A, FreeGroup.of A⁆ = 1 := by simp
    have h2 : FreeGroup.of A * FreeGroup.of A * (FreeGroup.of A)⁻¹ = FreeGroup.of A := by group
    rw [h1, h2, fox_one]
    by_cases hA : g = A <;> simp [hA]
  · show fox g (FreeGroup.of A * FreeGroup.of B * (FreeGroup.of A)⁻¹ * (FreeGroup.of B)⁻¹) = _
    rw [fox_mul, fox_mul, fox_mul, fox_inv, fox_inv, fox_of, fox_of]
    by_cases hA : g = A <;> by_cases hB : g = B <;>
      simp [hA, hB, hAB, hAB.symm, grp_mul, commutatorElement_def] <;> noncomm_ring

/-- The Fox derivative of a commutator of two free generators, read in a quotient in which
the two images commute. -/
theorem proj_fox_commutator {β : Type*} [DecidableEq β] (Nsub : Subgroup (FreeGroup β))
    [Nsub.Normal] (A B g : β)
    (hcomm : Commute (QuotientGroup.mk (FreeGroup.of A) : FreeGroup β ⧸ Nsub)
      (QuotientGroup.mk (FreeGroup.of B))) :
    proj Nsub (fox g ⁅FreeGroup.of A, FreeGroup.of B⁆)
      = (if g = A then 1 - qgrp Nsub (FreeGroup.of B) else 0)
        + (if g = B then qgrp Nsub (FreeGroup.of A) - 1 else 0) := by
  have hconj : (QuotientGroup.mk (FreeGroup.of A * FreeGroup.of B * (FreeGroup.of A)⁻¹)
      : FreeGroup β ⧸ Nsub) = QuotientGroup.mk (FreeGroup.of B) := by
    show (QuotientGroup.mk' Nsub) (FreeGroup.of A * FreeGroup.of B * (FreeGroup.of A)⁻¹)
      = (QuotientGroup.mk' Nsub) (FreeGroup.of B)
    rw [map_mul, map_mul, map_inv]
    simp
    rw [hcomm.eq, mul_inv_cancel_right]
  have hcom1 : (QuotientGroup.mk ⁅FreeGroup.of A, FreeGroup.of B⁆ : FreeGroup β ⧸ Nsub) = 1 := by
    show (QuotientGroup.mk' Nsub) ⁅FreeGroup.of A, FreeGroup.of B⁆ = 1
    rw [map_commutatorElement]
    simp
    exact commutatorElement_eq_one_iff_commute.2 hcomm
  have hq1 : qgrp Nsub (FreeGroup.of A * FreeGroup.of B * (FreeGroup.of A)⁻¹)
      = qgrp Nsub (FreeGroup.of B) :=
    congrArg (fun q => MonoidAlgebra.single q 1) hconj
  have hq2 : qgrp Nsub ⁅FreeGroup.of A, FreeGroup.of B⁆ = 1 := by
    unfold qgrp
    rw [hcom1]
    rfl
  rw [fox_commutator_free, map_add, apply_ite (proj Nsub), apply_ite (proj Nsub),
    map_zero, map_sub, map_sub, map_one, proj_grp, proj_grp, proj_grp, hq1, hq2]

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem yRing_eq_qgrp (i : I) (s : Bool) :
    yRing (r := r) i s
      = qgrp (relSub (relY r)) (FreeGroup.of (Sum.inr (i, s)) : FreeGroup (GenY I)) := rfl

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
/-- In `G(Y_D)` the generators `x_k` are trivial, so they are trivial in the group ring. -/
theorem qgrp_xGen (hM : ExpSurjective r) (k : I) :
    qgrp (relSub (relY r)) (FreeGroup.of (Sum.inl k) : FreeGroup (GenY I)) = 1 := by
  have h : (QuotientGroup.mk (FreeGroup.of (Sum.inl k))) = 1 :=
    xEl_eq_one hM k
  unfold qgrp
  rw [h]
  rfl

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
/-- The commutator `[a_k, b_k]` is trivial in `G(Y_D)`. -/
theorem qgrp_comm_inv (hM : ExpSurjective r) (k : I) :
    qgrp (relSub (relY r)) (⁅(FreeGroup.of (Sum.inr (k, false)) : FreeGroup (GenY I)),
      FreeGroup.of (Sum.inr (k, true))⁆⁻¹) = 1 := by
  have h : (QuotientGroup.mk (⁅(FreeGroup.of (Sum.inr (k, false)) : FreeGroup (GenY I)),
      FreeGroup.of (Sum.inr (k, true))⁆⁻¹) : GroupY r) = 1 := by
    show (QuotientGroup.mk' (relSub (relY r)))
      (⁅(FreeGroup.of (Sum.inr (k, false))),
        FreeGroup.of (Sum.inr (k, true))⁆⁻¹) = 1
    rw [map_inv, map_commutatorElement, inv_eq_one]
    exact commutator_yEl_eq_one hM k
  unfold qgrp
  rw [h]
  rfl

omit [Fintype I] [Fintype J] [DecidableEq J] in
/-- The Fox matrix of `Y_D` at a new generator and an old two-cell vanishes. -/
theorem foxMatrix_inr_inl (i : I) (s : Bool) (j : J) :
    foxMatrixPres (relY r) (Sum.inr (i, s)) (Sum.inl j) = 0 := by
  show proj (relSub (relY r)) (fox (Sum.inr (i, s)) (FreeGroup.map Sum.inl (r j))) = 0
  rw [fox_map_of_not_mem_range Sum.inl (fun k => by simp), map_zero]

omit [Fintype I] [Fintype J] [DecidableEq J] in
/-- The Fox matrix of `Y_D` at a new generator and a cell `x_k[a_k,b_k]⁻¹`. -/
theorem foxMatrix_inr_mid (hM : ExpSurjective r) (i k : I) (s : Bool) :
    foxMatrixPres (relY r) (Sum.inr (i, s)) (Sum.inr (Sum.inl k))
      = if k = i then (if s then -(yRing (r := r) i false - 1) else yRing (r := r) i true - 1) else 0 := by
  show proj (relSub (relY r)) (fox (Sum.inr (i, s))
    ((FreeGroup.of (Sum.inl k)) *
      ⁅FreeGroup.of (Sum.inr (k, false)), FreeGroup.of (Sum.inr (k, true))⁆⁻¹)) = _
  have hx : proj (relSub (relY r))
      (fox (Sum.inr (i, s)) (FreeGroup.of (Sum.inl k))) = 0 := by
    rw [fox_of, if_neg (by simp), map_zero]
  have hcomm := proj_fox_commutator (relSub (relY r)) (Sum.inr (k, false)) (Sum.inr (k, true))
    (Sum.inr (i, s)) (commute_yEl hM k k false true)
  rw [fox_mul, fox_inv, map_add, map_mul, map_neg, map_mul, hx, zero_add, proj_grp,
    qgrp_xGen hM, one_mul, proj_grp, qgrp_comm_inv hM, one_mul, hcomm]
  rw [← yRing_eq_qgrp, ← yRing_eq_qgrp]
  by_cases hik : k = i
  · grind
  · grind

omit [Fintype I] [Fintype J] [DecidableEq J] in
/-- The Fox matrix of `Y_D` at a new generator and a cross-commutator. -/
theorem foxMatrix_inr_cross (hM : ExpSurjective r) (i : I) (s : Bool) (c : CrossY I) :
    foxMatrixPres (relY r) (Sum.inr (i, s)) (Sum.inr (Sum.inr c))
      = (if (i, s) = (c.1.1.1, c.2.1) then 1 - yRing (r := r) c.1.1.2 c.2.2 else 0)
        + (if (i, s) = (c.1.1.2, c.2.2) then yRing (r := r) c.1.1.1 c.2.1 - 1 else 0) := by
  obtain ⟨⟨⟨p, q⟩, hpq⟩, u, v⟩ := c
  show proj (relSub (relY r)) (fox (Sum.inr (i, s))
    ⁅(FreeGroup.of (Sum.inr (p, u))), FreeGroup.of (Sum.inr (q, v))⁆) = _
  rw [proj_fox_commutator (relSub (relY r)) (Sum.inr (p, u)) (Sum.inr (q, v))
    (Sum.inr (i, s)) (commute_yEl hM p q u v), ← yRing_eq_qgrp, ← yRing_eq_qgrp]
  simp [Prod.ext_iff]

/-! ### The evaluation homomorphism -/

variable (r)

/-- The homomorphism of the free group onto `⊕_i (ℤ a_i ⊕ ℤ b_i)` used in Lemma 3.1: the
generators `x_i` go to `0` and the generators `a_i, b_i` to the corresponding basis
vectors. -/
def thetaFree : FreeGroup (GenY I) →* Multiplicative (I × Bool →₀ ℤ) :=
  FreeGroup.lift fun g =>
    match g with
    | Sum.inl _ => 1
    | Sum.inr P => Multiplicative.ofAdd (Finsupp.single P (1 : ℤ))



/-- The homomorphism `G(Y_D) → ⊕_i (ℤ a_i ⊕ ℤ b_i)` of Lemma 3.1. -/
def thetaY : GroupY r →* Multiplicative (I × Bool →₀ ℤ) :=
  QuotientGroup.lift (relSub (relY r)) thetaFree
    (by
      have hsub : relSub (relY r) ≤ thetaFree.ker := by
        refine Subgroup.normalClosure_le_normal ?_
        rintro _ ⟨c, rfl⟩
        exact (by
          match c with
          | Sum.inl j => exact (by
            have h : thetaFree.comp (FreeGroup.map (Sum.inl : I → GenY I))
                = (1 : FreeGroup I →* Multiplicative (I × Bool →₀ ℤ)) := by
              refine FreeGroup.ext_hom _ _ fun i => ?_
              show thetaFree (FreeGroup.of (Sum.inl i)) = 1
              rw [thetaFree, FreeGroup.lift_apply_of]
            exact congrArg (fun f : FreeGroup I →* Multiplicative (I × Bool →₀ ℤ) => f (r j)) h)
          | Sum.inr (Sum.inl i) =>
              show thetaFree ((FreeGroup.of (Sum.inl i) : FreeGroup (GenY I)) *
                ⁅FreeGroup.of (Sum.inr (i, false)), FreeGroup.of (Sum.inr (i, true))⁆⁻¹) = 1
              rw [map_mul, map_inv, map_commutatorElement,
                commutatorElement_eq_one_iff_commute.2 (Commute.all _ _)]
              simp [thetaFree, FreeGroup.lift_apply_of]
          | Sum.inr (Sum.inr ⟨⟨(p, q), hpq⟩, u, v⟩) =>
              show thetaFree ⁅(FreeGroup.of (Sum.inr (p, u)) : FreeGroup (GenY I)),
                FreeGroup.of (Sum.inr (q, v))⁆ = 1
              rw [map_commutatorElement]
              exact commutatorElement_eq_one_iff_commute.2 (Commute.all _ _))
      exact fun w hw => hsub hw)

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem thetaY_yEl (i : I) (s : Bool) :
    Multiplicative.toAdd (thetaY r (yEl r i s)) = Finsupp.single (i, s) 1 := by
  show Multiplicative.toAdd (thetaFree (FreeGroup.of (Sum.inr (i, s))))
    = Finsupp.single (i, s) 1
  rw [thetaFree, FreeGroup.lift_apply_of]
  rfl

/-- The coordinate functional `ℤ[G(Y_D)] → ℤ` attached to a generator `y_P`: the
composition of `thetaY` with the `P`-th coordinate.  It kills products of two elements of
the augmentation ideal, which is what makes the cycle equations computable. -/
def psiY (P : I × Bool) : MonoidAlgebra ℤ (GroupY r) →ₗ[ℤ] ℤ :=
  (Finsupp.linearCombination ℤ fun g : GroupY r => (Multiplicative.toAdd (thetaY r g)) P).comp
    (MonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem psiY_single (P : I × Bool) (g : GroupY r) (n : ℤ) :
    psiY r P (MonoidAlgebra.single g n) = n * (Multiplicative.toAdd (thetaY r g)) P := by simp_all [psiY, thetaY]

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
/-- **The key computation.**  Evaluating `z · (g - 1)` returns the augmentation of `z`
times the `P`-th coordinate of the image of `g`; in particular products of two elements of
the augmentation ideal are killed. -/
theorem psiY_mul_group_sub_one (P : I × Bool) (g : GroupY r)
    (z : MonoidAlgebra ℤ (GroupY r)) :
    psiY r P (z * (MonoidAlgebra.of ℤ (GroupY r) g - 1))
      = augPres (relY r) z * (Multiplicative.toAdd (thetaY r g)) P := by
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add z₁ z₂ h₁ h₂ =>
      rw [add_mul, map_add, h₁, h₂, map_add, add_mul]
  | single h n =>
      have hmul : (MonoidAlgebra.single h n) *
          (MonoidAlgebra.of ℤ (GroupY r) g - 1)
          = MonoidAlgebra.single (h * g) n - MonoidAlgebra.single h n := by
        rw [mul_sub, mul_one]
        congr 1
        show MonoidAlgebra.single h n * MonoidAlgebra.single g 1 = _
        rw [MonoidAlgebra.single_mul_single, mul_one]
      rw [hmul, map_sub, psiY_single, psiY_single, augQ_single]
      have hhom : Multiplicative.toAdd (thetaY r (h * g))
          = Multiplicative.toAdd (thetaY r h) + Multiplicative.toAdd (thetaY r g) := by
        rw [map_mul]
        rfl
      rw [hhom]
      simp [mul_add]

omit [Fintype I] [Fintype J] [DecidableEq J] in
theorem psiY_mul_sub_one (P Q : I × Bool) (z : MonoidAlgebra ℤ (GroupY r)) :
    psiY r P (z * (yRing (r := r) Q.1 Q.2 - 1)) = augPres (relY r) z * (if Q = P then 1 else 0) := by
  rw [show yRing Q.1 Q.2 = MonoidAlgebra.of ℤ (GroupY r) (yEl r Q.1 Q.2) from rfl,
    psiY_mul_group_sub_one, thetaY_yEl]
  simp [Finsupp.single_apply]


/-! ### Lemma 3.1 -/

variable {r}

omit [Fintype I] [Fintype J] [DecidableEq J] in
/-- The contribution of a cross-commutator cell to the cycle equation at a generator
`y_{i,s}`, evaluated in the coordinate `P`. -/
theorem psiY_cross_term (hM : ExpSurjective r) (P : I × Bool) (i : I) (s : Bool)
    (c : CrossY I) (z : MonoidAlgebra ℤ (GroupY r)) :
    psiY r P (z * foxMatrixPres (relY r) (Sum.inr (i, s)) (Sum.inr (Sum.inr c)))
      = (if (i, s) = (c.1.1.1, c.2.1)
            then -(augPres (relY r) z * (if (c.1.1.2, c.2.2) = P then 1 else 0)) else 0)
        + (if (i, s) = (c.1.1.2, c.2.2)
            then augPres (relY r) z * (if (c.1.1.1, c.2.1) = P then 1 else 0) else 0) := by
  rw [foxMatrix_inr_cross hM, mul_add, map_add]
  congr 1
  · by_cases h : (i, s) = (c.1.1.1, c.2.1)
    · rw [if_pos h, if_pos h]
      exact (by
        have h : z * (1 - yRing (c.1.1.2, c.2.2).1 (c.1.1.2, c.2.2).2) = -(z * (yRing (c.1.1.2, c.2.2).1 (c.1.1.2, c.2.2).2 - 1)) := by noncomm_ring
        rw [h, map_neg, psiY_mul_sub_one])
    · rw [if_neg h, if_neg h, mul_zero, map_zero]
  · by_cases h : (i, s) = (c.1.1.2, c.2.2)
    · rw [if_pos h, if_pos h]
      exact psiY_mul_sub_one r P (c.1.1.1, c.2.1) z
    · rw [if_neg h, if_neg h, mul_zero, map_zero]

/-! ### The inclusion `D ⊂ Y_D` -/

variable (r)

variable {r}

/-! ### The fundamental group of `Y_D` -/

end FiniteChains

section
open scoped Classical
namespace FiniteChains
open BlockFamily

variable {I J : Type} [LinearOrder I] [DecidableEq I] (r : J → FreeGroup I)

omit [LinearOrder I] in
theorem expSurjective_of_expMatrix_surjective
    (h : Function.Surjective (expMatrix r)) : ExpSurjective r := by
  have he  := funext (expCol_eq_expVec r)
  rw [ExpSurjective, he]
  exact h

/-- A supported cycle can be read through any additive coefficient
functional which detects one cell. -/
theorem fs_boundary_extract {A L : Type} [DecidableEq A]
    (ρ : L → FreeGroup A) (ψ : MonoidAlgebra ℤ (PresGroup ρ) →+ ℤ)
    (a : A) (k : L) (s : ℤ)
    (hterm : ∀ (j : L) (z : MonoidAlgebra ℤ (PresGroup ρ)),
      ψ (z * foxMatrixPres ρ a j) = if j = k then s * augPres ρ z else 0)
    (v : L →₀ MonoidAlgebra ℤ (PresGroup ρ)) :
    ψ (coverSecondBoundary (relSub ρ) ρ v a) = s * augPres ρ (v k) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp [map_add, Finsupp.add_apply, hv, hw, mul_add]
  | single j z =>
      rw [fsCoverSecondBoundary_apply, Finsupp.sum_single_index (zero_mul _), hterm]
      by_cases hj : j = k
      · subst j
        simp
      · simp_all




theorem psiY_cross_mid_zero (hM : ExpSurjective r) {p q : I} (hpq : p < q)
    (u w : Bool) (k : I) (z : MonoidAlgebra ℤ (GroupY r)) :
    psiY r (q, w)
      (z * foxMatrixPres (relY r) (Sum.inr (p, u)) (Sum.inr (Sum.inl k))) = 0 := by
  rw [foxMatrix_inr_mid hM]
  by_cases hk : k = p
  · subst k
    have hne b : (p, b) ≠ (q, w) :=
      fun h => (ne_of_lt hpq) (congrArg Prod.fst h)
    rw [if_pos rfl]
    cases u
    · change psiY r (q, w) (z * (yRing p true - 1)) = 0
      rw [psiY_mul_sub_one r (q, w) (p, true), if_neg (hne true), mul_zero]
    · change psiY r (q, w) (z * -(yRing p false - 1)) = 0
      rw [mul_neg, map_neg, psiY_mul_sub_one r (q, w) (p, false),
        if_neg (hne false), mul_zero, neg_zero]
  · simp_all



theorem fs_aug_cycle_cross (hM : ExpSurjective r)
    {v : CellY I J →₀ MonoidAlgebra ℤ (GroupY r)}
    (hv : FSIsFoxCycle (relY r) v) (c₀ : CrossY I) :
    augPres (relY r) (v (Sum.inr (Sum.inr c₀))) = 0 := by
  have h := fs_boundary_extract (relY r)
    (psiY r (c₀.1.1.2, c₀.2.2)).toAddMonoidHom
    (Sum.inr (c₀.1.1.1, c₀.2.1)) (Sum.inr (Sum.inr c₀)) (-1)
    (by intro c z; simpa [neg_one_mul, LinearMap.toAddMonoidHom_coe] using (by
      cases c with
      | inl j => simp [foxMatrix_inr_inl, mul_zero, map_zero, Sum.inl_ne_inr, if_false]
      | inr c =>
        cases c with
        | inl k =>
          rw [psiY_cross_mid_zero r hM c₀.1.property]
          simp
        | inr c => simpa using (by
          obtain ⟨⟨⟨p, q⟩, hpq⟩, u, w⟩ := c₀
          by_cases hc : c = (⟨(p, q), hpq⟩, u, w)
          · subst c
            have hne : (p, u) ≠ (q, w) :=
              fun h => (ne_of_lt hpq) (congrArg Prod.fst h)
            rw [psiY_cross_term hM]
            simp [hne]
          · obtain ⟨⟨⟨p', q'⟩, hpq'⟩, u', w'⟩ := c
            rw [psiY_cross_term hM, if_neg hc]
            have hfirst : (p, u) = (p', u') → (q', w') ≠ (q, w) := by
              intro h₁ h₂
              apply hc
              have hp : p' = p := (congrArg Prod.fst h₁).symm
              have hu : u' = u := (congrArg Prod.snd h₁).symm
              have hq : q' = q := congrArg Prod.fst h₂
              have hw : w' = w := congrArg Prod.snd h₂
              subst p'
              subst q'
              subst u'
              subst w'
              rfl
            have hsecond : (p, u) = (q', w') → (p', u') ≠ (q, w) := by
              intro h₁ h₂
              have hq' : q' = p := (congrArg Prod.fst h₁).symm
              have hp' : p' = q := congrArg Prod.fst h₂
              rw [hp', hq'] at hpq'
              exact lt_asymm hpq hpq'
            by_cases h₁ : (p, u) = (p', u') <;>
              by_cases h₂ : (p, u) = (q', w')
            · simp_all
            · grind
            · grind
            · grind))) v
  change coverSecondBoundary _ _ v = 0 at hv
  simp_all

/-- The same concrete initial presentation as in Lemma 3.1, now for any
sets of core generators and core relators. -/

theorem fsIsCockcroft_relY_of_expMatrix_bijective
    (hM : Function.Bijective (expMatrix r)) : FSIsCockcroft (relY r) :=
  (by
    let extra  := fun c => relY r (Sum.inr c)
    have he : corePres r extra = relY r := by
      funext c
      cases c <;> rfl
    have href := corePres_fsAugmentation_reflect r extra (hM.1)
    rw [he] at href
    intro v hv
    apply href v hv
    intro c
    cases c with
    | inl i => exact (by
      have h := fs_boundary_extract (relY r) (psiY r (i, true)).toAddMonoidHom
        (Sum.inr (i, false)) (Sum.inr (Sum.inl i)) 1
        (by intro c z; simpa [one_mul, LinearMap.toAddMonoidHom_coe] using (by
          cases c with
          | inl j => simp [foxMatrix_inr_inl, mul_zero, map_zero, Sum.inl_ne_inr, if_false]
          | inr c =>
            cases c with
            | inl k =>
              by_cases hk : k = i
              · subst k
                rw [foxMatrix_inr_mid (expSurjective_of_expMatrix_surjective r hM.2), if_pos rfl]
                simpa using psiY_mul_sub_one r (i, true) (i, true) z
              · simp [foxMatrix_inr_mid (expSurjective_of_expMatrix_surjective r hM.2), hk]
            | inr c =>
              rw [(show psiY r (i, true)
              (z * foxMatrixPres (relY r) (Sum.inr (i, false)) (Sum.inr (Sum.inr c))) = 0 by
                obtain ⟨⟨⟨p, q⟩, hpq⟩, u, w⟩ := c
                rw [psiY_cross_term (expSurjective_of_expMatrix_surjective r hM.2)]
                grind)]
              simp)) v
      change coverSecondBoundary _ _ v = 0 at hv
      simp_all)
    | inr c => exact fs_aug_cycle_cross r (expSurjective_of_expMatrix_surjective r hM.2) hv c)

end FiniteChains

namespace FiniteChains.InitialFS
open RelativeNormalForm

variable {A M : Type}

def chosenOrder (A : Type) : LinearOrder A :=
  IsWellOrder.linearOrder (@WellOrderingRel A)

abbrev ExtraGen (A : Type) := (A × Bool) ⊕ PUnit

def ExtraCell (A : Type) : Type :=
  letI : LinearOrder A := chosenOrder A
  A ⊕ CrossY A

/-- A canonical genuinely new generator, independent of whether `A` is empty. -/
def fresh (A : Type) : ExtraGen A := Sum.inr PUnit.unit


def generatorEmbedding : GenY A → A ⊕ ExtraGen A
  | Sum.inl a => Sum.inl a
  | Sum.inr b => Sum.inr (Sum.inl b)

theorem generatorEmbedding_injective :
    Function.Injective (generatorEmbedding (A := A)) := by
  intro x y h
  cases x <;> cases y <;> simp_all [generatorEmbedding]

def baseRel (core : M → FreeGroup A) : M ⊕ ExtraCell A → FreeGroup (GenY A) :=
  letI : LinearOrder A := chosenOrder A
  relY core

@[simp] theorem baseRel_core (core : M → FreeGroup A) (m : M) :
    baseRel core (Sum.inl m) = FreeGroup.map Sum.inl (core m) := rfl

def extra (core : M → FreeGroup A) : ExtraCell A → FreeGroup (A ⊕ ExtraGen A) :=
  fun c => FreeGroup.map generatorEmbedding (baseRel core (Sum.inr c))


theorem rawPresentation_eq_padding (core : M → FreeGroup A) :
    rawPresentation core (extra core) = FreePadding.rel (baseRel core) generatorEmbedding := by
  funext c
  cases c with
  | inl m => exact (show FreeGroup.map generatorEmbedding (FreeGroup.map Sum.inl (core m)) =
      FreeGroup.map (Sum.inl) (core m) by
    have h : (FreeGroup.map generatorEmbedding).comp (FreeGroup.map Sum.inl) =
        FreeGroup.map (Sum.inl (β := ExtraGen A)) := by
      apply FreeGroup.ext_hom
      intro a
      simp [generatorEmbedding]
    exact congrArg (fun f : FreeGroup A →* FreeGroup (A ⊕ ExtraGen A) => f (core m)) h).symm
  | inr c => rfl



/-- The explicit initial pair is Cockcroft for arbitrary supported core
chains. The extra free generator preserves Cockcroftness by the actual
free-padding structural map and its proved generation theorem. -/
theorem isCockcroft (core : M → FreeGroup A)
    (hcore : Function.Bijective (expMatrix core)) :
    FSIsCockcroft (rawPresentation core (extra core)) := by
  rw [rawPresentation_eq_padding]
  exact fsIsCockcroft_of_generates
    (FreePadding.structuralMap (baseRel core) generatorEmbedding generatorEmbedding_injective)
    (FreePadding.structuralMap_generates (baseRel core) generatorEmbedding generatorEmbedding_injective)
    (by
      letI := chosenOrder A
      letI : DecidableEq A := Classical.decEq A
      exact fsIsCockcroft_relY_of_expMatrix_bijective core hcore)

/-- The original core maps trivially into the actual padded initial group. -/
theorem core_trivial (core : M → FreeGroup A)
    (hcore : Function.Surjective (expMatrix core)) (a : A) :
    (QuotientGroup.mk (FreeGroup.of (Sum.inl a)) :
      PresGroup (rawPresentation core (extra core))) = 1 := by
  rw [rawPresentation_eq_padding]
  have h := congrArg (FreePadding.groupHom (baseRel core) generatorEmbedding)
    (show (QuotientGroup.mk (FreeGroup.of (Sum.inl a))) = 1 by
      letI := chosenOrder A
      letI : DecidableEq A := Classical.decEq A
      exact xEl_eq_one (expSurjective_of_expMatrix_surjective core hcore) a)
  rw [map_one] at h
  change (QuotientGroup.mk
    (FreeGroup.map generatorEmbedding (FreeGroup.of (Sum.inl a)))) = 1 at h
  simpa only [FreeGroup.map.of, generatorEmbedding] using h

end FiniteChains.InitialFS

namespace FiniteChains

theorem FSIsCockcroft.redecide {A J : Type} [dA : DecidableEq A]
    {ρ : J → FreeGroup A} (h : FSIsCockcroft ρ) (dA' : DecidableEq A) :
    @FSIsCockcroft A J dA' ρ := by
  have hd : dA' = dA := Subsingleton.elim _ _
  subst dA'
  exact h

end FiniteChains

namespace FiniteChains.RelativeNormalForm
variable {A C : Type} (core : C → FreeGroup A)
  (hcore : Function.Bijective (expMatrix core))


def actualAmbientChain (n : ℕ) : AmbientChain core n :=
  ambientChains core hcore (by
    refine AmbientChain.initial (core := core) (InitialFS.fresh A) (InitialFS.extra core)
      ?_ (InitialFS.core_trivial core hcore.2)
    exact @FSIsCockcroft.redecide _ _ _ _ (InitialFS.isCockcroft core hcore) _) n

theorem actualAmbientChain_finite [Finite A] (n : ℕ) :
    Finite (actualAmbientChain core hcore n).extraGen ∧
      Finite (actualAmbientChain core hcore n).extraCell := by
  induction n with
  | zero =>
      change Finite (InitialFS.ExtraGen A) ∧ Finite (InitialFS.ExtraCell A)
      constructor
      · infer_instance
      · unfold InitialFS.ExtraCell
        infer_instance
  | succ n ih =>
      letI := ih.1
      letI := ih.2
      change Finite (NextExtraGen core hcore.2 (actualAmbientChain core hcore n).rel) ∧
        Finite (NextExtraCell core hcore.2 (actualAmbientChain core hcore n).rel)
      constructor <;> infer_instance

end FiniteChains.RelativeNormalForm
end

namespace FiniteChains.RelativeAttachment
open scoped unitInterval Topology Classical ContinuousMap
universe u
variable {D P : Type u} [TopologicalSpace D] [TopologicalSpace P]
  (S : Set D) (a₀ a₁ : C(S, P)) (H : a₀.Homotopy a₁)
  (L₀ : C(I × D, Space a₀ Subtype.val))
  (L₁ : C(I × D, Space a₁ Subtype.val))
  (h₀ : ∀ d, L₀ (0, d) = cell a₀ Subtype.val d)
  (h₁ : ∀ d, L₁ (0, d) = cell a₁ Subtype.val d)
  (hs₀ : ∀ t a, L₀ (t, a.val) = old a₀ Subtype.val (H (t, a)))
  (hs₁ : ∀ t a, L₁ (t, a.val) = old a₁ Subtype.val (H.symm (t, a)))

def chosenAttachingBackward : C(Space a₁ Subtype.val, Space a₀ Subtype.val) :=
  desc a₁ Subtype.val ⟨old a₀ Subtype.val, old_continuous _ _⟩
    (L₀.comp ⟨fun d => (1, d), continuous_const.prodMk continuous_id⟩)
    (fun a => by
      change old a₀ Subtype.val (a₁ a) = L₀ (1, a.val)
      rw [hs₀, H.apply_one])

def chosenAttachingForward : C(Space a₀ Subtype.val, Space a₁ Subtype.val) :=
  desc a₀ Subtype.val ⟨old a₁ Subtype.val, old_continuous _ _⟩
    (L₁.comp ⟨fun d => (1, d), continuous_const.prodMk continuous_id⟩)
    (fun a => by
      change old a₁ Subtype.val (a₀ a) = L₁ (1, a.val)
      rw [hs₁, H.symm.apply_one])

@[simp] theorem chosenAttachingBackward_cell (d : D) :
    chosenAttachingBackward S a₀ a₁ H L₀ hs₀ (cell a₁ Subtype.val d) = L₀ (1, d) := by
  unfold chosenAttachingBackward
  rw [desc_cell]
  rfl

@[simp] theorem chosenAttachingForward_cell (d : D) :
    chosenAttachingForward S a₀ a₁ H L₁ hs₁ (cell a₀ Subtype.val d) = L₁ (1, d) := by
  unfold chosenAttachingForward
  rw [desc_cell]
  rfl

def attachingHomotopyEquivOfExtensions (hS : IsClosed S)
    (hfull : HasHomotopyExtension (Subtype.val : FullCylinderBoundary S → I × D)) :
    Space a₀ Subtype.val ≃ₕ Space a₁ Subtype.val where
  toFun := chosenAttachingForward S a₀ a₁ H L₁ hs₁
  invFun := chosenAttachingBackward S a₀ a₁ H L₀ hs₀
  left_inv := attachingBacktrack_homotopic_id S hS hfull a₀ a₁ H _ _
    (fun _ => rfl) (fun _ => rfl) L₀ L₁ h₀ h₁ hs₀ hs₁
    (chosenAttachingBackward_cell S a₀ a₁ H L₀ hs₀)
    (chosenAttachingForward_cell S a₀ a₁ H L₁ hs₁)
  right_inv := by
    apply attachingBacktrack_homotopic_id S hS hfull a₁ a₀ H.symm _ _
      (fun _ => rfl) (fun _ => rfl) L₁ L₀ h₁ h₀ hs₁ _
      (chosenAttachingForward_cell S a₀ a₁ H L₁ hs₁)
      (chosenAttachingBackward_cell S a₀ a₁ H L₀ hs₀)
    intro t a
    simpa only [ContinuousMap.Homotopy.symm_symm] using hs₀ t a

end FiniteChains.RelativeAttachment

namespace FiniteChains.RelativeAttachment
open scoped Classical Topology unitInterval
variable {J K E X Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace X] [TopologicalSpace Y]

theorem ballHomotopyExtension_natural
    (f : C(X, Y)) (d : C(ClosedUnitBall E, X)) (d' : C(ClosedUnitBall E, Y))
    (H : C(I × UnitBoundary E, X)) (H' : C(I × UnitBoundary E, Y))
    (h₀ : ∀ a, H (0, a) = d (unitBoundaryInclusion E a))
    (h₀' : ∀ a, H' (0, a) = d' (unitBoundaryInclusion E a))
    (hd : ∀ x, f (d x) = d' x) (hH : ∀ t a, f (H (t, a)) = H' (t, a))
    (t : I) (x : ClosedUnitBall E) :
    f (ballHomotopyExtension d H h₀ (t, x)) =
      ballHomotopyExtension d' H' h₀' (t, x) := by
  let z := ballCylinderRetraction (t, x)
  change f (if hz : z.val.1 = 0 then d z.val.2 else
      H (z.val.1, ⟨z.val.2.val, z.property.resolve_left hz⟩)) =
    if hz : z.val.1 = 0 then d' z.val.2 else
      H' (z.val.1, ⟨z.val.2.val, z.property.resolve_left hz⟩)
  grind

variable (r₀ r₁ : C(BoundaryFamily J E, X)) (H : r₀.Homotopy r₁)

omit [NormedSpace ℝ E] in
theorem naturalDiskBoundaryStart (j : J) (a : UnitBoundary E) :
    old r₀ (boundaryFamilyInclusion J E) (H (0, ⟨j, a⟩)) =
      cell r₀ (boundaryFamilyInclusion J E) ⟨j, unitBoundaryInclusion E a⟩ := by
  rw [H.apply_zero]
  exact (cell_boundary r₀ _ (boundaryFamilyInclusion_isClosedEmbedding J E).injective
    ⟨j, a⟩).symm

def naturalDiskExtensionAt (j : J) : C(I × ClosedUnitBall E, DiskAttachment r₀) :=
  ballHomotopyExtension
    ⟨fun x => cell r₀ (boundaryFamilyInclusion J E) ⟨j, x⟩,
      (cell_continuous _ _).comp
        (continuous_sigmaMk («σ» := fun _ : J => ClosedUnitBall E) (i := j))⟩
    ⟨fun ta => old r₀ (boundaryFamilyInclusion J E) (H (ta.1, ⟨j, ta.2⟩)),
      (old_continuous _ _).comp (H.continuous.comp
        (continuous_fst.prodMk
          ((continuous_sigmaMk («σ» := fun _ : J => UnitBoundary E) (i := j)).comp
            continuous_snd)))⟩
    (naturalDiskBoundaryStart r₀ r₁ H j)

def naturalDiskExtension : C(I × DiskFamily J E, DiskAttachment r₀) :=
  (⟨fun z : Σ _ : J, I × ClosedUnitBall E => naturalDiskExtensionAt r₀ r₁ H z.1 z.2,
    continuous_sigma (fun j => (naturalDiskExtensionAt r₀ r₁ H j).continuous)⟩ :
      C((Σ _ : J, I × ClosedUnitBall E), DiskAttachment r₀)).comp
    (sigmaCylinderHomeomorph (D := fun _ : J => ClosedUnitBall E)).symm.toContinuousMap

theorem naturalDiskExtension_zero (d : DiskFamily J E) :
    naturalDiskExtension r₀ r₁ H (0, d) = cell r₀ (boundaryFamilyInclusion J E) d := by
  change naturalDiskExtensionAt r₀ r₁ H d.1 (0, d.2) = _
  unfold naturalDiskExtensionAt
  rw [ballHomotopyExtension_zero]
  rfl

theorem naturalDiskExtension_boundary (t : I) (a : BoundaryFamily J E) :
    naturalDiskExtension r₀ r₁ H (t, boundaryFamilyInclusion J E a) =
      old r₀ (boundaryFamilyInclusion J E) (H (t, a)) := by
  change naturalDiskExtensionAt r₀ r₁ H a.1 (t, unitBoundaryInclusion E a.2) = _
  unfold naturalDiskExtensionAt
  rw [ballHomotopyExtension_boundary]
  rfl

def naturalDiskBackward : C(DiskAttachment r₁, DiskAttachment r₀) :=
  desc r₁ (boundaryFamilyInclusion J E)
    ⟨old r₀ (boundaryFamilyInclusion J E), old_continuous _ _⟩
    ((naturalDiskExtension r₀ r₁ H).comp
      ⟨fun d => (1, d), continuous_const.prodMk continuous_id⟩)
    (fun a => by
      change old r₀ (boundaryFamilyInclusion J E) (r₁ a) =
        naturalDiskExtension r₀ r₁ H (1, boundaryFamilyInclusion J E a)
      rw [naturalDiskExtension_boundary, H.apply_one])

@[simp] theorem naturalDiskBackward_old (x : X) :
    naturalDiskBackward r₀ r₁ H (old r₁ (boundaryFamilyInclusion J E) x) =
      old r₀ (boundaryFamilyInclusion J E) x := rfl

@[simp] theorem naturalDiskBackward_cell (d : DiskFamily J E) :
    naturalDiskBackward r₀ r₁ H (cell r₁ (boundaryFamilyInclusion J E) d) =
      naturalDiskExtension r₀ r₁ H (1, d) := by
  unfold naturalDiskBackward
  rw [desc_cell]
  rfl

variable (s₀ s₁ : C(BoundaryFamily K E, Y)) (G : s₀.Homotopy s₁)
  (f : C(X, Y)) (i : J → K)
  (h₀ : ∀ j a, f (r₀ ⟨j, a⟩) = s₀ ⟨i j, a⟩)
  (h₁ : ∀ j a, f (r₁ ⟨j, a⟩) = s₁ ⟨i j, a⟩)
  (hH : ∀ t j a, f (H (t, ⟨j, a⟩)) = G (t, ⟨i j, a⟩))

include hH in
theorem naturalDiskExtension_natural (t : I) (j : J) (x : ClosedUnitBall E) :
    diskFamilyMap r₀ s₀ f i h₀ (naturalDiskExtension r₀ r₁ H (t, ⟨j, x⟩)) =
      naturalDiskExtension s₀ s₁ G (t, ⟨i j, x⟩) := by
  apply ballHomotopyExtension_natural (diskFamilyMap r₀ s₀ f i h₀) _ _ _ _
    (naturalDiskBoundaryStart r₀ r₁ H j) (naturalDiskBoundaryStart s₀ s₁ G (i j))
  · intro d
    exact diskFamilyMap_cell r₀ s₀ f i h₀ j d
  · intro τ a
    change diskFamilyMap r₀ s₀ f i h₀
      (old r₀ (boundaryFamilyInclusion J E) (H (τ, ⟨j, a⟩))) =
        old s₀ (boundaryFamilyInclusion K E) (G (τ, ⟨i j, a⟩))
    rw [diskFamilyMap_old, hH]

include hH in
theorem naturalDiskBackward_natural :
    (diskFamilyMap r₀ s₀ f i h₀).comp (naturalDiskBackward r₀ r₁ H) =
      (naturalDiskBackward s₀ s₁ G).comp (diskFamilyMap r₁ s₁ f i h₁) := by
  apply hom_ext r₁ (boundaryFamilyInclusion J E)
  · intro x
    rfl
  · rintro ⟨j, x⟩
    dsimp only [ContinuousMap.comp_apply]
    rw [naturalDiskBackward_cell, naturalDiskExtension_natural r₀ r₁ H s₀ s₁ G f i h₀ hH,
      diskFamilyMap_cell, naturalDiskBackward_cell]

end FiniteChains.RelativeAttachment

namespace FiniteChains.RelativeAttachment
open scoped Classical Topology unitInterval ContinuousMap
variable {J E X : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace X]

def naturalDiskReparam (r : C(BoundaryFamily J E, X)) :=
  attachmentBoundaryReparam r (boundaryFamilyInclusion J E)
    (boundaryFamilyInclusion_isClosedEmbedding J E).injective
    (diskFamilyBoundarySet J E) (diskFamilyBoundaryHomeomorph J E) (fun _ => rfl)

def naturalSubspaceExtension (r₀ r₁ : C(BoundaryFamily J E, X)) (H : r₀.Homotopy r₁) :
    C(I × DiskFamily J E,
      Space (r₀ ∘ (diskFamilyBoundaryHomeomorph J E).symm) Subtype.val) :=
  (naturalDiskReparam r₀).toContinuousMap.comp (naturalDiskExtension r₀ r₁ H)

theorem naturalSubspaceExtension_zero (r₀ r₁ : C(BoundaryFamily J E, X))
    (H : r₀.Homotopy r₁) (d : DiskFamily J E) :
    naturalSubspaceExtension r₀ r₁ H (0, d) =
      cell (r₀ ∘ (diskFamilyBoundaryHomeomorph J E).symm) Subtype.val d := by
  change naturalDiskReparam r₀ (naturalDiskExtension r₀ r₁ H (0, d)) = _
  rw [naturalDiskExtension_zero]
  exact attachmentBoundaryReparam_cell ..

theorem naturalSubspaceExtension_side (r₀ r₁ : C(BoundaryFamily J E, X))
    (H : r₀.Homotopy r₁) (t : I) (a : diskFamilyBoundarySet J E) :
    naturalSubspaceExtension r₀ r₁ H (t, a.val) =
      old (r₀ ∘ (diskFamilyBoundaryHomeomorph J E).symm) Subtype.val
        ((H.compContinuousMap (diskFamilyBoundaryHomeomorph J E).symm.toContinuousMap) (t, a)) := by
  let b := diskFamilyBoundaryHomeomorph J E
  have ha : boundaryFamilyInclusion J E (b.symm a) = a.val :=
    congrArg Subtype.val (b.apply_symm_apply a)
  change naturalDiskReparam r₀ (naturalDiskExtension r₀ r₁ H (t, a.val)) = _
  rw [← ha, naturalDiskExtension_boundary]
  rfl

def naturalDiskAttachingEquiv (r₀ r₁ : C(BoundaryFamily J E, X))
    (H : r₀.Homotopy r₁) : DiskAttachment r₀ ≃ₕ DiskAttachment r₁ :=
  let b := diskFamilyBoundaryHomeomorph J E
  let e := attachingHomotopyEquivOfExtensions (diskFamilyBoundarySet J E)
    (r₀.comp b.symm.toContinuousMap) (r₁.comp b.symm.toContinuousMap)
    (H.compContinuousMap b.symm.toContinuousMap)
    (naturalSubspaceExtension r₀ r₁ H) (naturalSubspaceExtension r₁ r₀ H.symm)
    (naturalSubspaceExtension_zero r₀ r₁ H) (naturalSubspaceExtension_zero r₁ r₀ H.symm)
    (naturalSubspaceExtension_side r₀ r₁ H) (naturalSubspaceExtension_side r₁ r₀ H.symm)
    (diskFamilyBoundarySet_isClosed J E) (diskFamilyFullCylinder_hasHomotopyExtension E J)
  ((naturalDiskReparam r₀).toHomotopyEquiv.trans e).trans
    (naturalDiskReparam r₁).symm.toHomotopyEquiv

theorem naturalDiskAttachingEquiv_toFun (r₀ r₁ : C(BoundaryFamily J E, X))
    (H : r₀.Homotopy r₁) :
    (naturalDiskAttachingEquiv r₀ r₁ H).toFun = naturalDiskBackward r₁ r₀ H.symm := by
  apply hom_ext r₀ (boundaryFamilyInclusion J E)
  · intro x
    rfl
  · intro d
    let b := diskFamilyBoundaryHomeomorph J E
    change (naturalDiskReparam r₁).symm
      (chosenAttachingForward (diskFamilyBoundarySet J E)
        (r₀.comp b.symm.toContinuousMap) (r₁.comp b.symm.toContinuousMap)
        (H.compContinuousMap b.symm.toContinuousMap)
        (naturalSubspaceExtension r₁ r₀ H.symm)
        (naturalSubspaceExtension_side r₁ r₀ H.symm)
        (naturalDiskReparam r₀ (cell r₀ (boundaryFamilyInclusion J E) d))) = _
    rw [show naturalDiskReparam r₀ (cell r₀ (boundaryFamilyInclusion J E) d) =
      cell (r₀ ∘ (diskFamilyBoundaryHomeomorph J E).symm) Subtype.val d
        from attachmentBoundaryReparam_cell ..]
    change (naturalDiskReparam r₁).symm (desc _ _ _ _ _ (cell _ _ d)) = _
    rw [desc_cell]
    change (naturalDiskReparam r₁).symm
      (naturalDiskReparam r₁ (naturalDiskExtension r₁ r₀ H.symm (1, d))) = _
    rw [Homeomorph.symm_apply_apply, naturalDiskBackward_cell]


theorem naturalDiskAttachingEquiv_natural
    {K Y : Type} [TopologicalSpace Y]
    (r₀ r₁ : C(BoundaryFamily J E, X)) (H : r₀.Homotopy r₁)
    (s₀ s₁ : C(BoundaryFamily K E, Y)) (G : s₀.Homotopy s₁)
    (f : C(X, Y)) (i : J → K)
    (h₀ : ∀ j a, f (r₀ ⟨j, a⟩) = s₀ ⟨i j, a⟩)
    (h₁ : ∀ j a, f (r₁ ⟨j, a⟩) = s₁ ⟨i j, a⟩)
    (hH : ∀ t j a, f (H (t, ⟨j, a⟩)) = G (t, ⟨i j, a⟩)) :
    (diskFamilyMap r₁ s₁ f i h₁).comp (naturalDiskAttachingEquiv r₀ r₁ H).toFun =
      (naturalDiskAttachingEquiv s₀ s₁ G).toFun.comp (diskFamilyMap r₀ s₀ f i h₀) := by
  rw [naturalDiskAttachingEquiv_toFun, naturalDiskAttachingEquiv_toFun]
  exact naturalDiskBackward_natural r₁ r₀ H.symm s₁ s₀ G.symm f i h₁ h₀
    (fun t j a => hH (unitInterval.symm t) j a)

end FiniteChains.RelativeAttachment

namespace FiniteChains.Comb
open CategoryTheory TopologicalSingular SingularSubdivision
variable {P : Type} [PartialOrder P]

/-- Realization of the carried small-chain approximation in every degree. -/
def orderSmallSingularApproximation (P : Type) [PartialOrder P] (n : ℕ) :
    smallChains (orderNerveRealizationOpenStar P) n →ₗ[ℤ] Chain (orderNerveRealization P) n :=
  (orderNerveGradedRealize P n).comp (orderSmallToNerve P n)

theorem orderSmallSingularApproximation_boundary (n : ℕ)
    (c : smallChains (orderNerveRealizationOpenStar P) (n + 1)) :
    boundary n (orderSmallSingularApproximation P (n + 1) c) =
      orderSmallSingularApproximation P n (smallBoundary (orderNerveRealizationOpenStar P) n c) := by
  erw [orderNerveGradedRealize_boundary n (orderSmallToNerve_mem_inc (n + 1) c),
    orderSmallToNerve_boundary]
  rfl

theorem orderSmallSingularApproximation_carrier (n : ℕ) (σ : OrderSmallSimplex P n) :
    orderSmallSingularApproximation P n (orderSmallSingle σ 1) ∈
      orderSingularCarrierChains σ.val n :=
  orderNerveGradedRealize_supported n _ (orderSmallToNerve_carrier n σ)

theorem orderSmallSingularApproximation_zero :
    orderSmallSingularApproximation P 0 = orderSmallSingularApproximation0 := by
  apply orderSmallSingle_spans
  intro σ
  change orderNerveGradedRealize P 0 (orderSmallToNerve0 (orderSmallSingle σ 1)) = _
  erw [orderSmallToNerve0_single, one_smul, orderSmallSingularApproximation0_single]
  have hl : orderNerveVertexList (ComposableArrows.mk₀ (orderSmallChosenVertex σ)) =
      [orderSmallChosenVertex σ] := by simp [orderNerveVertexList, List.ofFn_succ]
  change (orderNerveExplicitSingularMap P).f 0
    (orderNerveGradedDecode 0 (FreeAbelianGroup.of [orderSmallChosenVertex σ])) = _
  erw [orderNerveGradedDecode_of, ← hl, orderNerveGradedDecodeList_vertexList,
    orderNerveExplicitSingularMap_single]
  rfl

end FiniteChains.Comb

namespace FiniteChains.Comb
open TopologicalSingular SingularSubdivision
variable {P : Type} [PartialOrder P]

/-- Carried homotopy data, with the identity on boundaries needed for extension. -/
structure OrderSmallHomotopyStage (P : Type) [PartialOrder P] (n : ℕ) where
  map : smallChains (orderNerveRealizationOpenStar P) n →ₗ[ℤ]
    Chain (orderNerveRealization P) (n + 1)
  carrier : ∀ σ : OrderSmallSimplex P n,
    map (orderSmallSingle σ 1) ∈ orderSingularCarrierChains σ.val (n + 1)
  on_boundary : ∀ c : smallChains (orderNerveRealizationOpenStar P) (n + 1),
    boundary n (map (smallBoundary (orderNerveRealizationOpenStar P) n c)) =
      boundary n c.val - orderSmallSingularApproximation P n
        (smallBoundary (orderNerveRealizationOpenStar P) n c)

def orderSmallHomotopyStageZero : OrderSmallHomotopyStage P 0 where
  map := orderSmallHomotopy0
  carrier := orderSmallHomotopy0_carrier
  on_boundary c := by
    rw [orderSmallHomotopy0_boundary, orderSmallSingularApproximation_zero]
    rfl

theorem orderSmallHomotopyStage_fill {n : ℕ} (s : OrderSmallHomotopyStage P n)
    (σ : OrderSmallSimplex P (n + 1)) :
    ∃ b : Chain (orderNerveRealization P) (n + 2),
      b ∈ orderSingularCarrierChains σ.val (n + 2) ∧
      boundary (n + 1) b = Finsupp.single σ.val 1 -
        orderSmallSingularApproximation P (n + 1) (orderSmallSingle σ 1) -
        s.map (smallBoundary (orderNerveRealizationOpenStar P) n (orderSmallSingle σ 1)) := by
  apply orderSingularCarrierChains_cycle_bounds σ.val σ.property n
  · exact Submodule.sub_mem _
      (Submodule.sub_mem _ (orderSingularCarrierChains_single σ.val 1)
        (orderSmallSingularApproximation_carrier (n + 1) σ))
      (orderSmallBoundary_map_carrier s.map s.carrier σ)
  · rw [map_sub, map_sub, orderSmallSingularApproximation_boundary, s.on_boundary]
    exact sub_self _

def orderSmallHomotopyStageNextMap {n : ℕ} (s : OrderSmallHomotopyStage P n) :
    smallChains (orderNerveRealizationOpenStar P) (n + 1) →ₗ[ℤ]
      Chain (orderNerveRealization P) (n + 2) :=
  (Finsupp.linearCombination ℤ (fun σ => (orderSmallHomotopyStage_fill s σ).choose)).comp
    (orderSmallChainEquiv P (n + 1)).toLinearMap

theorem orderSmallHomotopyStageNextMap_single {n : ℕ} (s : OrderSmallHomotopyStage P n)
    (σ : OrderSmallSimplex P (n + 1)) :
    orderSmallHomotopyStageNextMap s (orderSmallSingle σ 1) =
      (orderSmallHomotopyStage_fill s σ).choose := by
  have he := (orderSmallChainEquiv P (n + 1)).apply_symm_apply (Finsupp.single σ 1)
  rw [orderSmallChainEquiv_symm_single] at he
  change (Finsupp.linearCombination ℤ (fun τ : OrderSmallSimplex P (n + 1) =>
    (orderSmallHomotopyStage_fill s τ).choose))
      ((orderSmallChainEquiv P (n + 1)) (orderSmallSingle σ 1)) = _
  simp_all

theorem orderSmallHomotopyStageNextMap_boundary {n : ℕ} (s : OrderSmallHomotopyStage P n)
    (c : smallChains (orderNerveRealizationOpenStar P) (n + 1)) :
    boundary (n + 1) (orderSmallHomotopyStageNextMap s c) =
      c.val - orderSmallSingularApproximation P (n + 1) c -
        s.map (smallBoundary (orderNerveRealizationOpenStar P) n c) := by
  have he : (boundary (n + 1)).comp (orderSmallHomotopyStageNextMap s) =
      (smallChains (orderNerveRealizationOpenStar P) (n + 1)).subtype -
        orderSmallSingularApproximation P (n + 1) -
        s.map.comp (smallBoundary (orderNerveRealizationOpenStar P) n) := by
    apply orderSmallSingle_spans
    intro σ
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, orderSmallHomotopyStageNextMap_single]
    exact (orderSmallHomotopyStage_fill s σ).choose_spec.2
  exact DFunLike.congr_fun he c

def orderSmallHomotopyStageNext {n : ℕ} (s : OrderSmallHomotopyStage P n) :
    OrderSmallHomotopyStage P (n + 1) where
  map := orderSmallHomotopyStageNextMap s
  carrier σ := by
    rw [orderSmallHomotopyStageNextMap_single]
    exact (orderSmallHomotopyStage_fill s σ).choose_spec.1
  on_boundary c := by
    rw [orderSmallHomotopyStageNextMap_boundary]
    have hd := DFunLike.congr_fun (smallBoundary_squared (orderNerveRealizationOpenStar P) n) c
    change smallBoundary (orderNerveRealizationOpenStar P) n
      (smallBoundary (orderNerveRealizationOpenStar P) (n + 1) c) = 0 at hd
    rw [hd, map_zero, sub_zero]
    rfl

def orderSmallHomotopyStage (P : Type) [PartialOrder P] :
    (n : ℕ) → OrderSmallHomotopyStage P n
  | 0 => orderSmallHomotopyStageZero
  | n + 1 => orderSmallHomotopyStageNext (orderSmallHomotopyStage P n)

def orderSmallHomotopy (P : Type) [PartialOrder P] (n : ℕ) :
    smallChains (orderNerveRealizationOpenStar P) n →ₗ[ℤ]
      Chain (orderNerveRealization P) (n + 1) :=
  (orderSmallHomotopyStage P n).map

/-- A carried chain homotopy from the realized approximation to inclusion, in every degree. -/
theorem orderSmallHomotopy_boundary (n : ℕ)
    (c : smallChains (orderNerveRealizationOpenStar P) (n + 1)) :
    boundary (n + 1) (orderSmallHomotopy P (n + 1) c) =
      c.val - orderSmallSingularApproximation P (n + 1) c -
        orderSmallHomotopy P n (smallBoundary (orderNerveRealizationOpenStar P) n c) :=
  orderSmallHomotopyStageNextMap_boundary (orderSmallHomotopyStage P n) c

theorem orderSmallSingularApproximation_homologous (n : ℕ)
    (c : smallChains (orderNerveRealizationOpenStar P) (n + 1))
    (hc : smallBoundary (orderNerveRealizationOpenStar P) n c = 0) :
    ∃ b : Chain (orderNerveRealization P) (n + 2),
      boundary (n + 1) b = c.val - orderSmallSingularApproximation P (n + 1) c := by
  refine ⟨orderSmallHomotopy P (n + 1) c, ?_⟩
  rw [orderSmallHomotopy_boundary, hc, map_zero, sub_zero]

end FiniteChains.Comb

namespace FiniteChains.Comb
open CategoryTheory TopologicalSingular SingularSubdivision
variable {P : Type} [PartialOrder P]

/-- Every positive-degree singular cycle has a homogeneous order-chain representative. -/
theorem orderNerveRealization_cycle_nerveRepresentative (n : ℕ)
    (c : Chain (orderNerveRealization P) (n + 1)) (hc : boundary n c = 0) :
    ∃ z : Nerve.Ch P, z ∈ Nerve.Inc P ∧ Nerve.lengthProjection (n + 2) z = z ∧
      Nerve.bdry z = 0 ∧ ∃ b : Chain (orderNerveRealization P) (n + 2),
        boundary (n + 1) b = c - orderNerveGradedRealize P (n + 1) z := by
  obtain ⟨d, hd, hz, a, ha⟩ := orderNerveRealization_exists_small_cycle P n c hc
  let d' : smallChains (orderNerveRealizationOpenStar P) (n + 1) := ⟨d, hd⟩
  have hd' : smallBoundary (orderNerveRealizationOpenStar P) n d' = 0 := Subtype.ext hz
  obtain ⟨b, hb⟩ := orderSmallSingularApproximation_homologous n d' hd'
  refine ⟨orderSmallToNerve P (n + 1) d', orderSmallToNerve_mem_inc _ _,
    orderSmallToNerve_length _ _, ?_, b - a, ?_⟩
  · rw [orderSmallToNerve_boundary, hd', map_zero]
  · rw [map_sub, hb, ha]
    change d - orderNerveGradedRealize P (n + 1) (orderSmallToNerve P (n + 1) d') - (d - c) = _
    abel

end FiniteChains.Comb

namespace FiniteChains.Comb
open CategoryTheory AlgebraicTopology TopologicalSingular


/-- The canonical realized-simplex map computes the actual positive integral
singular homology of every order-nerve realization, without finiteness assumptions. -/

def orderNervePositiveSingularHomologyIso (P : Type) [PartialOrder P] (n : ℕ) :
    (AlternatingFaceMapComplex.obj (mathlibOrderNerveModule P)).homology (n + 1) ≅
      (((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 1)).obj (ModuleCat.of ℤ ℤ)).obj
        (orderNerveRealization P)) := by
  letI := (show IsIso (HomologicalComplex.homologyMap (orderNerveExplicitSingularMap P) (n + 1)) by
    letI := orderNerveExplicitSingularHomology_mono P n
    letI := (show Epi (HomologicalComplex.homologyMap (orderNerveExplicitSingularMap P) (n + 1)) by
      unfold HomologicalComplex.homologyMap HomologicalComplex.shortComplexFunctor
      apply shortComplex_homologyMap_epi_of_representatives
      intro c hc
      change (complex (orderNerveRealization P)).d (n + 1)
        ((ComplexShape.down ℕ).next (n + 1)) c = 0 at hc
      erw [ChainComplex.next_nat_succ, complex_d] at hc
      obtain ⟨z, hz, _, hz0, b, hb⟩ := orderNerveRealization_cycle_nerveRepresentative n c hc
      refine ⟨orderNerveGradedDecode (n + 1) z, ?_, ?_⟩
      · change (AlternatingFaceMapComplex.obj (mathlibOrderNerveModule P)).d (n + 1)
          ((ComplexShape.down ℕ).next (n + 1)) _ = 0
        erw [ChainComplex.next_nat_succ, AlternatingFaceMapComplex.obj_d_eq]
        apply orderNerveGradedEncode_injective n
        erw [orderNerveGradedEncode_boundary, orderNerveGradedEncode_decode _ hz,
          ← Nerve.lengthProjection_bdry, hz0, map_zero]
      · change ∃ a : (complex (orderNerveRealization P)).X ((ComplexShape.down ℕ).prev (n + 1)),
          (complex (orderNerveRealization P)).d ((ComplexShape.down ℕ).prev (n + 1)) (n + 1) a = _
        erw [ChainComplex.prev]
        refine ⟨b, ?_⟩
        erw [complex_d]
        exact hb)
    exact isIso_of_mono_of_epi _)
  exact asIso (HomologicalComplex.homologyMap (orderNerveExplicitSingularMap P) (n + 1)) ≪≫
    homologyMathlibIso (orderNerveRealization P) (n + 1)

end FiniteChains.Comb

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
  AlgebraicTopology Simplicial

/-- The normalization projector annihilates every degree in which all simplices
are degenerate. This is a statement about the actual free simplicial module. -/
theorem freeSSet_PInfty_eq_zero (X : SSet) (d n : ℕ)
    [X.HasDimensionLT d] (hn : d ≤ n) :
    (DoldKan.PInfty (X := X ⋙ ModuleCat.free ℤ)).f n = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  change ((DoldKan.PInfty (X := X ⋙ ModuleCat.free ℤ)).f n).hom c = 0
  induction c using Finsupp.induction_linear with
  | zero => exact map_zero _
  | add c e hc he => erw [map_add, hc, he, add_zero]
  | single s r =>
    have hs : s ∈ X.degenerate n := by
      erw [X.degenerate_eq_top_of_hasDimensionLT d n hn]
      trivial
    obtain ⟨m, hm, θ, y, rfl⟩ := hs
    have hθ : ¬ Mono θ := by
      intro hθ
      exact (not_le_of_gt hm) (SimplexCategory.len_le_of_mono θ)
    have h := DoldKan.degeneracy_comp_PInfty (X ⋙ ModuleCat.free ℤ) n θ hθ
    have hv := congrArg (fun f => f.hom (Finsupp.single y r)) h
    simpa [ModuleCat.free] using hv

/-- Homology of the alternating-face complex vanishes above simplicial dimension. -/
theorem freeSSet_homology_isZero_of_dimension (X : SSet) (d n : ℕ)
    [X.HasDimensionLT d] (hn : d ≤ n) :
    Limits.IsZero ((AlternatingFaceMapComplex.obj (X ⋙ ModuleCat.free ℤ)).homology n) := by
  let K := AlternatingFaceMapComplex.obj (X ⋙ ModuleCat.free ℤ)
  let p : K ⟶ K := DoldKan.PInfty
  have hp  := freeSSet_PInfty_eq_zero X d n hn
  have hz : HomologicalComplex.homologyMap p n = 0 := by
    erw [← cancel_epi (K.homologyπ n), HomologicalComplex.homologyπ_naturality,
      comp_zero]
    have hc : HomologicalComplex.cyclesMap p n = 0 := by
      erw [← cancel_mono (K.iCycles n), HomologicalComplex.cyclesMap_i, hp,
        zero_comp, comp_zero]
    erw [hc, zero_comp]
  apply (IsZero.iff_id_eq_zero _).mpr
  have hh := (DoldKan.homotopyPInftyToId (X ⋙ ModuleCat.free ℤ)).homologyMap_eq n
  erw [HomologicalComplex.homologyMap_id] at hh
  exact hh.symm.trans hz

/-- The dimension bound controls the precise singular homology used in Challenge. -/
theorem orderNerve_singularHomology_isZero_of_dimension (P : Type) [PartialOrder P]
    (d n : ℕ) [(nerve P).HasDimensionLE d] (hn : d < n) :
    Limits.IsZero (((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
      (ModuleCat.of ℤ ℤ)).obj (orderNerveRealization P)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt (Nat.zero_le d |>.trans_lt hn))
  exact (freeSSet_homology_isZero_of_dimension (nerve P) (d + 1) (k + 1) hn).of_iso
    (orderNervePositiveSingularHomologyIso P k).symm

end FiniteChains.Comb
end

namespace FiniteChains.Comb
open CategoryTheory AlgebraicTopology TopologicalSingular
variable (P : Type) [PartialOrder P]

/-- In dimension two the first and second actual singular homology groups
are the only positive-degree obstructions to the acyclicity in Challenge. -/
theorem orderRealization_acyclic_iff_homology_one_two [(nerve P).HasDimensionLE 2] :
    Whitehead.Acyclic (orderNerveRealization P) ↔
      Limits.IsZero (((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
        (ModuleCat.of ℤ ℤ)).obj (orderNerveRealization P)) ∧
      Limits.IsZero (((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
        (ModuleCat.of ℤ ℤ)).obj (orderNerveRealization P)) := by
  constructor
  · intro h
    exact ⟨h 1 (by decide), h 2 (by decide)⟩
  · rintro ⟨h1, h2⟩ n hn
    by_cases he1 : n = 1
    · subst n
      exact h1
    by_cases he2 : n = 2
    · subst n
      exact h2
    exact orderNerve_singularHomology_isZero_of_dimension P 2 n (by omega)

/-- Genuine finite fillings in the order nerve annihilate actual singular H2. -/
theorem orderRealization_homology_two_isZero_of_fillings
    (hfill : ∀ c : OrdTri P →₀ ℤ, bdry2 (orderCx P) c = 0 →
      ∃ b : OrdTet P →₀ ℤ, ordBoundary3 b = c) :
    Limits.IsZero (((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
      (ModuleCat.of ℤ ℤ)).obj (orderNerveRealization P)) := by
  have hz (z : OrderNerveH2 P) : z = 0 := by
    induction z using Submodule.Quotient.induction_on with
    | H c =>
      exact (orderNerveH2Class_eq_zero_iff P c.val c.property).mpr
        (hfill c.val c.property)
  letI : Subsingleton (OrderNerveH2 P) := ⟨fun x y => (hz x).trans (hz y).symm⟩
  letI := (orderCellSingularH2Equiv P).surjective.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

/-- The weak nerve's degenerate chains introduce no extra H2 obstruction. -/
theorem orderRealization_homology_two_isZero_of_strict_cycles_zero
    (hz : ∀ c : StrictOrdTri P →₀ ℤ, bdry2 (strictOrderCx P) c = 0 → c = 0) :
    Limits.IsZero (((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
      (ModuleCat.of ℤ ℤ)).obj (orderNerveRealization P)) := by
  apply orderRealization_homology_two_isZero_of_fillings P
  apply weak_twoCycle_filling_of_strict
  intro c hc
  exact ⟨0, by rw [map_zero, hz c hc]⟩

end FiniteChains.Comb

namespace FiniteChains.Comb
open CategoryTheory AlgebraicTopology TopologicalSingular Topology
variable {P Q : Type} [PartialOrder P] [PartialOrder Q]

/-- Actual strict edge-cycle fillings give genuine singular one-cycle fillings. -/
theorem orderRealization_oneCycle_bounds_of_strict_fillings
    (hfill : ∀ c : StrictOrdEdge P →₀ ℤ, bdry1 (strictOrderCx P) c = 0 →
      ∃ b : StrictOrdTri P →₀ ℤ, bdry2 (strictOrderCx P) b = c)
    (c : Chain (orderNerveRealization P) 1) (hc : boundary 0 c = 0) :
    ∃ b : Chain (orderNerveRealization P) 2, boundary 1 b = c := by
  obtain ⟨z, hz, hd, hz0, b, hb⟩ := orderNerveRealization_cycle_nerveRepresentative 0 c hc
  obtain ⟨a, ha, ha0⟩ := nerve_oneCycle_filling_of_strict hfill z hz hd hz0
  refine ⟨b + orderNerveGradedRealize P 2 a, ?_⟩
  rw [map_add, hb, orderNerveGradedRealize_boundary 1 ha, ha0]
  abel

theorem orderRealization_homology_one_isZero_of_strict_fillings
    (hfill : ∀ c : StrictOrdEdge P →₀ ℤ, bdry1 (strictOrderCx P) c = 0 →
      ∃ b : StrictOrdTri P →₀ ℤ, bdry2 (strictOrderCx P) b = c) :
    Limits.IsZero (((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)).obj (orderNerveRealization P)) := by
  have he : (complex (orderNerveRealization P)).ExactAt 1 := by
    rw [HomologicalComplex.exactAt_iff' (K := complex (orderNerveRealization P))
      (i := 2) (j := 1) (k := 0) (ChainComplex.prev ℕ 1) (ChainComplex.next_nat_succ 0)]
    apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro c hc
    change (complex (orderNerveRealization P)).d 1 0 c = 0 at hc
    rw [complex_d] at hc
    change ∃ b : Chain (orderNerveRealization P) 2,
      (complex (orderNerveRealization P)).d 2 1 b = c
    rw [complex_d]
    exact orderRealization_oneCycle_bounds_of_strict_fillings hfill c hc
  exact he.isZero_homology.of_iso (homologyMathlibIso (orderNerveRealization P) 1).symm

/-- Acyclicity of the actual strict cellular complex implies the exact singular
acyclicity of Challenge, for every two-dimensional order realization. -/
theorem orderRealization_acyclic_of_strict_isAcyclic [(nerve P).HasDimensionLE 2]
    (hP : IsAcyclic (strictOrderCx P)) : Whitehead.Acyclic (orderNerveRealization P) := by
  apply (orderRealization_acyclic_iff_homology_one_two P).mpr
  refine ⟨orderRealization_homology_one_isZero_of_strict_fillings hP.h1,
    orderRealization_homology_two_isZero_of_strict_cycles_zero P ?_⟩
  intro c hc
  exact hP.h2 (hc.trans (map_zero _).symm)

namespace IsPosetCover

/-- A connected acyclic strict cellular cover with transitive order deck maps
realizes to a genuine acyclic regular cover. The cover need not be universal. -/
theorem hasAcyclicRegularCover [Nonempty Q] [(nerve Q).HasDimensionLE 2]
    {f : P → Q} (hf : IsPosetCover f)
    (hP : IsConnected (orderCx P)) (hQ : IsConnected (orderCx Q))
    (hdeck : ∀ v w : P, f v = f w →
      ∃ e : P ≃o P, (∀ p, f (e p) = f p) ∧ e v = w)
    (hacyc : IsAcyclic (strictOrderCx P)) :
    Whitehead.HasAcyclicRegularCover (orderNerveTwoComplex Q hQ) := by
  obtain ⟨q⟩ := (inferInstance : Nonempty Q)
  obtain ⟨p, _⟩ := hf.surj q
  letI : Nonempty P := ⟨p⟩
  letI := hf.realization_hasDimensionLE 2
  letI := orderNerveRealization_pathConnectedSpace P hP
  exact ⟨orderNerveRealization P, inferInstance,
    ⟨orderNerveRealizationMap f hf.mono, (orderNerveRealizationMap f hf.mono).hom.continuous⟩,
    hf.realizationMap_isCoveringMap, hf.realizationMap_surjective,
    inferInstance, hf.realizationMap_regular hdeck,
    orderRealization_acyclic_of_strict_isAcyclic hacyc⟩

end IsPosetCover
end FiniteChains.Comb

namespace FiniteChains.Comb
open CategoryTheory AlgebraicTopology
variable {P Q : Type} [PartialOrder P] [PartialOrder Q]

/-- The stated nerve dimension bound excludes actual strictly increasing tetrahedra. -/
theorem strictOrdTet_isEmpty_of_dimension_two [(nerve P).HasDimensionLE 2] :
    IsEmpty (StrictOrdTet P) := by
  refine ⟨fun t => ?_⟩
  let s := ordTetNerveEquiv P ⟨t.1, t.2.1.le, t.2.2.1.le, t.2.2.2.le⟩
  have hs : s ∈ (nerve P).nonDegenerate 3 := by
    apply (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono s).mpr
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i
    · exact t.2.1
    · exact t.2.2.1
    · exact t.2.2.2
  have hdim := (nerve P).dim_le_of_nonDegenerate ⟨s, hs⟩ 2
  omega

theorem normalizeOrdBoundary3_eq_zero_of_dimension_two [(nerve P).HasDimensionLE 2]
    (b : OrdTet P →₀ ℤ) : normalizeOrdChain2 (ordBoundary3 b) = 0 := by
  letI := strictOrdTet_isEmpty_of_dimension_two (P := P)
  erw [normalizeOrdChain2_ordBoundary3]
  have hz : normalizeOrdChain3 b = 0 := Subsingleton.elim _ _
  simp_all

end FiniteChains.Comb

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
namespace FiniteChains.Comb
open CategoryTheory AlgebraicTopology
variable {P : Type} [PartialOrder P]

/-- Zero actual singular H1 produces finite weak order-chain fillings. -/
theorem weak_oneCycle_filling_of_singular_homology_zero
    (hH : Limits.IsZero (((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)).obj (orderNerveRealization P)))
    (c : OrdEdge P →₀ ℤ) (hc : bdry1 (orderCx P) c = 0) :
    ∃ b : OrdTri P →₀ ℤ, bdry2 (orderCx P) b = c := by
  let K := AlternatingFaceMapComplex.obj (mathlibOrderNerveModule P)
  have he : K.ExactAt 1 := by
    apply (HomologicalComplex.exactAt_iff_isZero_homology K 1).mpr
    exact hH.of_iso (orderNervePositiveSingularHomologyIso P 0)
  rw [HomologicalComplex.exactAt_iff' (K := K) (i := 2) (j := 1) (k := 0)
    (ChainComplex.prev ℕ 1) (ChainComplex.next_nat_succ 0)] at he
  have hex := (ShortComplex.moduleCat_exact_iff _).mp he
  let z := ordNerveChain1 c
  have hz  := ordNerveChain1_mem_inc c
  have hlen  := ordNerveChain1_lengthProjection c
  have hz0  := (ordNerveChain1_cycle_iff c).mpr hc
  have hd : K.d 1 0 (orderNerveGradedDecode 1 z) = 0 := by
    erw [AlternatingFaceMapComplex.obj_d_eq]
    apply orderNerveGradedEncode_injective 0
    erw [map_zero, orderNerveGradedEncode_boundary,
      orderNerveGradedEncode_decode 1 hz, hlen, hz0]
  obtain ⟨a, ha⟩ := hex (orderNerveGradedDecode 1 z) hd
  change K.d 2 1 a = orderNerveGradedDecode 1 z at ha
  erw [AlternatingFaceMapComplex.obj_d_eq] at ha
  have haInc : orderNerveGradedEncode 2 a ∈ Nerve.Inc P := by
    clear ha
    induction a using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy => simpa using AddSubgroup.add_mem _ hx hy
    | single s r =>
      erw [orderNerveGradedEncode_single]
      exact AddSubgroup.zsmul_mem _ (Nerve.of_mem_inc (orderNerveVertexList_chain s)) r
  refine ⟨decodeOrdNerve2 (orderNerveGradedEncode 2 a), ?_⟩
  apply ordNerveChain1_injective
  erw [ordNerveChain1_bdry2,
    ordNerveChain2_decode haInc,
    orderNerveGradedEncode_length, ← orderNerveGradedEncode_boundary, ha,
    orderNerveGradedEncode_decode 1 hz, hlen]

/-- The genuine H1-zero condition is equivalent to strict cellular one-cycle
fillability; all maps between weak, normalized and singular chains are proved. -/
theorem orderRealization_homology_one_isZero_iff_strict_fillings :
    Limits.IsZero (((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)).obj (orderNerveRealization P)) ↔
      ∀ c : StrictOrdEdge P →₀ ℤ, bdry1 (strictOrderCx P) c = 0 →
        ∃ b : StrictOrdTri P →₀ ℤ, bdry2 (strictOrderCx P) b = c := by
  constructor
  · intro hH c hc
    have hd : bdry1 (orderCx P) (chain1 (strictOrderIncl P) c) = 0 := by
      erw [bdry1_chain1, hc, map_zero]
    obtain ⟨b, hb⟩ := weak_oneCycle_filling_of_singular_homology_zero hH _ hd
    refine ⟨normalizeOrdChain2 b, ?_⟩
    erw [bdry2_normalizeOrdChain2, hb]
    exact normalizeOrdChain1_inclusion c
  · exact orderRealization_homology_one_isZero_of_strict_fillings

/-- In dimension two a strict two-cycle can be zero in actual singular
homology only if every coefficient is zero. -/
theorem strict_twoCycle_eq_zero_of_singular_homology_zero [(nerve P).HasDimensionLE 2]
    (hH : Limits.IsZero (((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
      (ModuleCat.of ℤ ℤ)).obj (orderNerveRealization P)))
    (c : StrictOrdTri P →₀ ℤ) (hc : bdry2 (strictOrderCx P) c = 0) : c = 0 := by
  letI := ModuleCat.subsingleton_of_isZero hH
  have hi : bdry2 (orderCx P) (chain2 (strictOrderIncl P) c) = 0 := by
    erw [bdry2_chain2, hc, map_zero]
  have hz : orderNerveH2Class P (chain2 (strictOrderIncl P) c) hi = 0 := by
    apply (orderCellSingularH2Equiv P).injective
    exact Subsingleton.elim _ _
  obtain ⟨b, hb⟩ := (orderNerveH2Class_eq_zero_iff P _ hi).mp hz
  have hn := congrArg normalizeOrdChain2 hb
  erw [normalizeOrdBoundary3_eq_zero_of_dimension_two] at hn
  have he  :=
    normalizeOrdChain2_inclusion c
  exact (hn.trans he).symm

end FiniteChains.Comb
end

namespace FiniteChains.Comb
open CategoryTheory
variable (P : Type) [PartialOrder P] [Nonempty P] [(nerve P).HasDimensionLE 2]

/-- Exact comparison of actual singular acyclicity and the strict cellular
acyclicity predicate, for every connected two-dimensional order realization. -/
theorem orderRealization_acyclic_iff_strict_isAcyclic (hP : IsConnected (orderCx P)) :
    Whitehead.Acyclic (orderNerveRealization P) ↔ IsAcyclic (strictOrderCx P) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · apply (injective_iff_map_eq_zero (bdry2 (strictOrderCx P))).mpr
      exact strict_twoCycle_eq_zero_of_singular_homology_zero (h 2 (by decide))
    · exact orderRealization_homology_one_isZero_iff_strict_fillings.mp (h 1 (by decide))
    · exact strict_order_zeroCycle_filling_of_connected (P := P)
        (Classical.choice ‹Nonempty P›) hP
  · exact orderRealization_acyclic_of_strict_isAcyclic

end FiniteChains.Comb

namespace FiniteChains.Comb
open CategoryTheory Simplicial Topology
open scoped Classical
variable {P : Type} [PartialOrder P]

def orderReach (a : P) : Set P :=
  {b | ∃ p, IsPath (orderCx P).src (orderCx P).tgt p a b}

theorem orderReach_le_iff (a : P) {b c : P} (h : b ≤ c) :
    b ∈ orderReach a ↔ c ∈ orderReach a := by
  let e : (orderCx P).E := ⟨(b, c), h⟩
  constructor
  · rintro ⟨p, hp⟩
    have hs : IsPath (orderCx P).src (orderCx P).tgt [(e, true)] b c := ⟨rfl, rfl⟩
    exact ⟨p ++ [(e, true)], hp.append hs⟩
  · rintro ⟨p, hp⟩
    have hs : IsPath (orderCx P).src (orderCx P).tgt [(e, false)] c b := ⟨rfl, rfl⟩
    exact ⟨p ++ [(e, false)], hp.append hs⟩

theorem orderNerveRealizationSubcomplex_isClosed (A : Set P) :
    IsClosed (orderNerveRealizationSubcomplex P A : Set (orderNerveRealization P)) := by
  rw [← orderNerveRealizationSubtype_range A]
  exact (orderNerveRealizationSubtype_isClosedEmbedding A).isClosed_range


theorem orderCx_isConnected_of_realization [PreconnectedSpace (orderNerveRealization P)] :
    IsConnected (orderCx P) := by
  intro a b
  change P at a b
  let A := orderNerveRealizationSubcomplex P (orderReach a)
  have ha  :=
    (orderNerveRealizationVertex_mem_subcomplex (orderReach a) a).mpr ⟨[], rfl⟩
  have hopen : IsOpen (A : Set (orderNerveRealization P)) := by
    apply isClosed_compl_iff.mp
    rw [(show (orderNerveRealizationSubcomplex P (orderReach a) : Set (orderNerveRealization P))ᶜ =
      orderNerveRealizationSubcomplex P (orderReach a)ᶜ by
      let A := orderReach a
      have hcover : ∀ x : orderNerveRealization P,
          x ∈ orderNerveRealizationSubcomplex P A ∨
            x ∈ orderNerveRealizationSubcomplex P Aᶜ := by
        intro x
        obtain ⟨n, s, z, rfl⟩ := orderNerveRealizationSimplex_jointly_surjective P x
        have hm  := fun i =>
          orderReach_le_iff a (leOfHom (s.map (homOfLE (Fin.zero_le i))))
        by_cases h : s.obj 0 ∈ A
        · exact Or.inl (orderNerveRealizationSimplex_supported A s
            (fun i => (hm i).mp h) ⟨z, rfl⟩)
        · exact Or.inr (orderNerveRealizationSimplex_supported Aᶜ s
            (fun i hi => h ((hm i).mpr hi)) ⟨z, rfl⟩)
      have hdisjoint : ∀ x : orderNerveRealization P,
          x ∈ orderNerveRealizationSubcomplex P A →
          x ∈ orderNerveRealizationSubcomplex P Aᶜ → False := by
        intro x hx hy
        obtain ⟨v, hv⟩ := orderNerveRealizationOpenStar_cover P x
        have hzero : orderNerveRealizationCoordinates P x v = 0 := by
          by_cases h : v ∈ A
          · exact hy v (by simpa using h)
          · exact hx v h
        change 0 < orderNerveRealizationCoordinates P x v at hv
        rw [hzero] at hv
        exact lt_irrefl _ hv
      ext x
      constructor
      · intro hx
        exact (hcover x).resolve_left hx
      · intro hx hy
        exact hdisjoint x hy hx)]
    exact orderNerveRealizationSubcomplex_isClosed _
  have hall  :=
    (show IsClopen (A : Set (orderNerveRealization P)) from
      ⟨orderNerveRealizationSubcomplex_isClosed _, hopen⟩).eq_univ ⟨_, ha⟩
  have hb : orderNerveRealizationVertex b ∈ (A : Set (orderNerveRealization P)) := by
    rw [hall]
    exact Set.mem_univ _
  exact (orderNerveRealizationVertex_mem_subcomplex (orderReach a) b).mp hb

end FiniteChains.Comb

namespace FiniteChains.Comb.TopologicalOrderCover
open CategoryTheory Topology
open scoped Classical
variable {P : Type} [PartialOrder P] {E : Type} [TopologicalSpace E]
  (p : C(E, orderNerveRealization P)) (hp : IsCoveringMap p)
  (hs : Function.Surjective p)

include hs in
theorem realization_connected [ConnectedSpace E] :
    ConnectedSpace (orderNerveRealization (Cover p hp)) :=
  (realizationHomeomorph p hp hs).symm.surjective.connectedSpace
    (realizationHomeomorph p hp hs).symm.continuous

include hs in
theorem orderCover_connected [ConnectedSpace E] : IsConnected (orderCx (Cover p hp)) := by
  letI := realization_connected p hp hs
  exact orderCx_isConnected_of_realization



/-- The returned action has the edge and face compatibility needed by
actual regular-cover chain descent, in addition to ordinary regularity. -/
theorem reconstructed_cover_conclusions [ConnectedSpace E] [(nerve P).HasDimensionLE 2]
    (hr : Whitehead.Regular p) (hac : Whitehead.Acyclic E) :
    IsCovering (strictProjection p hp hs) ∧
    IsRegular (strictProjection p hp hs) (strictDeckAction p hp) ∧
    IsConnected (strictOrderCx (Cover p hp)) ∧
    IsAcyclic (strictOrderCx (Cover p hp)) ∧
    (∀ g e, (strictProjection p hp hs).onE ((strictDeckAction p hp).smulE g e) =
      (strictProjection p hp hs).onE e) ∧
    (∀ g t, (strictProjection p hp hs).onF ((strictDeckAction p hp).smulF g t) =
      (strictProjection p hp hs).onF t) :=
  ⟨strictProjection_isCovering p hp hs, strictProjection_isRegular p hp hs hr,
    (strictOrderCx_isConnected (orderCover_connected p hp hs)), (by
      letI := realization_connected p hp hs
      obtain ⟨x⟩ := (inferInstance : Nonempty (orderNerveRealization (Cover p hp)))
      obtain ⟨n, s, z, hz⟩ := orderNerveRealizationSimplex_jointly_surjective (Cover p hp) x
      letI : Nonempty (Cover p hp) := ⟨s.obj 0⟩
      letI := (projection_isPosetCover p hp hs).realization_hasDimensionLE 2
      apply (orderRealization_acyclic_iff_strict_isAcyclic (Cover p hp)
        (orderCover_connected p hp hs)).mp
      exact (Whitehead.acyclic_iff_of_homotopyEquiv
        (realizationHomeomorph p hp hs).toHomotopyEquiv).mpr hac),
    strictDeck_edges p hp hs, strictDeck_faces p hp hs⟩

end TopologicalOrderCover

open CategoryTheory Topology

end FiniteChains.Comb

namespace FiniteChains.Comb.SpanningTree
universe u
variable {X Y : Complex2.{u}} {TX : SpanningTree X} {TY : SpanningTree Y}
  [DecidableEq (NonTree TX)] [DecidableEq (NonTree TY)]
  {h : Hom X Y} (hiff : ∀ e : X.E, TY.isTree (h.onE e) ↔ TX.isTree e)
  (hE : Function.Injective h.onE)

theorem zeroPi2_of_zeroPi2_presInclHom
    (hz : ZeroPi2 (presInclHom (nonTreeIncl hiff) (nonTreeIncl_injective hiff hE)
      (treeRel TX) (treeRel TY) h.onF (treeRel_onF hiff))) : ZeroPi2 h := by
  have hzero := (zeroPi2_presInclHom_iff (ρ := treeRel TX)
    (nonTreeIncl hiff) (nonTreeIncl_injective hiff hE) h.onF (treeRel_onF hiff)).mp hz
  intro x z hz
  have hcycle := (mem_pi2_iff_bdry2_univCover TX z).mp hz
  have hinj : Function.Injective (chain2 (treeUnivHom TY (h.onV x))) :=
    Finsupp.mapDomain_injective (uvFace_injective TY)
  apply hinj
  rw [map_zero, chain2_treeUnivHom_square hiff hE]
  exact hzero _ hcycle

end FiniteChains.Comb.SpanningTree
