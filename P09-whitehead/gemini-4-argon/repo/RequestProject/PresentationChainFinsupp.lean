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
public import RequestProject.CoverAcyclic
public import RequestProject.TorsionFreeGroupRing
public import RequestProject.ChainFormulaMod
public import RequestProject.Pi2DictionaryFinsupp

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace FiniteChains

open MonoidAlgebra

universe u

variable {α J : Type u}

structure PresChainFS (ρ : J → FreeGroup α) (n : ℕ) where
  gen : ℕ → Type u
  cell : ℕ → Type u
  decGen : ∀ r, DecidableEq (gen r)
  rel : ∀ r, cell r → FreeGroup (gen r)
  genIncl : ∀ r, gen r → gen (r + 1)
  genIncl_injective : ∀ r, Function.Injective (genIncl r)
  cellIncl : ∀ r, cell r → cell (r + 1)
  cellIncl_injective : ∀ r, Function.Injective (cellIncl r)
  rel_incl : ∀ r c, rel (r + 1) (cellIncl r c) = FreeGroup.map (genIncl r) (rel r c)
  baseGen : α → gen 0
  baseGen_injective : Function.Injective baseGen
  baseCell : J → cell 0
  baseCell_injective : Function.Injective baseCell
  rel_base : ∀ j, rel 0 (baseCell j) = FreeGroup.map baseGen (ρ j)
  zero_pi2 : ∀ r, r < n →
      ∀ u : ((FreeGroup (gen r) ⧸ relSub (rel r)) × cell r) →₀ ℤ,
        Comb.bdry2 (@Comb.univCover _ (decGen r) _ (rel r)) u = 0 →
        Finsupp.mapDomain (Prod.map
          (⇑(QuotientGroup.map (relSub (rel r)) (relSub (rel (r + 1)))
            (FreeGroup.map (genIncl r)) (Subgroup.normalClosure_le_normal (by
              rintro _ ⟨c, rfl⟩
              exact Subgroup.mem_comap.2 ((rel_incl r c).symm ▸
                Subgroup.subset_normalClosure (Set.mem_range_self _))))))
          (cellIncl r)) u = 0

namespace PresChainFS

variable {ρ : J → FreeGroup α} {n : ℕ} (h : PresChainFS ρ n)

def gmap (h : PresChainFS ρ n) : ∀ r, α → h.gen r
  | 0 => h.baseGen
  | r + 1 => fun i => h.genIncl r (gmap h r i)

def cmap (h : PresChainFS ρ n) : ∀ r, J → h.cell r
  | 0 => h.baseCell
  | r + 1 => fun j => h.cellIncl r (cmap h r j)

@[simp] theorem cmap_zero : h.cmap 0 = h.baseCell := rfl

theorem gmap_injective (h : PresChainFS ρ n) : ∀ r, Function.Injective (h.gmap r)
  | 0 => h.baseGen_injective
  | r + 1 => fun _ _ hii => gmap_injective h r (h.genIncl_injective r hii)

theorem cmap_injective (h : PresChainFS ρ n) : ∀ r, Function.Injective (h.cmap r)
  | 0 => h.baseCell_injective
  | r + 1 => fun _ _ hjj => cmap_injective h r (h.cellIncl_injective r hjj)

theorem rel_cmap (h : PresChainFS ρ n) : ∀ (r : ℕ) (j : J),
    h.rel r (h.cmap r j) = FreeGroup.map (h.gmap r) (ρ j)
  | 0, j => h.rel_base j
  | r + 1, j => by
      change h.rel (r + 1) (h.cellIncl r (h.cmap r j)) = _
      rw [h.rel_incl r (h.cmap r j), rel_cmap h r j, FreeGroup.map.comp]; rfl

def psi (r : ℕ) : PresGroup (h.rel r) →* PresGroup (h.rel (r + 1)) :=
  QuotientGroup.map _ _ (FreeGroup.map (h.genIncl r))
    (Subgroup.normalClosure_le_normal (by
      rintro _ ⟨c, rfl⟩
      exact Subgroup.mem_comap.2 ((h.rel_incl r c).symm ▸
        Subgroup.subset_normalClosure (Set.mem_range_self _))))

def phi (r : ℕ) : PresGroup ρ →* PresGroup (h.rel r) :=
  QuotientGroup.map _ _ (FreeGroup.map (h.gmap r))
    (Subgroup.normalClosure_le_normal (by
      rintro _ ⟨j, rfl⟩
      exact Subgroup.mem_comap.2 (h.rel_cmap r j ▸
        Subgroup.subset_normalClosure (Set.mem_range_self _))))

@[simp] theorem psi_mk (r : ℕ) (w : FreeGroup (h.gen r)) :
    h.psi r (QuotientGroup.mk w) = QuotientGroup.mk (FreeGroup.map (h.genIncl r) w) := rfl

def bdry (r : ℕ) (a : h.gen r) (c : h.cell r) : MonoidAlgebra ℤ (PresGroup (h.rel r)) :=
  quotRingHom ℤ (relSub (h.rel r)) (@fox _ (h.decGen r) a (h.rel r c))

theorem quot_freeRingMap (r : ℕ) (x : FreeGroupRing α) :
    letI := h.decGen r
    quotRingHom ℤ (relSub (h.rel r)) (freeRingMap (h.gmap r) x)
      = MonoidAlgebra.mapDomainRingHom ℤ (h.phi r) (quotRingHom ℤ (relSub ρ) x) := by
  letI := h.decGen r
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add _ _ hx hy => simp only [map_add, hx, hy]
  | single w m =>
      show quotRingHom ℤ (relSub (h.rel r))
          (MonoidAlgebra.mapDomain (FreeGroup.map (h.gmap r)) (MonoidAlgebra.single w m)) =
        MonoidAlgebra.mapDomain (h.phi r) (quotRingHom ℤ (relSub ρ) (MonoidAlgebra.single w m))
      rw [MonoidAlgebra.mapDomain_single, quotRingHom_single, quotRingHom_single,
        MonoidAlgebra.mapDomain_single]; rfl

end PresChainFS

theorem hasCellChainsLift_of_presChainsFS [DecidableEq α]
    (ρ : J → FreeGroup α)
    (hchains : ∀ n : ℕ, Nonempty (PresChainFS ρ n)) :
    HasCellChainsLift (foxMatrixPres ρ) := by
  intro n
  obtain ⟨h⟩ := hchains n
  let inp : ChainInput (foxMatrixPres ρ) n (fun r => PresGroup (h.rel r)) h.gen h.cell :=
    { phi := h.phi
      psi := h.psi
      phi_succ := fun r => by
        ext w
        show h.psi r (h.phi r (QuotientGroup.mk (FreeGroup.of w))) =
          h.phi (r + 1) (QuotientGroup.mk (FreeGroup.of w))
        change QuotientGroup.mk (FreeGroup.map (h.genIncl r) (FreeGroup.map (h.gmap r) _)) = _
        rw [FreeGroup.map.comp]; rfl
      genIncl := h.gmap
      cellIncl := h.cmap
      cellIncl_injective := h.cmap_injective
      cellStep := h.cellIncl
      cellStep_injective := h.cellIncl_injective
      bdry := h.bdry
      bdry_old := fun r i j => by
        letI := h.decGen r
        show quotRingHom ℤ (relSub (h.rel r)) (fox (h.gmap r i) (h.rel r (h.cmap r j))) = _
        rw [h.rel_cmap r j, fox_map (h.gmap r) (h.gmap_injective r) i (ρ j), h.quot_freeRingMap r]; rfl
      bdry_new := fun r a ha j => by
        letI := h.decGen r
        show quotRingHom ℤ (relSub (h.rel r)) (fox a (h.rel r (h.cmap r j))) = 0
        rw [h.rel_cmap r j, fox_map_of_not_mem_range (h.gmap r) ha (ρ j), map_zero]
      zero_pi2 := fun r hr u hu => by
        letI := h.decGen r
        letI : DecidableEq (h.cell r) := Classical.decEq _
        exact (Comb.fs_univCover_zero_pi2_iff (h.rel r) (h.psi r) (h.cellIncl r)
          (h.cellIncl_injective r)).1 (h.zero_pi2 r hr) u hu }
  refine ⟨fun r => PresGroup (h.rel r), fun _ => inferInstance, h.gen, h.cell, inp, fun m r _ u hu => ?_⟩
  letI := h.decGen r
  obtain ⟨v, hv, z, hz⟩ := fs_exists_cycle_of_boundary_nsmul (h.rel r) m u
    (fun i => by simpa only [fs_coverSecondBoundary_apply, inp, PresChainFS.bdry, foxMatrixPres] using hu i)
  exact ⟨v, fun i => by
    simpa only [fs_coverSecondBoundary_apply, inp, PresChainFS.bdry, foxMatrixPres, Finsupp.zero_apply] using
      congrArg (fun c => c i) hv, z, hz⟩
