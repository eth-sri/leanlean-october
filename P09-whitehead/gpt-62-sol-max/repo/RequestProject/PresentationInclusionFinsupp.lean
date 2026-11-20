module

public import RequestProject.FreeGeneratorPaddingFinsupp
public import RequestProject.FinsuppBasis
public import RequestProject.ChainLinearNaturality

@[expose] public section

/-! Literal labelled presentation inclusions as actual supported structural
maps. The boundary proof includes both generator and cell index changes.
Awaiting final Lean verification.
-/

noncomputable section
open scoped Classical

namespace FiniteChains.PresInclusionFS
open BlockFamily

section Transport

variable {G H L : Type*} [Group G] [Group H] [Group L] {I J K : Type*}

/-- Transport a group-ring chain along maps on its coefficients and cell labels. -/
def cellTransport (g : G →* H) (f : I → J) (x : I →₀ MonoidAlgebra ℤ G) :
    J →₀ MonoidAlgebra ℤ H :=
  Finsupp.mapDomain f (x.mapRange (MonoidAlgebra.mapDomainRingHom ℤ g) (map_zero _))

@[simp] theorem cellTransport_id (x : I →₀ MonoidAlgebra ℤ G) :
    cellTransport (MonoidHom.id G) id x = x := by
  simp [cellTransport, MonoidAlgebra.mapDomainRingHom_id]

theorem cellTransport_comp (g : G →* H) (h : H →* L) (f : I → J) (k : J → K)
    (x : I →₀ MonoidAlgebra ℤ G) :
    cellTransport h k (cellTransport g f x) = cellTransport (h.comp g) (k ∘ f) x := by
  unfold cellTransport
  rw [← Finsupp.mapDomain_mapRange f _ _ _ (map_add (MonoidAlgebra.mapDomainRingHom ℤ h)),
    ← Finsupp.mapDomain_comp]
  congr 1
  ext i : 1
  simp only [Finsupp.mapRange_apply, MonoidAlgebra.mapDomainRingHom_comp, RingHom.comp_apply]

theorem cellTransport_square {G' : Type*} [Group G'] {J' : Type*}
    {a : G →* H} {b : H →* L} {c : G →* G'} {d : G' →* L}
    {f : I → J} {k : J → K} {f' : I → J'} {k' : J' → K}
    (hg : b.comp a = d.comp c) (hf : ∀ i, k (f i) = k' (f' i))
    (x : I →₀ MonoidAlgebra ℤ G) :
    cellTransport b k (cellTransport a f x) = cellTransport d k' (cellTransport c f' x) := by
  rw [cellTransport_comp, cellTransport_comp, hg, show k ∘ f = k' ∘ f' from funext hf]

end Transport

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

@[simp] theorem groupHom_mk (w : FreeGroup A) :
    groupHom ρ τ g f hrel (QuotientGroup.mk w) = QuotientGroup.mk (FreeGroup.map g w) := rfl

def coefficients := MonoidAlgebra.mapDomainRingHom ℤ (groupHom ρ τ g f hrel)

theorem coefficients_proj (x : FreeGroupRing A) :
    coefficients ρ τ g f hrel (proj (relSub ρ) x) =
      proj (relSub τ) (freeRingMap g x) :=
  quotRingHom_natural (relSub τ) (FreeGroup.map g) (groupHom ρ τ g f hrel) rfl x

variable [DecidableEq A] [DecidableEq B]

include hg in
theorem gradient (j : J) :
    coverFoxGradient (relSub τ) (τ (f j)) =
      Finsupp.mapDomain g ((coverFoxGradient (relSub ρ) (ρ j)).mapRange
        (coefficients ρ τ g f hrel) (map_zero _)) := by
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
    rw [fox_map_of_not_mem_range g (fun a h => hb ⟨a, h.symm⟩), map_zero]

def cells (x : J →₀ MonoidAlgebra ℤ (PresGroup ρ)) :
    K →₀ MonoidAlgebra ℤ (PresGroup τ) :=
  cellTransport (groupHom ρ τ g f hrel) f x

omit [DecidableEq A] [DecidableEq B] in
@[simp] theorem cells_single (j : J) (a : MonoidAlgebra ℤ (PresGroup ρ)) :
    cells ρ τ g f hrel (Finsupp.single j a) =
      Finsupp.single (f j) (coefficients ρ τ g f hrel a) := by
  simp [cells, cellTransport, coefficients]

include hg in
theorem boundary (x : J →₀ MonoidAlgebra ℤ (PresGroup ρ)) :
    coverSecondBoundary (relSub τ) τ (cells ρ τ g f hrel x) =
      Finsupp.mapDomain g ((coverSecondBoundary (relSub ρ) ρ x).mapRange
        (coefficients ρ τ g f hrel) (map_zero _)) := by
  unfold coverSecondBoundary cells cellTransport
  rw [Finsupp.linearCombination_mapDomain]
  let σ := coefficients ρ τ g f hrel
  exact Finsupp.linearCombination_semilinear
    ((Finsupp.lmapDomain _ _ g).comp (Finsupp.mapRange.linearMap σ.toSemilinearMap))
    (fun j => (gradient ρ τ g f hg hrel j).symm) x

def mor : PresMorFS ρ τ where
  hom := groupHom ρ τ g f hrel
  cells := (Finsupp.lmapDomain _ _ f).comp
    (Finsupp.mapRange.linearMap (MonoidAlgebra.mapDomainRingHom ℤ (groupHom ρ τ g f hrel)).toSemilinearMap)
  cells_cycle := by
    intro x hx
    change coverSecondBoundary _ _ (cells ρ τ g f hrel x) = 0
    rw [boundary ρ τ g f hg hrel, hx]
    simp
  cells_aug := by
    intro x hx k
    by_cases hk : k ∈ Set.range f
    · obtain ⟨j, rfl⟩ := hk
      change augPres τ (Finsupp.mapDomain f _ (f j)) = 0
      rw [Finsupp.mapDomain_apply_of_injective hf]
      exact (augQ_mapDomain (groupHom ρ τ g f hrel) (x j)).trans (hx j)
    simp [Finsupp.mapDomain_notin_range _ k hk]

theorem mor_cells (x : J →₀ MonoidAlgebra ℤ (PresGroup ρ)) :
    (mor ρ τ g f hg hf hrel).cells x = cellTransport (groupHom ρ τ g f hrel) f x := rfl

end FiniteChains.PresInclusionFS
