module

public import RequestProject.Pi2Extension
public import RequestProject.BaseChangeCycles
public import RequestProject.FoxFinsupp

@[expose] public section

/-! Structural maps and equation (3.3) with actual finite-support chains.

The generator and relator sets are arbitrary. This is the algebra used when
the fixed-core induction replaces all its positive stages simultaneously;
it does not assert an inclusion of a stage in its own replacement.

-/

noncomputable section


namespace FiniteChains

universe u

variable {α J α' J' α'' J'' : Type u}

/-- The genuine second Fox cycle condition for an arbitrary presentation. -/
def FSIsFoxCycle (ρ : J → FreeGroup α)
    (y : J →₀ MonoidAlgebra ℤ (PresGroup ρ)) : Prop :=
  coverSecondBoundary (relSub ρ) ρ y = 0

/-- Vanishing of the Hurewicz image, with finite support in both coordinates. -/
def FSIsCockcroft (ρ : J → FreeGroup α) : Prop :=
  ∀ y : J →₀ MonoidAlgebra ℤ (PresGroup ρ), FSIsFoxCycle ρ y →
    ∀ j, augPres ρ (y j) = 0

/-- A structural map of presentation chain modules, without finiteness of
the set of cells. Its coefficient homomorphism is part of the data. -/
structure PresMorFS (ρ : J → FreeGroup α) (τ : J' → FreeGroup α') where
  hom : PresGroup ρ →* PresGroup τ
  cells : (J →₀ MonoidAlgebra ℤ (PresGroup ρ)) →ₛₗ[MonoidAlgebra.mapDomainRingHom ℤ hom]
    (J' →₀ MonoidAlgebra ℤ (PresGroup τ))
  cells_cycle : ∀ y, FSIsFoxCycle ρ y → FSIsFoxCycle τ (cells y)
  cells_aug : ∀ y, (∀ j, augPres ρ (y j) = 0) →
    ∀ j', augPres τ (cells y j') = 0

namespace PresMorFS

variable {ρ : J → FreeGroup α} {τ : J' → FreeGroup α'}
  {υ : J'' → FreeGroup α''}

theorem cells_add (f : PresMorFS ρ τ) (x y : J →₀ MonoidAlgebra ℤ (PresGroup ρ)) :
    f.cells (x + y) = f.cells x + f.cells y := map_add _ _ _

@[simp] theorem cells_zero (f : PresMorFS ρ τ) : f.cells 0 = 0 := map_zero _

theorem cells_smul (f : PresMorFS ρ τ) (a : MonoidAlgebra ℤ (PresGroup ρ))
    (x : J →₀ MonoidAlgebra ℤ (PresGroup ρ)) :
    f.cells (a • x) = MonoidAlgebra.mapDomainRingHom ℤ f.hom a • f.cells x := map_smulₛₗ _ _ _

theorem cells_sub (f : PresMorFS ρ τ) (x y : J →₀ MonoidAlgebra ℤ (PresGroup ρ)) :
    f.cells (x - y) = f.cells x - f.cells y := map_sub _ _ _

def comp (g : PresMorFS τ υ) (f : PresMorFS ρ τ) : PresMorFS ρ υ where
  hom := g.hom.comp f.hom
  cells :=
    { toFun := fun x => g.cells (f.cells x)
      map_add' x y := by rw [map_add, map_add]
      map_smul' a y := by
        rw [map_smulₛₗ, map_smulₛₗ, ← MonoidAlgebra.mapDomainRingHom_apply_comp] }
  cells_cycle := fun y hy => g.cells_cycle _ (f.cells_cycle y hy)
  cells_aug := fun y hy => g.cells_aug _ (f.cells_aug y hy)


def castTarget {τ' : J' → FreeGroup α'} (f : PresMorFS ρ τ) (h : τ = τ') :
    PresMorFS ρ τ' := h ▸ f

/-- A semilinear structural map sends a span into the span of its image. -/
theorem cells_mem_span (g : PresMorFS τ υ)
    {S : Set (J' →₀ MonoidAlgebra ℤ (PresGroup τ))}
    {y : J' →₀ MonoidAlgebra ℤ (PresGroup τ)}
    (hy : y ∈ Submodule.span (MonoidAlgebra ℤ (PresGroup τ)) S) :
    g.cells y ∈ Submodule.span (MonoidAlgebra ℤ (PresGroup υ)) (g.cells '' S) := by
  change y ∈ (Submodule.span _ (g.cells '' S)).comap g.cells
  refine Submodule.span_le.2 ?_ hy
  exact fun z hz => Submodule.subset_span ⟨z, hz, rfl⟩

end PresMorFS

/-- Equation (3.3), retaining finite support even for an infinite core. -/
def FSGenerates {ρ : J → FreeGroup α} {τ : J' → FreeGroup α'}
    (f : PresMorFS ρ τ) : Prop :=
  ∀ y, FSIsFoxCycle τ y →
    y ∈ Submodule.span (MonoidAlgebra ℤ (PresGroup τ))
      {z | ∃ x, FSIsFoxCycle ρ x ∧ z = f.cells x}

variable {ρ : J → FreeGroup α} {τ : J' → FreeGroup α'}
  {υ : J'' → FreeGroup α''}

/-- Arbitrarily large individual presentations cause no problem with
composition: every element of the generated module is still a finite sum. -/
theorem FSGenerates.comp {g : PresMorFS τ υ} {f : PresMorFS ρ τ}
    (hg : FSGenerates g) (hf : FSGenerates f) : FSGenerates (g.comp f) := by
  intro y hy
  refine Submodule.span_le.2 ?_ (hg y hy)
  rintro _ ⟨z, hz, rfl⟩
  refine Submodule.span_le.2 ?_ (g.cells_mem_span (hf z hz))
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  exact Submodule.subset_span ⟨x, hx, rfl⟩

theorem FSGenerates.castTarget {τ' : J' → FreeGroup α'} {f : PresMorFS ρ τ}
    (hf : FSGenerates f) (h : τ = τ') : FSGenerates (f.castTarget h) := by
  cases h
  exact hf

/-- Equation (3.3) transports Cockcroftness for arbitrary presentations. -/
theorem fsIsCockcroft_of_generates (f : PresMorFS ρ τ) (hf : FSGenerates f)
    (hρ : FSIsCockcroft ρ) : FSIsCockcroft τ := by
  intro y hy j
  let A := (augPres τ).toSemilinearMap.comp (Finsupp.lapply j)
  exact (show y ∈ LinearMap.ker A from Submodule.span_le.2
    (by rintro _ ⟨x, hx, rfl⟩; exact f.cells_aug x (hρ x hx) j) (hf y hy))

/-- The terminal use of (3.3): killing the original cycle images suffices
to kill every cycle of the replacement. -/
theorem fsCells_eq_zero_of_generates_comp (f : PresMorFS ρ τ) (g : PresMorFS τ υ)
    (hf : FSGenerates f)
    (hcomp : ∀ x, FSIsFoxCycle ρ x → g.cells (f.cells x) = 0)
    {y : J' →₀ MonoidAlgebra ℤ (PresGroup τ)} (hy : FSIsFoxCycle τ y) :
    g.cells y = 0 := by
  exact (Submodule.span_le.2 (by rintro _ ⟨x, hx, rfl⟩; exact hcomp x hx) (hf y hy) :
    y ∈ LinearMap.ker g.cells)

/-- The fixed-core induction transports each old zero arrow through a
commuting replacement square. It does not require `P` to include in `T(P)`. -/
theorem fsCells_eq_zero_of_generates {β K β' K' : Type u}
    {σ : K → FreeGroup β} {σ' : K' → FreeGroup β'}
    (eta : PresMorFS ρ σ) (eta' : PresMorFS τ σ')
    (j : PresMorFS ρ τ) (Tj : PresMorFS σ σ')
    (hsq : ∀ x, Tj.cells (eta.cells x) = eta'.cells (j.cells x))
    (hzero : ∀ x, FSIsFoxCycle ρ x → j.cells x = 0)
    (hgen : FSGenerates eta)
    {y : K →₀ MonoidAlgebra ℤ (PresGroup σ)} (hy : FSIsFoxCycle σ y) :
    Tj.cells y = 0 := by
  apply fsCells_eq_zero_of_generates_comp eta Tj hgen ?_ hy
  intro x hx
  rw [hsq x, hzero x hx, eta'.cells_zero]










end FiniteChains
