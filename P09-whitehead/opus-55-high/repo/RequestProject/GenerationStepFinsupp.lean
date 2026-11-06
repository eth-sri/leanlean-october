import RequestProject.GenerationStep
import RequestProject.FoxFinsupp
import RequestProject.Tac


/-! Structural maps and equation (3.3) with actual finite-support chains.

The generator and relator sets are arbitrary. This is the algebra used when
the fixed-core induction replaces all its positive stages simultaneously;
it does not assert an inclusion of a stage in its own replacement.

-/

noncomputable section

bwd

namespace FiniteChains

universe u

variable {α J α' J' α'' J'' : Type u}
  [DecidableEq α] [DecidableEq α'] [DecidableEq α'']

/-- The genuine second Fox cycle condition for an arbitrary presentation. -/
def FSIsFoxCycle (ρ : J → FreeGroup α)
    (y : J →₀ MonoidAlgebra ℤ (PresGroup ρ)) :=
  coverSecondBoundary _ ρ y = 0

/-- Vanishing of the Hurewicz image, with finite support in both coordinates. -/
def FSIsCockcroft (ρ : J → FreeGroup α) :=
  ∀ y, FSIsFoxCycle ρ y →
    ∀ j, augPres ρ (y j) = 0

/-- A structural map of presentation chain modules, without finiteness of
the set of cells. Its coefficient homomorphism is part of the data. -/
structure PresMorFS (ρ : J → FreeGroup α) (τ : J' → FreeGroup α') where
  hom : PresGroup ρ →* PresGroup τ
  cells : (J →₀ MonoidAlgebra ℤ (PresGroup ρ)) →
    (J' →₀ MonoidAlgebra ℤ (PresGroup τ))
  cells_add : ∀ y z, cells (y + z) = cells y + cells z
  cells_smul : ∀ (a : MonoidAlgebra ℤ (PresGroup ρ)) y,
    cells (a • y) = MonoidAlgebra.mapDomainRingHom ℤ hom a • cells y
  cells_cycle : ∀ y, FSIsFoxCycle ρ y → FSIsFoxCycle τ (cells y)
  cells_aug : ∀ y, (∀ j, augPres ρ (y j) = 0) →
    ∀ j', augPres τ (cells y j') = 0

namespace PresMorFS

variable {ρ : J → FreeGroup α} {τ : J' → FreeGroup α'}
  {υ : J'' → FreeGroup α''}

@[simp] theorem cells_zero (f : PresMorFS ρ τ) : f.cells 0 = 0 := by
  have h := f.cells_smul 0 0
  grind [zero_smul, map_zero]

@[simp] theorem cells_neg (f : PresMorFS ρ τ)
    x : f.cells (-x) = -f.cells x := by
  have h := f.cells_smul (-1) x
  simpa [neg_one_smul, map_neg, map_one] using h

theorem cells_sub (f : PresMorFS ρ τ)
    x y :
    f.cells (x - y) = f.cells x - f.cells y := by
  grind [sub_eq_add_neg, f.cells_add, f.cells_neg]

def comp (g : PresMorFS τ υ) (f : PresMorFS ρ τ) : PresMorFS ρ υ where
  hom := g.hom.comp f.hom
  cells := fun y => g.cells (f.cells y)
  cells_add := fun y z => by rw [f.cells_add, g.cells_add]
  cells_smul := by
    simp [f.cells_smul, g.cells_smul, PresMor.mapDomainRingHom_comp]
  cells_cycle := fun y hy => g.cells_cycle _ (f.cells_cycle y hy)
  cells_aug := fun y hy => g.cells_aug _ (f.cells_aug y hy)


def castTarget {τ' : J' → FreeGroup α'} (f : PresMorFS ρ τ) (h : τ = τ') :
    PresMorFS ρ τ' := h ▸ f

/-- A semilinear structural map sends a span into the span of its image. -/
theorem cells_mem_span (g : PresMorFS τ υ)
    {S}
    {y}
    (hy : y ∈ Submodule.span (MonoidAlgebra ℤ (PresGroup τ)) S) :
    g.cells y ∈ Submodule.span (MonoidAlgebra ℤ (PresGroup υ)) (g.cells '' S) := by
  induction hy using Submodule.span_induction with
  | mem y hy => aesop
  | zero => simp
  | add y z _ _ hy hz => rw [g.cells_add]; aesop
  | smul a y _ hy => rw [g.cells_smul]; aesop

end PresMorFS

/-- Equation (3.3), retaining finite support even for an infinite core. -/
def FSGenerates {ρ : J → FreeGroup α} {τ : J' → FreeGroup α'}
    (f : PresMorFS ρ τ) :=
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
  aesop

theorem FSGenerates.castTarget {f : PresMorFS ρ τ}
    (hf : FSGenerates f) (h : τ = τ') : FSGenerates (f.castTarget h) := by
  aesop

/-- Equation (3.3) transports Cockcroftness for arbitrary presentations. -/
theorem fsIsCockcroft_of_generates (f : PresMorFS ρ τ) (hf : FSGenerates f)
    (hρ : FSIsCockcroft ρ) : FSIsCockcroft τ := by
  intro y hy
  have hspan := hf y hy
  clear hy
  induction hspan using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨x, hx, rfl⟩ := hz
      exact f.cells_aug x (hρ x hx)
  | zero => simp
  | add x z _ _ hx hz =>
      simp_all
  | smul a x _ hx =>
      simp_all

/-- The terminal use of (3.3): killing the original cycle images suffices
to kill every cycle of the replacement. -/
theorem fsCells_eq_zero_of_generates_comp f (g : PresMorFS τ υ)
    (hf : FSGenerates f)
    (hcomp : ∀ x, FSIsFoxCycle ρ x → g.cells (f.cells x) = 0)
    {y} (hy : FSIsFoxCycle τ y) :
    g.cells y = 0 := by
  have hspan := hf y hy
  clear hy
  induction hspan using Submodule.span_induction with
  | mem z hz =>
      grind
  | zero => exact g.cells_zero
  | add x z _ _ hx hz => rw [g.cells_add, hx, hz, add_zero]
  | smul a x _ hx => rw [g.cells_smul, hx, smul_zero]

/-- The fixed-core induction transports each old zero arrow through a
commuting replacement square. It does not require `P` to include in `T(P)`. -/
theorem fsCells_eq_zero_of_generates {β K β' K'}
    [DecidableEq β] [DecidableEq β']
    {σ : K → FreeGroup β} {σ' : K' → FreeGroup β'}
    eta (eta' : PresMorFS τ σ')
    (j : PresMorFS ρ τ) (Tj : PresMorFS σ σ')
    (hsq : ∀ x, Tj.cells (eta.cells x) = eta'.cells (j.cells x))
    (hzero : ∀ x, FSIsFoxCycle ρ x → j.cells x = 0)
    (hgen : FSGenerates eta)
    {y} (hy : FSIsFoxCycle σ y) :
    Tj.cells y = 0 := by
  apply fsCells_eq_zero_of_generates_comp eta Tj hgen ?_ hy
  simp_all
