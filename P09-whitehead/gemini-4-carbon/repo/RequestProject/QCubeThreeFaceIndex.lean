module

public import RequestProject.GenusLoops
public import RequestProject.CylinderPi1Surjective
public import RequestProject.GenusUniversalPolygonTransport
public import RequestProject.OrderNerveOneDecoding
public import RequestProject.CombPi1
public import RequestProject.PresPosetReading
public import RequestProject.GenusCollapseIteration
public import RequestProject.GenusQuotientRelativeSupport
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian

@[expose] public section
noncomputable section
namespace FiniteChains

universe u

variable {α J α' J' α'' J'' : Type u}
  [DecidableEq α] [DecidableEq α'] [DecidableEq α'']

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
  simp_all

@[simp] theorem cells_neg (f : PresMorFS ρ τ)
    (x : J →₀ MonoidAlgebra ℤ (PresGroup ρ)) : f.cells (-x) = -f.cells x := by
  have h := f.cells_smul (-1) x
  simpa only [neg_one_smul, map_neg, map_one] using h

theorem cells_sub (f : PresMorFS ρ τ)
    (x y : J →₀ MonoidAlgebra ℤ (PresGroup ρ)) :
    f.cells (x - y) = f.cells x - f.cells y := by
  rw [sub_eq_add_neg, f.cells_add, f.cells_neg, sub_eq_add_neg]

def comp (g : PresMorFS τ υ) (f : PresMorFS ρ τ) : PresMorFS ρ υ where
  hom := g.hom.comp f.hom
  cells := fun y => g.cells (f.cells y)
  cells_add := fun y z => by rw [f.cells_add, g.cells_add]
  cells_smul := by
    intro a y
    rw [f.cells_smul, g.cells_smul, PresMor.mapDomainRingHom_comp]
  cells_cycle := fun y hy => g.cells_cycle _ (f.cells_cycle y hy)
  cells_aug := fun y hy => g.cells_aug _ (f.cells_aug y hy)

@[simp] theorem comp_cells (g : PresMorFS τ υ) (f : PresMorFS ρ τ)
    (y : J →₀ MonoidAlgebra ℤ (PresGroup ρ)) :
    (g.comp f).cells y = g.cells (f.cells y) := rfl

def castTarget {τ' : J' → FreeGroup α'} (f : PresMorFS ρ τ) (h : τ = τ') :
    PresMorFS ρ τ' := h ▸ f

/-- A semilinear structural map sends a span into the span of its image. -/
theorem cells_mem_span (g : PresMorFS τ υ)
    {S : Set (J' →₀ MonoidAlgebra ℤ (PresGroup τ))}
    {y : J' →₀ MonoidAlgebra ℤ (PresGroup τ)}
    (hy : y ∈ Submodule.span (MonoidAlgebra ℤ (PresGroup τ)) S) :
    g.cells y ∈ Submodule.span (MonoidAlgebra ℤ (PresGroup υ)) (g.cells '' S) := by
  induction hy using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
  | zero => simp
  | add y z _ _ hy hz => rw [g.cells_add]; exact Submodule.add_mem _ hy hz
  | smul a y _ hy => rw [g.cells_smul]; exact Submodule.smul_mem _ _ hy

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
  intro y hy
  have hspan := hf y hy
  clear hy
  induction hspan using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨x, hx, rfl⟩ := hz
      exact f.cells_aug x (hρ x hx)
  | zero => simp
  | add x z _ _ hx hz => simp_all
  | smul a x _ hx => simp_all

/-- The terminal use of (3.3): killing the original cycle images suffices
to kill every cycle of the replacement. -/
theorem fsCells_eq_zero_of_generates_comp (f : PresMorFS ρ τ) (g : PresMorFS τ υ)
    (hf : FSGenerates f)
    (hcomp : ∀ x, FSIsFoxCycle ρ x → g.cells (f.cells x) = 0)
    {y : J' →₀ MonoidAlgebra ℤ (PresGroup τ)} (hy : FSIsFoxCycle τ y) :
    g.cells y = 0 := by
  have hspan := hf y hy
  clear hy
  induction hspan using Submodule.span_induction with
  | mem z hz => grind
  | zero => simp
  | add x z _ _ hx hz => rw [g.cells_add, hx, hz, add_zero]
  | smul a x _ hx => rw [g.cells_smul, hx, smul_zero]

/-- The fixed-core induction transports each old zero arrow through a
commuting replacement square. It does not require `P` to include in `T(P)`. -/
theorem fsCells_eq_zero_of_generates {β K β' K' : Type u}
    [DecidableEq β] [DecidableEq β']
    {σ : K → FreeGroup β} {σ' : K' → FreeGroup β'}
    (eta : PresMorFS ρ σ) (eta' : PresMorFS τ σ')
    (j : PresMorFS ρ τ) (Tj : PresMorFS σ σ')
    (hsq : ∀ x, Tj.cells (eta.cells x) = eta'.cells (j.cells x))
    (hzero : ∀ x, FSIsFoxCycle ρ x → j.cells x = 0)
    (hgen : FSGenerates eta)
    {y : K →₀ MonoidAlgebra ℤ (PresGroup σ)} (hy : FSIsFoxCycle σ y) :
    Tj.cells y = 0 := by
  apply fsCells_eq_zero_of_generates_comp eta Tj hgen ?_ hy
  simp_all



end FiniteChains

namespace FiniteChains.BlockFamily

universe u

section Chains

variable {Jr Sx R : Type u} {Mt : Sx → Type u} [Ring R]

/-- The part of a two-chain supported on the substituted blocks. -/
def fsBlockPart (x : (Jr ⊕ (Σ s, Mt s)) →₀ R) : (Σ s, Mt s) →₀ R :=
  x.comapDomain Sum.inr Sum.inr_injective.injOn

/-- The actual finitely supported chain in one block. -/
def fsBlockSlice (x : (Jr ⊕ (Σ s, Mt s)) →₀ R) (s : Sx) : Mt s →₀ R :=
  (fsBlockPart x).split s

@[simp] theorem fsBlockSlice_apply (x : (Jr ⊕ (Σ s, Mt s)) →₀ R)
    (s : Sx) (m : Mt s) : fsBlockSlice x s m = x (Sum.inr ⟨s, m⟩) := rfl

/-- Only the finitely many occupied block labels are needed for coefficients. -/
def fsBlockSupport (x : (Jr ⊕ (Σ s, Mt s)) →₀ R) : Finset Sx :=
  (fsBlockPart x).splitSupport


/-- A finitely supported family of polygon coefficients expands along the
actual finitely supported surface chains. -/
def fsFillBlocks (c : ∀ s, Mt s →₀ R) (w : Sx →₀ R) : (Σ s, Mt s) →₀ R := by
  classical
  refine Finsupp.onFinset (w.support.sigma fun s => (c s).support)
    (fun p => w p.1 * c p.1 p.2) ?_
  intro p hp
  apply Finset.mem_sigma.mpr
  constructor
  · apply Finsupp.mem_support_iff.mpr
    intro hw
    exact hp (by change w p.1 * c p.1 p.2 = 0; rw [hw, zero_mul])
  · apply Finsupp.mem_support_iff.mpr
    intro hc
    exact hp (by change w p.1 * c p.1 p.2 = 0; rw [hc, mul_zero])

@[simp] theorem fsFillBlocks_apply (c : ∀ s, Mt s →₀ R) (w : Sx →₀ R)
    (p : Σ s, Mt s) : fsFillBlocks c w p = w p.1 * c p.1 p.2 := rfl

/-- The substituted two-chain map after extending coefficients to the target
ring: retain old cells and replace each polygon by its chosen surface chain. -/
def fsCellsBase (c : ∀ s, Mt s →₀ R) :
    ((Jr ⊕ Sx) →₀ R) →ₗ[R] ((Jr ⊕ (Σ s, Mt s)) →₀ R) where
  toFun y := Finsupp.sumElim
    (y.comapDomain Sum.inl Sum.inl_injective.injOn)
    (fsFillBlocks c (y.comapDomain Sum.inr Sum.inr_injective.injOn))
  map_add' y z := by
    ext k
    cases k with
    | inl j => rfl
    | inr p =>
        change (y (Sum.inr p.1) + z (Sum.inr p.1)) * c p.1 p.2 = _
        exact add_mul _ _ _
  map_smul' a y := by
    ext k
    cases k with
    | inl j => rfl
    | inr p =>
        change (a * y (Sum.inr p.1)) * c p.1 p.2 =
          a * (y (Sum.inr p.1) * c p.1 p.2)
        exact mul_assoc _ _ _

@[simp] theorem fsCellsBase_inl (c : ∀ s, Mt s →₀ R)
    (y : (Jr ⊕ Sx) →₀ R) (j : Jr) :
    fsCellsBase c y (Sum.inl j) = y (Sum.inl j) := rfl

@[simp] theorem fsCellsBase_inr (c : ∀ s, Mt s →₀ R)
    (y : (Jr ⊕ Sx) →₀ R) (s : Sx) (m : Mt s) :
    fsCellsBase c y (Sum.inr ⟨s, m⟩) = y (Sum.inr s) * c s m := rfl

/-- Local witnesses can be selected with finite support, even if zero blocks
admit nonzero scalar witnesses. Thus no injectivity of a surface chain is
needed to obtain finitely supported polygon coefficients. -/
theorem exists_fsBlockCoefficients (c : ∀ s, Mt s →₀ R)
    (x : (Jr ⊕ (Σ s, Mt s)) →₀ R)
    (h : ∀ s, ∃ a : R, ∀ m, x (Sum.inr ⟨s, m⟩) = a * c s m) :
    ∃ w : Sx →₀ R, w.support ⊆ fsBlockSupport x ∧
      ∀ s m, x (Sum.inr ⟨s, m⟩) = w s * c s m := by
  classical
  choose a ha using h
  let w  := Finsupp.onFinset (fsBlockSupport x)
    (fun s => if s ∈ fsBlockSupport x then a s else 0)
    (by intro s hs; by_contra hn; exact hs (if_neg hn))
  refine ⟨w, Finsupp.support_onFinset_subset, ?_⟩
  intro s m
  by_cases hs : s ∈ fsBlockSupport x
  · grind
  · have hz := congrArg (fun b : Mt s →₀ R => b m)
      (show fsBlockSlice x s = 0 by
        by_contra h
        exact hs ((Finsupp.mem_splitSupport_iff_nonzero (fsBlockPart x) s).mpr h))
    simpa only [fsBlockSlice_apply, Finsupp.zero_apply, w,
      Finsupp.onFinset_apply, if_neg hs, zero_mul] using hz

/-- Assemble the local surface coefficients and the retained coefficients into
an actual preimage of the full substituted two-chain. -/
theorem exists_fsCellsBase_preimage (c : ∀ s, Mt s →₀ R)
    (x : (Jr ⊕ (Σ s, Mt s)) →₀ R)
    (h : ∀ s, ∃ a : R, ∀ m, x (Sum.inr ⟨s, m⟩) = a * c s m) :
    ∃ y : (Jr ⊕ Sx) →₀ R, fsCellsBase c y = x ∧
      (∀ j, y (Sum.inl j) = x (Sum.inl j)) ∧
      (y.comapDomain Sum.inr Sum.inr_injective.injOn).support ⊆ fsBlockSupport x := by
  obtain ⟨w, hw, he⟩ := exists_fsBlockCoefficients c x h
  let y  :=
    Finsupp.sumElim (x.comapDomain Sum.inl Sum.inl_injective.injOn) w
  refine ⟨y, ?_, fun _ => rfl, ?_⟩
  · ext k
    cases k with
    | inl j => rfl
    | inr p => exact (he p.1 p.2).symm
  · have hy : y.comapDomain Sum.inr Sum.inr_injective.injOn = w := by
      ext s
      rfl
    rw [hy]
    exact hw

end Chains

section Fox

variable {α Jr Sx : Type u} {Zt Mt : Sx → Type u}
  [DecidableEq α] [DecidableEq Sx] [∀ s, DecidableEq (Zt s)]
  (ρ : Jr ⊕ Sx → FreeGroup α)
  (bsub : ∀ s, Mt s → FreeGroup (α ⊕ Zt s))
local notation "R'" => MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub))


/-- The existing genuine finitely supported Fox boundary, in matrix coordinates. -/
theorem fsCoverSecondBoundary_apply {A J : Type u} [DecidableEq A]
    (σ : J → FreeGroup A) (x : J →₀ MonoidAlgebra ℤ (PresGroup σ)) (i : A) :
    coverSecondBoundary (relSub σ) σ x i =
      x.sum (fun j a => a * foxMatrixPres σ i j) := by
  simp only [coverSecondBoundary, Finsupp.linearCombination_apply, Finsupp.sum,
    Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul]
  rfl

/-- Internal coordinates of the actual substituted Fox boundary see exactly
one block, with a finite sum even for an infinite block-relator set. -/
theorem fsCoverSecondBoundary_inr
    (x : (Jr ⊕ (Σ s, Mt s)) →₀ R') (s : Sx) (z : Zt s) :
    coverSecondBoundary (relSub (substPresF ρ bsub)) (substPresF ρ bsub) x
        (Sum.inr ⟨s, z⟩) =
      (fsBlockSlice x s).sum (fun m a => a *
        foxMatrixPres (substPresF ρ bsub) (Sum.inr ⟨s, z⟩) (Sum.inr ⟨s, m⟩)) := by
  rw [fsCoverSecondBoundary_apply]
  let old := x.comapDomain Sum.inl Sum.inl_injective.injOn
  let blocks := fsBlockPart x
  have hx : x = Finsupp.sumElim old blocks := by
    ext k
    cases k <;> rfl
  have ho : old.sum (fun j a => a *
      foxMatrixPres (substPresF ρ bsub) (Sum.inr ⟨s, z⟩) (Sum.inl j)) = 0 := by
    simp [foxMatrix_inr_inl ρ bsub]
  calc
    x.sum (fun k a => a * foxMatrixPres (substPresF ρ bsub) (Sum.inr ⟨s, z⟩) k) =
        old.sum (fun j a => a *
          foxMatrixPres (substPresF ρ bsub) (Sum.inr ⟨s, z⟩) (Sum.inl j)) +
        blocks.sum (fun p a => a *
          foxMatrixPres (substPresF ρ bsub) (Sum.inr ⟨s, z⟩) (Sum.inr p)) := by
      rw [hx, Finsupp.sum_sumElim]
      rfl
    _ = blocks.sum (fun p a => a *
        foxMatrixPres (substPresF ρ bsub) (Sum.inr ⟨s, z⟩) (Sum.inr p)) := by
      rw [ho, zero_add]
    _ = (fsBlockSlice x s).sum (fun m a => a *
        foxMatrixPres (substPresF ρ bsub) (Sum.inr ⟨s, z⟩) (Sum.inr ⟨s, m⟩)) := by
      rw [Finsupp.sigma_sum]
      apply Finset.sum_eq_single s
      · intro t _ hts
        simp [foxMatrix_inr_inr_of_ne ρ bsub hts z]
      · intro hs
        have hz : blocks.split s = 0 := by
          by_contra h
          exact hs ((Finsupp.mem_splitSupport_iff_nonzero blocks s).mpr h)
        simp [hz]

/-- The geometric block-local B2 input, with genuine finite support in the
block relators and coefficients in the whole substituted presentation group. -/
def BlockSurfaceGeneratesFS (c : ∀ s, Mt s →₀ R') : Prop :=
  ∀ (s : Sx) (β : Mt s →₀ R'),
    (∀ z : Zt s, β.sum (fun m a => a *
      foxMatrixPres (substPresF ρ bsub) (Sum.inr ⟨s, z⟩) (Sum.inr ⟨s, m⟩)) = 0) →
    ∃ w : R', ∀ m, β m = w * c s m

/-- A finite-block geometric B2 calculation feeds the arbitrary-family
assembly directly. Only each individual block's relator set is finite;
the ambient family and the retained presentation have no finiteness bound. -/
theorem blockSurfaceGeneratesFS_of_finite_blocks [∀ s, Fintype (Mt s)]
    (c : ∀ s, Mt s →₀ R')
    (hblock : ∀ (s : Sx) (β : Mt s → R'),
      (∀ z : Zt s, ∑ m : Mt s, β m *
        foxMatrixPres (substPresF ρ bsub) (Sum.inr ⟨s, z⟩) (Sum.inr ⟨s, m⟩) = 0) →
      ∃ w : R', ∀ m, β m = w * c s m) :
    BlockSurfaceGeneratesFS ρ bsub c := by simp_all [Finsupp.sum_fintype, hblock, BlockSurfaceGeneratesFS]

/-- Block-local B2 supplies a finite global preimage for every chain whose
actual Fox boundary lies entirely on the old generators. No finite-family
assumption and no global generation hypothesis is used. -/
theorem fsCellsBase_preimage_of_internal_zero (c : ∀ s, Mt s →₀ R')
    (hblock : BlockSurfaceGeneratesFS ρ bsub c)
    (x : (Jr ⊕ (Σ s, Mt s)) →₀ R')
    (hx : ∀ (s : Sx) (z : Zt s),
      coverSecondBoundary (relSub (substPresF ρ bsub)) (substPresF ρ bsub) x
        (Sum.inr ⟨s, z⟩) = 0) :
    ∃ y : (Jr ⊕ Sx) →₀ R', fsCellsBase c y = x ∧
      (∀ j, y (Sum.inl j) = x (Sum.inl j)) ∧
      (y.comapDomain Sum.inr Sum.inr_injective.injOn).support ⊆ fsBlockSupport x := by
  apply exists_fsCellsBase_preimage c x
  intro s
  apply hblock s (fsBlockSlice x s)
  intro z
  rw [← fsCoverSecondBoundary_inr ρ bsub]
  exact hx s z

/-- The actual coefficient-changing structural map has finite support at both
levels; its coefficient map is the already constructed `coeffF`. -/
def fsCellsF (hfill : FilledF ρ bsub) (c : ∀ s, Mt s →₀ R')
    (y : (Jr ⊕ Sx) →₀ MonoidAlgebra ℤ (PresGroup ρ)) :
    (Jr ⊕ (Σ s, Mt s)) →₀ R' :=
  fsCellsBase c (y.mapRange (coeffF ρ bsub hfill) (map_zero _))

omit [DecidableEq α] [DecidableEq Sx] [∀ s, DecidableEq (Zt s)] in
@[simp] theorem fsCellsF_inl (hfill : FilledF ρ bsub) (c : ∀ s, Mt s →₀ R')
    (y : (Jr ⊕ Sx) →₀ MonoidAlgebra ℤ (PresGroup ρ)) (j : Jr) :
    fsCellsF ρ bsub hfill c y (Sum.inl j) = coeffF ρ bsub hfill (y (Sum.inl j)) := rfl

omit [DecidableEq α] [DecidableEq Sx] [∀ s, DecidableEq (Zt s)] in
@[simp] theorem fsCellsF_inr (hfill : FilledF ρ bsub) (c : ∀ s, Mt s →₀ R')
    (y : (Jr ⊕ Sx) →₀ MonoidAlgebra ℤ (PresGroup ρ)) (s : Sx) (m : Mt s) :
    fsCellsF ρ bsub hfill c y (Sum.inr ⟨s, m⟩) =
      coeffF ρ bsub hfill (y (Sum.inr s)) * c s m := rfl

end Fox

end FiniteChains.BlockFamily

section
open scoped Classical
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Davis.Genus
open RACG Mirror Comb BlockFamily
variable (q : ℕ) [NeZero q]

theorem sum_namedSpineRel {M : Type*} [AddCommMonoid M]
    (f : NamedSpineRel q → M) :
    (∑ m, f m) = (∑ j : SpinePresentationRel q, f (Sum.inl j)) +
      ∑ i : Fin q × Bool, f (Sum.inr i) := by
  have hu : (Finset.univ : Finset (NamedSpineRel q)) =
      @Finset.univ (NamedSpineRel q)
        (instFintypeSum (SpinePresentationRel q) (Fin q × Bool)) :=
    congrArg (@Finset.univ (NamedSpineRel q)) (Subsingleton.elim _ _)
  simp_all

def namedSpineSurfaceWord : FreeGroup (NamedSpineGen q) :=
  commWord (fun i : Fin q × Bool => FreeGroup.of (Sum.inr i)) (finitePairs q)

def namedSpineSurfaceMarkingCoefficient (i : Fin q × Bool) :
    MonoidAlgebra ℤ (PresGroup (namedSpinePresentation q)) :=
  quotRingHom ℤ (relSub (namedSpinePresentation q))
    (fox (Sum.inr i) (namedSpineSurfaceWord q))

def normalizedNamedSpineVector (d : (universalNamedSpineCover q).F →₀ ℤ) :
    NamedSpineRel q → MonoidAlgebra ℤ (PresGroup (namedSpinePresentation q)) :=
  Sum.elim (fun j => ReceivedTree.cellCoefficient j d) (namedSpineSurfaceMarkingCoefficient q)

theorem universalSpineWordCoefficient (x : FreeGroupRing (SpinePresentationGen q)) :
    ReceivedTree.coefficientMap (markedSpineTree q) (universalSpineWordReceiver q) x =
      NamedPresentation.wordCoefficientMap (spinePresentation q) (spinePresentationMarkedWord q) x := by
  change MonoidAlgebra.mapDomainRingHom ℤ (universalSpineWordReceiver q)
      (MonoidAlgebra.mapDomainRingHom ℤ (QuotientGroup.mk' (relSub (spinePresentation q))) x) =
    MonoidAlgebra.mapDomainRingHom ℤ (QuotientGroup.mk' (relSub (namedSpinePresentation q)))
      (MonoidAlgebra.mapDomainRingHom ℤ (FreeGroup.map Sum.inl) x)
  simp only [BlockMor.mapDomainRingHom_comp']
  congr 1

theorem namedSpineSurfaceWord_fox_internal (z : SpinePresentationGen q) :
    fox (Sum.inl z) (namedSpineSurfaceWord q) = 0 := by
  have hw : namedSpineSurfaceWord q = FreeGroup.map Sum.inr
      (commWord (fun i : Fin q × Bool => FreeGroup.of i) (finitePairs q)) := by
    simp only [namedSpineSurfaceWord, map_commWord, FreeGroup.map.of]
  erw [hw]
  exact fox_map_of_not_mem_range Sum.inr (fun _ => Sum.inl_ne_inr) _

/-- An initial filling with this exact boundary exists before geometric
normalization. Its arbitrary homology class will subsequently be adjusted to
the explicitly constructed degree-one polygon. -/
theorem exists_universalNamedSpine_markedFilling :
    ∃ d : (universalNamedSpineCover q).F →₀ ℤ,
      Comb.bdry2 (universalNamedSpineCover q) d =
        ReceivedTree.markedChain (markedSpineTree q) (universalSpineWordReceiver q)
          (treeMarkedSpineLoop q) (namedSpineSurfaceMarkingCoefficient q) := by
  have hw : namedSpineSurfaceWord q ∈ relSub (namedSpinePresentation q) := by
    apply (QuotientGroup.eq_one_iff _).mp
    change (QuotientGroup.mk' (relSub (namedSpinePresentation q))) (namedSpineSurfaceWord q) = 1
    erw [namedSpineSurfaceWord, map_commWord]
    exact namedSpine_surface_filling q
  obtain ⟨c, hc⟩ := exists_coverSecondBoundary_of_mem_normalClosure
    (N := relSub (namedSpinePresentation q)) (ρ := namedSpinePresentation q)
    (fun m => Subgroup.subset_normalClosure ⟨m, rfl⟩) hw
  have hrow (a : NamedSpineGen q) :
      (∑ m, c m * foxMatrixPres (namedSpinePresentation q) a m) =
        quotRingHom ℤ (relSub (namedSpinePresentation q)) (fox a (namedSpineSurfaceWord q)) := by
    have h := congrArg (fun x => x a) hc
    erw [fsCoverSecondBoundary_apply, Finsupp.sum_fintype _ _ (fun _ => zero_mul _)] at h
    exact h
  have hm (i : Fin q × Bool) : c (Sum.inr i) = namedSpineSurfaceMarkingCoefficient q i := by
    have h := hrow (Sum.inr i)
    erw [sum_namedSpineRel] at h
    simpa [namedSpinePresentation,
      NamedPresentation.matrix_marked_relator, NamedPresentation.matrix_marked_name,
      namedSpineSurfaceMarkingCoefficient] using h
  let d  :=
    (ReceivedTree.cellCoordinates (SpinePresentationRel q)).symm (fun j => c (Sum.inl j))
  refine ⟨d, ?_⟩
  apply ReceivedTree.bdry2_eq_markedChain_of_coordinates
    (markedSpineTree q) (universalSpineWordReceiver q)
    (treeMarkedSpineLoop q) (namedSpineSurfaceMarkingCoefficient q) d
  intro z
  rw (config := { transparency := .default }) [ReceivedTree.cellCoefficient_bdry2]
  simp only [d, ReceivedTree.cellCoefficient_coordinates_symm,
    universalSpineWordCoefficient, treeMarkedSpineLoop]
  have hz := hrow (Sum.inl z)
  rw (config := { transparency := .default }) [namedSpineSurfaceWord_fox_internal, map_zero] at hz
  rw (config := { transparency := .default }) [sum_namedSpineRel] at hz
  simp only [namedSpinePresentation, NamedPresentation.matrix_internal_relator,
    NamedPresentation.matrix_internal_name, mul_neg, Finset.sum_neg_distrib,
    ← sub_eq_add_neg] at hz
  refine (sub_eq_zero.mp hz).trans ?_
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun x => x * NamedPresentation.wordCoefficientMap
    (spinePresentation q) (spinePresentationMarkedWord q)
    (fox z (spinePresentationMarkedWord q i))) (hm i)

/-- Every actual filling with the prescribed marked boundary gives all Fox
coordinates, including the name-relator coordinates, with their exact signs. -/

theorem spineReorderHom_fox (a : NamedSpineGen q) (w : FreeGroup (NamedSpineGen q)) :
    MonoidAlgebra.mapDomainRingHom ℤ (spineReorderHom q)
      (quotRingHom ℤ (relSub (namedSpinePresentation q)) (fox a w)) =
    quotRingHom ℤ (relSub (markedSpineBeta q))
      (fox (Sum.swap a) (FreeGroup.map Sum.swap w)) := by
  simpa only [fox_map Sum.swap (Equiv.sumComm _ _).injective] using
    spineReorderHom_coeff q (fox a w)

theorem spineReorderHom_matrix (a : NamedSpineGen q) (m : NamedSpineRel q) :
    MonoidAlgebra.mapDomainRingHom ℤ (spineReorderHom q)
      (foxMatrixPres (namedSpinePresentation q) a m) =
    foxMatrixPres (markedSpineBeta q) (Sum.swap a) m :=
  spineReorderHom_fox q a (namedSpinePresentation q m)

def normalizedMarkedSpineFilling (d : (universalNamedSpineCover q).F →₀ ℤ) :
    NamedSpineRel q →₀ MonoidAlgebra ℤ (PresGroup (markedSpineBeta q)) :=
  Finsupp.equivFunOnFinite.symm (fun m =>
    MonoidAlgebra.mapDomainRingHom ℤ (spineReorderHom q) (normalizedNamedSpineVector q d m))

@[simp] theorem normalizedMarkedSpineFilling_apply
    (d : (universalNamedSpineCover q).F →₀ ℤ) (m : NamedSpineRel q) :
    normalizedMarkedSpineFilling q d m =
      MonoidAlgebra.mapDomainRingHom ℤ (spineReorderHom q) (normalizedNamedSpineVector q d m) := rfl

/-- This is the full pre-substitution B1 certificate for the normalized
reference; it can replace the arbitrary Crowell choice without changing any
of the later substitution or family arguments. -/
theorem normalizedMarkedSpineFilling_boundary
    (d : (universalNamedSpineCover q).F →₀ ℤ)
    (hd : Comb.bdry2 (universalNamedSpineCover q) d =
      ReceivedTree.markedChain (markedSpineTree q) (universalSpineWordReceiver q)
        (treeMarkedSpineLoop q) (namedSpineSurfaceMarkingCoefficient q))
    (a : MarkedSpineGen q) :
    (∑ m, normalizedMarkedSpineFilling q d m * foxMatrixPres (markedSpineBeta q) a m) =
      quotRingHom ℤ (relSub (markedSpineBeta q))
        (fox a (commWord (fun i : Fin q × Bool => FreeGroup.of (Sum.inl i)) (finitePairs q))) := by
  have h := congrArg (MonoidAlgebra.mapDomainRingHom ℤ (spineReorderHom q))
    (show (∑ m, normalizedNamedSpineVector q d m * foxMatrixPres (namedSpinePresentation q) (Sum.swap a) m) =
      quotRingHom ℤ (relSub (namedSpinePresentation q)) (fox (Sum.swap a) (namedSpineSurfaceWord q)) by
      cases (Sum.swap a) with
      | inl z =>
          have h := congrArg (ReceivedTree.cellCoefficient z.1) hd
          erw [ReceivedTree.cellCoefficient_bdry2, ReceivedTree.cellCoefficient_markedChain] at h
          simp only [universalSpineWordCoefficient, treeMarkedSpineLoop] at h
          erw [namedSpineSurfaceWord_fox_internal, map_zero]
          rw (config := { transparency := .default }) [sum_namedSpineRel]
          simp only [namedSpinePresentation, NamedPresentation.matrix_internal_relator,
            NamedPresentation.matrix_internal_name, normalizedNamedSpineVector,
            Sum.elim_inl, Sum.elim_inr, mul_neg, Finset.sum_neg_distrib]
          convert sub_eq_zero.mpr h using 1 <;>
            simp only [sub_eq_add_neg, spinePresentation, spinePresentationMarkedWord] <;> rfl
      | inr i =>
          rw (config := { transparency := .default }) [sum_namedSpineRel]
          simp [namedSpinePresentation, NamedPresentation.matrix_marked_relator,
            NamedPresentation.matrix_marked_name, normalizedNamedSpineVector,
            namedSpineSurfaceMarkingCoefficient])
  simp only [map_sum, map_mul, spineReorderHom_matrix, spineReorderHom_fox,
    Sum.swap_swap] at h
  have hw : FreeGroup.map Sum.swap (namedSpineSurfaceWord q) =
      commWord (fun i : Fin q × Bool => FreeGroup.of (Sum.inl i)) (finitePairs q) := by
    simp only [namedSpineSurfaceWord, map_commWord, FreeGroup.map.of, Sum.swap_inr]
  simp_all

end FiniteChains.Davis.Genus
end

section
open scoped Classical
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

theorem universalOldBasePath :
    IsPath (spineOldCx q).src (spineOldCx q).tgt []
      (universalSpineOldBase q) (spineOldBase q) := universalSpineOldBase_eq q

def universalOldBaseTransport :
    Hom (uCover (spineOldCx q) (spineOldBase q))
      (uCover (spineOldCx q) (universalSpineOldBase q)) :=
  uCoverPathTransport (universalOldBasePath q)

theorem universalOldBaseTransport_base :
    (universalOldBaseTransport q).onV (UV.base (spineOldCx q) (spineOldBase q)) =
      UV.base (spineOldCx q) (universalSpineOldBase q) := by
  erw [universalOldBaseTransport, uCoverPathTransport_base]
  rfl

def universalSpineMarkingChains :
    ((PresGroup (namedSpinePresentation q) × (Fin q × Bool)) →₀ ℤ) →ₗ[ℤ]
      ((uCover (spineOldCx q) (universalSpineOldBase q)).E →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun x => pathChain (uLiftPath (spineOldMarking q x.2)
    (deckV (universalSpineOldReceiver q x.1) (UV.base (spineOldCx q) (universalSpineOldBase q)))))

def universalSurfaceMarkingChains :
    ((PresGroup (namedSpinePresentation q) × (Fin q × Bool)) →₀ ℤ) →ₗ[ℤ]
      ((uCover (spineOldCx q) (universalSpineOldBase q)).E →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun x => pathChain (uLiftPath (surfaceOldMarking q x.2)
    (deckV (universalSpineOldReceiver q x.1) (UV.base (spineOldCx q) (universalSpineOldBase q)))))

def universalOldMarkingCorrection (g : PresGroup (namedSpinePresentation q)) (i : Fin q × Bool) :
    (uCover (spineOldCx q) (universalSpineOldBase q)).F →₀ ℤ :=
  (univDeck (spineOldCx q) (universalSpineOldBase q)).faceChains
    (universalSpineOldReceiver q g)
    (chain2 (universalOldBaseTransport q) (spineOldMarkingCorrection q i))

theorem universalOldMarkingCorrection_boundary
    (g : PresGroup (namedSpinePresentation q)) (i : Fin q × Bool) :
    Comb.bdry2 _ (universalOldMarkingCorrection q g i) =
      pathChain (uLiftPath (spineOldMarking q i)
        (deckV (universalSpineOldReceiver q g) (UV.base (spineOldCx q) (universalSpineOldBase q)))) -
      pathChain (uLiftPath (surfaceOldMarking q i)
        (deckV (universalSpineOldReceiver q g) (UV.base (spineOldCx q) (universalSpineOldBase q)))) := by
  erw [universalOldMarkingCorrection, DeckAction.faceChains_boundary, bdry2_chain2,
    spineOldMarkingCorrection_boundary, map_sub, map_sub]
  have hp : IsPath (spineOldCx q).src (spineOldCx q).tgt (spineOldMarking q i)
      (endV (UV.base (spineOldCx q) (universalSpineOldBase q))) (universalSpineOldBase q) := by
    erw [endV_base, universalSpineOldBase_eq]
    exact spineOldMarking_isPath q i
  have hs : IsPath (spineOldCx q).src (spineOldCx q).tgt (surfaceOldMarking q i)
      (endV (UV.base (spineOldCx q) (universalSpineOldBase q))) (universalSpineOldBase q) := by
    erw [endV_base, universalSpineOldBase_eq]
    exact surfaceOldMarking_isPath q i
  erw [universalOldBaseTransport,
    uCoverPathTransport_pathChain _ _ (spineOldMarking_isPath q i),
    uCoverPathTransport_pathChain _ _ (surfaceOldMarking_isPath q i)]
  erw [universalOldBaseTransport_base, univDeck_pathChain _ _ _ hp,
    univDeck_pathChain _ _ _ hs]

def universalOldMarkingCorrections :
    ((PresGroup (namedSpinePresentation q) × (Fin q × Bool)) →₀ ℤ) →ₗ[ℤ]
      ((uCover (spineOldCx q) (universalSpineOldBase q)).F →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun x => universalOldMarkingCorrection q x.1 x.2)

theorem universalOldMarkingCorrections_boundary
    (c : (PresGroup (namedSpinePresentation q) × (Fin q × Bool)) →₀ ℤ) :
    Comb.bdry2 _ (universalOldMarkingCorrections q c) =
      universalSpineMarkingChains q c - universalSurfaceMarkingChains q c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
    erw [map_add, map_add, hc, hd, map_add, map_add]
    abel
  | single x n =>
    simp only [universalOldMarkingCorrections, universalSpineMarkingChains,
      universalSurfaceMarkingChains, Finsupp.linearCombination_single, map_smul,
      universalOldMarkingCorrection_boundary, smul_sub]

theorem universalSpine_marking_path (i : Fin q × Bool) :
    mapPath (universalSpineToOld q) (treeMarkedSpineLoop q i).1 = spineOldMarking q i := by
  erw [← mapPath_comp, markedSpineLoop_inclusion]
  rfl

theorem universalSpine_receiver_root (g : PresGroup (namedSpinePresentation q)) :
    ReceivedTree.receiverVertex (markedSpineTree q) (universalSpineToOld q)
      (universalSpineOldReceiver q) g (markedSpineTree q).root =
        deckV (universalSpineOldReceiver q g) (UV.base (spineOldCx q) (universalSpineOldBase q)) := by
  simp only [ReceivedTree.receiverVertex, SpanningTree.mappedTreeReference,
    SpanningTree.treePath_root, mapPath, List.map_nil, extendList_nil]

theorem universalSpineMarkingChains_eq
    (c : (PresGroup (namedSpinePresentation q) × (Fin q × Bool)) →₀ ℤ) :
    chain1 (universalNamedSpineComparison q)
      (ReceivedTree.markedChainMap (markedSpineTree q) (universalSpineWordReceiver q)
        (fun i => (treeMarkedSpineLoop q i).1) c) = universalSpineMarkingChains q c := by
  erw [universalNamedSpineComparison, ReceivedTree.comparison_markedChainMap]
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single x n =>
    simp only [ReceivedTree.geometricMarkedChainMap, universalSpineMarkingChains,
      Finsupp.linearCombination_single, universalSpine_marking_path, universalSpine_receiver_root]

def universalReferenceMarkingCoefficients :
    (PresGroup (namedSpinePresentation q) × (Fin q × Bool)) →₀ ℤ :=
  (ReceivedTree.cellCoordinates (Fin q × Bool)).symm (namedSpineSurfaceMarkingCoefficient q)

def universalReferenceOldChain :
    (uCover (spineOldCx q) (universalSpineOldBase q)).F →₀ ℤ :=
  universalOldPolygonChain q + universalOldMarkingCorrections q (universalReferenceMarkingCoefficients q)

/-- Once the exact polygon boundary is read in marked Fox coordinates, the
prescribed old class has precisely the original received-spine boundary. -/
theorem universalReferenceOldChain_boundary
    (hpolygon : Comb.bdry2 _ (universalOldPolygonChain q) =
      universalSurfaceMarkingChains q (universalReferenceMarkingCoefficients q)) :
    Comb.bdry2 _ (universalReferenceOldChain q) =
      chain1 (universalNamedSpineComparison q)
        (ReceivedTree.markedChain (markedSpineTree q) (universalSpineWordReceiver q)
          (treeMarkedSpineLoop q) (namedSpineSurfaceMarkingCoefficient q)) := by
  erw [ReceivedTree.markedChain, universalSpineMarkingChains_eq]
  erw [universalReferenceOldChain, map_add, hpolygon, universalOldMarkingCorrections_boundary]
  abel

end FiniteChains.Davis.Genus
end

namespace FiniteChains

open MonoidAlgebra

universe u v w x

variable {H : Type u} {G : Type v} [Group H] [Group G]
  {J : Type w} [Fintype J] {I : Type x}

/-- Principal generation of matrix cycles survives an injective group-ring extension.
Only the column type is finite.  Multiplication is in the indicated order,
so this applies to noncommutative group rings. -/
theorem principal_cycles_baseChange (f : H →* G) (hf : Function.Injective f)
    (A : I → J → MonoidAlgebra ℤ H) (c : J → MonoidAlgebra ℤ H)
    (hgen : ∀ y : J → MonoidAlgebra ℤ H,
      (∀ i, ∑ j, y j * A i j = 0) →
        ∃ r : MonoidAlgebra ℤ H, ∀ j, y j = r * c j)
    (v : J → MonoidAlgebra ℤ G)
    (hv : ∀ i, ∑ j, v j * MonoidAlgebra.mapDomainRingHom ℤ f (A i j) = 0) :
    ∃ r : MonoidAlgebra ℤ G,
      ∀ j, v j = r * MonoidAlgebra.mapDomainRingHom ℤ f (c j) := by
  let e  := MonoidHom.ofInjective hf
  let er  :=
    MonoidAlgebra.mapDomainRingHom ℤ e.toMonoidHom
  let eri  :=
    MonoidAlgebra.mapDomainRingHom ℤ e.symm.toMonoidHom
  have hinc z :
      subRingHom f.range (er z) = MonoidAlgebra.mapDomainRingHom ℤ f z := by
    show MonoidAlgebra.mapDomain f.range.subtype (MonoidAlgebra.mapDomain e.toMonoidHom z) =
      MonoidAlgebra.mapDomain f z
    rw [← MonoidAlgebra.mapDomain_comp]
    rfl
  have her_inj : Function.Injective er := MonoidAlgebra.mapDomain_injective e.injective
  have her_eri z : er (eri z) = z := by
    show MonoidAlgebra.mapDomain e.toMonoidHom
      (MonoidAlgebra.mapDomain e.symm.toMonoidHom z) = z
    rw [← MonoidAlgebra.mapDomain_comp]
    have he : e.toMonoidHom ∘
        e.symm.toMonoidHom = id := by
      funext g
      exact e.apply_symm_apply g
    rw [he, MonoidAlgebra.mapDomain_id]
  let Ar := fun i j => er (A i j)
  have hvr : ∀ i, ∑ j, v j * subRingHom f.range (Ar i j) = 0 := by
    intro i
    simpa only [Ar, hinc] using hv i
  have hspan := cycle_mem_span_subgroup_cycles f.range Ar v hvr
  refine Submodule.span_induction
   
    ?_ ?_ ?_ ?_ hspan
  · rintro z ⟨y, hy, rfl⟩
    have hy' : ∀ i, ∑ j, eri (y j) * A i j = 0 := by
      intro i
      apply her_inj
      rw [map_sum, map_zero]
      rw [← hy i]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, her_eri]
    obtain ⟨r, hr⟩ := hgen (fun j => eri (y j)) hy'
    refine ⟨MonoidAlgebra.mapDomainRingHom ℤ f r, fun j => ?_⟩
    calc
      subRingHom f.range (y j) = MonoidAlgebra.mapDomainRingHom ℤ f (eri (y j)) := by
        rw [← hinc, her_eri]
      _ = MonoidAlgebra.mapDomainRingHom ℤ f (r * c j) :=
        congrArg (MonoidAlgebra.mapDomainRingHom ℤ f) (hr j)
      _ = MonoidAlgebra.mapDomainRingHom ℤ f r *
          MonoidAlgebra.mapDomainRingHom ℤ f (c j) := map_mul _ _ _
  · refine ⟨0, fun j => ?_⟩
    simp
  · rintro a b _ _ ⟨r, hr⟩ ⟨s, hs⟩
    refine ⟨r + s, fun j => ?_⟩
    change a j + b j = (r + s) * MonoidAlgebra.mapDomainRingHom ℤ f (c j)
    rw [hr j, hs j, add_mul]
  · rintro a z _ ⟨r, hr⟩
    refine ⟨a * r, fun j => ?_⟩
    change a * z j = (a * r) * MonoidAlgebra.mapDomainRingHom ℤ f (c j)
    rw [hr j, mul_assoc]

end FiniteChains

section
open scoped Classical
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb
universe u
variable {X : Complex2.{u}} {a : X.V} {I : Type u}
  (N : Subgroup (FreeGroup I)) [N.Normal]
  (p : I → Loop X a) (ψ : (FreeGroup I ⧸ N) →* Pi1 X a)
  (hψ : ∀ i, ψ (qof N i) = Pi1.mk (p i))

def loopCoefficientVertex (g : FreeGroup I ⧸ N) : UV X a :=
  deckV (ψ g) (UV.base X a)

theorem loopCoefficientVertex_end (g : FreeGroup I ⧸ N) :
    endV (loopCoefficientVertex N ψ g) = a := by
  rw [loopCoefficientVertex, endV_deckV, endV_base]

include hψ in
theorem extendList_loopCoefficientVertex (i : I) (g : FreeGroup I ⧸ N) :
    extendList (p i).1 (loopCoefficientVertex N ψ g) =
      loopCoefficientVertex N ψ (g * qof N i) := by
  rw [loopCoefficientVertex, extendList_deckV, ← deckV_loop_base, ← hψ,
    ← deckV_mul, ← map_mul]
  rfl



def loopCoefficientChainMap : ((FreeGroup I ⧸ N) × I →₀ ℤ) →ₗ[ℤ] (UE X a →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun x =>
    pathChain (uLiftPath (p x.2).1 (loopCoefficientVertex N ψ x.1)))

include hψ in
/-- Replace each formal generator edge by its actual lifted loop. Negative
letters contribute the reverse path at the preceding sheet, exactly as Fox
differentiation requires. -/
theorem loopCoefficientChainMap_liftPath (l : List (I × Bool)) (g : FreeGroup I ⧸ N) :
    loopCoefficientChainMap N p ψ (pathChain (liftPath (Nsub := N) l g)) =
      pathChain (uLiftPath (wordPath p l) (loopCoefficientVertex N ψ g)) := by
  induction l generalizing g with
  | nil => rfl
  | cons ib l ih =>
      obtain ⟨i, b⟩ := ib
      cases b with
      | true =>
          have hp : IsPath X.src X.tgt (p i).1 (endV (loopCoefficientVertex N ψ g)) a := by
            rw [loopCoefficientVertex_end]
            exact (p i).2
          rw [liftPath_cons_true, pathChain_cons, wordPath_cons, germLoopPath_pos,
            uLiftPath_append _ _ _ a hp, pathChain_append,
            extendList_loopCoefficientVertex N p ψ hψ, map_add, ih]
          simp only [↓reduceIte, loopCoefficientChainMap,
            Finsupp.linearCombination_single, one_smul]
      | false =>
          have hp : IsPath X.src X.tgt (revPath (p i).1)
              (endV (loopCoefficientVertex N ψ g)) a := by
            rw [loopCoefficientVertex_end]
            exact isPath_revPath (p i).2
          rw [liftPath_cons_false, pathChain_cons, wordPath_cons, germLoopPath_neg,
            uLiftPath_append _ _ _ a hp, pathChain_append,
            (show extendList (revPath (p i).1) (loopCoefficientVertex N ψ g) =
      loopCoefficientVertex N ψ (g * (qof N i)⁻¹) by
              rw [loopCoefficientVertex, extendList_deckV]
              rw [← deckV_loop_base ⟨revPath (p i).1, isPath_revPath (p i).2⟩]
              change deckV (ψ g) (deckV ((Pi1.mk (p i))⁻¹) (UV.base X a)) = _
              rw [← hψ, ← map_inv, ← deckV_mul, ← map_mul]
              rfl), map_add, ih,
            (show pathChain (uLiftPath (revPath (p i).1) (loopCoefficientVertex N ψ g)) =
      -pathChain (uLiftPath (p i).1 (loopCoefficientVertex N ψ (g * (qof N i)⁻¹))) by
              have hp : IsPath X.src X.tgt (p i).1
                  (endV (loopCoefficientVertex N ψ (g * (qof N i)⁻¹))) a := by
                rw [loopCoefficientVertex_end]
                exact (p i).2
              have hl := isPath_uLiftPath (p i).1 (loopCoefficientVertex N ψ (g * (qof N i)⁻¹)) a hp
              have hcancel : (g * (qof N i)⁻¹) * qof N i = g := by group
              rw [extendList_loopCoefficientVertex N p ψ hψ, hcancel] at hl
              have hr := eq_uLiftPath_of_isPath _ _ _ (isPath_revPath hl)
              have hproj : mapPath (univProj X a)
                  (uLiftPath (p i).1 (loopCoefficientVertex N ψ (g * (qof N i)⁻¹))) = (p i).1 :=
                map_uLiftPath (p i).1 _ a hp
              rw [mapPath_revPath, hproj] at hr
              rw [← hr, pathChain_revPath])]
          simp only [Bool.false_eq_true, ↓reduceIte, map_neg,
            loopCoefficientChainMap, Finsupp.linearCombination_single, one_smul]

variable [Fintype I] [DecidableEq I]

include hψ in
/-- The full coefficient vector is the projected Fox gradient of the word;
the result keeps each individual translated generator-loop chain. -/
theorem lifted_wordPath_fox (l : List (I × Bool)) :
    pathChain (uLiftPath (wordPath p l) (UV.base X a)) =
      loopCoefficientChainMap N p ψ
        ((coords N I).symm (fun i => proj N (fox i (FreeGroup.mk l)))) := by
  have hcoords : coords N I (pathChain (liftPath l 1)) =
      fun i => proj N (fox i (FreeGroup.mk l)) := by
    simpa only [show (MonoidAlgebra.single (1 : FreeGroup I ⧸ N) (1 : ℤ)) = 1 from rfl,
      one_mul] using coords_pathChain_liftPath l (1 : FreeGroup I ⧸ N)
  have hc := congrArg (coords N I).symm hcoords
  rw [LinearEquiv.symm_apply_apply] at hc
  rw [← hc, loopCoefficientChainMap_liftPath N p ψ hψ]
  simp only [loopCoefficientVertex, map_one, deckV_one]

end FiniteChains.Comb
end

namespace FiniteChains.BlockFamily


variable {α Jr Sx : Type} {Zt Mt : Sx → Type}
  (ρ : Jr ⊕ Sx → FreeGroup α)
  (bsub : ∀ s : Sx, Mt s → FreeGroup (α ⊕ Zt s))

/-- Replace only the selected original relator, retaining all other entries. -/
abbrev IndividualGroup (s : Sx) :=
  PresGroup (substPresF (oneRel ρ s) (fun _ : PUnit.{1} => bsub s))

/-- The actual inclusion of the generators of one individual substitution. -/
def individualGenEmb (s : Sx) :
    α ⊕ (Σ _ : PUnit.{1}, Zt s) → α ⊕ (Σ t : Sx, Zt t) :=
  Sum.elim Sum.inl (fun p => Sum.inr ⟨s, p.2⟩)

theorem individualGenEmb_old (s : Sx) (w : FreeGroup α) :
    FreeGroup.map (individualGenEmb (Zt := Zt) s)
        (FreeGroup.map (Sum.inl (β := Σ _ : PUnit.{1}, Zt s)) w) =
      FreeGroup.map (Sum.inl (β := Σ t : Sx, Zt t)) w := by
  have h : (FreeGroup.map (individualGenEmb (α := α) s)).comp
      (FreeGroup.map (Sum.inl)) =
      FreeGroup.map (Sum.inl (β := Σ t : Sx, Zt t)) := by
    apply FreeGroup.ext_hom
    intro a
    simp [individualGenEmb]
  exact DFunLike.congr_fun h w

theorem individualGenEmb_block (s : Sx) (w : FreeGroup (α ⊕ Zt s)) :
    FreeGroup.map (individualGenEmb (Zt := Zt) s)
        (FreeGroup.map (genEmb (Zt := fun _ : PUnit.{1} => Zt s) PUnit.unit) w) =
      FreeGroup.map (genEmb (Zt := Zt) s) w := by
  have h : (FreeGroup.map (individualGenEmb (α := α) s)).comp
      (FreeGroup.map (genEmb PUnit.unit)) =
      FreeGroup.map (genEmb (Zt := Zt) s) := by
    apply FreeGroup.ext_hom
    rintro (a | z) <;> simp [individualGenEmb, genEmb]
  exact DFunLike.congr_fun h w

/-- The canonical map of an individual substituted factor to the simultaneous group.
Its definition uses the genuine simultaneous fillings to kill the other old entries. -/
def factorToFamily (hfill : FilledF ρ bsub) (s : Sx) :
    IndividualGroup ρ bsub s →* PresGroup (substPresF ρ bsub) :=
  QuotientGroup.lift _
    ((QuotientGroup.mk' (relSub (substPresF ρ bsub))).comp
      (FreeGroup.map (individualGenEmb (Zt := Zt) s))) (by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨k, rfl⟩
    change (QuotientGroup.mk (FreeGroup.map (individualGenEmb (Zt := Zt) s)
      (substPresF (oneRel ρ s) (fun _ : PUnit.{1} => bsub s) k)) :
      PresGroup (substPresF ρ bsub)) = 1
    rcases k with (r | ⟨p, m⟩)
    · rw [substPresF_inl, individualGenEmb_old]
      rcases r with (r | t)
      · exact (QuotientGroup.eq_one_iff _).2
          (Subgroup.subset_normalClosure ⟨Sum.inl r, rfl⟩)
      · exact (QuotientGroup.eq_one_iff _).2 (hfill t.val)
    · cases p
      rw [substPresF_inr, individualGenEmb_block]
      exact (QuotientGroup.eq_one_iff _).2
        (Subgroup.subset_normalClosure ⟨Sum.inr ⟨s, m⟩, rfl⟩))

@[simp] theorem factorToFamily_mk (hfill : FilledF ρ bsub) (s : Sx)
    (w : FreeGroup (α ⊕ (Σ _ : PUnit.{1}, Zt s))) :
    factorToFamily ρ bsub hfill s (QuotientGroup.mk w) =
      QuotientGroup.mk (FreeGroup.map (individualGenEmb (Zt := Zt) s) w) := rfl

/-- The original group maps to an individual factor by the single substitution,
with the original relator indexing restored. -/
def individualBase
    (hone : ∀ s, FilledF (oneRel ρ s) (fun _ : PUnit.{1} => bsub s))
    (s : Sx) : PresGroup ρ →* IndividualGroup ρ bsub s :=
  (substHomF (oneRel ρ s) (fun _ : PUnit.{1} => bsub s) (hone s)).comp
    (oneEquiv ρ s).toMonoidHom

@[simp] theorem individualBase_mk
    (hone : ∀ s, FilledF (oneRel ρ s) (fun _ : PUnit.{1} => bsub s))
    (s : Sx) (w : FreeGroup α) :
    individualBase ρ bsub hone s (QuotientGroup.mk w) =
      QuotientGroup.mk (FreeGroup.map (Sum.inl (β := Σ _ : PUnit.{1}, Zt s)) w) := rfl


/-- The block free group maps to its own individual substituted factor. -/
def individualBlockFree (s : Sx) : FreeGroup (α ⊕ Zt s) →* IndividualGroup ρ bsub s :=
  (QuotientGroup.mk' _).comp
    (FreeGroup.map (genEmb (Zt := fun _ : PUnit.{1} => Zt s) PUnit.unit))

theorem individualBlockFree_mark
    (hone : ∀ s, FilledF (oneRel ρ s) (fun _ : PUnit.{1} => bsub s))
    (s : Sx) (a : α) :
    individualBlockFree ρ bsub s (FreeGroup.of (Sum.inl a)) =
      individualBase ρ bsub hone s (QuotientGroup.mk (FreeGroup.of a)) := rfl


/-- A concrete marked receiver in the wide amalgamated product of the individual factors. -/
def familyAmalgamMaps
    (hone : ∀ s, FilledF (oneRel ρ s) (fun _ : PUnit.{1} => bsub s)) :
    BlockMaps ρ bsub (Monoid.PushoutI.base (individualBase ρ bsub hone)) where
  b s := (Monoid.PushoutI.of s).comp (individualBlockFree ρ bsub s)
  mark s a := by
    rw [MonoidHom.comp_apply, individualBlockFree_mark ρ bsub hone,
      Monoid.PushoutI.of_apply_eq_base]
  rel s m := by rw [MonoidHom.comp_apply, (show individualBlockFree ρ bsub s (bsub s m) = 1 by
    apply (QuotientGroup.eq_one_iff _).2
    exact Subgroup.subset_normalClosure ⟨Sum.inr ⟨PUnit.unit, m⟩, rfl⟩), map_one]

/-- The comparison from the simultaneous presentation to the actual wide pushout. -/
def familyToAmalgam
    (hone : ∀ s, FilledF (oneRel ρ s) (fun _ : PUnit.{1} => bsub s)) :
    PresGroup (substPresF ρ bsub) →* Monoid.PushoutI (individualBase ρ bsub hone) :=
  (familyAmalgamMaps ρ bsub hone).psi

@[simp] theorem familyToAmalgam_old
    (hone : ∀ s, FilledF (oneRel ρ s) (fun _ : PUnit.{1} => bsub s)) (a : α) :
    familyToAmalgam ρ bsub hone (QuotientGroup.mk (FreeGroup.of (Sum.inl a))) =
      Monoid.PushoutI.base (individualBase ρ bsub hone)
        (QuotientGroup.mk (FreeGroup.of a)) := rfl

@[simp] theorem familyToAmalgam_internal
    (hone : ∀ s, FilledF (oneRel ρ s) (fun _ : PUnit.{1} => bsub s))
    (s : Sx) (z : Zt s) :
    familyToAmalgam ρ bsub hone
        (QuotientGroup.mk (FreeGroup.of (Sum.inr ⟨s, z⟩))) =
      Monoid.PushoutI.of s (individualBlockFree ρ bsub s (FreeGroup.of (Sum.inr z))) := rfl

/-- The factor comparison triangle identifies the composite with the genuine pushout injection. -/
theorem familyToAmalgam_comp_factor (hfill : FilledF ρ bsub)
    (hone : ∀ s, FilledF (oneRel ρ s) (fun _ : PUnit.{1} => bsub s)) (s : Sx) :
    (familyToAmalgam ρ bsub hone).comp (factorToFamily ρ bsub hfill s) =
      Monoid.PushoutI.of s := by
  have hw : ((familyToAmalgam ρ bsub hone).comp (factorToFamily ρ bsub hfill s)).comp
      (QuotientGroup.mk' _) =
      (Monoid.PushoutI.of s).comp
        (QuotientGroup.mk' _) := by
    apply FreeGroup.ext_hom
    rintro (a | ⟨p, z⟩)
    · change familyToAmalgam ρ bsub hone
        (QuotientGroup.mk (FreeGroup.of (Sum.inl a))) =
          Monoid.PushoutI.of s
            (individualBase ρ bsub hone s (QuotientGroup.mk (FreeGroup.of a)))
      rw [familyToAmalgam_old, Monoid.PushoutI.of_apply_eq_base]
    · rfl
  apply MonoidHom.ext
  intro x
  induction x using QuotientGroup.induction_on with
  | _ w => exact DFunLike.congr_fun hw w




/-- Each individual factor embeds when every individual substitution embeds the original group.
The only injectivity input concerns the already constructed individual base maps. -/
theorem factorToFamily_injective (hfill : FilledF ρ bsub)
    (hone : ∀ s, FilledF (oneRel ρ s) (fun _ : PUnit.{1} => bsub s))
    (hinj : ∀ s, Function.Injective
      (substHomF (oneRel ρ s) (fun _ : PUnit.{1} => bsub s) (hone s)))
    (s : Sx) : Function.Injective (factorToFamily ρ bsub hfill s) := by
  have hj : ∀ s, Function.Injective (individualBase ρ bsub hone s) :=
    fun t => (hinj t).comp (oneEquiv ρ t).injective
  have hs := Monoid.PushoutI.of_injective hj s
  intro x y hxy
  apply hs
  calc
    Monoid.PushoutI.of s x =
        familyToAmalgam ρ bsub hone (factorToFamily ρ bsub hfill s x) :=
      (DFunLike.congr_fun (familyToAmalgam_comp_factor ρ bsub hfill hone s) x).symm
    _ = familyToAmalgam ρ bsub hone (factorToFamily ρ bsub hfill s y) :=
      congrArg (familyToAmalgam ρ bsub hone) hxy
    _ = Monoid.PushoutI.of s y :=
      DFunLike.congr_fun (familyToAmalgam_comp_factor ρ bsub hfill hone s) y

end FiniteChains.BlockFamily

namespace FiniteChains.Davis.Genus

open RACG Mirror Comb PresModel BlockFamily


variable {α Jr Sx : Type} (ρ : Jr ⊕ Sx → FreeGroup α)
  (q : Sx → ℕ) [∀ s, NeZero (q s)]
  (u : ∀ s, Fin (q s) × Bool → FreeGroup α)
  (hrho : ∀ s, ρ (Sum.inr s) = commWord (u s) (finitePairs (q s)))

include hrho in
/-- The genuine fillings in each individual substitution. -/
theorem finiteSpineIndividualFillings :
    ∀ s, FilledF (oneRel ρ s)
      (fun _ : PUnit.{1} => familyFiniteSpineWordBlock q u s) :=
  fun s => finiteSpineWordBlock_filled (oneRel ρ s) (q s) (u s) (hrho s)

/-- The concrete map of an individual spine substitution into the simultaneous one. -/
def finiteSpineFactorToFamily (s : Sx) :
    IndividualGroup ρ (familyFiniteSpineWordBlock q u) s →*
      PresGroup (substPresF ρ (familyFiniteSpineWordBlock q u)) :=
  factorToFamily ρ (familyFiniteSpineWordBlock q u)
    (familyFiniteSpineWordBlock_filled ρ q u hrho) s

@[simp] theorem finiteSpineFactorToFamily_mk (s : Sx)
    (w : FreeGroup (α ⊕ (Σ _ : PUnit.{1}, SpinePresentationGen (q s)))) :
    finiteSpineFactorToFamily ρ q u hrho s (QuotientGroup.mk w) =
      QuotientGroup.mk (FreeGroup.map
        (individualGenEmb (Zt := fun t => SpinePresentationGen (q t)) s) w) := rfl

/-- Every actual individual spine factor embeds, for an arbitrary family of genera. -/
theorem finiteSpineFactorToFamily_injective (s : Sx) :
    Function.Injective (finiteSpineFactorToFamily ρ q u hrho s) :=
  factorToFamily_injective ρ (familyFiniteSpineWordBlock q u)
    (familyFiniteSpineWordBlock_filled ρ q u hrho)
    (finiteSpineIndividualFillings ρ q u hrho)
    (fun t => finiteSpineWordBlock_injective (oneRel ρ t) (q t) (u t) (hrho t)) s

/-- The coefficient inclusion of an actual individual spine factor. -/
def finiteSpineFactorRingHom (s : Sx) :
    MonoidAlgebra ℤ (IndividualGroup ρ (familyFiniteSpineWordBlock q u) s) →+*
      MonoidAlgebra ℤ (PresGroup (substPresF ρ (familyFiniteSpineWordBlock q u))) :=
  MonoidAlgebra.mapDomainRingHom ℤ (finiteSpineFactorToFamily ρ q u hrho s)

end FiniteChains.Davis.Genus

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Davis
open Comb
universe u v

def commutatorLetterBlock {ι : Type u} (p : ι × ι) : List (ι × Bool) :=
  [(p.1, true), (p.2, true), (p.1, false), (p.2, false)]

def commutatorLetters {ι : Type u} (ps : List (ι × ι)) : List (ι × Bool) :=
  ps.flatMap commutatorLetterBlock

theorem mk_commutatorLetterBlock {ι : Type u} (p : ι × ι) :
    FreeGroup.mk (commutatorLetterBlock p) =
      FreeGroup.of p.1 * FreeGroup.of p.2 * (FreeGroup.of p.1)⁻¹ * (FreeGroup.of p.2)⁻¹ := rfl

theorem mk_commutatorLetters {ι : Type u} (ps : List (ι × ι)) :
    FreeGroup.mk (commutatorLetters ps) = commWord FreeGroup.of ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      erw [← FreeGroup.mul_mk, mk_commutatorLetterBlock, ih, commWord_cons]

theorem wordPath_commutatorLetters {X : Complex2.{u}} {a : X.V} {ι : Type u}
    (f : ι → Loop X a) (ps : List (ι × ι)) :
    wordPath f (commutatorLetters ps) = surfacePath f ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      erw [wordPath_append, ih]
      simp only [commutatorLetterBlock, wordPath_cons, wordPath_nil,
        germLoopPath_pos, germLoopPath_neg, List.append_nil, surfacePath,
        List.append_assoc]

theorem surfacePath_append {X : Complex2.{u}} {a : X.V} {ι : Type u}
    (f : ι → Loop X a) (ps rs : List (ι × ι)) :
    surfacePath f (ps ++ rs) = surfacePath f ps ++ surfacePath f rs := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [List.cons_append, surfacePath, ih, List.append_assoc]

theorem surfacePath_eq_flatMap {X : Complex2.{u}} {a : X.V} {ι : Type u}
    (f : ι → Loop X a) (ps : List (ι × ι)) :
    surfacePath f ps = ps.flatMap (fun p =>
      (f p.1).1 ++ (f p.2).1 ++ revPath (f p.1).1 ++ revPath (f p.2).1) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [surfacePath, List.flatMap_cons, ih, List.append_assoc]

theorem wordPath_map_letters {X : Complex2.{u}} {a : X.V} {ι κ : Type v}
    (f : κ → Loop X a) (j : ι → κ) (l : List (ι × Bool)) :
    wordPath f (l.map (fun x => (j x.1, x.2))) = wordPath (fun i => f (j i)) l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
      simp only [List.map_cons, wordPath_cons, ih]
      rfl

namespace Genus
open RACG Mirror PresModel BlockFamily
variable (q : ℕ)

/-- Exactly the four oriented letters of each handle, in polygon order. -/
def genusSurfaceLetters : List ((Fin q × Bool) × Bool) :=
  (finitePairs q).flatMap (fun p =>
    [(p.1, true), (p.2, true), (p.1, false), (p.2, false)])


variable [NeZero q]

def naturalSurfaceLoops (i : ℕ × Bool) : Loop (sdCx (gc q)) (gBase q) :=
  ⟨gSig q i, isPath_gSig q i⟩


/-- Every initial string of complete handle blocks is the actual polygon
boundary prefix, with its original edge order and signs. -/
theorem surfacePath_genPairs_eq_bdPath {n : ℕ} (hn : n ≤ q) :
    surfacePath (naturalSurfaceLoops q) (genPairs n) = bdPath (gc q) (8 * n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hlt : n < q := by omega
      have hpairs : genPairs (n + 1) = genPairs n ++ [((n, false), (n, true))] := by
        simp only [genPairs, List.range_succ, List.map_append, List.map_singleton]
      erw [hpairs, surfacePath_append, ih (by omega),
        (show surfacePath (naturalSurfaceLoops q) [((n, false), (n, true))] = gBlock q n by
          have ha : (naturalSurfaceLoops q (n, false)).1 = gPath q (8 * n) := by
            simp only [naturalSurfaceLoops, gSig, Nat.mod_eq_of_lt hlt, Bool.false_eq_true,
              ↓reduceIte, Nat.add_zero]
          have hb : (naturalSurfaceLoops q (n, true)).1 = gPath q (8 * n + 2) := by
            simp only [naturalSurfaceLoops, gSig, Nat.mod_eq_of_lt hlt, ↓reduceIte]
          simp only [surfacePath, ha, hb, List.append_nil]
          erw [← gPath_rev_a q hlt, ← gPath_rev_b q hlt]), bdPath_block]

theorem finiteSurfacePath_eq_bdPath :
    surfacePath (finiteMarkedLoops q) (finitePairs q) = bdPath (gc q) (8 * q) := by
  have hreindex : surfacePath (finiteMarkedLoops q) (finitePairs q) =
      surfacePath (naturalSurfaceLoops q) (genPairs q) := by
    simp only [surfacePath_eq_flatMap, finitePairs, genPairs, List.flatMap_map]
    have hrange := List.map_coe_finRange_eq_range (n := q)
    erw [← hrange, List.flatMap_map]
    rfl
  exact hreindex.trans (surfacePath_genPairs_eq_bdPath q (le_refl q))

/-- The marked free-group word traverses the genuine polygon boundary exactly. -/
theorem genusSurfaceLetters_wordPath :
    wordPath (finiteMarkedLoops q) (genusSurfaceLetters q) = bdPath (gc q) (8 * q) := by
  erw [wordPath_commutatorLetters, finiteSurfacePath_eq_bdPath]

variable {I : Type}

/-- The same literal word on the named alphabet; no internal generator occurs. -/
def genusNamedSurfaceLetters : List ((I ⊕ (Fin q × Bool)) × Bool) :=
  (genusSurfaceLetters q).map (fun x => (Sum.inr x.1, x.2))

omit [NeZero q] in
theorem genusNamedSurfaceLetters_mk :
    FreeGroup.mk (genusNamedSurfaceLetters (I := I) q) =
      commWord (fun i : Fin q × Bool => FreeGroup.of (Sum.inr (α := I) i)) (finitePairs q) := by
  erw [genusNamedSurfaceLetters, ← FreeGroup.map.mk, (mk_commutatorLetters (finitePairs q)), map_commWord]
  simp

end Genus
end FiniteChains.Davis
end

section
open scoped Classical
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Comb
universe u v
theorem wordPath_map_values {X Y : Complex2.{u}} {a : X.V} {b : Y.V} {I : Type v}
    (f : Hom X Y) (p : I → Loop X a) (r : I → Loop Y b)
    (hr : ∀ i, (r i).1 = mapPath f (p i).1) (l : List (I × Bool)) :
    wordPath r l = mapPath f (wordPath p l) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
      obtain ⟨i, t⟩ := x
      cases t <;> simp only [wordPath_cons, germLoopPath_pos, germLoopPath_neg,
        hr, ih, mapPath_append, mapPath_revPath]

end FiniteChains.Comb

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

def universalOldSurfaceLoop (i : Fin q × Bool) :
    Loop (spineOldCx q) (universalSpineOldBase q) :=
  ⟨surfaceOldMarking q i, by
    rw (config := { transparency := .default }) [universalSpineOldBase_eq]
    exact surfaceOldMarking_isPath q i⟩


/-- Internal generators do not occur in the polygon word. Representatives
are chosen only to apply the general word-chain dictionary on the full named
alphabet; the marked loops remain the original explicit surface paths. -/
def universalOldNamedLoop : NamedSpineGen q → Loop (spineOldCx q) (universalSpineOldBase q)
  | .inl z => Classical.choose (Quotient.exists_rep
      (universalSpineOldReceiver q (QuotientGroup.mk (FreeGroup.of (Sum.inl z)))))
  | .inr i => universalOldSurfaceLoop q i

theorem universalOldNamedLoop_class (a : NamedSpineGen q) :
    universalSpineOldReceiver q (qof (relSub (namedSpinePresentation q)) a) =
      Pi1.mk (universalOldNamedLoop q a) := by
  cases a with
  | inl z => exact (Classical.choose_spec (Quotient.exists_rep
      (universalSpineOldReceiver q (QuotientGroup.mk (FreeGroup.of (Sum.inl z)))))).symm
  | inr i => exact (show universalSpineOldReceiver q (QuotientGroup.mk (FreeGroup.of (Sum.inr i))) =
      Pi1.mk (universalOldSurfaceLoop q i) by
    erw [← namedSpinePi1Equiv_marked q i]
    change pi1Map (universalSpineToOld q) (markedSpineTree q).root
      ((namedSpinePi1Equiv q).symm
        ((namedSpinePi1Equiv q) (Pi1.mk (treeMarkedSpineLoop q i)))) = _
    erw [MulEquiv.symm_apply_apply]
    apply Quotient.sound
    change Htpy (spineOldCx q) (universalSpineOldBase q) (universalSpineOldBase q)
      (mapPath (universalSpineToOld q) (treeMarkedSpineLoop q i).1) (surfaceOldMarking q i)
    rw (config := { transparency := .default }) [universalSpine_marking_path, universalSpineOldBase_eq]
    exact spineMarkedLoop_toOld_htpy q i)

theorem universalOldNamedLoop_polygon_word :
    wordPath (universalOldNamedLoop q)
      (genusNamedSurfaceLetters (I := SpinePresentationGen q) q) =
    mapPath (surfCx (cmpRel (GenusVertex q))) (bdPath (gc q) (8 * q)) := by
  erw [genusNamedSurfaceLetters, wordPath_map_letters]
  erw [wordPath_map_values (surfCx (cmpRel (GenusVertex q))) (finiteMarkedLoops q)
    (fun i => universalOldNamedLoop q (Sum.inr i)) (fun _ => rfl)]
  erw [genusSurfaceLetters_wordPath]

theorem universalPolygonFoxCoordinates :
    (coords (relSub (namedSpinePresentation q)) (NamedSpineGen q)).symm
      (fun a => proj (relSub (namedSpinePresentation q)) (fox a (namedSpineSurfaceWord q))) =
    Finsupp.mapDomain
      (fun x : PresGroup (namedSpinePresentation q) × (Fin q × Bool) => (x.1, Sum.inr x.2))
      (universalReferenceMarkingCoefficients q) := by
  apply (coords (relSub (namedSpinePresentation q)) (NamedSpineGen q)).injective
  erw [LinearEquiv.apply_symm_apply]
  funext a
  ext g
  erw [coords_apply]
  cases a with
  | inl z =>
      erw [namedSpineSurfaceWord_fox_internal, map_zero, Finsupp.zero_apply,
        Finsupp.mapDomain_notin_range]
      rintro ⟨⟨h, i⟩, he⟩
      exact Sum.inr_ne_inl (congrArg Prod.snd he)
  | inr i =>
      have hinj : Function.Injective
          (fun x : PresGroup (namedSpinePresentation q) × (Fin q × Bool) =>
            (x.1, Sum.inr (α := SpinePresentationGen q) x.2)) := by
        intro x y h
        exact Prod.ext
          (congrArg (fun z : PresGroup (namedSpinePresentation q) × NamedSpineGen q => z.1) h)
          (Sum.inr.inj (congrArg
            (fun z : PresGroup (namedSpinePresentation q) × NamedSpineGen q => z.2) h))
      erw [Finsupp.mapDomain_apply_of_injective hinj (a := (g, i))]
      erw [← ReceivedTree.cellCoordinates_apply (Fin q × Bool)
        (universalReferenceMarkingCoefficients q) i g]

theorem universalOldNamedLoop_chainMap_marked
    (c : PresGroup (namedSpinePresentation q) × (Fin q × Bool) →₀ ℤ) :
    loopCoefficientChainMap (relSub (namedSpinePresentation q))
      (universalOldNamedLoop q) (universalSpineOldReceiver q)
      (Finsupp.mapDomain (fun x => (x.1, Sum.inr x.2)) c) =
    universalSurfaceMarkingChains q c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [Finsupp.mapDomain_add, map_add, hc, hd]
  | single x n =>
      simp only [Finsupp.mapDomain_single, loopCoefficientChainMap,
        universalSurfaceMarkingChains, Finsupp.linearCombination_single,
        universalOldNamedLoop, universalOldSurfaceLoop, loopCoefficientVertex]

/-- No degree or boundary hypothesis is left: the explicitly constructed
polygon boundary is exactly the original named surface Fox gradient. -/
theorem universalOldPolygonChain_boundary_marked :
    Comb.bdry2 _ (universalOldPolygonChain q) =
      universalSurfaceMarkingChains q (universalReferenceMarkingCoefficients q) := by
  erw [universalOldPolygonChain_boundary, ← universalOldNamedLoop_polygon_word]
  erw [lifted_wordPath_fox (relSub (namedSpinePresentation q))
    (universalOldNamedLoop q) (universalSpineOldReceiver q) (universalOldNamedLoop_class q)]
  erw [genusNamedSurfaceLetters_mk]
  erw [universalPolygonFoxCoordinates, universalOldNamedLoop_chainMap_marked]

end FiniteChains.Davis.Genus

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

theorem normalizedSpineReference_exists :
    ∃ d : (universalNamedSpineCover q).F →₀ ℤ,
      Comb.bdry2 (universalNamedSpineCover q) d =
        ReceivedTree.markedChain (markedSpineTree q) (universalSpineWordReceiver q)
          (treeMarkedSpineLoop q) (namedSpineSurfaceMarkingCoefficient q) ∧
      ∃ y ∈ Nerve.Inc (universalOldOrder q),
        universalNerveChain2 (universalReferenceOldChain q) =
          universalNerveChain2 (chain2 (universalNamedSpineComparison q) d) + Nerve.bdry y := by
  obtain ⟨d, hd⟩ := exists_universalNamedSpine_markedFilling q
  have hz : Comb.bdry2 _ (universalReferenceOldChain q) =
      chain1 (universalNamedSpineComparison q) (Comb.bdry2 (universalNamedSpineCover q) d) := by
    rw [hd]
    exact universalReferenceOldChain_boundary q (universalOldPolygonChain_boundary_marked q)
  obtain ⟨d', hd', y, hy, hzy⟩ := universalSpine_adjust_to_chain q d (universalReferenceOldChain q) hz
  grind

/-- Genuine received-spine coordinates of the geometrically normalized
surface filling. This choice uses no core or substituted word. -/
def normalizedSpineReference : (universalNamedSpineCover q).F →₀ ℤ :=
  Classical.choose (normalizedSpineReference_exists q)

theorem normalizedSpineReference_boundary :
    Comb.bdry2 (universalNamedSpineCover q) (normalizedSpineReference q) =
      ReceivedTree.markedChain (markedSpineTree q) (universalSpineWordReceiver q)
        (treeMarkedSpineLoop q) (namedSpineSurfaceMarkingCoefficient q) :=
  (Classical.choose_spec (normalizedSpineReference_exists q)).1

theorem normalizedSpineReference_geometry :
    ∃ y ∈ Nerve.Inc (universalOldOrder q),
      universalNerveChain2 (universalReferenceOldChain q) =
        universalNerveChain2 (chain2 (universalNamedSpineComparison q) (normalizedSpineReference q)) +
          Nerve.bdry y :=
  (Classical.choose_spec (normalizedSpineReference_exists q)).2

/-- After removing the exact old marking correction, the chosen chain
represents the actual degree-one source polygon modulo an old three-boundary. -/
theorem normalizedSpineReference_corrected_geometry :
    ∃ y ∈ Nerve.Inc (universalOldOrder q),
      universalNerveChain2
        (chain2 (universalNamedSpineComparison q) (normalizedSpineReference q) -
          universalOldMarkingCorrections q (universalReferenceMarkingCoefficients q)) =
        universalNerveChain2 (universalOldPolygonChain q) + Nerve.bdry y := by
  obtain ⟨y, hy, hzy⟩ := normalizedSpineReference_geometry q
  refine ⟨-y, (Nerve.Inc _).neg_mem hy, ?_⟩
  rw [universalReferenceOldChain, map_add] at hzy
  rw [map_sub, map_neg]
  grind

end FiniteChains.Davis.Genus
end

namespace FiniteChains
open MonoidAlgebra
variable {G : Type*} [Group G] (H : Subgroup G) {J α ι : Type*}

/-- Extend the coefficients of each matrix column from the subgroup ring. -/
def fsExtendedBoundary (A : J → α →₀ MonoidAlgebra ℤ H) :
    (J →₀ MonoidAlgebra ℤ G) →ₗ[MonoidAlgebra ℤ G] (α →₀ MonoidAlgebra ℤ G) :=
  Finsupp.linearCombination _ (fun j => (A j).mapRange (subRingHom H) (map_zero _))

/-- Taking a coset slice commutes with a boundary whose entries lie in the subgroup ring. -/
theorem fs_slice_extendedBoundary (A : J → α →₀ MonoidAlgebra ℤ H)
    (g : G) (c : J →₀ MonoidAlgebra ℤ G) :
    (fsExtendedBoundary H A c).mapRange (slice H g) (map_zero _) =
      Finsupp.linearCombination (MonoidAlgebra ℤ H) A
        (c.mapRange (slice H g) (map_zero _)) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
    rw [map_add, Finsupp.mapRange_add, Finsupp.mapRange_add, map_add, hc, hd] <;> exact fun x y => map_add _ x y
  | single j x =>
    simp only [fsExtendedBoundary, Finsupp.linearCombination_single, Finsupp.mapRange_single]
    apply Finsupp.ext
    intro i
    exact slice_mul H g x (A j i)

/-- A finite-support vector has only finitely many occupied subgroup cosets. -/
def fsCosetSupport (c : J →₀ MonoidAlgebra ℤ G) : Finset (G ⧸ H) := by
  classical
  exact c.support.biUnion fun j =>
    (c j).coeff.support.image (fun g => (QuotientGroup.mk g : G ⧸ H))

/-- Reassemble the finitely many coset slices of a chain. -/
theorem fs_sum_cosetSlices (c : J →₀ MonoidAlgebra ℤ G) :
    (∑ C ∈ fsCosetSupport H c,
      (single (Quotient.out C) (1 : ℤ) : MonoidAlgebra ℤ G) •
        (c.mapRange (slice H (Quotient.out C)) (map_zero _)).mapRange
          (subRingHom H) (map_zero _)) = c := by
  classical
  apply Finsupp.ext
  intro j
  rw [Finsupp.finset_sum_apply]
  apply sum_cosetPieces_of_subset
  by_cases hj : j ∈ c.support
  · exact Finset.subset_biUnion_of_mem
      (fun j => (c j).coeff.support.image (fun g => (QuotientGroup.mk g))) hj
  · simp_all

/-- Every cycle over the larger group ring is generated by cycles over the subgroup ring,
without a finite-cell restriction. -/
theorem fs_cycle_mem_span_subgroup_cycles
    (A : J → α →₀ MonoidAlgebra ℤ H) (c : J →₀ MonoidAlgebra ℤ G)
    (hc : fsExtendedBoundary H A c = 0) :
    c ∈ Submodule.span (MonoidAlgebra ℤ G)
      {v : J →₀ MonoidAlgebra ℤ G | ∃ w : J →₀ MonoidAlgebra ℤ H,
        Finsupp.linearCombination (MonoidAlgebra ℤ H) A w = 0 ∧
        v = w.mapRange (subRingHom H) (map_zero _)} := by
  rw [← fs_sum_cosetSlices H c]
  apply Submodule.sum_mem
  intro C hC
  apply Submodule.smul_mem
  apply Submodule.subset_span
  refine ⟨c.mapRange (slice H (Quotient.out C)) (map_zero _), ?_, rfl⟩
  rw [← fs_slice_extendedBoundary, hc, Finsupp.mapRange_zero]

end FiniteChains

namespace FiniteChains

section RingMap

variable {R S : Type*} [Ring R] [Ring S] {J I : Type*}

/-- Extend every finite matrix column along a coefficient ring homomorphism. -/
def fsRingMapBoundary (φ : R →+* S) (A : J → I →₀ R) :
    (J →₀ S) →ₗ[S] (I →₀ S) :=
  Finsupp.linearCombination S (fun j => (A j).mapRange φ (map_zero _))

/-- The base-changed boundary commutes with the actual coefficient map. -/
theorem fsRingMapBoundary_mapRange (φ : R →+* S) (A : J → I →₀ R)
    (y : J →₀ R) :
    fsRingMapBoundary φ A (y.mapRange φ (map_zero _)) =
      (Finsupp.linearCombination R A y).mapRange φ (map_zero _) := by
  induction y using Finsupp.induction_linear with
  | zero => simp
  | add y z hy hz =>
      rw [Finsupp.mapRange_add, map_add, map_add, Finsupp.mapRange_add, hy, hz] <;>
        exact fun a b => map_add φ a b
  | single j a =>
      simp only [Finsupp.mapRange_single, fsRingMapBoundary,
        Finsupp.linearCombination_single]
      ext i
      exact (map_mul φ a (A j i)).symm

end RingMap

section GroupMap

variable {G G' : Type*} [Group G] [Group G'] {J I : Type*}

/-- For an injective group map, the cycles of the base-changed finite-support
matrix are generated by coefficient images of original-group cycles. -/
theorem fs_cycle_mem_span_groupMap_cycles (f : G →* G') (hf : Function.Injective f)
    (A : J → I →₀ MonoidAlgebra ℤ G) (x : J →₀ MonoidAlgebra ℤ G')
    (hx : fsRingMapBoundary (MonoidAlgebra.mapDomainRingHom ℤ f) A x = 0) :
    x ∈ Submodule.span (MonoidAlgebra ℤ G')
      {v : J →₀ MonoidAlgebra ℤ G' | ∃ y : J →₀ MonoidAlgebra ℤ G,
        Finsupp.linearCombination (MonoidAlgebra ℤ G) A y = 0 ∧
        v = y.mapRange (MonoidAlgebra.mapDomainRingHom ℤ f) (map_zero _)} := by
  let H := f.range
  let e  := MonoidHom.ofInjective hf
  let φ :=
    MonoidAlgebra.mapDomainRingHom ℤ e.toMonoidHom
  let ψ :=
    MonoidAlgebra.mapDomainRingHom ℤ e.symm.toMonoidHom
  let θ :=
    MonoidAlgebra.mapDomainRingHom ℤ f
  have hφ : ∀ a, subRingHom H (φ a) = θ a := by
    intro a
    change MonoidAlgebra.mapDomain _ (MonoidAlgebra.mapDomain _ a) = MonoidAlgebra.mapDomain _ a
    rw [← MonoidAlgebra.mapDomain_comp]
    rfl
  have hφψ : ∀ a, φ (ψ a) = a := by
    intro a
    change MonoidAlgebra.mapDomain _ (MonoidAlgebra.mapDomain _ a) = a
    rw [← MonoidAlgebra.mapDomain_comp]
    have he : e.toMonoidHom ∘ e.symm.toMonoidHom = id := by
      funext g
      exact e.apply_symm_apply g
    rw [he, MonoidAlgebra.mapDomain_id]
  have hφinj : Function.Injective φ := fun _ _ h => MonoidAlgebra.coeff_injective (Finsupp.mapDomain_injective e.injective (congrArg MonoidAlgebra.coeff h))
  let A' :=
    fun j => (A j).mapRange φ (map_zero _)
  have hboundary : fsExtendedBoundary H A' = fsRingMapBoundary θ A := by
    apply Finsupp.lhom_ext
    intro j a
    simp only [fsExtendedBoundary, fsRingMapBoundary, Finsupp.linearCombination_single]
    congr 1
    ext i : 1
    exact hφ (A j i)
  have hx' : fsExtendedBoundary H A' x = 0 := by
    rw [hboundary]
    exact hx
  have hmem := fs_cycle_mem_span_subgroup_cycles H A' x hx'
  refine Submodule.span_mono ?_ hmem
  rintro v ⟨w, hw, rfl⟩
  let y := w.mapRange ψ (map_zero _)
  have hy : y.mapRange φ (map_zero _) = w := by
    ext j : 1
    exact hφψ (w j)
  refine ⟨y, ?_, ?_⟩
  · have hb : (Finsupp.linearCombination (MonoidAlgebra ℤ G) A y).mapRange
        φ (map_zero _) = 0 := by
      rw [← fsRingMapBoundary_mapRange]
      change Finsupp.linearCombination (MonoidAlgebra ℤ H) A'
        (y.mapRange φ (map_zero _)) = 0
      rw [hy]
      exact hw
    apply Finsupp.ext
    intro i
    apply hφinj
    have hi := congrArg (fun z : I →₀ MonoidAlgebra ℤ H => z i) hb
    simpa only [Finsupp.mapRange_apply, Finsupp.zero_apply, map_zero] using hi
  · grind

end GroupMap

namespace BlockFamily

universe u

section ChainColumns

variable {Jr Sx R : Type u} {Mt : Sx → Type u} [Ring R]

/-- The filling of one block, in the actual substituted cell coordinates. -/
def fsSurfaceChain (c : ∀ s, Mt s →₀ R) (s : Sx) : (Jr ⊕ (Σ s, Mt s)) →₀ R :=
  (c s).mapDomain (fun m => Sum.inr ⟨s, m⟩)

@[simp] theorem fsSurfaceChain_inl (c : ∀ s, Mt s →₀ R) (s : Sx) (j : Jr) :
    fsSurfaceChain c s (Sum.inl j) = 0 := by
  apply Finsupp.mapDomain_notin_range
  rintro ⟨m, h⟩
  exact Sum.inr_ne_inl h

@[simp] theorem fsSurfaceChain_inr (c : ∀ s, Mt s →₀ R) (s : Sx) (m : Mt s) :
    fsSurfaceChain (Jr := Jr) c s (Sum.inr ⟨s, m⟩) = c s m := by
  apply Finsupp.mapDomain_apply_of_injective
  intro a b h
  exact eq_of_heq (Sigma.mk.inj (Sum.inr_injective h)).2


@[simp] theorem fsCellsBase_single_inl (c : ∀ s, Mt s →₀ R) (j : Jr) :
    fsCellsBase c (Finsupp.single (Sum.inl j) 1) = Finsupp.single (Sum.inl j) 1 := by
  classical
  ext k
  cases k with
  | inl i => simp only [fsCellsBase_inl, Finsupp.single_apply, Sum.inl.injEq]
  | inr p => obtain ⟨s, m⟩ := p; simp

@[simp] theorem fsCellsBase_single_inr (c : ∀ s, Mt s →₀ R) (s : Sx) :
    fsCellsBase (Jr := Jr) c (Finsupp.single (Sum.inr s) 1) = fsSurfaceChain c s := by
  ext k
  cases k with
  | inl j => simp
  | inr p =>
      obtain ⟨t, m⟩ := p
      by_cases hst : s = t
      · subst t
        simp
      · simp [hst, (show fsSurfaceChain (Jr := Jr) c s (Sum.inr ⟨t, m⟩) = 0 by
        apply Finsupp.mapDomain_notin_range
        rintro ⟨a, h⟩
        exact hst (congrArg Sigma.fst (Sum.inr_injective h)))]

/-- Include old generator chains by extension by zero on the internal ones. -/
def fsOldOneIncl {α Z : Type u} : (α →₀ R) →ₗ[R] ((α ⊕ Z) →₀ R) where
  toFun x := Finsupp.sumElim x 0
  map_add' x y := by ext k; cases k <;> simp [Finsupp.sumElim_apply]
  map_smul' a x := by ext k; cases k <;> simp [Finsupp.sumElim_apply]

@[simp] theorem fsOldOneIncl_inl {α Z : Type u} (x : α →₀ R) (i : α) :
    fsOldOneIncl (Z := Z) x (Sum.inl i) = x i := rfl

@[simp] theorem fsOldOneIncl_inr {α Z : Type u} (x : α →₀ R) (z : Z) :
    fsOldOneIncl x (Sum.inr z) = 0 := rfl

theorem fsOldOneIncl_injective {α Z : Type u} :
    Function.Injective (fsOldOneIncl (α := α) (Z := Z) (R := R)) := by
  intro x y h
  ext i
  exact congrArg (fun z : (α ⊕ Z) →₀ R => z (Sum.inl i)) h

end ChainColumns

section Substitution

variable {α Jr Sx : Type u} {Zt Mt : Sx → Type u}
  [DecidableEq α] [DecidableEq Sx] [∀ s, DecidableEq (Zt s)]
  (ρ : Jr ⊕ Sx → FreeGroup α)
  (bsub : ∀ s, Mt s → FreeGroup (α ⊕ Zt s))
  (hfill : FilledF ρ bsub)

local notation "R'" => MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub))
local notation "R₀" => MonoidAlgebra ℤ (PresGroup ρ)

/-- The old Fox boundary over the actual substituted group ring. -/
def fsFoxPushBoundary : ((Jr ⊕ Sx) →₀ R') →ₗ[R'] (α →₀ R') :=
  fsRingMapBoundary (coeffF ρ bsub hfill)
    (fun k => coverFoxGradient (relSub ρ) (ρ k))

omit [DecidableEq Sx] [∀ s, DecidableEq (Zt s)] in
@[simp] theorem fsFoxPushBoundary_single (k : Jr ⊕ Sx) (i : α) :
    fsFoxPushBoundary ρ bsub hfill (Finsupp.single k 1) i =
      coeffF ρ bsub hfill (foxMatrixPres ρ i k) := by
  simp only [fsFoxPushBoundary, fsRingMapBoundary, Finsupp.linearCombination_single,
    one_smul, Finsupp.mapRange_apply]
  rfl

/-- B1 in finite-support coordinates: the surface filling has the replaced
polygon's old boundary and zero internal boundary in its own block. -/
structure IsFillingFS (c : ∀ s, Mt s →₀ R') : Prop where
  base : ∀ (s : Sx) (i : α),
    (c s).sum (fun m a => a *
      foxMatrixPres (substPresF ρ bsub) (Sum.inl i) (Sum.inr ⟨s, m⟩)) =
        coeffF ρ bsub hfill (foxMatrixPres ρ i (Sum.inr s))
  internal : ∀ (s : Sx) (z : Zt s),
    (c s).sum (fun m a => a *
      foxMatrixPres (substPresF ρ bsub) (Sum.inr ⟨s, z⟩) (Sum.inr ⟨s, m⟩)) = 0

/-- A geometric B1 calculation on each finite block supplies the supported
input without imposing any finiteness on the family or the old presentation. -/
theorem isFillingFS_of_finite_blocks [∀ s, Fintype (Mt s)]
    (c : ∀ s, Mt s →₀ R')
    (hbase : ∀ (s : Sx) (i : α), ∑ m : Mt s, c s m *
      foxMatrixPres (substPresF ρ bsub) (Sum.inl i) (Sum.inr ⟨s, m⟩) =
        coeffF ρ bsub hfill (foxMatrixPres ρ i (Sum.inr s)))
    (hinternal : ∀ (s : Sx) (z : Zt s), ∑ m : Mt s, c s m *
      foxMatrixPres (substPresF ρ bsub) (Sum.inr ⟨s, z⟩) (Sum.inr ⟨s, m⟩) = 0) :
    IsFillingFS ρ bsub hfill c where
  base s i := by
    rw [Finsupp.sum_fintype _ _ (fun _ => zero_mul _)]
    exact hbase s i
  internal s z := by
    rw [Finsupp.sum_fintype _ _ (fun _ => zero_mul _)]
    exact hinternal s z

theorem fsSurfaceChain_boundary_apply (c : ∀ s, Mt s →₀ R') (s : Sx)
    (i : α ⊕ (Σ s, Zt s)) :
    coverSecondBoundary (relSub (substPresF ρ bsub)) (substPresF ρ bsub)
        (fsSurfaceChain c s) i =
      (c s).sum (fun m a => a *
        foxMatrixPres (substPresF ρ bsub) i (Sum.inr ⟨s, m⟩)) := by
  rw [fsCoverSecondBoundary_apply]
  exact Finsupp.sum_mapDomain_index (fun _ => zero_mul _)
    (fun _ _ _ => add_mul _ _ _)

/-- B1 extends from every single actual surface filling to the full
simultaneous substitution chain map, without finite index assumptions. -/
theorem fsCellsBase_chainMap (c : ∀ s, Mt s →₀ R')
    (hc : IsFillingFS ρ bsub hfill c) :
    (coverSecondBoundary (relSub (substPresF ρ bsub)) (substPresF ρ bsub)).comp
        (fsCellsBase c) =
      fsOldOneIncl.comp (fsFoxPushBoundary ρ bsub hfill) := by
  apply Finsupp.lhom_ext
  intro k a
  rw [← Finsupp.smul_single_one k a, map_smul, map_smul]
  congr 1
  simp
  cases k with
  | inl j =>
      rw [fsCellsBase_single_inl]
      ext i : 1
      cases i with
      | inl i =>
          rw [fsOldOneIncl_inl, fsFoxPushBoundary_single, fsCoverSecondBoundary_apply]
          simp [foxMatrix_inl_inl ρ bsub hfill]
      | inr p =>
          rw [fsOldOneIncl_inr, fsCoverSecondBoundary_apply]
          simp [foxMatrix_inr_inl ρ bsub]
  | inr s =>
      rw [fsCellsBase_single_inr]
      ext i : 1
      cases i with
      | inl i =>
          rw [fsOldOneIncl_inl, fsFoxPushBoundary_single, fsSurfaceChain_boundary_apply]
          exact hc.base s i
      | inr p =>
          obtain ⟨t, z⟩ := p
          rw [fsOldOneIncl_inr, fsSurfaceChain_boundary_apply]
          by_cases hst : s = t
          · subst t
            exact hc.internal s z
          · simp [foxMatrix_inr_inr_of_ne ρ bsub hst z]

/-- The supported structural map carries the actual old boundary to the
actual new boundary using the existing coefficient homomorphism. -/
theorem fsCellsF_boundary (c : ∀ s, Mt s →₀ R')
    (hc : IsFillingFS ρ bsub hfill c) (y : (Jr ⊕ Sx) →₀ R₀) :
    coverSecondBoundary (relSub (substPresF ρ bsub)) (substPresF ρ bsub)
        (fsCellsF ρ bsub hfill c y) =
      fsOldOneIncl ((coverSecondBoundary (relSub ρ) ρ y).mapRange
        (coeffF ρ bsub hfill) (map_zero _)) := by
  have h := LinearMap.congr_fun (fsCellsBase_chainMap ρ bsub hfill c hc)
    (y.mapRange (coeffF ρ bsub hfill) (map_zero _))
  change _ = fsOldOneIncl (fsFoxPushBoundary ρ bsub hfill
    (y.mapRange (coeffF ρ bsub hfill) (map_zero _))) at h
  rw [fsFoxPushBoundary, fsRingMapBoundary_mapRange] at h
  exact h

/-- Under B1, every cycle preimage constructed by block-local B2 is an
actual cycle for the base-changed old Fox boundary. -/
theorem fsCycle_preimage (c : ∀ s, Mt s →₀ R')
    (hc : IsFillingFS ρ bsub hfill c)
    (hblock : BlockSurfaceGeneratesFS ρ bsub c)
    (x : (Jr ⊕ (Σ s, Mt s)) →₀ R')
    (hx : coverSecondBoundary (relSub (substPresF ρ bsub)) (substPresF ρ bsub) x = 0) :
    ∃ y : (Jr ⊕ Sx) →₀ R', fsFoxPushBoundary ρ bsub hfill y = 0 ∧
      fsCellsBase c y = x := by
  obtain ⟨y, hy, _, _⟩ := fsCellsBase_preimage_of_internal_zero ρ bsub c hblock x
    (fun s z => congrArg (fun v => v (Sum.inr ⟨s, z⟩)) hx)
  refine ⟨y, ?_, hy⟩
  apply fsOldOneIncl_injective (Z := Σ s, Zt s)
  rw [map_zero]
  have h := LinearMap.congr_fun (fsCellsBase_chainMap ρ bsub hfill c hc) y
  change coverSecondBoundary (relSub (substPresF ρ bsub)) (substPresF ρ bsub)
    (fsCellsBase c y) = fsOldOneIncl (fsFoxPushBoundary ρ bsub hfill y) at h
  rw [hy, hx] at h
  exact h.symm

/-- Full arbitrary-family generation by actual original-group cycles. The
only remaining inputs are the geometric B1 filling, block-local B2, and the
already separately constructed injection of presentation groups. -/
theorem fsGenerates_familySubst (c : ∀ s, Mt s →₀ R')
    (hc : IsFillingFS ρ bsub hfill c)
    (hblock : BlockSurfaceGeneratesFS ρ bsub c)
    (hinj : Function.Injective (substHomF ρ bsub hfill))
    (x : (Jr ⊕ (Σ s, Mt s)) →₀ R')
    (hx : coverSecondBoundary (relSub (substPresF ρ bsub)) (substPresF ρ bsub) x = 0) :
    x ∈ Submodule.span R'
      {v : (Jr ⊕ (Σ s, Mt s)) →₀ R' | ∃ y : (Jr ⊕ Sx) →₀ R₀,
        coverSecondBoundary (relSub ρ) ρ y = 0 ∧ v = fsCellsF ρ bsub hfill c y} := by
  obtain ⟨y, hy, hxy⟩ := fsCycle_preimage ρ bsub hfill c hc hblock x hx
  have hmem := fs_cycle_mem_span_groupMap_cycles (substHomF ρ bsub hfill) hinj
    (fun k => coverFoxGradient (relSub ρ) (ρ k)) y hy
  rw [← hxy]
  clear hy hxy
  induction hmem using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨a, ha, rfl⟩ := hv
      apply Submodule.subset_span
      exact ⟨a, ha, rfl⟩
  | zero => simp
  | add v w hv hw hv' hw' =>
      rw [map_add]
      exact Submodule.add_mem _ hv' hw'
  | smul a v hv hv' =>
      rw [map_smul]
      exact Submodule.smul_mem _ a hv'

end Substitution

end BlockFamily
end FiniteChains

section
open scoped Classical
namespace FiniteChains

/-- Fox chain rule for a finite source alphabet and an arbitrary target alphabet. -/
theorem fox_wordHom_chainRule {A B : Type*} [Fintype A] [DecidableEq A]
    [DecidableEq B] (φ : FreeGroup A →* FreeGroup B) (b : B) (w : FreeGroup A) :
    fox b (φ w) = ∑ i : A,
      MonoidAlgebra.mapDomainRingHom ℤ φ (fox i w) * fox b (φ (FreeGroup.of i)) := by
  induction w using FreeGroup.induction_on with
  | one => simp
  | of j => simp
  | inv_of j ih =>
      rw [map_inv, fox_inv, ih]
      simp only [fox_inv, map_neg, map_mul, groupRingMap_grp]
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [map_inv]
      simp
  | mul v w hv hw =>
      rw [map_mul, fox_mul, hv, hw]
      simp only [fox_mul, map_add, map_mul, groupRingMap_grp, add_mul]
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl (fun i _ => (mul_assoc _ _ _).symm)

/-- Transport a genuine filling through a word homomorphism and its induced
quotient homomorphism. No injectivity of the word substitution is required. -/
theorem fox_filling_wordHom {A B J : Type*} [Fintype A] [DecidableEq A]
    [DecidableEq B] [Fintype J] (σ : J → FreeGroup A)
    (N : Subgroup (FreeGroup B)) [N.Normal]
    (φ : FreeGroup A →* FreeGroup B) (ψ : PresGroup σ →* (FreeGroup B ⧸ N))
    (hψ : ∀ w, ψ (QuotientGroup.mk w) = QuotientGroup.mk (φ w))
    (c : J → MonoidAlgebra ℤ (PresGroup σ)) (w : FreeGroup A)
    (hc : ∀ i, ∑ j, c j * foxMatrixPres σ i j =
      quotRingHom ℤ (relSub σ) (fox i w)) (b : B) :
    (∑ j, MonoidAlgebra.mapDomainRingHom ℤ ψ (c j) *
      quotRingHom ℤ N (fox b (φ (σ j)))) = quotRingHom ℤ N (fox b (φ w)) := by
  let C := MonoidAlgebra.mapDomainRingHom ℤ ψ
  have hcoeff (x : FreeGroupRing A) :
      C (quotRingHom ℤ (relSub σ) x) =
        quotRingHom ℤ N (MonoidAlgebra.mapDomainRingHom ℤ φ x) := by
    change MonoidAlgebra.mapDomainRingHom ℤ ψ
        (MonoidAlgebra.mapDomainRingHom ℤ (QuotientGroup.mk' (relSub σ)) x) =
      MonoidAlgebra.mapDomainRingHom ℤ (QuotientGroup.mk' N)
        (MonoidAlgebra.mapDomainRingHom ℤ φ x)
    have hh : ψ.comp (QuotientGroup.mk' (relSub σ)) =
        (QuotientGroup.mk' N).comp φ := MonoidHom.ext hψ
    rw [BlockMor.mapDomainRingHom_comp', BlockMor.mapDomainRingHom_comp', hh]
  have hfox (v : FreeGroup A) : quotRingHom ℤ N (fox b (φ v)) =
      ∑ i : A, C (quotRingHom ℤ (relSub σ) (fox i v)) *
        quotRingHom ℤ N (fox b (φ (FreeGroup.of i))) := by
    rw [fox_wordHom_chainRule, map_sum]
    exact Finset.sum_congr rfl (fun i _ => by rw [map_mul, hcoeff])
  have hcol (j : J) := hfox (σ j)
  rw [hfox w]
  simp_rw [hcol, Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_mul]
  congr 1
  simpa only [map_mul, map_sum, MonoidHom.comp_apply, C, foxMatrixPres] using congrArg C (hc i)

end FiniteChains

namespace FiniteChains.Davis.Genus

open RACG Mirror Comb PresModel BlockFamily

/-- The genuine marked surface word, prior to any substitution in a core. -/
def markedSpineSurfaceWord (n : ℕ) [NeZero n] : FreeGroup (MarkedSpineGen n) :=
  commWord (fun x : Fin n × Bool => FreeGroup.of (Sum.inl x)) (finitePairs n)

/-- Choose the degree-one geometric surface class once in the genuine marked
spine. This choice is independent of the core and all substituted words. -/
def markedSpineFilling (n : ℕ) [NeZero n] :
    NamedSpineRel n →₀ MonoidAlgebra ℤ (PresGroup (markedSpineBeta n)) :=
  normalizedMarkedSpineFilling n (normalizedSpineReference n)

theorem markedSpineFilling_boundary (n : ℕ) [NeZero n] (i : MarkedSpineGen n) :
    (∑ m, markedSpineFilling n m * foxMatrixPres (markedSpineBeta n) i m) =
      quotRingHom ℤ (relSub (markedSpineBeta n)) (fox i (markedSpineSurfaceWord n)) := by
  exact normalizedMarkedSpineFilling_boundary n (normalizedSpineReference n)
    (normalizedSpineReference_boundary n) i

@[simp] theorem markedSpineFilling_named_coeff (n : ℕ) [NeZero n] (m : NamedSpineRel n) :
    markedSpineFilling n m =
      MonoidAlgebra.mapDomainRingHom ℤ (spineReorderHom n)
        (normalizedNamedSpineVector n (normalizedSpineReference n) m) :=
  normalizedMarkedSpineFilling_apply n (normalizedSpineReference n) m

variable {α Jr Sx : Type} (ρ : Jr ⊕ Sx → FreeGroup α)
  (q : Sx → ℕ) [∀ s, NeZero (q s)]
  (u : ∀ s, Fin (q s) × Bool → FreeGroup α)
  (hrho : ∀ s, ρ (Sum.inr s) = commWord (u s) (finitePairs (q s)))

/-- The actual marked receiver in an individual substituted factor. -/
def finiteSpineIndividualMarkedHom (s : Sx) :
    PresGroup (markedSpineBeta (q s)) →*
      IndividualGroup ρ (familyFiniteSpineWordBlock q u) s :=
  markedBlockHom (oneRel ρ s) (fun _ : PUnit.{1} => u s)
    (fun _ : PUnit.{1} => markedSpineBeta (q s)) PUnit.unit

/-- The actual marked receiver in the simultaneous substituted group. -/
def finiteSpineFamilyMarkedHom (s : Sx) :
    PresGroup (markedSpineBeta (q s)) →*
      PresGroup (substPresF ρ (familyFiniteSpineWordBlock q u)) :=
  markedBlockHom ρ u (fun s => markedSpineBeta (q s)) s

def finiteSpineIndividualFilling (s : Sx) : NamedSpineRel (q s) →₀
    MonoidAlgebra ℤ (IndividualGroup ρ (familyFiniteSpineWordBlock q u) s) :=
  (markedSpineFilling (q s)).mapRange
    (MonoidAlgebra.mapDomainRingHom ℤ (finiteSpineIndividualMarkedHom ρ q u s))
    (map_zero _)

def finiteSpineFamilyFilling (s : Sx) : NamedSpineRel (q s) →₀
    MonoidAlgebra ℤ (PresGroup (substPresF ρ (familyFiniteSpineWordBlock q u))) :=
  (markedSpineFilling (q s)).mapRange
    (MonoidAlgebra.mapDomainRingHom ℤ (finiteSpineFamilyMarkedHom ρ q u s))
    (map_zero _)

include hrho in
theorem finiteSpineFamily_surfaceWord (s : Sx) :
    FreeGroup.map (genEmb (Zt := fun s => SpinePresentationGen (q s)) s)
      (blockSubst (Zt := fun s => SpinePresentationGen (q s)) u s
        (markedSpineSurfaceWord (q s))) =
    FreeGroup.map (Sum.inl (β := Σ s, SpinePresentationGen (q s))) (ρ (Sum.inr s)) := by
  have hm : (FreeGroup.map (genEmb (Zt := fun s => SpinePresentationGen (q s)) s)).comp
      (FreeGroup.map (Sum.inl (β := SpinePresentationGen (q s)))) =
      FreeGroup.map (Sum.inl (α := α)) := by
    apply FreeGroup.ext_hom
    intro a
    simp
  rw [markedSpineSurfaceWord, map_commWord, map_commWord]
  simp only [blockSubst_of_inl]
  simp_rw [← MonoidHom.comp_apply, hm]
  rw [← map_commWord, hrho s]

/-- Actual B1 for the arbitrary genus family, with no geometric hypothesis left. -/
theorem finiteSpineFamilyFilling_isFilling :
    IsFillingFS ρ (familyFiniteSpineWordBlock q u)
      (familyFiniteSpineWordBlock_filled ρ q u hrho)
      (finiteSpineFamilyFilling ρ q u) := by
  have hboundary (s : Sx) (i : α ⊕ (Σ s, SpinePresentationGen (q s))) :=
    fox_filling_wordHom (markedSpineBeta (q s))
      (relSub (substPresF ρ (familyFiniteSpineWordBlock q u)))
      ((FreeGroup.map (genEmb s)).comp
        (blockSubst (Zt := fun s => SpinePresentationGen (q s)) u s))
      (finiteSpineFamilyMarkedHom ρ q u s) (fun _ => rfl)
      (markedSpineFilling (q s)) (markedSpineSurfaceWord (q s))
      (markedSpineFilling_boundary (q s)) i
  apply isFillingFS_of_finite_blocks
  · intro s i
    have h := hboundary s (Sum.inl i)
    change (∑ m, finiteSpineFamilyFilling ρ q u s m *
      foxMatrixPres (substPresF ρ (familyFiniteSpineWordBlock q u))
        (Sum.inl i) (Sum.inr ⟨s, m⟩)) =
      quotRingHom ℤ _ (fox (Sum.inl i)
        (FreeGroup.map (genEmb s) (blockSubst u s (markedSpineSurfaceWord (q s))))) at h
    rw [finiteSpineFamily_surfaceWord ρ q u hrho,
      fox_map Sum.inl Sum.inl_injective, ← coeffF_quotRingHom ρ
        (familyFiniteSpineWordBlock q u) (familyFiniteSpineWordBlock_filled ρ q u hrho)] at h
    exact h
  · intro s z
    have h := hboundary s (Sum.inr ⟨s, z⟩)
    change (∑ m, finiteSpineFamilyFilling ρ q u s m *
      foxMatrixPres (substPresF ρ (familyFiniteSpineWordBlock q u))
        (Sum.inr ⟨s, z⟩) (Sum.inr ⟨s, m⟩)) =
      quotRingHom ℤ _ (fox (Sum.inr ⟨s, z⟩)
        (FreeGroup.map (genEmb s) (blockSubst u s (markedSpineSurfaceWord (q s))))) at h
    rw [finiteSpineFamily_surfaceWord ρ q u hrho,
      fox_map_of_not_mem_range Sum.inl (fun _ => Sum.inr_ne_inl), map_zero] at h
    exact h

theorem finiteSpineFactor_marked (s : Sx) :
    (finiteSpineFactorToFamily ρ q u hrho s).comp
      (finiteSpineIndividualMarkedHom ρ q u s) = finiteSpineFamilyMarkedHom ρ q u s := by
  apply MonoidHom.ext
  intro x
  induction x using QuotientGroup.induction_on with
  | _ w =>
      change QuotientGroup.mk (FreeGroup.map
        (individualGenEmb (α := α) (Zt := fun s => SpinePresentationGen (q s)) s)
        (FreeGroup.map (genEmb
          PUnit.unit) (blockSubst (Zt := fun s => SpinePresentationGen (q s)) u s w))) = _
      rw [individualGenEmb_block]
      rfl

/-- The reference family filling is the coefficient image of the individual one. -/
theorem finiteSpineFamilyFilling_coeff (s : Sx) (m : NamedSpineRel (q s)) :
    finiteSpineFamilyFilling ρ q u s m =
      finiteSpineFactorRingHom ρ q u hrho s (finiteSpineIndividualFilling ρ q u s m) := by
  change MonoidAlgebra.mapDomainRingHom ℤ (finiteSpineFamilyMarkedHom ρ q u s)
      (markedSpineFilling (q s) m) =
    MonoidAlgebra.mapDomainRingHom ℤ (finiteSpineFactorToFamily ρ q u hrho s)
      (MonoidAlgebra.mapDomainRingHom ℤ (finiteSpineIndividualMarkedHom ρ q u s)
        (markedSpineFilling (q s) m))
  rw [BlockMor.mapDomainRingHom_comp', finiteSpineFactor_marked]

/-- The actual internal Fox matrix commutes with the individual factor inclusion. -/
theorem finiteSpineFactor_internalMatrix (s : Sx) (z : SpinePresentationGen (q s))
    (m : NamedSpineRel (q s)) :
    foxMatrixPres (substPresF ρ (familyFiniteSpineWordBlock q u))
      (Sum.inr ⟨s, z⟩) (Sum.inr ⟨s, m⟩) =
    finiteSpineFactorRingHom ρ q u hrho s
      (foxMatrixPres (substPresF (oneRel ρ s)
        (fun _ : PUnit.{1} => familyFiniteSpineWordBlock q u s))
        (Sum.inr ⟨PUnit.unit, z⟩) (Sum.inr ⟨PUnit.unit, m⟩)) := by
  have hf : foxMatrixPres (substPresF ρ (familyFiniteSpineWordBlock q u))
      (Sum.inr ⟨s, z⟩) (Sum.inr ⟨s, m⟩) =
      MonoidAlgebra.mapDomainRingHom ℤ (finiteSpineFamilyMarkedHom ρ q u s)
        (foxMatrixPres (markedSpineBeta (q s)) (Sum.inr z) m) := by
    convert foxMatrix_markedBlock_internal ρ u (fun t => markedSpineBeta (q t)) s z m using 1 <;> rfl
  have hi : foxMatrixPres (substPresF (oneRel ρ s)
      (fun _ : PUnit.{1} => familyFiniteSpineWordBlock q u s))
      (Sum.inr ⟨PUnit.unit, z⟩) (Sum.inr ⟨PUnit.unit, m⟩) =
      MonoidAlgebra.mapDomainRingHom ℤ (finiteSpineIndividualMarkedHom ρ q u s)
        (foxMatrixPres (markedSpineBeta (q s)) (Sum.inr z) m) := by
    convert foxMatrix_markedBlock_internal (oneRel ρ s)
        (fun _ : PUnit.{1} => u s) (fun _ : PUnit.{1} => markedSpineBeta (q s))
        PUnit.unit z m using 1 <;> rfl
  rw [hf, hi]
  change _ = MonoidAlgebra.mapDomainRingHom ℤ (finiteSpineFactorToFamily ρ q u hrho s)
    (MonoidAlgebra.mapDomainRingHom ℤ (finiteSpineIndividualMarkedHom ρ q u s) _)
  rw [BlockMor.mapDomainRingHom_comp', finiteSpineFactor_marked]

/-- The remaining geometric statement, over each actual individual substituted
group and with the fixed genuine marked-surface coefficients. -/
def FiniteSpineIndividualB2 : Prop :=
  ∀ (s : Sx) (v : NamedSpineRel (q s) →
    MonoidAlgebra ℤ (IndividualGroup ρ (familyFiniteSpineWordBlock q u) s)),
    (∀ z : SpinePresentationGen (q s), ∑ m, v m *
      foxMatrixPres (substPresF (oneRel ρ s)
        (fun _ : PUnit.{1} => familyFiniteSpineWordBlock q u s))
        (Sum.inr ⟨PUnit.unit, z⟩) (Sum.inr ⟨PUnit.unit, m⟩) = 0) →
    ∃ r, ∀ m, v m = r * finiteSpineIndividualFilling ρ q u s m

include hrho in
/-- Individual B2 implies family B2 through the proved injective factor maps.
No finiteness of the old presentation or of the replaced family is imposed. -/
theorem finiteSpineFamilyB2_of_individual (hB2 : FiniteSpineIndividualB2 ρ q u) :
    BlockSurfaceGeneratesFS ρ (familyFiniteSpineWordBlock q u)
      (finiteSpineFamilyFilling ρ q u) := by
  apply blockSurfaceGeneratesFS_of_finite_blocks
  intro s v hv
  obtain ⟨r, hr⟩ := principal_cycles_baseChange
    (finiteSpineFactorToFamily ρ q u hrho s)
    (finiteSpineFactorToFamily_injective ρ q u hrho s)
    (fun z m => foxMatrixPres (substPresF (oneRel ρ s)
      (fun _ : PUnit.{1} => familyFiniteSpineWordBlock q u s))
      (Sum.inr ⟨PUnit.unit, z⟩) (Sum.inr ⟨PUnit.unit, m⟩))
    (finiteSpineIndividualFilling ρ q u s) (hB2 s) v (by
      intro z
      simpa only [finiteSpineFactor_internalMatrix ρ q u hrho,
        finiteSpineFactorRingHom] using hv z)
  refine ⟨r, fun m => ?_⟩
  rw [finiteSpineFamilyFilling_coeff ρ q u hrho]
  exact hr m

/-- Actual arbitrary-family finite-support generation, with B1 and injection
fully discharged. Only the concrete individual B2 remains as an input. -/
theorem finiteSpineFamily_fsGenerates (hB2 : FiniteSpineIndividualB2 ρ q u)
    (x : (Jr ⊕ (Σ s, NamedSpineRel (q s))) →₀
      MonoidAlgebra ℤ (PresGroup (substPresF ρ (familyFiniteSpineWordBlock q u))))
    (hx : coverSecondBoundary (relSub (substPresF ρ (familyFiniteSpineWordBlock q u)))
      (substPresF ρ (familyFiniteSpineWordBlock q u)) x = 0) :
    x ∈ Submodule.span
      (MonoidAlgebra ℤ (PresGroup (substPresF ρ (familyFiniteSpineWordBlock q u))))
      {v | ∃ y : (Jr ⊕ Sx) →₀ MonoidAlgebra ℤ (PresGroup ρ),
        coverSecondBoundary (relSub ρ) ρ y = 0 ∧
        v = fsCellsF ρ (familyFiniteSpineWordBlock q u)
          (familyFiniteSpineWordBlock_filled ρ q u hrho)
          (finiteSpineFamilyFilling ρ q u) y} :=
  fsGenerates_familySubst ρ (familyFiniteSpineWordBlock q u)
    (familyFiniteSpineWordBlock_filled ρ q u hrho) (finiteSpineFamilyFilling ρ q u)
    (finiteSpineFamilyFilling_isFilling ρ q u hrho)
    (finiteSpineFamilyB2_of_individual ρ q u hrho hB2)
    (familyFiniteSpineWordBlock_injective ρ q u hrho) x hx

end FiniteChains.Davis.Genus

namespace FiniteChains.Comb.ReceivedTree
universe u
variable {G H E : Type u} [Group G] [Group H] (φ : G →* H)

/-- Changing the receiving group retains each cell coordinate and pushes
forward its full group-ring coefficient, including coincident sheets. -/
theorem cellCoefficient_mapSheets (e : E) (c : (G × E) →₀ ℤ) :
    cellCoefficient e (Finsupp.mapDomain (fun x : G × E => (φ x.1, x.2)) c) =
      MonoidAlgebra.mapDomainRingHom ℤ φ (cellCoefficient e c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [Finsupp.mapDomain_add, map_add, hc, hd]
  | single x n =>
    obtain ⟨g, j⟩ := x
    erw [Finsupp.mapDomain_single, cellCoefficient_single, cellCoefficient_single]
    by_cases hj : j = e
    · simp_all
    · simp_all

theorem cellCoordinates_symm_mapSheets [Fintype E] (v : E → MonoidAlgebra ℤ G) :
    (cellCoordinates E).symm (fun e => MonoidAlgebra.mapDomainRingHom ℤ φ (v e)) =
      Finsupp.mapDomain (fun x : G × E => (φ x.1, x.2)) ((cellCoordinates E).symm v) := by
  apply (cellCoordinates E).injective
  funext e
  erw [LinearEquiv.apply_symm_apply, ← cellCoefficient_eq_coordinates,
    cellCoefficient_mapSheets, cellCoefficient_coordinates_symm]

end FiniteChains.Comb.ReceivedTree

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb BlockFamily
variable {α Jr S : Type} (ρ : Jr ⊕ S → FreeGroup α)
  (q : S → ℕ) [∀ s, NeZero (q s)] (u : ∀ s, Fin (q s) × Bool → FreeGroup α)

theorem finiteSpineFamilyFilling_named_coeff (s : S) (m : NamedSpineRel (q s)) :
    finiteSpineFamilyFilling ρ q u s m =
      MonoidAlgebra.mapDomainRingHom ℤ (familySpineHom ρ q u s)
        (normalizedNamedSpineVector (q s) (normalizedSpineReference (q s)) m) := by
  change MonoidAlgebra.mapDomainRingHom ℤ (finiteSpineFamilyMarkedHom ρ q u s)
    (markedSpineFilling (q s) m) = _
  erw [markedSpineFilling_named_coeff, BlockMor.mapDomainRingHom_comp']
  rfl

theorem finiteSpineFamilyFilling_faceChain (s : S) :
    receivedSpineFaceChain ρ q u s (finiteSpineFamilyFilling ρ q u s) =
      Finsupp.mapDomain
        (fun x : PresGroup (namedSpinePresentation (q s)) × SpinePresentationRel (q s) =>
          (familySpineHom ρ q u s x.1, x.2)) (normalizedSpineReference (q s)) := by
  apply (ReceivedTree.cellCoordinates (SpinePresentationRel (q s))).injective
  funext j
  erw [← ReceivedTree.cellCoefficient_eq_coordinates,
    receivedSpineFaceChain_coefficient, ← ReceivedTree.cellCoefficient_eq_coordinates,
    ReceivedTree.cellCoefficient_mapSheets, finiteSpineFamilyFilling_named_coeff]
  rfl

theorem finiteSpineFamilyFilling_markingChain (s : S) :
    (ReceivedTree.cellCoordinates (Fin (q s) × Bool)).symm
      (fun i => finiteSpineFamilyFilling ρ q u s (Sum.inr i)) =
      Finsupp.mapDomain
        (fun x : PresGroup (namedSpinePresentation (q s)) × (Fin (q s) × Bool) =>
          (familySpineHom ρ q u s x.1, x.2)) (universalReferenceMarkingCoefficients (q s)) := by
  simp only [finiteSpineFamilyFilling_named_coeff, normalizedNamedSpineVector, Sum.elim_inr]
  exact ReceivedTree.cellCoordinates_symm_mapSheets (familySpineHom ρ q u s)
    (namedSpineSurfaceMarkingCoefficient (q s))

end FiniteChains.Davis.Genus
end

section
open scoped Classical
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily
variable {α Jr : Type} (ρ : Jr ⊕ PUnit.{1} → FreeGroup α)
  (q : ℕ) [NeZero q] (u : Fin q × Bool → FreeGroup α)

def singleFiniteSpineReference : NamedSpineRel q →₀
    MonoidAlgebra ℤ (PresGroup (substPresF ρ (finiteSpineWordBlock q u))) :=
  finiteSpineFamilyFilling ρ (fun _ : PUnit.{1} => q) (fun _ => u) PUnit.unit

theorem singleFiniteSpineReference_internal
    (hrho : ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q))
    (z : SpinePresentationGen q) :
    (∑ m, singleFiniteSpineReference ρ q u m *
      foxMatrixPres (substPresF ρ (finiteSpineWordBlock q u))
        (Sum.inr ⟨PUnit.unit, z⟩) (Sum.inr ⟨PUnit.unit, m⟩)) = 0 := by
  letI : DecidableEq PUnit.{1} := Classical.decEq _
  have h := (finiteSpineFamilyFilling_isFilling ρ
    (fun _ : PUnit.{1} => q) (fun _ => u) (fun s => by cases s; exact hrho)).internal
      PUnit.unit z
  rw [Finsupp.sum_fintype _ _ (fun _ => zero_mul _)] at h
  have hwords : familyFiniteSpineWordBlock (fun _ : PUnit.{1} => q) (fun _ => u) =
      finiteSpineWordBlock q u := by
    funext s
    cases s
    rfl
  with_reducible
    convert h using 1
    apply Finset.sum_congr rfl
    intro m hm
    congr 2
    all_goals first
      | exact Subsingleton.elim _ _
      | (unfold singleFiniteSpineReference; rfl)
      | exact (congrArg (substPresF ρ) hwords).symm
      | exact congrArg (fun r => NamedSpineRel q →₀ MonoidAlgebra ℤ (PresGroup r))
          (congrArg (substPresF ρ) hwords).symm
      | exact congrArg (fun r => fun _ : NamedSpineRel q => MonoidAlgebra ℤ (PresGroup r))
          (congrArg (substPresF ρ) hwords).symm

theorem singleFiniteSpineReference_faceChain :
    receivedSpineFaceChain ρ (fun _ : PUnit.{1} => q) (fun _ => u) PUnit.unit
      (singleFiniteSpineReference ρ q u) =
    Finsupp.mapDomain
      (fun x : PresGroup (namedSpinePresentation q) × SpinePresentationRel q =>
        (familySpineHom ρ (fun _ : PUnit.{1} => q) (fun _ => u) PUnit.unit x.1, x.2))
      (normalizedSpineReference q) :=
  finiteSpineFamilyFilling_faceChain ρ (fun _ : PUnit.{1} => q) (fun _ => u) PUnit.unit

theorem singleFiniteSpineReference_markingChain :
    (ReceivedTree.cellCoordinates (Fin q × Bool)).symm
      (fun i => singleFiniteSpineReference ρ q u (Sum.inr i)) =
    Finsupp.mapDomain
      (fun x : PresGroup (namedSpinePresentation q) × (Fin q × Bool) =>
        (familySpineHom ρ (fun _ : PUnit.{1} => q) (fun _ => u) PUnit.unit x.1, x.2))
      (universalReferenceMarkingCoefficients q) :=
  finiteSpineFamilyFilling_markingChain ρ (fun _ : PUnit.{1} => q) (fun _ => u) PUnit.unit

variable {S : Type} (σ : Jr ⊕ S → FreeGroup α)
  (qs : S → ℕ) [∀ s, NeZero (qs s)] (us : ∀ s, Fin (qs s) × Bool → FreeGroup α)

theorem singleFiniteSpineReference_oneRel (s : S) :
    singleFiniteSpineReference (oneRel σ s) (qs s) (us s) =
      finiteSpineIndividualFilling σ qs us s := rfl

end FiniteChains.Davis.Genus

namespace FiniteChains.Comb
universe u
variable {K X Y : Complex2.{u}}

theorem univLiftV_extendList (f : Hom X Y) (a : X.V)
    (v : UV X a) {p : List (X.E × Bool)} {b : X.V}
    (hp : IsPath X.src X.tgt p (endV v) b) :
    univLiftV a f (extendList p v) =
      extendList (mapPath f p) (univLiftV a f v) := by
  induction p generalizing v with
  | nil => rfl
  | cons e p ih =>
      have htail : IsPath X.src X.tgt p (endV (extend e v)) b := by
        rw [endV_extend hp.1]
        exact hp.2
      change univLiftV a f (extendList p (extend e v)) =
        extendList (mapPath f p) (extend (f.onE e.1, e.2) (univLiftV a f v))
      rw [ih (extend e v) htail, univLiftV_extend a f hp.1]

theorem SpanningTree.univLiftV_mappedTreeReference (T : SpanningTree K)
    (f : Hom K X) (j : Hom X Y) (a : K.V) :
    univLiftV (f.onV T.root) j (T.mappedTreeReference f a) =
      T.mappedTreeReference (j.comp f) a := by
  rw [SpanningTree.mappedTreeReference,
    univLiftV_extendList j (f.onV T.root) (UV.base X (f.onV T.root))
      (isPath_mapPath f (T.treePath_isPath a))]
  change extendList (mapPath j (mapPath f (T.treePath a))) (UV.base _ _) =
    extendList (mapPath (j.comp f) (T.treePath a)) (UV.base _ _)
  rw [mapPath_comp]

end FiniteChains.Comb

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily Nerve
variable {α Jr : Type} (ρ : Jr ⊕ PUnit.{1} → FreeGroup α)
  (q : ℕ) [NeZero q] (u : Fin q × Bool → FreeGroup α)
  (hrho : ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q))

/-- Equality on the entire named source group follows from the already
proved compatibility on the surjective tree-presentation inclusion. -/
theorem universalSpineOldReceiver_to_single_old
    (g : PresGroup (namedSpinePresentation q)) :
    finiteSpineOldRootReceiver q ρ u hrho (singleSpineNamedReceiver ρ q u g) =
      pi1Map (oldIntoNamedQuotient q ρ u) (universalSpineOldBase q)
        (universalSpineOldReceiver q g) := by
  obtain ⟨z, rfl⟩ := (namedSpineGroupEquiv q).surjective g
  have h₁ := DFunLike.congr_fun (finiteSpineOldRootReceiver_compatible q ρ u hrho) z
  have h₂ := DFunLike.congr_fun (universalSpineOldReceiver_compatible q) z
  calc
    _ = pi1Map (markedSpineToNamedQuotient q ρ u) (markedSpineTree q).root
        (SpanningTree.presToPi1 (markedSpineTree q) z) := h₁
    _ = pi1Map (oldIntoNamedQuotient q ρ u) (universalSpineOldBase q)
        (pi1Map (universalSpineToOld q) (markedSpineTree q).root
          (SpanningTree.presToPi1 (markedSpineTree q) z)) :=
      pi1Map_comp_apply (universalSpineToOld q) (oldIntoNamedQuotient q ρ u)
        (markedSpineTree q).root _
    _ = _ := congrArg (pi1Map (oldIntoNamedQuotient q ρ u) (universalSpineOldBase q)) h₂.symm

def universalReceivedSpineToSingle :
    Hom (universalNamedSpineCover q) (singleReceivedSpineCover q ρ u) :=
  ReceivedTree.changeGroup (markedSpineTree q) (universalSpineWordReceiver q)
    (singleSpineNamedReceiver ρ q u)

theorem universalNamedSpineComparison_vertex_factor
    (g : PresGroup (namedSpinePresentation q)) (a : (markedSpineCx q).V) :
    (receivedSpineToQuotient q ρ u hrho).onV (singleSpineNamedReceiver ρ q u g, a) =
      (universalOldToNamedQuotient ρ q u).onV
        ((universalNamedSpineComparison q).onV (g, a)) := by
  have he : univLiftV (universalSpineOldBase q) (oldIntoNamedQuotient q ρ u)
      (ReceivedTree.receiverVertex (markedSpineTree q) (universalSpineToOld q)
        (universalSpineOldReceiver q) g a) =
      ReceivedTree.receiverVertex (markedSpineTree q) (markedSpineToNamedQuotient q ρ u)
        (finiteSpineOldRootReceiver q ρ u hrho) (singleSpineNamedReceiver ρ q u g) a := by
    rw [ReceivedTree.receiverVertex, univLiftV_deckV,
      SpanningTree.univLiftV_mappedTreeReference,
      ← universalSpineOldReceiver_to_single_old ρ q u hrho g]
    rfl
  exact congrArg (pathTransportV (spineQuotientCylinderPath_isPath q ρ u)) he.symm

/-- The square consists of actual cellular maps, before taking chains. -/
theorem universalNamedSpineComparison_square :
    (receivedSpineToQuotient q ρ u hrho).comp (universalReceivedSpineToSingle ρ q u) =
      (universalOldToNamedQuotient ρ q u).comp (universalNamedSpineComparison q) := by
  apply Hom.ext'
  · funext x
    exact universalNamedSpineComparison_vertex_factor ρ q u hrho x.1 x.2
  · funext e
    apply Subtype.ext
    exact Prod.ext (universalNamedSpineComparison_vertex_factor ρ q u hrho e.1 _ ) rfl
  · funext t
    apply Subtype.ext
    exact Prod.ext (universalNamedSpineComparison_vertex_factor ρ q u hrho t.1 _ ) rfl




theorem universalOldToNamedQuotient_chain2_deck
    (g : PresGroup (namedSpinePresentation q))
    (c : (uCover (spineOldCx q) (universalSpineOldBase q)).F →₀ ℤ) :
    chain2 (universalOldToNamedQuotient ρ q u)
      ((univDeck (spineOldCx q) (universalSpineOldBase q)).faceChains
        (universalSpineOldReceiver q g) c) =
      (univDeck (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).faceChains
        (finiteSpineToQuotient ρ q u hrho (singleSpineNamedReceiver ρ q u g))
        (chain2 (universalOldToNamedQuotient ρ q u) c) := by
  change Finsupp.mapDomain (universalOldToNamedQuotient ρ q u).onF
      (Finsupp.mapDomain (deckF (universalSpineOldReceiver q g)) c) =
    Finsupp.mapDomain _ (Finsupp.mapDomain (universalOldToNamedQuotient ρ q u).onF c)
  rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  congr 1
  funext t
  exact (by
    apply Subtype.ext
    exact Prod.ext (by
      change (uCoverPathTransport (spineQuotientCylinderPath_isPath q ρ u)).onV
        (univLiftV (universalSpineOldBase q) (oldIntoNamedQuotient q ρ u)
          (deckV (universalSpineOldReceiver q g) (t.1.1))) = _
      rw [univLiftV_deckV, uCoverPathTransport_deckV,
        ← universalSpineOldReceiver_to_single_old ρ q u hrho g]
      change deckV (pi1Conj (spineQuotientCylinderPath_isPath q ρ u)
        (pi1Conj (isPath_revPath (spineQuotientCylinderPath_isPath q ρ u))
          (finiteSpineToQuotient ρ q u hrho (singleSpineNamedReceiver ρ q u g)))) _ = _
      rw [pi1Conj_cancel_reverse]
      rfl) rfl)

theorem universalOldToNamedQuotient_baseTransport_vertex
    (v : UV (spineOldCx q) (spineOldBase q)) :
    (universalOldToNamedQuotient ρ q u).onV ((universalOldBaseTransport q).onV v) =
      (oldCoverToNamedQuotient q ρ u).onV v := by
  induction v using UV.ind with
  | h p => rfl

theorem universalOldToNamedQuotient_baseTransport_square :
    (universalOldToNamedQuotient ρ q u).comp (universalOldBaseTransport q) =
      oldCoverToNamedQuotient q ρ u := by
  apply Hom.ext'
  · funext v
    exact universalOldToNamedQuotient_baseTransport_vertex ρ q u v
  · funext e
    apply Subtype.ext
    exact Prod.ext (universalOldToNamedQuotient_baseTransport_vertex ρ q u e.1.1) rfl
  · funext t
    apply Subtype.ext
    exact Prod.ext (universalOldToNamedQuotient_baseTransport_vertex ρ q u t.1.1) rfl

/-- The correction uses exactly the same old-cell filling after substitution. -/
theorem universalOldMarkingCorrection_factor
    (g : PresGroup (namedSpinePresentation q)) (i : Fin q × Bool) :
    chain2 (universalOldToNamedQuotient ρ q u) (universalOldMarkingCorrection q g i) =
      quotientMarkingCorrection q ρ u hrho (singleSpineNamedReceiver ρ q u g) i := by
  rw [universalOldMarkingCorrection, universalOldToNamedQuotient_chain2_deck,
    ← chain2_comp_apply, universalOldToNamedQuotient_baseTransport_square]
  rfl

theorem universalOldMarkingCorrections_factor
    (c : (PresGroup (namedSpinePresentation q) × (Fin q × Bool)) →₀ ℤ) :
    chain2 (universalOldToNamedQuotient ρ q u) (universalOldMarkingCorrections q c) =
      quotientMarkingCorrections q ρ u hrho
        (Finsupp.mapDomain (fun x : PresGroup (namedSpinePresentation q) × (Fin q × Bool) =>
          (singleSpineNamedReceiver ρ q u x.1, x.2)) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, Finsupp.mapDomain_add, hc, hd]
  | single x n =>
      rw [universalOldMarkingCorrections, Finsupp.linearCombination_single, map_smul,
        universalOldMarkingCorrection_factor, Finsupp.mapDomain_single,
        quotientMarkingCorrections, Finsupp.linearCombination_single]

theorem singleFiniteSpineReference_corrected_chain :
    quotientCorrectedRelativeChain q ρ u hrho (singleFiniteSpineReference ρ q u) =
      chain2 (universalOldToNamedQuotient ρ q u)
        (chain2 (universalNamedSpineComparison q) (normalizedSpineReference q) -
          universalOldMarkingCorrections q (universalReferenceMarkingCoefficients q)) := by
  rw [quotientCorrectedRelativeChain, singleFiniteSpineReference_faceChain,
    singleFiniteSpineReference_markingChain, map_sub]
  rw [show chain2 (receivedSpineToQuotient q ρ u hrho)
      (Finsupp.mapDomain (fun x : PresGroup (namedSpinePresentation q) × SpinePresentationRel q =>
        (familySpineHom ρ (fun _ : PUnit.{1} => q) (fun _ => u) PUnit.unit x.1, x.2))
        (normalizedSpineReference q)) =
      chain2 (universalOldToNamedQuotient ρ q u)
        (chain2 (universalNamedSpineComparison q) (normalizedSpineReference q)) from
      (by
        change chain2 (receivedSpineToQuotient q ρ u hrho)
          (chain2 (universalReceivedSpineToSingle ρ q u) _) = _
        rw [← chain2_comp_apply, universalNamedSpineComparison_square, chain2_comp_apply])]
  rw [universalOldMarkingCorrections_factor]
  rfl

/-- The actual canonical coefficient vector has the actual degree-one
attaching reference modulo a genuine old three-boundary. -/
theorem singleFiniteSpineReference_corrected_geometry :
    ∃ y ∈ IncOn (fun p => InQOld (uOrderEnd p)),
      quotientCorrectedRelativeNerveChain q ρ u hrho (singleFiniteSpineReference ρ q u) =
        cmap Subtype.val (transportedUniversalPolygonAttachingChain ρ q u) + Nerve.bdry y := by
  have h := universalOldToNamedQuotient_polygon_reference ρ q u
    (chain2 (universalNamedSpineComparison q) (normalizedSpineReference q) -
      universalOldMarkingCorrections q (universalReferenceMarkingCoefficients q))
    (normalizedSpineReference_corrected_geometry q)
  simpa only [quotientCorrectedRelativeNerveChain, singleFiniteSpineReference_corrected_chain]
    using h

end FiniteChains.Davis.Genus
end

section
open scoped Classical
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

def normalizedWeakChain1To (f : P → Q) (hf : Monotone f) :
    (OrdEdge P →₀ ℤ) →ₗ[ℤ] (StrictOrdEdge Q →₀ ℤ) :=
  normalizeOrdChain1.comp (chain1 (orderCxMap f hf))

theorem normalizeOrdEdge_apply_zero_of_endpoints_ne
    (d : OrdEdge Q) (e : StrictOrdEdge Q) (h : d.1 ≠ e.1) :
    normalizeOrdEdge d e = 0 := by
  unfold normalizeOrdEdge
  grind

theorem normalizedWeakChain1To_single (f : P → Q) (hf : Monotone f)
    (d : OrdEdge P) (n : ℤ) :
    normalizedWeakChain1To f hf (Finsupp.single d n) =
      n • normalizeOrdEdge ((orderCxMap f hf).onE d) := by
  change normalizeOrdChain1 (Finsupp.mapDomain (orderCxMap f hf).onE
    (Finsupp.single d n)) = _
  simp

theorem normalizedWeakChain1To_path_apply_zero
    (f : P → Q) (hf : Monotone f) (p : List (OrdEdge P × Bool))
    (e : StrictOrdEdge Q)
    (hp : ∀ a ∈ p, (f a.1.1.1, f a.1.1.2) ≠ e.1) :
    normalizedWeakChain1To f hf (pathChain p) e = 0 := by
  induction p with
  | nil => simp
  | cons a p ih =>
      have ha := hp a (List.mem_cons_self ..)
      have ht := ih (fun b hb => hp b (List.mem_cons_of_mem a hb))
      have hs : normalizedWeakChain1To f hf (Finsupp.single a.1 1) e = 0 := by
        erw [normalizedWeakChain1To_single, one_smul]
        exact normalizeOrdEdge_apply_zero_of_endpoints_ne _ e ha
      erw [pathChain_cons]
      cases a.2 <;>
        simp only [Bool.false_eq_true, ↓reduceIte, map_add,
          map_neg, Finsupp.add_apply, Finsupp.neg_apply, hs, ht, neg_zero, add_zero]

theorem normalizedWeakChain1To_positive_first_coefficient
    (f : P → Q) (hf : Monotone f) (d : OrdEdge P)
    (p : List (OrdEdge P × Bool)) (e₀ e : StrictOrdEdge Q)
    (hfirst : e₀.1 = (f d.1.1, f d.1.2))
    (htail : ∀ a ∈ p, (f a.1.1.1, f a.1.1.2) ≠ e.1) :
    normalizedWeakChain1To f hf (pathChain ((d, true) :: p)) e =
      if e₀ = e then 1 else 0 := by
  have hne : f d.1.1 ≠ f d.1.2 := by
    have h := e₀.2.ne
    simpa only [hfirst] using h
  have hs : normalizeOrdEdge ((orderCxMap f hf).onE d) = Finsupp.single e₀ 1 := by
    unfold normalizeOrdEdge
    dsimp only [orderCxMap]
    erw [dif_neg hne]
    congr 1
    exact Subtype.ext hfirst.symm
  erw [pathChain_cons]
  simp only [↓reduceIte, map_add, Finsupp.add_apply,
    normalizedWeakChain1To_single, one_smul, hs,
    normalizedWeakChain1To_path_apply_zero f hf p e htail, add_zero,
    Finsupp.single_apply]

theorem normalizedWeakChain1To_normalize (f : P → Q) (hf : Monotone f)
    (c : OrdEdge P →₀ ℤ) :
    normalizedWeakChain1To f hf c =
      normalizedChain1To f hf (normalizeOrdChain1 c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single e n =>
      rw [normalizedWeakChain1To_single, normalizeOrdChain1_single, map_smul]
      congr 1
      obtain ⟨⟨a, b⟩, hab⟩ := e
      by_cases he : a = b
      · subst b
        simp [normalizeOrdEdge, orderCxMap]
      · have hlt  := lt_of_le_of_ne hab he
        have hn : normalizeOrdEdge ⟨(a, b), hab⟩ =
            Finsupp.single ⟨(a, b), hlt⟩ 1 := by
          simp [normalizeOrdEdge, he]
        erw [hn]
        change normalizeOrdEdge ((orderCxMap f hf).onE ⟨(a, b), hab⟩) =
          normalizeOrdChain1 (Finsupp.mapDomain (orderCxMap f hf).onE
            (Finsupp.mapDomain (strictOrderIncl P).onE
              (Finsupp.single ⟨(a, b), hlt⟩ 1)))
        erw [Finsupp.mapDomain_single, Finsupp.mapDomain_single,
          normalizeOrdChain1_single, one_smul]
        rfl

theorem normalizeOrdChain1_strict_map (f : P → Q) (hf : StrictMono f)
    (c : OrdEdge P →₀ ℤ) :
    normalizeOrdChain1 (chain1 (orderCxMap f hf.monotone) c) =
      chain1 (strictOrderCxMap f hf) (normalizeOrdChain1 c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single e n =>
      obtain ⟨⟨a, b⟩, hab⟩ := e
      by_cases he : a = b
      · subst b
        simp [chain1, normalizeOrdChain1, normalizeOrdEdge, orderCxMap]
      · have hlt  := lt_of_le_of_ne hab he
        simp [chain1, normalizeOrdChain1, normalizeOrdEdge, orderCxMap,
          strictOrderCxMap, he, (hf hlt).ne]

end FiniteChains.Comb
end

section
open scoped Classical
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily Nerve
variable (q : ℕ) [NeZero q] {α Jr : Type}
  (ρ : Jr ⊕ PUnit.{1} → FreeGroup α) (u : Fin q × Bool → FreeGroup α)
  (hrho : ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q))

abbrev namedSurfaceForward : namedAttachingCover q ρ u → NamedSurfaceCover ρ q u :=
  attachingToSurfaceCover (namedSurfaceLabel ρ q u) (namedQuotientBase ρ q u)
    (namedQuotientPos_isConnected ρ q u)

theorem namedSurfaceForward_monotone : Monotone (namedSurfaceForward q ρ u) :=
  attachingToSurfaceCover_monotone (namedSurfaceLabel ρ q u)
    (namedQuotientBase ρ q u) (namedQuotientPos_isConnected ρ q u)

abbrev namedAttachingSurfaceChain1 :=
  attachingSurfaceChain1 (namedSurfaceLabel ρ q u) (namedQuotientBase ρ q u)
    (namedQuotientPos_isConnected ρ q u)

abbrev namedAttachingDeckHom (g : QuotientMarkingGroup q ρ u) :=
  orderCxMap (namedAttachingDeck ρ q u g) (namedAttachingDeck ρ q u g).monotone

theorem exists_referenceMarkingFirst (i : Fin q × Bool) :
    ∃ e : OrdEdge (namedAttachingCover q ρ u),
      ∃ p : List (OrdEdge (namedAttachingCover q ρ u) × Bool),
        namedAttachingMarkingPath q ρ u hrho 1 i = (e, true) :: p ∧
        e.1.1 = namedAttachingReference q ρ u hrho 1 ∧
        (namedAttachingProjection q ρ u).onE e = markingFirstEdge q i ∧
        mapPath (namedAttachingProjection q ρ u) p = markingTail q i := by
  have hm := (namedAttachingMarkingPath_spec q ρ u hrho 1 i).2
  rw [gSig_first_edge] at hm
  cases hp : namedAttachingMarkingPath q ρ u hrho 1 i with
  | nil => simp_all
  | cons a p =>
      have hm' : ((namedAttachingProjection q ρ u).onE a.1, a.2) =
          (markingFirstEdge q i, true) ∧
          mapPath (namedAttachingProjection q ρ u) p = markingTail q i := by
        simpa only [hp, mapPath, List.map_cons, List.cons.injEq] using hm
      have hb : a.2 = true := congrArg Prod.snd hm'.1
      have he := congrArg Prod.fst hm'.1
      have hs := (namedAttachingMarkingPath_spec q ρ u hrho 1 i).1
      rw [hp] at hs
      refine ⟨a.1, p, ?_, ?_, he, hm'.2⟩
      · exact congrArg (fun b => (a.1, b) :: p) hb
      · simpa only [hb, germSrc, orderCx, ite_true] using hs.1.symm

def referenceMarkingFirst (i : Fin q × Bool) : OrdEdge (namedAttachingCover q ρ u) :=
  Classical.choose (exists_referenceMarkingFirst q ρ u hrho i)

def referenceMarkingTail (i : Fin q × Bool) :
    List (OrdEdge (namedAttachingCover q ρ u) × Bool) :=
  Classical.choose (Classical.choose_spec (exists_referenceMarkingFirst q ρ u hrho i))

theorem referenceMarkingFirst_spec (i : Fin q × Bool) :
    namedAttachingMarkingPath q ρ u hrho 1 i =
        (referenceMarkingFirst q ρ u hrho i, true) :: referenceMarkingTail q ρ u hrho i ∧
      (referenceMarkingFirst q ρ u hrho i).1.1 = namedAttachingReference q ρ u hrho 1 ∧
      (namedAttachingProjection q ρ u).onE (referenceMarkingFirst q ρ u hrho i) =
        markingFirstEdge q i ∧
      mapPath (namedAttachingProjection q ρ u) (referenceMarkingTail q ρ u hrho i) =
        markingTail q i :=
  Classical.choose_spec (Classical.choose_spec (exists_referenceMarkingFirst q ρ u hrho i))

def allNamedAttachingMarkingPath (g : QuotientMarkingGroup q ρ u) (i : Fin q × Bool) :=
  mapPath (namedAttachingDeckHom q ρ u g) (namedAttachingMarkingPath q ρ u hrho 1 i)

def allNamedAttachingFirst (g : QuotientMarkingGroup q ρ u) (i : Fin q × Bool) :=
  (namedAttachingDeckHom q ρ u g).onE (referenceMarkingFirst q ρ u hrho i)

def allNamedAttachingTail (g : QuotientMarkingGroup q ρ u) (i : Fin q × Bool) :=
  mapPath (namedAttachingDeckHom q ρ u g) (referenceMarkingTail q ρ u hrho i)

theorem allNamedAttachingMarkingPath_cons (g : QuotientMarkingGroup q ρ u)
    (i : Fin q × Bool) :
    allNamedAttachingMarkingPath q ρ u hrho g i =
      (allNamedAttachingFirst q ρ u hrho g i, true) :: allNamedAttachingTail q ρ u hrho g i := by
  simpa only [allNamedAttachingMarkingPath, allNamedAttachingFirst,
    allNamedAttachingTail, mapPath, List.map_cons] using
    congrArg (mapPath (namedAttachingDeckHom q ρ u g))
      (referenceMarkingFirst_spec q ρ u hrho i).1

theorem allNamedAttachingFirst_lastEndpoints (g : QuotientMarkingGroup q ρ u)
    (i : Fin q × Bool) :
    (namedSurfaceProjection ρ q u
        (namedSurfaceForward q ρ u (allNamedAttachingFirst q ρ u hrho g i).1.1),
      namedSurfaceProjection ρ q u
        (namedSurfaceForward q ρ u (allNamedAttachingFirst q ρ u hrho g i).1.2)) =
      (markingBaseCell q, markingBedCell q i false) := by
  have he := (referenceMarkingFirst_spec q ρ u hrho i).2.2.1
  have hs := congrArg (fun e : MarkingSurfaceEdge q => e.1.1) he
  have ht := congrArg (fun e : MarkingSurfaceEdge q => e.1.2) he
  change qAttachingCoverEnd (namedQuotientBase ρ q u)
    (referenceMarkingFirst q ρ u hrho i).1.1 = (markingFirstEdge q i).1.1 at hs
  change qAttachingCoverEnd (namedQuotientBase ρ q u)
    (referenceMarkingFirst q ρ u hrho i).1.2 = (markingFirstEdge q i).1.2 at ht
  change (chainMax (qAttachingCoverEnd (namedQuotientBase ρ q u)
      (namedAttachingDeck ρ q u g (referenceMarkingFirst q ρ u hrho i).1.1)),
    chainMax (qAttachingCoverEnd (namedQuotientBase ρ q u)
      (namedAttachingDeck ρ q u g (referenceMarkingFirst q ρ u hrho i).1.2))) = _
  rw [namedAttachingDeck_projection, namedAttachingDeck_projection, hs, ht]
  simp only [markingFirstEdge, markingBaseFlag, chainMax_spx1, chainMax_spx2]


def allNamedSurfaceFirst (g : QuotientMarkingGroup q ρ u) (i : Fin q × Bool) :
    StrictOrdEdge (NamedSurfaceCover ρ q u) :=
  ⟨(namedSurfaceForward q ρ u (allNamedAttachingFirst q ρ u hrho g i).1.1,
      namedSurfaceForward q ρ u (allNamedAttachingFirst q ρ u hrho g i).1.2),
    (by
      apply lt_of_le_of_ne ((namedSurfaceForward_monotone q ρ u)
        (allNamedAttachingFirst q ρ u hrho g i).2)
      intro he
      have hp := allNamedAttachingFirst_lastEndpoints q ρ u hrho g i
      have hs := congrArg Prod.fst hp
      have ht := congrArg Prod.snd hp
      have hh := congrArg (namedSurfaceProjection ρ q u) he
      dsimp only at hs ht
      rw [hs, ht] at hh
      cases hh)⟩

theorem allNamedSurfaceFirst_source (g : QuotientMarkingGroup q ρ u)
    (i : Fin q × Bool) :
    (allNamedSurfaceFirst q ρ u hrho g i).1.1 =
      namedSurfaceDeck ρ q u g
        (namedSurfaceForward q ρ u (namedAttachingReference q ρ u hrho 1)) := by
  change namedSurfaceForward q ρ u
      (namedAttachingDeck ρ q u g (referenceMarkingFirst q ρ u hrho i).1.1) = _
  rw [(referenceMarkingFirst_spec q ρ u hrho i).2.1]
  exact namedAttachingToSurface_deck ρ q u g _

theorem allNamedSurfaceFirst_target_projection (g : QuotientMarkingGroup q ρ u)
    (i : Fin q × Bool) :
    namedSurfaceProjection ρ q u (allNamedSurfaceFirst q ρ u hrho g i).1.2 =
      markingBedCell q i false :=
  congrArg Prod.snd (allNamedAttachingFirst_lastEndpoints q ρ u hrho g i)


theorem markingTail_lastEndpoints_avoids (i j : Fin q × Bool)
    (a : MarkingSurfaceEdge q × Bool) (ha : a ∈ markingTail q j) :
    (chainMax a.1.1.1, chainMax a.1.1.2) ≠
      (markingBaseCell q, markingBedCell q i false) := by
  simp only [markingTail, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [markingBedBaseFlag, markingBedMidFlag, markingMidFlag, markingBaseFlag,
      markingBaseCell, markingBedCell, markingMidCell]
  all_goals intro h
  · cases h
  · cases h
  · grind

theorem allNamedAttachingTail_surface_avoids (g h : QuotientMarkingGroup q ρ u)
    (i j : Fin q × Bool) (a : OrdEdge (namedAttachingCover q ρ u) × Bool)
    (ha : a ∈ allNamedAttachingTail q ρ u hrho h j) :
    (namedSurfaceForward q ρ u a.1.1.1, namedSurfaceForward q ρ u a.1.1.2) ≠
      (allNamedSurfaceFirst q ρ u hrho g i).1 := by
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  have hb' : ((namedAttachingProjection q ρ u).onE b.1, b.2) ∈ markingTail q j := by
    rw [← (referenceMarkingFirst_spec q ρ u hrho j).2.2.2]
    exact List.mem_map.mpr ⟨b, hb, rfl⟩
  intro he
  have hp := (congrArg (fun z : NamedSurfaceCover ρ q u × NamedSurfaceCover ρ q u =>
    (namedSurfaceProjection ρ q u z.1, namedSurfaceProjection ρ q u z.2)) he).trans
      (allNamedAttachingFirst_lastEndpoints q ρ u hrho g i)
  change (chainMax (qAttachingCoverEnd (namedQuotientBase ρ q u)
      (namedAttachingDeck ρ q u h b.1.1.1)),
    chainMax (qAttachingCoverEnd (namedQuotientBase ρ q u)
      (namedAttachingDeck ρ q u h b.1.1.2))) = _ at hp
  rw [namedAttachingDeck_projection, namedAttachingDeck_projection] at hp
  exact markingTail_lastEndpoints_avoids q i j _ hb' hp

def allNamedAttachingMarkingChains :
    ((QuotientMarkingGroup q ρ u × (Fin q × Bool)) →₀ ℤ) →ₗ[ℤ]
      (OrdEdge (namedAttachingCover q ρ u) →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun x => pathChain (allNamedAttachingMarkingPath q ρ u hrho x.1 x.2))

def allNamedSurfaceMarkingChains :
    ((QuotientMarkingGroup q ρ u × (Fin q × Bool)) →₀ ℤ) →ₗ[ℤ]
      (StrictOrdEdge (NamedSurfaceCover ρ q u) →₀ ℤ) :=
  (normalizedWeakChain1To (namedSurfaceForward q ρ u) (namedSurfaceForward_monotone q ρ u)).comp
    (allNamedAttachingMarkingChains q ρ u hrho)

theorem allNamedSurfaceMarkingChains_coefficient
    (c : (QuotientMarkingGroup q ρ u × (Fin q × Bool)) →₀ ℤ)
    (g : QuotientMarkingGroup q ρ u) (i : Fin q × Bool) :
    allNamedSurfaceMarkingChains q ρ u hrho c (allNamedSurfaceFirst q ρ u hrho g i) = c (g, i) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single x n =>
      change normalizedWeakChain1To _ _
        (allNamedAttachingMarkingChains q ρ u hrho (Finsupp.single x n)) _ = _
      rw [allNamedAttachingMarkingChains, Finsupp.linearCombination_single ℤ, map_zsmul,
        Finsupp.smul_apply, allNamedAttachingMarkingPath_cons,
        normalizedWeakChain1To_positive_first_coefficient _ _ _ _
          (allNamedSurfaceFirst q ρ u hrho x.1 x.2) _ rfl
          (allNamedAttachingTail_surface_avoids q ρ u hrho g x.1 i x.2)]
      have hinj := (show Function.Injective (fun x : QuotientMarkingGroup q ρ u × (Fin q × Bool) =>
      allNamedSurfaceFirst q ρ u hrho x.1 x.2) by
        intro x y h
        have hs := congrArg (fun e : StrictOrdEdge (NamedSurfaceCover ρ q u) => e.1.1) h
        dsimp only at hs
        rw [allNamedSurfaceFirst_source, allNamedSurfaceFirst_source] at hs
        have hg := congrArg (fun v : NamedSurfaceCover ρ q u => v.1.1) hs
        have hg'  := deckV_injective_in_group _
          (namedSurfaceForward q ρ u (namedAttachingReference q ρ u hrho 1)).1.1 hg
        have ht := congrArg (fun e : StrictOrdEdge (NamedSurfaceCover ρ q u) =>
          namedSurfaceProjection ρ q u e.1.2) h
        dsimp only at ht
        rw [allNamedSurfaceFirst_target_projection, allNamedSurfaceFirst_target_projection] at ht
        have hi := congrArg (fun z : Fin q × Bool × Bool => (z.1, z.2.1)) (Cell.bed.inj ht)
        exact Prod.ext hg' hi)
      have heq : allNamedSurfaceFirst q ρ u hrho x.1 x.2 =
          allNamedSurfaceFirst q ρ u hrho g i ↔ x = (g, i) := by
        constructor
        · exact @hinj x (g, i)
        · rintro rfl
          rfl
      by_cases hx : x = (g, i) <;> simp only [heq, hx, ↓reduceIte, Finsupp.single_apply,
        smul_eq_mul, mul_one, mul_zero]

theorem allNamedSurfaceMarkingChains_injective :
    Function.Injective (allNamedSurfaceMarkingChains q ρ u hrho) := by
  intro c d he
  ext x
  have h := congrArg (fun z : StrictOrdEdge (NamedSurfaceCover ρ q u) →₀ ℤ =>
    z (allNamedSurfaceFirst q ρ u hrho x.1 x.2)) he
  simpa only [allNamedSurfaceMarkingChains_coefficient] using h

theorem namedAttachingIntoUniversal_chain1_injective :
    Function.Injective (chain1 (namedAttachingIntoUniversal q ρ u)) := by
  apply Finsupp.mapDomain_injective
  intro e f h
  have he := uOrderEdge_injective h
  apply Subtype.ext
  exact Prod.ext (Subtype.ext (congrArg (fun d => d.1.1) he))
    (Subtype.ext (congrArg (fun d => d.1.2) he))

theorem allNamedAttachingMarkingChains_image
    (c : (QuotientMarkingGroup q ρ u × (Fin q × Bool)) →₀ ℤ) :
    chain1 (namedAttachingIntoUniversal q ρ u) (allNamedAttachingMarkingChains q ρ u hrho c) =
      allQuotientSurfaceMarkingChains q ρ u c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single x n =>
      simp only [allNamedAttachingMarkingChains, allQuotientSurfaceMarkingChains,
        liftedMarkingChainMap, Finsupp.linearCombination_single ℤ, map_smul]
      erw [Finsupp.linearCombination_single ℤ]
      apply congrArg (fun z => n • z)
      have hbase : chain1 (namedAttachingIntoUniversal q ρ u)
          (pathChain (namedAttachingMarkingPath q ρ u hrho 1 x.2)) =
          pathChain (uLiftPath
            (mapPath (oldIntoNamedQuotient q ρ u) (surfaceOldMarking q x.2))
            (quotientCylinderVertex q ρ u)) := by
        change Finsupp.mapDomain (namedAttachingIntoUniversal q ρ u).onE _ = _
        rw [← pathChain_map]
        change pathChain (mapPath (namedAttachingIntoUniversal q ρ u)
          (namedAttachingMarkingPath q ρ u hrho 1 x.2)) = _
        rw [namedAttachingMarkingPath_image]
        simp only [map_one, deckV_one]
      have hp : IsPath (orderCx (namedQuotientPos ρ q u)).src
          (orderCx (namedQuotientPos ρ q u)).tgt
          (mapPath (oldIntoNamedQuotient q ρ u) (surfaceOldMarking q x.2))
          (endV (quotientCylinderVertex q ρ u))
          ((oldIntoNamedQuotient q ρ u).onV (spineOldBase q)) := by
        rw [quotientCylinderVertex_end]
        exact isPath_mapPath _ (surfaceOldMarking_isPath q x.2)
      unfold allNamedAttachingMarkingPath
      rw [mapPath, pathChain_map]
      change chain1 (namedAttachingIntoUniversal q ρ u)
        (chain1 (namedAttachingDeckHom q ρ u x.1)
          (pathChain (namedAttachingMarkingPath q ρ u hrho 1 x.2))) = _
      rw [namedAttachingIntoUniversal_chain1_deck, hbase]
      simpa only [quotientSurfaceMarking_first_edge, allQuotientMarkingVertex] using
        univDeck_pathChain (K := orderCx (namedQuotientPos ρ q u))
          (namedQuotientBase ρ q u) x.1 (quotientCylinderVertex q ρ u) hp


theorem namedSurfaceMarkingChains_factor
    (c : (PresGroup (substPresF ρ (finiteSpineWordBlock q u)) × (Fin q × Bool)) →₀ ℤ) :
    normalizedWeakChain1To (namedSurfaceForward q ρ u) (namedSurfaceForward_monotone q ρ u)
        (namedAttachingMarkingChains q ρ u hrho c) =
      allNamedSurfaceMarkingChains q ρ u hrho
        (Finsupp.mapDomain (fun x => (finiteSpineToQuotient ρ q u hrho x.1, x.2)) c) := by
  exact congrArg
    (normalizedWeakChain1To (namedSurfaceForward q ρ u) (namedSurfaceForward_monotone q ρ u))
    (by
      apply namedAttachingIntoUniversal_chain1_injective q ρ u
      rw [namedAttachingMarkingChains_image, allNamedAttachingMarkingChains_image,
        quotientSurfaceMarkingChains_factor])




theorem allNamedSurfaceMarkingChains_multiply
    (w : MonoidAlgebra ℤ (QuotientMarkingGroup q ρ u))
    (c : (QuotientMarkingGroup q ρ u × (Fin q × Bool)) →₀ ℤ) :
    allNamedSurfaceMarkingChains q ρ u hrho (ReceivedTree.multiplyCellChain c w) =
      Finsupp.linearCombination ℤ (fun g =>
        chain1 (strictOrderCxMap (namedSurfaceDeck ρ q u g) (namedSurfaceDeck ρ q u g).strictMono)
          (allNamedSurfaceMarkingChains q ρ u hrho c)) w.coeff := by
  induction w using MonoidAlgebra.induction_linear with
  | zero => simp
  | add w z hw hz => simp_all
  | single g n =>
      have hm : ReceivedTree.multiplyCellChain c (MonoidAlgebra.single g n) =
          n • ReceivedTree.translateCellChain g c := by
        simp [ReceivedTree.multiplyCellChain]
      rw [hm, map_zsmul, (show allNamedSurfaceMarkingChains q ρ u hrho (ReceivedTree.translateCellChain g c) =
      chain1 (strictOrderCxMap (namedSurfaceDeck ρ q u g) (namedSurfaceDeck ρ q u g).strictMono)
        (allNamedSurfaceMarkingChains q ρ u hrho c) by
        change normalizeOrdChain1
          (chain1 (orderCxMap (namedSurfaceForward q ρ u) (namedSurfaceForward_monotone q ρ u))
            (allNamedAttachingMarkingChains q ρ u hrho (ReceivedTree.translateCellChain g c))) = _
        rw [(show allNamedAttachingMarkingChains q ρ u hrho (ReceivedTree.translateCellChain g c) =
      chain1 (namedAttachingDeckHom q ρ u g) (allNamedAttachingMarkingChains q ρ u hrho c) by
          apply namedAttachingIntoUniversal_chain1_injective q ρ u
          rw [allNamedAttachingMarkingChains_image, namedAttachingIntoUniversal_chain1_deck,
            allNamedAttachingMarkingChains_image, allQuotientSurfaceMarkingChains_translate]), ← chain1_comp_apply,
          (show (orderCxMap (namedSurfaceForward q ρ u) (namedSurfaceForward_monotone q ρ u)).comp
        (namedAttachingDeckHom q ρ u g) =
      (orderCxMap (namedSurfaceDeck ρ q u g) (namedSurfaceDeck ρ q u g).monotone).comp
        (orderCxMap (namedSurfaceForward q ρ u) (namedSurfaceForward_monotone q ρ u)) by
            apply Hom.ext'
            · funext p
              exact namedAttachingToSurface_deck ρ q u g p
            · funext e
              apply Subtype.ext
              exact Prod.ext (namedAttachingToSurface_deck ρ q u g e.1.1)
                (namedAttachingToSurface_deck ρ q u g e.1.2)
            · funext t
              apply Subtype.ext
              exact Prod.ext (namedAttachingToSurface_deck ρ q u g t.1.1)
                (Prod.ext (namedAttachingToSurface_deck ρ q u g t.1.2.1)
                  (namedAttachingToSurface_deck ρ q u g t.1.2.2))), chain1_comp_apply,
          normalizeOrdChain1_strict_map (namedSurfaceDeck ρ q u g)
            (namedSurfaceDeck ρ q u g).strictMono]
        rfl)]
      let f := fun g => chain1
        (strictOrderCxMap (namedSurfaceDeck ρ q u g) (namedSurfaceDeck ρ q u g).strictMono)
        (allNamedSurfaceMarkingChains q ρ u hrho c)
      change n • f g = Finsupp.linearCombination ℤ f (Finsupp.single g n)
      exact (Finsupp.linearCombination_single ℤ n g).symm


/-- Exact recovery in the entire quotient group from the normalized surface
boundary. The chain map need only be injective on these genuine markings. -/
theorem namedSurfaceMarking_multiple_reflect
    (c d : (PresGroup (substPresF ρ (finiteSpineWordBlock q u)) × (Fin q × Bool)) →₀ ℤ)
    (w : MonoidAlgebra ℤ (QuotientMarkingGroup q ρ u))
    (h : namedAttachingSurfaceChain1 q ρ u
        (normalizeOrdChain1 (namedAttachingMarkingChains q ρ u hrho c)) =
      Finsupp.linearCombination ℤ (fun g =>
        chain1 (strictOrderCxMap (namedSurfaceDeck ρ q u g) (namedSurfaceDeck ρ q u g).strictMono)
          (namedAttachingSurfaceChain1 q ρ u
            (normalizeOrdChain1 (namedAttachingMarkingChains q ρ u hrho d)))) w.coeff) :
    quotientSurfaceMarkingChains q ρ u hrho c =
      Finsupp.linearCombination ℤ (fun g => chain1
        ((univDeck (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).cellHom g)
          (quotientSurfaceMarkingChains q ρ u hrho d)) w.coeff := by
  change normalizedChain1To (namedSurfaceForward q ρ u) (namedSurfaceForward_monotone q ρ u)
      (normalizeOrdChain1 (namedAttachingMarkingChains q ρ u hrho c)) =
    Finsupp.linearCombination ℤ (fun g =>
      chain1 (strictOrderCxMap (namedSurfaceDeck ρ q u g) (namedSurfaceDeck ρ q u g).strictMono)
        (normalizedChain1To (namedSurfaceForward q ρ u) (namedSurfaceForward_monotone q ρ u)
          (normalizeOrdChain1 (namedAttachingMarkingChains q ρ u hrho d)))) w.coeff at h
  simp only [← normalizedWeakChain1To_normalize, namedSurfaceMarkingChains_factor] at h
  rw [← allNamedSurfaceMarkingChains_multiply] at h
  have hc := allNamedSurfaceMarkingChains_injective q ρ u hrho h
  simp only [quotientSurfaceMarkingChains_factor]
  rw [hc, allQuotientSurfaceMarkingChains_multiply]

end FiniteChains.Davis.Genus

namespace FiniteChains.Comb
open Nerve
universe u
variable {P : Type u} [PartialOrder P]

theorem decodeOrdNerve2_boundary_of_encoded_boundary
    (c : Ch P) (hc : c ∈ Inc P) (hd : lengthProjection 3 c = c)
    (b : OrdEdge P →₀ ℤ) (hb : Nerve.bdry c = ordNerveChain1 b) :
    Comb.bdry2 (orderCx P) (decodeOrdNerve2 c) = b := by
  apply ordNerveChain1_injective
  rw [ordNerveChain1_bdry2, ordNerveChain2_decode hc, hd, hb]

end FiniteChains.Comb

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily Nerve
variable {α Jr : Type} (ρ : Jr ⊕ PUnit.{1} → FreeGroup α)
  (q : ℕ) [NeZero q] (u : Fin q × Bool → FreeGroup α)

/-- Decode and normalize the genuine marked boundary of the attaching chain.
All coefficients and cover sheets are retained. -/
theorem namedAttachingNerveSurfaceChain_marked_boundary
    (hrho : ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q))
    (c : Ch (namedAttachingCover q ρ u)) (hc : c ∈ Inc _)
    (hd : lengthProjection 3 c = c)
    (b : (PresGroup (substPresF ρ (finiteSpineWordBlock q u)) × (Fin q × Bool)) →₀ ℤ)
    (hb : Nerve.bdry c = namedAttachingNerveBoundary q ρ u hrho b) :
    Comb.bdry2 (strictOrderCx (NamedSurfaceCover ρ q u))
        (namedAttachingNerveSurfaceChain ρ q u c) =
      namedAttachingSurfaceChain1 q ρ u
        (normalizeOrdChain1 (namedAttachingMarkingChains q ρ u hrho b)) := by
  have hdecoded  :=
    decodeOrdNerve2_boundary_of_encoded_boundary c hc hd
      (namedAttachingMarkingChains q ρ u hrho b) hb
  change Comb.bdry2 (strictOrderCx (NamedSurfaceCover ρ q u))
      (normalizeOrdChain2 (chain2
        (orderCxMap (namedSurfaceForward q ρ u) (namedSurfaceForward_monotone q ρ u))
        (decodeOrdNerve2 c))) = _
  rw [bdry2_normalizeOrdChain2, bdry2_chain2, hdecoded]
  exact normalizedWeakChain1To_normalize
    (namedSurfaceForward q ρ u) (namedSurfaceForward_monotone q ρ u)
    (namedAttachingMarkingChains q ρ u hrho b)

/-- The old three-chain in the relative comparison does not alter the
actual attaching boundary. This proves the input of the preceding lemma. -/
theorem namedAttaching_marked_boundary_of_relative_class
    (hrho : ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q))
    (β : NamedSpineRel q → MonoidAlgebra ℤ
      (PresGroup (substPresF ρ (finiteSpineWordBlock q u))))
    (hβ : ∀ z : SpinePresentationGen q,
      (∑ m, β m * foxMatrixPres (substPresF ρ (finiteSpineWordBlock q u))
        (Sum.inr ⟨PUnit.unit, z⟩) (Sum.inr ⟨PUnit.unit, m⟩)) = 0)
    (c : Ch (namedAttachingCover q ρ u))
    (y : Ch (UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u)))
    (hC : quotientCorrectedRelativeNerveChain q ρ u hrho β =
      cmap Subtype.val c + Nerve.bdry y) :
    Nerve.bdry c = namedAttachingNerveBoundary q ρ u hrho
      ((ReceivedTree.cellCoordinates (Fin q × Bool)).symm (fun i => β (Sum.inr i))) := by
  apply cmap_val_injective _
    ⟨(namedAttachingReference q ρ u hrho 1).1, (namedAttachingReference q ρ u hrho 1).2⟩
  have h := congrArg Nerve.bdry hC
  rw [quotientCorrectedRelativeNerveChain_boundary q ρ u hrho β hβ,
    map_add, Nerve.bdry_bdry, add_zero, ← cmap_bdry,
    namedAttachingNerveBoundary_image] at h
  exact h.symm

theorem namedPolygonMultipleAt_boundary (v : NamedPolygonPole ρ q u)
    (w : MonoidAlgebra ℤ (NamedPolygonDeckGroup ρ q u)) :
    Comb.bdry2 (strictOrderCx (NamedSurfaceCover ρ q u))
        (namedPolygonMultipleAt ρ q u v w) =
      Finsupp.linearCombination ℤ (fun g =>
        chain1 (strictOrderCxMap (namedSurfaceDeck ρ q u g) (namedSurfaceDeck ρ q u g).strictMono)
          (Comb.bdry2 (strictOrderCx (NamedSurfaceCover ρ q u)) (namedPolygonFillingAt ρ q u v))) w.coeff := by
  induction w using MonoidAlgebra.induction_linear with
  | zero => simp
  | add w z hw hz => simp_all
  | single g n =>
      let f := fun g => chain2
        (strictOrderCxMap (namedSurfaceDeck ρ q u g) (namedSurfaceDeck ρ q u g).strictMono)
        (namedPolygonFillingAt ρ q u v)
      have hm : namedPolygonMultipleAt ρ q u v (MonoidAlgebra.single g n) = n • f g := by
        exact Finsupp.linearCombination_single ℤ n g
      rw [hm, map_zsmul, bdry2_chain2]
      let h := fun g => chain1
        (strictOrderCxMap (namedSurfaceDeck ρ q u g) (namedSurfaceDeck ρ q u g).strictMono)
        (Comb.bdry2 (strictOrderCx (NamedSurfaceCover ρ q u)) (namedPolygonFillingAt ρ q u v))
      change n • h g = Finsupp.linearCombination ℤ h (Finsupp.single g n)
      exact (Finsupp.linearCombination_single ℤ n g).symm


/-- Polygon rigidity itself supplies the previously separate equality of
universal-cover marking chains, for the same full quotient-group scalar. -/
theorem namedPolygon_reconstruction_marking_multiple
    (hrho : ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q))
    (c d : Ch (namedAttachingCover q ρ u)) (hc : c ∈ Inc _) (hd : d ∈ Inc _)
    (hcdegree : lengthProjection 3 c = c) (hddegree : lengthProjection 3 d = d)
    (b e : (PresGroup (substPresF ρ (finiteSpineWordBlock q u)) × (Fin q × Bool)) →₀ ℤ)
    (hcb : Nerve.bdry c = namedAttachingNerveBoundary q ρ u hrho b)
    (hdb : Nerve.bdry d = namedAttachingNerveBoundary q ρ u hrho e)
    (v : NamedPolygonPole ρ q u)
    (hreference : namedAttachingNerveSurfaceChain ρ q u d = namedPolygonFillingAt ρ q u v)
    (hrelative : PolygonRelativeChain (gc q) (namedSurfaceProjection ρ q u)
      (namedAttachingNerveSurfaceChain ρ q u c)) :
    quotientSurfaceMarkingChains q ρ u hrho b =
      Finsupp.linearCombination ℤ (fun g => chain1
        ((univDeck (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).cellHom g)
          (quotientSurfaceMarkingChains q ρ u hrho e))
        (namedPolygonCoefficientAt ρ q u v (namedAttachingNerveSurfaceChain ρ q u c)).coeff := by
  let w := namedPolygonCoefficientAt ρ q u v (namedAttachingNerveSurfaceChain ρ q u c)
  have hp  :=
    namedPolygon_reconstruct_at_pole ρ q u v _ hrelative
  have hb := congrArg (Comb.bdry2 (strictOrderCx (NamedSurfaceCover ρ q u))) hp
  rw [namedAttachingNerveSurfaceChain_marked_boundary ρ q u hrho c hc hcdegree b hcb,
    namedPolygonMultipleAt_boundary, ← hreference,
    namedAttachingNerveSurfaceChain_marked_boundary ρ q u hrho d hd hddegree e hdb] at hb
  exact namedSurfaceMarking_multiple_reflect q ρ u hrho b e w hb

/-- The geometric principal-vector theorem with the marking comparison
derived from reconstruction, rather than supplied as a hypothesis. -/
theorem finiteSpine_polygon_reference_principal_of_geometry
    (hrho : ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q))
    (β γ : NamedSpineRel q → MonoidAlgebra ℤ
      (PresGroup (substPresF ρ (finiteSpineWordBlock q u))))
    (hβ : ∀ z : SpinePresentationGen q,
      (∑ m, β m * foxMatrixPres (substPresF ρ (finiteSpineWordBlock q u))
        (Sum.inr ⟨PUnit.unit, z⟩) (Sum.inr ⟨PUnit.unit, m⟩)) = 0)
    (hγ : ∀ z : SpinePresentationGen q,
      (∑ m, γ m * foxMatrixPres (substPresF ρ (finiteSpineWordBlock q u))
        (Sum.inr ⟨PUnit.unit, z⟩) (Sum.inr ⟨PUnit.unit, m⟩)) = 0)
    (c d : Ch (namedAttachingCover q ρ u))
    (hc : c ∈ Inc _) (hd : d ∈ Inc _)
    (hcdegree : lengthProjection 3 c = c) (hddegree : lengthProjection 3 d = d)
    (yC yD : Ch (UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u)))
    (hyC : yC ∈ IncOn (fun p => InQOld (uOrderEnd p)))
    (hyD : yD ∈ IncOn (fun p => InQOld (uOrderEnd p)))
    (hC : quotientCorrectedRelativeNerveChain q ρ u hrho β =
      cmap Subtype.val c + Nerve.bdry yC)
    (hD : quotientCorrectedRelativeNerveChain q ρ u hrho γ =
      cmap Subtype.val d + Nerve.bdry yD)
    (v : NamedPolygonPole ρ q u)
    (hreference : namedAttachingNerveSurfaceChain ρ q u d = namedPolygonFillingAt ρ q u v)
    (hrelative : PolygonRelativeChain (gc q) (namedSurfaceProjection ρ q u)
      (namedAttachingNerveSurfaceChain ρ q u c)) :
    ∃ a : MonoidAlgebra ℤ (PresGroup (substPresF ρ (finiteSpineWordBlock q u))),
      ∀ m, β m = a * γ m := by
  have hcb := namedAttaching_marked_boundary_of_relative_class ρ q u hrho β hβ c yC hC
  have hdb := namedAttaching_marked_boundary_of_relative_class ρ q u hrho γ hγ d yD hD
  have hmark := namedPolygon_reconstruction_marking_multiple ρ q u hrho c d hc hd
    hcdegree hddegree _ _ hcb hdb v hreference hrelative
  exact finiteSpine_polygon_reference_principal ρ q u hrho β γ hβ hγ
    c d hc hd hcdegree hddegree yC yD hyC hyD hC hD v hreference hrelative hmark

end FiniteChains.Davis.Genus

namespace FiniteChains.Comb
universe u
variable {P Q I : Type u} [PartialOrder P] [PartialOrder Q]

theorem normalizedWeakChain1To_paths_boundary_support
    (f : P → Q) (hf : Monotone f) (S : Q → Prop)
    (p : I → List (OrdEdge P × Bool))
    (hp : ∀ i a, a ∈ p i → S (f a.1.1.1) ∧ S (f a.1.1.2))
    (c : I →₀ ℤ) :
    ∀ e ∈ (normalizedWeakChain1To f hf (Finsupp.linearCombination ℤ
      (fun i => pathChain (p i)) c)).support, S e.1.1 ∧ S e.1.2 := by
  intro e he
  by_contra hnot
  have hz (i : I) : normalizedWeakChain1To f hf (pathChain (p i)) e = 0 := by
    apply normalizedWeakChain1To_path_apply_zero
    intro a ha heq
    apply hnot
    rw [← heq]
    exact hp i a ha
  have hzero : normalizedWeakChain1To f hf
      (Finsupp.linearCombination ℤ (fun i => pathChain (p i)) c) e = 0 := by
    clear he
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add c d hc hd => simp_all
    | single i n => simp_all
  simp_all

end FiniteChains.Comb

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily Nerve
variable (q : ℕ) [NeZero q]

/-- Every edge of the original marking has both last vertices on the
identified polygon boundary, including the flags that normalize to zero. -/
theorem gSig_lastEndpoints_boundary (i : Fin q × Bool)
    (a : MarkingSurfaceEdge q × Bool) (ha : a ∈ gSig q (i.1.val, i.2)) :
    InPolygonBoundary (gc q) (chainMax a.1.1.1) ∧
      InPolygonBoundary (gc q) (chainMax a.1.1.2) := by
  rw [gSig_first_edge] at ha
  simp only [markingTail, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [markingFirstEdge, markingBaseFlag, markingBedBaseFlag, markingBedMidFlag,
      markingMidFlag, markingBaseCell, markingMidCell, markingBedCell, InPolygonBoundary]

variable {α Jr : Type} (ρ : Jr ⊕ PUnit.{1} → FreeGroup α)
  (u : Fin q × Bool → FreeGroup α)
  (hrho : ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q))


theorem namedSurfaceMarkingChains_boundary_support
    (b : (PresGroup (substPresF ρ (finiteSpineWordBlock q u)) × (Fin q × Bool)) →₀ ℤ) :
    ∀ e ∈ (normalizedWeakChain1To (namedSurfaceForward q ρ u)
        (namedSurfaceForward_monotone q ρ u) (namedAttachingMarkingChains q ρ u hrho b)).support,
      InPolygonBoundary (gc q) (namedSurfaceProjection ρ q u e.1.1) ∧
        InPolygonBoundary (gc q) (namedSurfaceProjection ρ q u e.1.2) := by
  exact normalizedWeakChain1To_paths_boundary_support
    (namedSurfaceForward q ρ u) (namedSurfaceForward_monotone q ρ u)
    (fun p : NamedSurfaceCover ρ q u =>
      InPolygonBoundary (gc q) (namedSurfaceProjection ρ q u p))
    (fun x : PresGroup (substPresF ρ (finiteSpineWordBlock q u)) × (Fin q × Bool) =>
      namedAttachingMarkingPath q ρ u hrho x.1 x.2)
    (fun x a ha => (by
      have hm : ((namedAttachingProjection q ρ u).onE a.1, a.2) ∈ gSig q ((x.2).1.val, (x.2).2) := by
        rw [← (namedAttachingMarkingPath_spec q ρ u hrho (x.1) (x.2)).2]
        exact List.mem_map.mpr ⟨a, ha, rfl⟩
      exact gSig_lastEndpoints_boundary q (x.2) _ hm)) b

/-- The relative condition follows from the actual marking boundary; it is
not an additional geometric assumption on the arbitrary B2 input chain. -/
theorem namedAttachingNerveSurfaceChain_polygonRelative
    (c : Ch (namedAttachingCover q ρ u)) (hc : c ∈ Inc _)
    (hd : lengthProjection 3 c = c)
    (b : (PresGroup (substPresF ρ (finiteSpineWordBlock q u)) × (Fin q × Bool)) →₀ ℤ)
    (hb : Nerve.bdry c = namedAttachingNerveBoundary q ρ u hrho b) :
    PolygonRelativeChain (gc q) (namedSurfaceProjection ρ q u)
      (namedAttachingNerveSurfaceChain ρ q u c) := by
  intro e he
  rw [namedAttachingNerveSurfaceChain_marked_boundary ρ q u hrho c hc hd b hb] at he
  change e ∈ (normalizedChain1To (namedSurfaceForward q ρ u) (namedSurfaceForward_monotone q ρ u)
    (normalizeOrdChain1 (namedAttachingMarkingChains q ρ u hrho b))).support at he
  rw [← normalizedWeakChain1To_normalize] at he
  exact namedSurfaceMarkingChains_boundary_support q ρ u hrho b e he

/-- Once the actual geometric reference is fixed, the only assumptions on
an arbitrary coefficient vector are the original internal B2 equations.
Its attaching filling and old correction are provided by the proved cover
filling theorem, and polygon relativity is derived from its marked boundary. -/
theorem finiteSpine_polygon_reference_generates
    (γ : NamedSpineRel q → MonoidAlgebra ℤ
      (PresGroup (substPresF ρ (finiteSpineWordBlock q u))))
    (hγ : ∀ z : SpinePresentationGen q,
      (∑ m, γ m * foxMatrixPres (substPresF ρ (finiteSpineWordBlock q u))
        (Sum.inr ⟨PUnit.unit, z⟩) (Sum.inr ⟨PUnit.unit, m⟩)) = 0)
    (d : Ch (namedAttachingCover q ρ u)) (hd : d ∈ Inc _)
    (hddegree : lengthProjection 3 d = d)
    (yD : Ch (UOrder (namedQuotientPos ρ q u) (namedQuotientBase ρ q u)))
    (hyD : yD ∈ IncOn (fun p => InQOld (uOrderEnd p)))
    (hD : quotientCorrectedRelativeNerveChain q ρ u hrho γ =
      cmap Subtype.val d + Nerve.bdry yD)
    (v : NamedPolygonPole ρ q u)
    (hreference : namedAttachingNerveSurfaceChain ρ q u d = namedPolygonFillingAt ρ q u v) :
    ∀ (β : NamedSpineRel q → MonoidAlgebra ℤ
        (PresGroup (substPresF ρ (finiteSpineWordBlock q u)))),
      (∀ z : SpinePresentationGen q,
        (∑ m, β m * foxMatrixPres (substPresF ρ (finiteSpineWordBlock q u))
          (Sum.inr ⟨PUnit.unit, z⟩) (Sum.inr ⟨PUnit.unit, m⟩)) = 0) →
      ∃ a : MonoidAlgebra ℤ (PresGroup (substPresF ρ (finiteSpineWordBlock q u))),
        ∀ m, β m = a * γ m := by
  intro β hβ
  obtain ⟨c, hc, hcdegree, hcb, yC, hyC, _hyCdegree, hC⟩ :=
    quotientCorrectedRelative_attaching_filling q ρ u hrho β hβ
  have hrelative := namedAttachingNerveSurfaceChain_polygonRelative q ρ u hrho
    c hc hcdegree _ hcb
  exact finiteSpine_polygon_reference_principal_of_geometry ρ q u hrho β γ hβ hγ
    c d hc hd hcdegree hddegree yC yD hyC hyD hC hD v hreference hrelative

end FiniteChains.Davis.Genus
end

section
open scoped Classical
namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily Nerve

variable {α Jr : Type} (ρ : Jr ⊕ PUnit.{1} → FreeGroup α)
  (q : ℕ) [NeZero q] (u : Fin q × Bool → FreeGroup α)
  (hrho : ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q))

include hrho in
/-- Actual single-block B2. The only premise on the arbitrary vector is
the original internal Fox-boundary equation, over the original substituted
group ring. No receiver, degree, comparison, or reference assumption remains. -/
theorem finiteSpineActualB2
    (β : NamedSpineRel q → MonoidAlgebra ℤ
      (PresGroup (substPresF ρ (finiteSpineWordBlock q u))))
    (hβ : ∀ z : SpinePresentationGen q,
      (∑ m, β m * foxMatrixPres (substPresF ρ (finiteSpineWordBlock q u))
        (Sum.inr ⟨PUnit.unit, z⟩) (Sum.inr ⟨PUnit.unit, m⟩)) = 0) :
    ∃ a : MonoidAlgebra ℤ (PresGroup (substPresF ρ (finiteSpineWordBlock q u))),
      ∀ m, β m = a * singleFiniteSpineReference ρ q u m := by
  obtain ⟨y, hy, hreference⟩ := singleFiniteSpineReference_corrected_geometry ρ q u hrho
  exact finiteSpine_polygon_reference_generates q ρ u hrho
    (singleFiniteSpineReference ρ q u) (singleFiniteSpineReference_internal ρ q u hrho)
    (transportedUniversalPolygonAttachingChain ρ q u)
    (transportedUniversalPolygonAttachingChain_mem_inc ρ q u)
    (transportedUniversalPolygonAttachingChain_degree ρ q u)
    y hy hreference (transportedUniversalPolygonPole ρ q u)
    (transportedUniversalPolygonAttachingChain_normalized ρ q u) β hβ

variable {S : Type} (σ : Jr ⊕ S → FreeGroup α)
  (qs : S → ℕ) [∀ s, NeZero (qs s)]
  (us : ∀ s, Fin (qs s) × Bool → FreeGroup α)
  (hσ : ∀ s, σ (Sum.inr s) = commWord (us s) (finitePairs (qs s)))

include hσ in
/-- The concrete individual input required by the already constructed
arbitrary-family base-change theorem, now with every geometric input proved. -/
theorem finiteSpineIndividualB2_actual : FiniteSpineIndividualB2 σ qs us := by
  intro s β hβ
  have h := finiteSpineActualB2 (oneRel σ s) (qs s) (us s) (hσ s) β hβ
  simp only [singleFiniteSpineReference_oneRel] at h
  convert h using 1 <;> rfl

/-- Actual finite-support cycle generation for simultaneous substitution.
The former individual-B2 assumption is discharged by the genus geometry. -/
theorem finiteSpineFamily_fsGenerates_actual
    (x : (Jr ⊕ (Σ s, NamedSpineRel (qs s))) →₀
      MonoidAlgebra ℤ (PresGroup (substPresF σ (familyFiniteSpineWordBlock qs us))))
    (hx : coverSecondBoundary (relSub (substPresF σ (familyFiniteSpineWordBlock qs us)))
      (substPresF σ (familyFiniteSpineWordBlock qs us)) x = 0) :
    x ∈ Submodule.span
      (MonoidAlgebra ℤ (PresGroup (substPresF σ (familyFiniteSpineWordBlock qs us))))
      {v | ∃ y : (Jr ⊕ S) →₀ MonoidAlgebra ℤ (PresGroup σ),
        coverSecondBoundary (relSub σ) σ y = 0 ∧
        v = fsCellsF σ (familyFiniteSpineWordBlock qs us)
          (familyFiniteSpineWordBlock_filled σ qs us hσ)
          (finiteSpineFamilyFilling σ qs us) y} :=
  finiteSpineFamily_fsGenerates σ qs us hσ (finiteSpineIndividualB2_actual σ qs us hσ) x hx

end FiniteChains.Davis.Genus

namespace FiniteChains.BlockFamily

universe u

variable {α Jr S : Type u} {Z M : S → Type u}
  [DecidableEq α] [DecidableEq S] [∀ s, DecidableEq (Z s)]
  (ρ : Jr ⊕ S → FreeGroup α) (b : ∀ s, M s → FreeGroup (α ⊕ Z s))
  (hfill : FilledF ρ b)
  (c : ∀ s, M s →₀ MonoidAlgebra ℤ (PresGroup (substPresF ρ b)))

/-- The finite-support structural map of an arbitrary simultaneous block
replacement, with exactly the original coefficient map and surface fillings. -/
def substMorFS (hc : IsFillingFS ρ b hfill c) : PresMorFS ρ (substPresF ρ b) where
  hom := substHomF ρ b hfill
  cells := fsCellsF ρ b hfill c
  cells_add := by
    intro y z
    ext k : 1
    exact congrFun (cellsF_add ρ b hfill (fun s => c s) y z) k
  cells_smul := by
    intro a y
    ext k : 1
    exact congrFun (cellsF_smul ρ b hfill (fun s => c s) a y) k
  cells_cycle := by
    intro y hy
    change coverSecondBoundary _ _ (fsCellsF ρ b hfill c y) = 0
    rw [fsCellsF_boundary ρ b hfill c hc y, hy]
    simp
  cells_aug := by
    intro y hy k
    change augPres (substPresF ρ b) (cellsF ρ b hfill (fun s => c s) y k) = 0
    exact augPres_cellsF_eq_zero hy k

/-- The structural map preserves the retained two-cells exactly, including
their actual coefficients in the new group ring. -/
theorem substMorFS_retained (hc : IsFillingFS ρ b hfill c)
    (j : Jr) (a : MonoidAlgebra ℤ (PresGroup ρ)) :
    (substMorFS ρ b hfill c hc).cells (Finsupp.single (Sum.inl j) a) =
      Finsupp.single (Sum.inl j) (coeffF ρ b hfill a) := by
  ext k : 1
  cases k with
  | inl k =>
      change coeffF ρ b hfill (Finsupp.single (Sum.inl j) a (Sum.inl k)) = _
      by_cases h : k = j
      · simp_all
      · simp_all
  | inr p =>
      change coeffF ρ b hfill (Finsupp.single (Sum.inl j) a (Sum.inr p.1)) *
        c p.1 p.2 = _
      simp

end FiniteChains.BlockFamily

namespace FiniteChains.Davis.Genus

open BlockFamily

variable {α Jr S : Type} (σ : Jr ⊕ S → FreeGroup α)
  (q : S → ℕ) [∀ s, NeZero (q s)]
  (u : ∀ s, Fin (q s) × Bool → FreeGroup α)
  (hσ : ∀ s, σ (Sum.inr s) = commWord (u s) (finitePairs (q s)))

/-- Rule 3 with all its geometric inputs supplied, including for an
infinite family over an infinite fixed core. -/
def finiteSpineFamilyStructuralMap :
    PresMorFS σ (substPresF σ (familyFiniteSpineWordBlock q u)) :=
  substMorFS σ (familyFiniteSpineWordBlock q u)
    (familyFiniteSpineWordBlock_filled σ q u hσ)
    (finiteSpineFamilyFilling σ q u)
    (finiteSpineFamilyFilling_isFilling σ q u hσ)

@[simp] theorem finiteSpineFamilyStructuralMap_cells
    (y : (Jr ⊕ S) →₀ MonoidAlgebra ℤ (PresGroup σ)) :
    (finiteSpineFamilyStructuralMap σ q u hσ).cells y =
      fsCellsF σ (familyFiniteSpineWordBlock q u)
        (familyFiniteSpineWordBlock_filled σ q u hσ)
        (finiteSpineFamilyFilling σ q u) y := rfl

/-- Actual equation (3.3) for the simultaneous genus replacement. -/
theorem finiteSpineFamilyStructuralMap_generates :
    FSGenerates (finiteSpineFamilyStructuralMap σ q u hσ) := by
  intro y hy
  exact finiteSpineFamily_fsGenerates_actual σ q u hσ y hy

/-- On a retained core two-cell the structural map is literally the
labelled inclusion with its induced change of group-ring coefficients. -/
theorem finiteSpineFamilyStructuralMap_core_cell
    (j : Jr) (a : MonoidAlgebra ℤ (PresGroup σ)) :
    (finiteSpineFamilyStructuralMap σ q u hσ).cells
        (Finsupp.single (Sum.inl j) a) =
      Finsupp.single (Sum.inl j)
        (MonoidAlgebra.mapDomainRingHom ℤ
          (finiteSpineFamilyStructuralMap σ q u hσ).hom a) :=
  substMorFS_retained σ (familyFiniteSpineWordBlock q u)
    (familyFiniteSpineWordBlock_filled σ q u hσ)
    (finiteSpineFamilyFilling σ q u)
    (finiteSpineFamilyFilling_isFilling σ q u hσ) j a



end FiniteChains.Davis.Genus
end

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped commutatorElement
namespace FiniteChains

variable {α : Type*} [DecidableEq α]

/-- The total exponent-sum homomorphism of a free group. -/
def expSumTotal : FreeGroup α →* Multiplicative (α →₀ ℤ) :=
  FreeGroup.lift fun k => Multiplicative.ofAdd (Finsupp.single k (1 : ℤ))

theorem expSumTotal_apply (w : FreeGroup α) (i : α) :
    Multiplicative.toAdd (expSumTotal w) i = Multiplicative.toAdd (expSum i w) := by
  induction w using FreeGroup.induction_on with
  | one => rfl
  | of k =>
      simp [expSumTotal, expSum, FreeGroup.lift_apply_of, Finsupp.single_apply, eq_comm]
  | inv_of k h => simp_all
  | mul u v hu hv => simp_all

/-- A word with vanishing exponent sums lies in the commutator subgroup. -/
theorem mem_commutator_of_expSum_eq_zero (w : FreeGroup α)
    (h : ∀ i : α, Multiplicative.toAdd (expSum i w) = 0) :
    w ∈ commutator (FreeGroup α) := by
  have hw : expSumTotal w = 1 := by
    have h0 : Multiplicative.toAdd (expSumTotal w) = 0 := by
      ext i
      rw [expSumTotal_apply]
      simpa using h i
    simpa using h0
  -- the retraction of the abelianization onto the free abelian group on the generators
  set psi : Multiplicative (α →₀ ℤ) →* Abelianization (FreeGroup α) :=
    MonoidHom.mk' (fun x => Additive.toMul
        (Finsupp.liftAddHom
          (fun k => (zmultiplesHom (Additive (Abelianization (FreeGroup α))))
            (Additive.ofMul (Abelianization.of (FreeGroup.of k))))
          (Multiplicative.toAdd x)))
      (fun x y => by simp [map_add]) with hpsi
  set phi : Abelianization (FreeGroup α) →* Multiplicative (α →₀ ℤ) :=
    Abelianization.lift expSumTotal with hphi
  have hcomp : psi.comp phi = MonoidHom.id (Abelianization (FreeGroup α)) := by
    refine Abelianization.hom_ext _ _ (FreeGroup.ext_hom _ _ fun k => ?_)
    simp [hpsi, hphi, expSumTotal, FreeGroup.lift_apply_of]
  have hof : Abelianization.of w = 1 := by
    have h1 : phi (Abelianization.of w) = 1 := by simp [hphi, hw]
    calc Abelianization.of w
        = psi (phi (Abelianization.of w)) := by
          rw [← MonoidHom.comp_apply, hcomp, MonoidHom.id_apply]
      _ = 1 := by rw [h1, map_one]
  rwa [show Abelianization.of w = QuotientGroup.mk' (commutator (FreeGroup α)) w from rfl,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hof

/-- **Rule 3 of Section 3.4.**  A word with vanishing exponent sums in every generator is a
product of `q ≥ 2` commutators, as required before substituting a block `B_q`. -/
theorem exists_commutator_factorization (w : FreeGroup α)
    (h : ∀ i : α, Multiplicative.toAdd (expSum i w) = 0) :
    ∃ (q : ℕ) (u v : Fin q → FreeGroup α), 2 ≤ q ∧
      w = (List.ofFn fun j : Fin q => ⁅u j, v j⁆).prod := by
  have hw  := mem_commutator_of_expSum_eq_zero w h
  have hsub : w ∈ Submonoid.closure (commutatorSet (FreeGroup α)) := by
    have h1 : w ∈ Submonoid.closure
        (commutatorSet (FreeGroup α) ∪ (commutatorSet (FreeGroup α))⁻¹) := by
      rw [← Subgroup.closure_toSubmonoid]
      rwa [commutator_eq_closure] at hw
    have h2 : (commutatorSet (FreeGroup α) ∪ (commutatorSet (FreeGroup α))⁻¹)
        = commutatorSet (FreeGroup α) := by
      ext x
      constructor
      · rintro (hx | hx)
        · exact hx
        · obtain ⟨a, b, hab⟩ := hx
          exact ⟨b, a, by rw [← commutatorElement_inv, hab, inv_inv]⟩
      · exact fun hx => Or.inl hx
    rwa [h2] at h1
  obtain ⟨l, hl, hlp⟩ := Submonoid.exists_list_of_mem_closure hsub
  -- pad with two trivial commutators so that `q ≥ 2`
  set l' : List (FreeGroup α) := l ++ [1, 1] with hl'
  have hmem : ∀ x ∈ l', ∃ ab : FreeGroup α × FreeGroup α, x = ⁅ab.1, ab.2⁆ := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨a, b, hab⟩ := hl x hx
      exact ⟨(a, b), hab.symm⟩
    · have : x = 1 := by
        rcases List.mem_cons.mp hx with h1 | h1
        · exact h1
        · rcases List.mem_cons.mp h1 with h2 | h2
          · exact h2
          · exact absurd h2 (List.not_mem_nil)
      exact ⟨(1, 1), by simp [this]⟩
  choose ab hab using hmem
  refine ⟨l'.length, fun j => (ab l'[j] (List.getElem_mem j.2)).1,
    fun j => (ab l'[j] (List.getElem_mem j.2)).2, ?_, ?_⟩
  · simp [hl']
  · have hofn : (List.ofFn fun j : Fin l'.length =>
        ⁅(ab l'[j] (List.getElem_mem j.2)).1,
          (ab l'[j] (List.getElem_mem j.2)).2⁆) = l' := by
      rw [show (fun j : Fin l'.length =>
          ⁅(ab l'[j] (List.getElem_mem j.2)).1,
            (ab l'[j] (List.getElem_mem j.2)).2⁆)
          = fun j => l'[j] from
        funext fun j => (hab _ (List.getElem_mem j.2)).symm]
      exact List.ofFn_getElem
    rw [hofn, hl', List.prod_append, hlp]
    simp

end FiniteChains
end

section
open scoped commutatorElement
namespace FiniteChains

open Finsupp

variable {α J : Type*} [DecidableEq α]

/-- The exponent vector of a word: its exponent sum in every generator. -/
def expVec (w : FreeGroup α) : α →₀ ℤ :=
  Multiplicative.toAdd (expSumTotal w)

@[simp] theorem expVec_apply (w : FreeGroup α) (i : α) :
    expVec w i = Multiplicative.toAdd (expSum i w) := by
  rw [expVec, expSumTotal_apply]

omit [DecidableEq α] in
theorem expVec_mul (w w' : FreeGroup α) : expVec (w * w') = expVec w + expVec w' := by
  simp [expVec, map_mul]

omit [DecidableEq α] in
theorem expVec_zpow (w : FreeGroup α) (n : ℤ) : expVec (w ^ n) = n • expVec w := by
  simp [expVec, map_zpow]

/-- **The exponent-sum map `M` of the core presentation** (formula (3.1) of the paper):
a coefficient vector `c` is sent to `∑_j c_j · (exponent vector of r_j)`. -/
def expMatrix (r : J → FreeGroup α) : (J →₀ ℤ) →ₗ[ℤ] (α →₀ ℤ) :=
  Finsupp.linearCombination ℤ fun j => expVec (r j)

omit [DecidableEq α] in
theorem expMatrix_apply (r : J → FreeGroup α) (c : J →₀ ℤ) :
    expMatrix r c = c.sum fun j n => n • expVec (r j) :=
  Finsupp.linearCombination_apply _ _

/-- The correcting word `∏_j r_j^{c_j}`, taken in a fixed order. -/
def correctionWord (r : J → FreeGroup α) (c : J →₀ ℤ) : FreeGroup α :=
  (c.support.toList.map fun j => r j ^ c j).prod

omit [DecidableEq α] in
theorem expVec_list_prod (L : List (FreeGroup α)) :
    expVec L.prod = (L.map expVec).sum := by
  induction L with
  | nil => rfl
  | cons a t ih => simp [expVec_mul, ih]


omit [DecidableEq α] in
/-- **Rule 2.**  If the exponent-sum map of the core relators is surjective — which is the
case for an acyclic core, where it is even bijective — then every word can be corrected by
a product of core relators so that all its exponent sums vanish. -/
theorem exists_correction (r : J → FreeGroup α) (w : FreeGroup α)
    (hM : Function.Surjective (expMatrix r)) :
    ∃ c : J →₀ ℤ, expVec (w * correctionWord r c) = 0 := by
  obtain ⟨c, hc⟩ := hM (-expVec w)
  exact ⟨c, by rw [expVec_mul, (show expVec (correctionWord r c) = expMatrix r c by
    rw [correctionWord, expVec_list_prod, List.map_map, expMatrix_apply, Finsupp.sum]
    have : ((expVec ∘ fun j => r j ^ c j) = fun j => c j • expVec (r j)) := by
      funext j
      simp [Function.comp, expVec_zpow]
    simp_all), hc, add_neg_cancel]⟩

end FiniteChains
end

section
open scoped Classical commutatorElement
namespace FiniteChains

universe v
variable {A J B K : Type v} [dA : DecidableEq A] [dB : DecidableEq B]
  {ρ : J → FreeGroup A} {τ : K → FreeGroup B}

/-- Changing the equality decision procedures preserves the actual group and cell maps. -/
def PresMorFS.redecide (f : PresMorFS ρ τ) (dA' : DecidableEq A) (dB' : DecidableEq B) :
    @PresMorFS A J B K dA' dB' ρ τ where
  hom := @PresMorFS.hom A J B K dA dB ρ τ f
  cells := @PresMorFS.cells A J B K dA dB ρ τ f
  cells_add := @PresMorFS.cells_add A J B K dA dB ρ τ f
  cells_smul := @PresMorFS.cells_smul A J B K dA dB ρ τ f
  cells_cycle := by
    have hA : dA' = dA := Subsingleton.elim _ _
    have hB : dB' = dB := Subsingleton.elim _ _
    subst dA'
    subst dB'
    exact f.cells_cycle
  cells_aug := @PresMorFS.cells_aug A J B K dA dB ρ τ f

theorem FSGenerates.redecide {f : PresMorFS ρ τ} (hf : FSGenerates f)
    (dA' : DecidableEq A) (dB' : DecidableEq B) :
    @FSGenerates A J B K dA' dB' ρ τ
      (@PresMorFS.redecide A J B K dA dB ρ τ f dA' dB') := by
  have hA : dA' = dA := Subsingleton.elim _ _
  have hB : dB' = dB := Subsingleton.elim _ _
  subst dA'
  subst dB'
  exact hf

end FiniteChains

namespace FiniteChains.RelativeNormalForm

open Davis Davis.Genus BlockFamily

variable {A C Z S : Type}

/-- All positive stages use these shared ambient pairs. -/
abbrev PairGen (A Z : Type) := A ⊕ (Z × Bool)

def forgetExtra : FreeGroup (A ⊕ Z) →* FreeGroup A :=
  FreeGroup.lift (Sum.elim FreeGroup.of (fun _ => 1))

def pairSubstitution : FreeGroup (A ⊕ Z) →* FreeGroup (PairGen A Z) :=
  FreeGroup.lift (Sum.elim (fun a => FreeGroup.of (Sum.inl a))
    (fun z => ⁅FreeGroup.of (Sum.inr (α := A) (z, false)),
      FreeGroup.of (Sum.inr (α := A) (z, true))⁆))

@[simp] theorem forgetExtra_core (a : A) :
    forgetExtra (FreeGroup.of (Sum.inl (β := Z) a)) = FreeGroup.of a := rfl

@[simp] theorem forgetExtra_extra (z : Z) :
    forgetExtra (FreeGroup.of (Sum.inr (α := A) z)) = 1 := rfl

@[simp] theorem pairSubstitution_core (a : A) :
    pairSubstitution (FreeGroup.of (Sum.inl (β := Z) a)) =
      FreeGroup.of (Sum.inl a) := rfl

@[simp] theorem pairSubstitution_extra (z : Z) :
    pairSubstitution (FreeGroup.of (Sum.inr (α := A) z)) =
      ⁅FreeGroup.of (Sum.inr (α := A) (z, false)),
        FreeGroup.of (Sum.inr (α := A) (z, true))⁆ := rfl

@[simp] theorem forgetExtra_map_core (w : FreeGroup A) :
    forgetExtra (FreeGroup.map (Sum.inl (β := Z)) w) = w := by
  have h : (forgetExtra (Z := Z)).comp (FreeGroup.map Sum.inl) =
      MonoidHom.id (FreeGroup A) := by
    apply FreeGroup.ext_hom
    intro a
    simp
  exact congrArg (fun f : FreeGroup A →* FreeGroup A => f w) h

@[simp] theorem pairSubstitution_map_core (w : FreeGroup A) :
    pairSubstitution (FreeGroup.map (Sum.inl (β := Z)) w) =
      FreeGroup.map (Sum.inl (β := Z × Bool)) w := by
  have h : (pairSubstitution (A := A)).comp (FreeGroup.map Sum.inl) =
      FreeGroup.map (Sum.inl (β := Z × Bool)) := by
    apply FreeGroup.ext_hom
    intro a
    simp
  exact congrArg (fun f : FreeGroup A →* FreeGroup (PairGen A Z) => f w) h

/-- Rule 1 leaves the core exponent sums unchanged and annihilates every
extra exponent sum. -/
theorem pairSubstitution_exp_core (w : FreeGroup (A ⊕ Z)) (a : A) :
    expSum (Sum.inl a) (pairSubstitution w) = expSum a (forgetExtra w) := by
  have h : (expSum (Sum.inl (β := Z × Bool) a)).comp pairSubstitution =
      (expSum a).comp forgetExtra := by
    apply FreeGroup.ext_hom
    intro x
    cases x with
    | inl x => simp [expSum]
    | inr z => rfl
  exact congrArg (fun f : FreeGroup (A ⊕ Z) →* Multiplicative ℤ => f w) h

theorem pairSubstitution_exp_pair (w : FreeGroup (A ⊕ Z)) (z : Z × Bool) :
    expSum (Sum.inr z) (pairSubstitution w) = 1 := by
  have h : (expSum (Sum.inr z)).comp pairSubstitution =
      (1 : FreeGroup (A ⊕ Z) →* Multiplicative ℤ) := by
    apply FreeGroup.ext_hom
    intro x
    cases x with
    | inl x => rfl
    | inr x =>
        simp
        exact commutatorElement_eq_one_iff_commute.mpr (Commute.all _ _)
  exact congrArg (fun f : FreeGroup (A ⊕ Z) →* Multiplicative ℤ => f w) h

variable (core : C → FreeGroup A)
  (hcore : Function.Surjective (expMatrix core))

/-- The correction is a finite core chain, chosen once for its ambient word. -/
def correctionCoefficients (w : FreeGroup (A ⊕ Z)) : C →₀ ℤ :=
  Classical.choose (exists_correction core (forgetExtra w) hcore)

theorem correctionCoefficients_spec (w : FreeGroup (A ⊕ Z)) :
    expVec (forgetExtra w * correctionWord core (correctionCoefficients core hcore w)) = 0 :=
  Classical.choose_spec (exists_correction core (forgetExtra w) hcore)

/-- Rule 2 is a product with actual retained core relators. -/
def correctedWord (w : FreeGroup (A ⊕ Z)) : FreeGroup (A ⊕ Z) :=
  w * FreeGroup.map Sum.inl (correctionWord core (correctionCoefficients core hcore w))

/-- The result of simultaneous rules 1 and 2, before genus replacement. -/
def normalizedWord (w : FreeGroup (A ⊕ Z)) : FreeGroup (PairGen A Z) :=
  pairSubstitution (correctedWord core hcore w)

theorem normalizedWord_eq (w : FreeGroup (A ⊕ Z)) :
    normalizedWord core hcore w = pairSubstitution w *
      FreeGroup.map Sum.inl (correctionWord core (correctionCoefficients core hcore w)) := by
  simp only [normalizedWord, correctedWord, map_mul, pairSubstitution_map_core]

theorem normalizedWord_exp_zero (w : FreeGroup (A ⊕ Z)) (i : PairGen A Z) :
    Multiplicative.toAdd (expSum i (normalizedWord core hcore w)) = 0 := by
  cases i with
  | inl a =>
      rw [normalizedWord, pairSubstitution_exp_core]
      have h := congrArg (fun v : A →₀ ℤ => v a) (correctionCoefficients_spec core hcore w)
      simpa only [expVec_apply, correctedWord, map_mul, forgetExtra_map_core,
        Finsupp.zero_apply] using h
  | inr z =>
      rw [normalizedWord, pairSubstitution_exp_pair]
      rfl

/-- Surface data is constructed from the normalized word; it is not a
hypothesis on the relative presentation. -/
structure SurfaceChoice (w : FreeGroup (PairGen A Z)) where
  genus : ℕ
  genus_ge_two : 2 ≤ genus
  loops : Fin genus × Bool → FreeGroup (PairGen A Z)
  word : w = commWord loops (finitePairs genus)


def surfaceChoice (w : FreeGroup (A ⊕ Z)) : SurfaceChoice (normalizedWord core hcore w) :=
  Classical.choice (by
    obtain ⟨q, a, b, hq, hword⟩ := exists_commutator_factorization
      (normalizedWord core hcore w) (normalizedWord_exp_zero core hcore w)
    refine ⟨⟨q, hq, (fun x => if x.2 then b x.1 else a x.1), ?_⟩⟩
    rw [hword]
    simp only [commWord, finitePairs, List.map_map, List.ofFn_eq_map,
      commutatorElement_def]
    rfl)

variable (extra : S → FreeGroup (A ⊕ Z))

def normalizedGenus (s : S) : ℕ := (surfaceChoice core hcore (extra s)).genus

instance normalizedGenus_neZero (s : S) : NeZero (normalizedGenus core hcore extra s) :=
  ⟨by have h := (surfaceChoice core hcore (extra s)).genus_ge_two
      change (surfaceChoice core hcore (extra s)).genus ≠ 0
      omega⟩

def normalizedLoops (s : S) :
    Fin (normalizedGenus core hcore extra s) × Bool → FreeGroup (PairGen A Z) :=
  (surfaceChoice core hcore (extra s)).loops

def beforeCorrection : C ⊕ S → FreeGroup (PairGen A Z) :=
  Sum.elim (fun c => FreeGroup.map Sum.inl (core c))
    (fun s => pairSubstitution (extra s))

def normalizedPresentation : C ⊕ S → FreeGroup (PairGen A Z) :=
  Sum.elim (fun c => FreeGroup.map Sum.inl (core c))
    (fun s => normalizedWord core hcore (extra s))

theorem normalizedPresentation_surface (s : S) :
    normalizedPresentation core hcore extra (Sum.inr s) =
      commWord (normalizedLoops core hcore extra s)
        (finitePairs (normalizedGenus core hcore extra s)) :=
  (surfaceChoice core hcore (extra s)).word

/-- Every correction belongs to the normal subgroup of retained core
relators, for arbitrary cardinalities of the core and the extra family. -/
theorem coreCorrection_mem (N : Subgroup (FreeGroup (PairGen A Z)))
    (hN : ∀ c, FreeGroup.map (Sum.inl (β := Z × Bool)) (core c) ∈ N)
    (v : C →₀ ℤ) :
    FreeGroup.map (Sum.inl (β := Z × Bool)) (correctionWord core v) ∈ N := by
  rw [correctionWord, map_list_prod, List.map_map]
  refine Subgroup.list_prod_mem _ ?_
  intro x hx
  obtain ⟨c, _, rfl⟩ := List.mem_map.mp hx
  simp
  exact N.zpow_mem (hN c) (v c)

/-- Simultaneous rule 2 does not change the presented group. No ordering
or enumeration of the entire (possibly infinite) extra family is used. -/
theorem relSub_normalizedPresentation :
    relSub (normalizedPresentation core hcore extra) =
      relSub (beforeCorrection core extra) := by
  apply le_antisymm
  · refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨c | s, rfl⟩
    · exact Subgroup.subset_normalClosure ⟨Sum.inl c, rfl⟩
    · change normalizedWord core hcore (extra s) ∈ _
      rw [normalizedWord_eq]
      exact Subgroup.mul_mem _
        (Subgroup.subset_normalClosure ⟨Sum.inr s, rfl⟩)
        (coreCorrection_mem core (relSub (beforeCorrection core extra)) (fun c =>
          Subgroup.subset_normalClosure ⟨Sum.inl c, rfl⟩) _)
  · refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨c | s, rfl⟩
    · exact Subgroup.subset_normalClosure ⟨Sum.inl c, rfl⟩
    · have hw : normalizedWord core hcore (extra s) ∈
          relSub (normalizedPresentation core hcore extra) :=
          Subgroup.subset_normalClosure ⟨Sum.inr s, rfl⟩
      have hc := coreCorrection_mem core
        (relSub (normalizedPresentation core hcore extra))
        (fun c => Subgroup.subset_normalClosure ⟨Sum.inl c, rfl⟩)
        (correctionCoefficients core hcore (extra s))
      rw [normalizedWord_eq] at hw
      exact (Subgroup.mul_mem_cancel_right _ hc).mp hw

/-- The final actual genus replacement of the normalized relative presentation. -/
def blockPresentation :
    C ⊕ (Σ s, NamedSpineRel (normalizedGenus core hcore extra s)) →
      FreeGroup (PairGen A Z ⊕ (Σ s, SpinePresentationGen
        (normalizedGenus core hcore extra s))) :=
  substPresF (normalizedPresentation core hcore extra)
    (familyFiniteSpineWordBlock (normalizedGenus core hcore extra)
      (normalizedLoops core hcore extra))

/-- The input word equality for the actual B1/B2 construction has been
derived from acyclicity of the core, not assumed of the extra relators. -/
def blockStructuralMap : PresMorFS (normalizedPresentation core hcore extra)
    (blockPresentation core hcore extra) := by
  let dSrc : DecidableEq (PairGen A Z) := inferInstance
  let dTgt : DecidableEq (PairGen A Z ⊕ (Σ s, SpinePresentationGen
      (normalizedGenus core hcore extra s))) := inferInstance
  letI : DecidableEq (PairGen A Z) := Classical.decEq _
  let dFamilyTgt : DecidableEq (PairGen A Z ⊕ (Σ s, SpinePresentationGen
      (normalizedGenus core hcore extra s))) :=
    @instDecidableEqSum _ _ (Classical.decEq _) inferInstance
  exact @PresMorFS.redecide _ _ _ _ (Classical.decEq _) dFamilyTgt _ _
    (finiteSpineFamilyStructuralMap (normalizedPresentation core hcore extra)
    (normalizedGenus core hcore extra) (normalizedLoops core hcore extra)
    (normalizedPresentation_surface core hcore extra)) dSrc dTgt

end FiniteChains.RelativeNormalForm
end

section
open scoped Classical
namespace FiniteChains.RelativeNormalForm

open Davis Davis.Genus BlockFamily

variable {A C Z S : Type} (core : C → FreeGroup A)
  (hcore : Function.Surjective (expMatrix core))
  (extra : S → FreeGroup (A ⊕ Z))

def restrictedPresentation (p : S → Prop) : C ⊕ {s // p s} → FreeGroup (PairGen A Z) :=
  Sum.elim (fun c => FreeGroup.map Sum.inl (core c))
    (fun s => normalizedWord core hcore (extra s.val))

def restrictedGenus (p : S → Prop) (s : {s // p s}) : ℕ :=
  normalizedGenus core hcore extra s.val

instance restrictedGenus_neZero (p : S → Prop) (s : {s // p s}) :
    NeZero (restrictedGenus core hcore extra p s) :=
  normalizedGenus_neZero core hcore extra s.val

def restrictedLoops (p : S → Prop) (s : {s // p s}) :
    Fin (restrictedGenus core hcore extra p s) × Bool → FreeGroup (PairGen A Z) :=
  normalizedLoops core hcore extra s.val

theorem restrictedPresentation_surface (p : S → Prop) (s : {s // p s}) :
    restrictedPresentation core hcore extra p (Sum.inr s) =
      commWord (restrictedLoops core hcore extra p s)
        (finitePairs (restrictedGenus core hcore extra p s)) :=
  normalizedPresentation_surface core hcore extra s.val

def restrictedBlockPresentation (p : S → Prop) :
    C ⊕ (Σ s : {s // p s}, NamedSpineRel (restrictedGenus core hcore extra p s)) →
      FreeGroup (PairGen A Z ⊕
        (Σ s : {s // p s}, SpinePresentationGen (restrictedGenus core hcore extra p s))) :=
  substPresF (restrictedPresentation core hcore extra p)
    (familyFiniteSpineWordBlock (restrictedGenus core hcore extra p)
      (restrictedLoops core hcore extra p))

def restrictedStructuralMap (p : S → Prop) :
    PresMorFS (restrictedPresentation core hcore extra p)
      (restrictedBlockPresentation core hcore extra p) := by
  let dSrc : DecidableEq (PairGen A Z) := inferInstance
  let dTgt : DecidableEq (PairGen A Z ⊕ (Σ s : {s // p s},
      SpinePresentationGen (restrictedGenus core hcore extra p s))) := inferInstance
  letI : DecidableEq (PairGen A Z) := Classical.decEq _
  letI : DecidableEq {s // p s} := Classical.decEq _
  let dFamilyTgt : DecidableEq (PairGen A Z ⊕ (Σ s : {s // p s},
      SpinePresentationGen (restrictedGenus core hcore extra p s))) :=
    @instDecidableEqSum _ _ (Classical.decEq _) inferInstance
  exact @PresMorFS.redecide _ _ _ _ (Classical.decEq _) dFamilyTgt _ _
    (finiteSpineFamilyStructuralMap (restrictedPresentation core hcore extra p)
    (restrictedGenus core hcore extra p) (restrictedLoops core hcore extra p)
    (restrictedPresentation_surface core hcore extra p)) dSrc dTgt

theorem restrictedStructuralMap_generates (p : S → Prop) :
    FSGenerates (restrictedStructuralMap core hcore extra p) := by
  let dSrc : DecidableEq (PairGen A Z) := inferInstance
  let dTgt : DecidableEq (PairGen A Z ⊕ (Σ s : {s // p s},
      SpinePresentationGen (restrictedGenus core hcore extra p s))) := inferInstance
  letI : DecidableEq (PairGen A Z) := Classical.decEq _
  letI : DecidableEq {s // p s} := Classical.decEq _
  let dFamilyTgt : DecidableEq (PairGen A Z ⊕ (Σ s : {s // p s},
      SpinePresentationGen (restrictedGenus core hcore extra p s))) :=
    @instDecidableEqSum _ _ (Classical.decEq _) inferInstance
  exact @FSGenerates.redecide _ _ _ _ (Classical.decEq _) dFamilyTgt _ _ _
    (finiteSpineFamilyStructuralMap_generates (restrictedPresentation core hcore extra p)
    (restrictedGenus core hcore extra p) (restrictedLoops core hcore extra p)
    (restrictedPresentation_surface core hcore extra p)) dSrc dTgt

variable {p t : S → Prop} (hpt : ∀ s, p s → t s)

def labelIncl (s : {s // p s}) : {s // t s} := ⟨s.val, hpt s.val s.property⟩

theorem labelIncl_injective : Function.Injective (labelIncl hpt) := by
  intro s s' h
  exact Subtype.ext (congrArg (fun x : {s // t s} => x.val) h)

def oldCellIncl : C ⊕ {s // p s} → C ⊕ {s // t s} := Sum.map id (labelIncl hpt)

theorem oldCellIncl_injective : Function.Injective (oldCellIncl (C := C) hpt) :=
  Function.Injective.sumMap Function.injective_id (labelIncl_injective hpt)

def blockGenIncl :
    (PairGen A Z ⊕ (Σ s : {s // p s}, SpinePresentationGen (restrictedGenus core hcore extra p s))) →
    (PairGen A Z ⊕ (Σ s : {s // t s}, SpinePresentationGen (restrictedGenus core hcore extra t s))) :=
  Sum.map id (fun z => ⟨labelIncl hpt z.1, z.2⟩)

def blockCellIncl :
    (C ⊕ (Σ s : {s // p s}, NamedSpineRel (restrictedGenus core hcore extra p s))) →
    (C ⊕ (Σ s : {s // t s}, NamedSpineRel (restrictedGenus core hcore extra t s))) :=
  Sum.map id (fun m => ⟨labelIncl hpt m.1, m.2⟩)

theorem sigma_labelIncl_injective {F : S → Type}
    : Function.Injective (fun z : Σ s : {s // p s}, F s.val =>
        (⟨labelIncl hpt z.1, z.2⟩ : Σ s : {s // t s}, F s.val)) := by
  rintro ⟨s, x⟩ ⟨s', x'⟩ h
  have hs  := labelIncl_injective hpt (congrArg Sigma.fst h)
  grind

theorem blockGenIncl_injective :
    Function.Injective (blockGenIncl core hcore extra hpt) :=
  Function.Injective.sumMap Function.injective_id
    (sigma_labelIncl_injective (F := fun s => SpinePresentationGen
      (normalizedGenus core hcore extra s)) hpt)

theorem blockCellIncl_injective :
    Function.Injective (blockCellIncl core hcore extra hpt) :=
  Function.Injective.sumMap Function.injective_id
    (sigma_labelIncl_injective (F := fun s => NamedSpineRel
      (normalizedGenus core hcore extra s)) hpt)

/-- Literal compatibility of the corrected relators, with the core fixed. -/
theorem restrictedPresentation_incl (c : C ⊕ {s // p s}) :
    restrictedPresentation core hcore extra t (oldCellIncl hpt c) =
      restrictedPresentation core hcore extra p c := by
  cases c <;> rfl

theorem blockGenIncl_genEmb (s : {s // p s}) :
    (FreeGroup.map (blockGenIncl core hcore extra hpt)).comp
      (FreeGroup.map (genEmb (α := PairGen A Z)
        (Zt := fun r => SpinePresentationGen (restrictedGenus core hcore extra p r)) s)) =
    FreeGroup.map (genEmb (α := PairGen A Z)
      (Zt := fun r => SpinePresentationGen (restrictedGenus core hcore extra t r))
      (labelIncl hpt s)) := by
  apply FreeGroup.ext_hom
  intro x
  rw [MonoidHom.comp_apply, FreeGroup.map.of, FreeGroup.map.of]
  erw [FreeGroup.map.of]
  cases x <;> rfl

/-- Actual genus relators, not an abstract presentation assignment, respect
the same ambient-label inclusion. -/
theorem restrictedBlockPresentation_incl
    (m : C ⊕ (Σ s : {s // p s}, NamedSpineRel (restrictedGenus core hcore extra p s))) :
    restrictedBlockPresentation core hcore extra t (blockCellIncl core hcore extra hpt m) =
      FreeGroup.map (blockGenIncl core hcore extra hpt)
        (restrictedBlockPresentation core hcore extra p m) := by
  cases m with
  | inl c =>
      have h : (FreeGroup.map (blockGenIncl core hcore extra hpt)).comp
          (FreeGroup.map Sum.inl) = FreeGroup.map Sum.inl := by
        apply FreeGroup.ext_hom
        intro x
        simp [blockGenIncl]
      exact (congrArg (fun f => f (FreeGroup.map Sum.inl (core c))) h).symm
  | inr m =>
      exact (congrArg (fun f => f
        (familyFiniteSpineWordBlock (restrictedGenus core hcore extra p)
          (restrictedLoops core hcore extra p) m.1 m.2))
        (blockGenIncl_genEmb core hcore extra hpt m.1)).symm

end FiniteChains.RelativeNormalForm
end

section
open scoped Classical
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

def cubePositiveVertex (c : QCube A) : QCube A :=
  ⟨∅, c.sgn, by simp [IsSimplex], fun _ h => by simp at h⟩

def cubeNegativeVertex (c : QCube A) (v : V) : QCube A :=
  ⟨∅, Function.update c.sgn v 1, by simp [IsSimplex],
    fun _ h => by simp at h⟩

theorem cubePositiveVertex_lt (c : QCube A) (v : V) (hv : v ∈ c.spx) :
    cubePositiveVertex c < c := by
  refine lt_of_le_of_ne ⟨Finset.empty_subset _, fun _ _ => rfl⟩ ?_
  intro h
  have hs : c.spx = ∅ := (congrArg QCube.spx h).symm
  simp [hs] at hv

theorem cubeNegativeVertex_lt (c : QCube A) (v : V) (hv : v ∈ c.spx) :
    cubeNegativeVertex c v < c := by
  refine lt_of_le_of_ne ⟨Finset.empty_subset _, ?_⟩ ?_
  · intro w hw
    have hne : w ≠ v := fun h => hw (h.symm ▸ hv)
    exact Function.update_of_ne hne _ _
  · intro h
    have hs : c.spx = ∅ := (congrArg QCube.spx h).symm
    simp [hs] at hv

/-- The two strict radial half-edges in the chosen free direction. -/
def cubeEdgeSubdivision (c : QCube A) (v : V) (hv : v ∈ c.spx) :
    (strictOrderCx (QCube A)).E →₀ ℤ :=
  Finsupp.single ⟨(cubeNegativeVertex c v, c), cubeNegativeVertex_lt c v hv⟩ 1 -
    Finsupp.single ⟨(cubePositiveVertex c, c), cubePositiveVertex_lt c v hv⟩ 1

/-- This actual subdivision has the positive endpoint minus the negative endpoint as boundary. -/
theorem cubeEdgeSubdivision_boundary (c : QCube A) (v : V) (hv : v ∈ c.spx) :
    Comb.bdry1 (strictOrderCx (QCube A)) (cubeEdgeSubdivision c v hv) =
      Finsupp.single (cubePositiveVertex c) 1 - Finsupp.single (cubeNegativeVertex c v) 1 := by
  simp only [cubeEdgeSubdivision, map_sub, Comb.bdry1_single, one_smul]
  simp only [strictOrderCx]
  abel

theorem cubeEndpoints_ne (c : QCube A) (v : V) (hv : v ∈ c.spx) :
    cubeNegativeVertex c v ≠ cubePositiveVertex c := by
  intro h
  have he := congrArg (fun d : QCube A => d.sgn v) h
  have hv0 := c.sgn_eq_zero v hv
  simp [cubeNegativeVertex, cubePositiveVertex, hv0] at he

/-- For a genuine one-dimensional cube these are its actual oriented subdivided edges. -/
def oneCubeSubdivision (c : QCube A) (v : V) (hs : c.spx = {v}) :
    (strictOrderCx (QCube A)).E →₀ ℤ :=
  cubeEdgeSubdivision c v (by rw [hs]; simp)

theorem oneCubeSubdivision_boundary (c : QCube A) (v : V) (hs : c.spx = {v}) :
    Comb.bdry1 (strictOrderCx (QCube A)) (oneCubeSubdivision c v hs) =
      Finsupp.single (cubePositiveVertex c) 1 - Finsupp.single (cubeNegativeVertex c v) 1 :=
  cubeEdgeSubdivision_boundary c v _

theorem cubeEdgeSubdivision_ne_zero (c : QCube A) (v : V) (hv : v ∈ c.spx) :
    cubeEdgeSubdivision c v hv ≠ 0 := by
  intro h
  have hb := congrArg (Comb.bdry1 (strictOrderCx (QCube A))) h
  rw [cubeEdgeSubdivision_boundary, map_zero] at hb
  have he := congrArg (fun z : QCube A →₀ ℤ => z (cubePositiveVertex c)) hb
  simp [cubeEndpoints_ne c v hv, Ne.symm (cubeEndpoints_ne c v hv)] at he

theorem cubeEdgeSubdivision_filter_tgt (d c : QCube A) (v : V) (hv : v ∈ d.spx) :
    (cubeEdgeSubdivision d v hv).filter
      (fun e : (strictOrderCx (QCube A)).E => e.1.2 = c) =
      if d = c then cubeEdgeSubdivision d v hv else 0 := by
  by_cases h : d = c <;> simp [cubeEdgeSubdivision, h, Finsupp.filter_single_of_pos, Finsupp.filter_single_of_neg]

end FiniteChains.Davis
end

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

def qCubeFacet (c : QCube A) (v : V) (s : ZMod 2) : QCube A where
  spx := c.spx.erase v
  sgn := Function.update c.sgn v s
  isSimplex := isSimplex_subset A (Finset.erase_subset _ _) c.isSimplex
  sgn_eq_zero w hw := by
    have h := Finset.mem_erase.mp hw
    rw [Function.update_of_ne h.1]
    exact c.sgn_eq_zero w h.2


theorem qCubeFacet_lt (c : QCube A) (v : V) (s : ZMod 2) (hv : v ∈ c.spx) :
    qCubeFacet c v s < c := by
  apply lt_of_le_of_ne (by
    refine ⟨Finset.erase_subset _ _, ?_⟩
    intro w hw
    have hne : w ≠ v := fun h => hw (h.symm ▸ hv)
    exact Function.update_of_ne hne _ _)
  intro h
  have hs : c.spx.erase v = c.spx := congrArg QCube.spx h
  simp_all

@[simp] theorem qCubeFacet_sgn_self (c : QCube A) (v : V) (s : ZMod 2) :
    (qCubeFacet c v s).sgn v = s := Function.update_self _ _ _

/-- Fixing two distinct directions gives the same actual face in either order. -/
theorem qCubeFacet_comm (c : QCube A) {v w : V} (hne : v ≠ w) (s t : ZMod 2) :
    qCubeFacet (qCubeFacet c v s) w t = qCubeFacet (qCubeFacet c w t) v s := by
  apply QCube.ext'
  · change (c.spx.erase v).erase w = (c.spx.erase w).erase v
    ext x
    simp
    tauto
  · intro x _
    change Function.update (Function.update c.sgn v s) w t x =
      Function.update (Function.update c.sgn w t) v s x
    by_cases hxv : x = v
    · subst x
      simp [hne]
    · by_cases hxw : x = w
      · subst x
        simp [Ne.symm hne]
      · simp [hxv, hxw]

theorem qCubeFacet_zero_of_singleton (c : QCube A) (v : V) (hs : c.spx = {v}) :
    qCubeFacet c v 0 = cubePositiveVertex c := by
  apply QCube.ext'
  · simp [qCubeFacet, cubePositiveVertex, hs]
  · intro w _
    change Function.update c.sgn v 0 w = c.sgn w
    by_cases h : w = v
    · subst w
      rw [Function.update_self]
      exact (c.sgn_eq_zero v (by rw [hs]; simp)).symm
    · exact Function.update_of_ne h _ _

theorem qCubeFacet_one_of_singleton (c : QCube A) (v : V) (hs : c.spx = {v}) :
    qCubeFacet c v 1 = cubeNegativeVertex c v := by
  apply QCube.ext'
  · simp [qCubeFacet, cubeNegativeVertex, hs]
  · intro _ _
    rfl

/-- The strict one-cell subdivision agrees with the actual oriented cubical facets. -/
theorem oneCubeSubdivision_facet_boundary (c : QCube A) (v : V) (hs : c.spx = {v}) :
    Comb.bdry1 (strictOrderCx (QCube A)) (oneCubeSubdivision c v hs) =
      Finsupp.single (qCubeFacet c v 0) 1 - Finsupp.single (qCubeFacet c v 1) 1 := by
  rw [oneCubeSubdivision_boundary, qCubeFacet_zero_of_singleton c v hs,
    qCubeFacet_one_of_singleton c v hs]


/-- Positive facets are exactly the positive coordinate fixes used by the collapse. -/
theorem qCubeFacet_coordinate_zero (c : QCube A) (v : V) :
    qCubeToCoordinate (qCubeFacet c v 0) =
      Function.update (qCubeToCoordinate c) v CubeCoord.pos := by
  funext w
  by_cases h : w = v
  · subst w
    simp [qCubeToCoordinate, qCubeFacet]
  · simp [qCubeToCoordinate, qCubeFacet, h]

/-- Negative facets are exactly the negative coordinate fixes used by the collapse. -/
theorem qCubeFacet_coordinate_one (c : QCube A) (v : V) :
    qCubeToCoordinate (qCubeFacet c v 1) =
      Function.update (qCubeToCoordinate c) v CubeCoord.neg := by
  funext w
  by_cases h : w = v
  · subst w
    simp [qCubeToCoordinate, qCubeFacet]
  · simp [qCubeToCoordinate, qCubeFacet, h]

end FiniteChains.Davis

section
open scoped Classical
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

theorem squareFacet_v_spx (c : QCube A) {v w : V} (hne : v ≠ w)
    (hs : c.spx = {v, w}) (s : ZMod 2) : (qCubeFacet c w s).spx = {v} := by
  ext x
  simp only [qCubeFacet, hs, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
  grind

theorem squareFacet_w_spx (c : QCube A) {v w : V} (hne : v ≠ w)
    (hs : c.spx = {v, w}) (s : ZMod 2) : (qCubeFacet c v s).spx = {w} := by
  simp [qCubeFacet, hs, hne]

/-- The oriented cubical boundary in the direction frame `(v, w)`.
For `w < v`, this agrees with the coordinate incidence convention in `MomentAngle`. -/
def cubeSquareEdgeBoundary (c : QCube A) (v w : V) (hne : v ≠ w)
    (hs : c.spx = {v, w}) : (strictOrderCx (QCube A)).E →₀ ℤ :=
  oneCubeSubdivision (qCubeFacet c w 0) v (squareFacet_v_spx c hne hs 0) -
  oneCubeSubdivision (qCubeFacet c w 1) v (squareFacet_v_spx c hne hs 1) -
  oneCubeSubdivision (qCubeFacet c v 0) w (squareFacet_w_spx c hne hs 0) +
  oneCubeSubdivision (qCubeFacet c v 1) w (squareFacet_w_spx c hne hs 1)

/-- Every actual oriented subdivided square boundary is a strict cellular edge cycle. -/
theorem cubeSquareEdgeBoundary_cycle (c : QCube A) (v w : V) (hne : v ≠ w)
    (hs : c.spx = {v, w}) :
    Comb.bdry1 (strictOrderCx (QCube A)) (cubeSquareEdgeBoundary c v w hne hs) = 0 := by
  rw [cubeSquareEdgeBoundary, map_add, map_sub, map_sub,
    oneCubeSubdivision_facet_boundary, oneCubeSubdivision_facet_boundary,
    oneCubeSubdivision_facet_boundary, oneCubeSubdivision_facet_boundary]
  rw [qCubeFacet_comm c (Ne.symm hne) 0 0, qCubeFacet_comm c (Ne.symm hne) 0 1,
    qCubeFacet_comm c (Ne.symm hne) 1 0, qCubeFacet_comm c (Ne.symm hne) 1 1]
  abel

end FiniteChains.Davis
end

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

def cubeLowerIncl (c : QCube A) :
    Hom (strictOrderCx (Set.Iio c)) (strictOrderCx (QCube A)) :=
  strictOrderCxMap Subtype.val (fun _ _ h => h)

def lowerFacetEdgeChain (c d : QCube A) (hd : d < c)
    (v : V) (hv : v ∈ d.spx) : (strictOrderCx (Set.Iio c)).E →₀ ℤ :=
  Finsupp.single ⟨(⟨cubeNegativeVertex d v, (cubeNegativeVertex_lt d v hv).trans hd⟩,
    ⟨d, hd⟩), cubeNegativeVertex_lt d v hv⟩ 1 -
  Finsupp.single ⟨(⟨cubePositiveVertex d, (cubePositiveVertex_lt d v hv).trans hd⟩,
    ⟨d, hd⟩), cubePositiveVertex_lt d v hv⟩ 1

theorem lowerFacetEdgeChain_projection (c d : QCube A) (hd : d < c)
    (v : V) (hv : v ∈ d.spx) :
    chain1 (cubeLowerIncl c) (lowerFacetEdgeChain c d hd v hv) =
      cubeEdgeSubdivision d v hv := by
  erw [lowerFacetEdgeChain, map_sub]
  simp [chain1, cubeLowerIncl, strictOrderCxMap, cubeEdgeSubdivision, Finsupp.lmapDomain_apply]

def lowerSquareEdgeBoundary (c : QCube A) (v w : V) (hne : v ≠ w)
    (hs : c.spx = {v, w}) : (strictOrderCx (Set.Iio c)).E →₀ ℤ :=
  lowerFacetEdgeChain c (qCubeFacet c w 0)
    (qCubeFacet_lt c w 0 (by rw (config := { transparency := .default }) [hs]; simp)) v
    (by rw (config := { transparency := .default }) [squareFacet_v_spx c hne hs 0]; simp) -
  lowerFacetEdgeChain c (qCubeFacet c w 1)
    (qCubeFacet_lt c w 1 (by rw (config := { transparency := .default }) [hs]; simp)) v
    (by rw (config := { transparency := .default }) [squareFacet_v_spx c hne hs 1]; simp) -
  lowerFacetEdgeChain c (qCubeFacet c v 0)
    (qCubeFacet_lt c v 0 (by rw (config := { transparency := .default }) [hs]; simp)) w
    (by rw (config := { transparency := .default }) [squareFacet_w_spx c hne hs 0]; simp) +
  lowerFacetEdgeChain c (qCubeFacet c v 1)
    (qCubeFacet_lt c v 1 (by rw (config := { transparency := .default }) [hs]; simp)) w
    (by rw (config := { transparency := .default }) [squareFacet_w_spx c hne hs 1]; simp)

theorem lowerSquareEdgeBoundary_projection (c : QCube A) (v w : V) (hne : v ≠ w)
    (hs : c.spx = {v, w}) :
    chain1 (cubeLowerIncl c) (lowerSquareEdgeBoundary c v w hne hs) =
      cubeSquareEdgeBoundary c v w hne hs := by
  simp only [lowerSquareEdgeBoundary, map_add, map_sub, lowerFacetEdgeChain_projection]
  rfl


/-- The actual two-cube is filled by its eight nondegenerate barycentric triangles. -/
def cubeSquareSubdivision (c : QCube A) (v w : V) (hne : v ≠ w)
    (hs : c.spx = {v, w}) : (strictOrderCx (QCube A)).F →₀ ℤ :=
  strictTopConeEdgeChain Subtype.val (fun _ _ h => h) c (fun x : Set.Iio c => x.2)
    (lowerSquareEdgeBoundary c v w hne hs)

/-- Its actual strict cellular boundary is precisely the oriented four-facet edge chain. -/
theorem cubeSquareSubdivision_boundary (c : QCube A) (v w : V) (hne : v ≠ w)
    (hs : c.spx = {v, w}) :
    Comb.bdry2 (strictOrderCx (QCube A)) (cubeSquareSubdivision c v w hne hs) =
      cubeSquareEdgeBoundary c v w hne hs := by
  erw [cubeSquareSubdivision, strictTopConeEdgeChain_cycle_boundary _ _ _ _ _
    (by
      apply Finsupp.mapDomain_injective Subtype.val_injective
      change chain0 (cubeLowerIncl c) (Comb.bdry1 (strictOrderCx (Set.Iio c))
        (lowerSquareEdgeBoundary c v w hne hs)) = chain0 (cubeLowerIncl c) 0
      erw [← bdry1_chain1, lowerSquareEdgeBoundary_projection, cubeSquareEdgeBoundary_cycle,
        map_zero])]
  exact lowerSquareEdgeBoundary_projection c v w hne hs

/-- The square subdivision uses only triangles whose largest cell is that square. -/
theorem cubeSquareSubdivision_eq_zero_off_top (c : QCube A) (v w : V) (hne : v ≠ w)
    (hs : c.spx = {v, w}) (t : (strictOrderCx (QCube A)).F) (ht : t.1.2.2 ≠ c) :
    cubeSquareSubdivision c v w hne hs t = 0 :=
  strictTopConeEdgeChain_eq_zero_off_top _ _ _ _ _ t ht

end FiniteChains.Davis
end

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}


theorem qCube_card_lt_of_lt {d c : QCube A} (h : d < c) : d.spx.card < c.spx.card :=
  Finset.card_lt_card ((Finset.ssubset_iff_subset_ne).mpr
    ⟨h.le.1, (by
      intro hs
      apply h.ne
      apply QCube.ext' hs
      intro v hv
      exact h.le.2 v hv)⟩)

/-- Fixing the only removed direction reconstructs the actual face, including its sign. -/
theorem qCube_eq_facet_of_spx_erase {d c : QCube A} (h : d ≤ c) (v : V)
    (hs : d.spx = c.spx.erase v) : d = qCubeFacet c v (d.sgn v) := by
  apply QCube.ext' hs
  intro w hw
  by_cases hwv : w = v
  · subst w
    simp
  · change d.sgn w = Function.update c.sgn v (d.sgn v) w
    rw [Function.update_of_ne hwv]
    apply h.2
    intro hc
    apply hw
    exact Finset.mem_erase.mpr ⟨hwv, hc⟩

/-- Every codimension-one face is one of the coordinate facets, with its actual fixed sign. -/
theorem exists_qCube_facet_of_card (d c : QCube A) (h : d ≤ c)
    (hcard : c.spx.card = d.spx.card + 1) :
    ∃ v ∈ c.spx, d = qCubeFacet c v (d.sgn v) := by
  have hdiff : (c.spx \ d.spx).card = 1 := by
    rw [Finset.card_sdiff_of_subset h.1, hcard]
    omega
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hdiff
  have hm : v ∈ c.spx \ d.spx := by rw [hv]; simp
  obtain ⟨hvc, hvd⟩ := Finset.mem_sdiff.mp hm
  refine ⟨v, hvc, qCube_eq_facet_of_spx_erase h v ?_⟩
  ext w
  constructor
  · intro hw
    exact Finset.mem_erase.mpr ⟨fun he => hvd (he ▸ hw), h.1 hw⟩
  · intro hw
    obtain ⟨hwv, hwc⟩ := Finset.mem_erase.mp hw
    by_contra hwd
    have hm  := Finset.mem_sdiff.mpr ⟨hwc, hwd⟩
    rw [hv, Finset.mem_singleton] at hm
    exact hwv hm

/-- The only two signs of a codimension-one face give the two actual coordinate facets. -/
theorem exists_qCube_zero_or_one_facet (d c : QCube A) (h : d ≤ c)
    (hcard : c.spx.card = d.spx.card + 1) :
    ∃ v ∈ c.spx, d = qCubeFacet c v 0 ∨ d = qCubeFacet c v 1 := by
  obtain ⟨v, hv, he⟩ := exists_qCube_facet_of_card d c h hcard
  refine ⟨v, hv, ?_⟩
  generalize d.sgn v = s at he
  fin_cases s
  · exact Or.inl he
  · exact Or.inr he

/-- A vertex strictly below an actual edge is one of that edge's two endpoints. -/
theorem qCube_vertex_below_edge (d c : QCube A) (h : d < c) (v : V)
    (hs : c.spx = {v}) : d = cubePositiveVertex c ∨ d = cubeNegativeVertex c v := by
  have hc : c.spx.card = 1 := by rw [hs]; simp
  have hd : d.spx.card = 0 := by
    have hh := qCube_card_lt_of_lt h
    omega
  obtain ⟨w, hw, he⟩ := exists_qCube_zero_or_one_facet d c h.le (by omega)
  have hwv : w = v := by simpa [hs] using hw
  subst w
  rcases he with he | he
  · exact Or.inl (he.trans (qCubeFacet_zero_of_singleton c v hs))
  · exact Or.inr (he.trans (qCubeFacet_one_of_singleton c v hs))

/-- A genuine triangle below dimension two is necessarily a vertex-edge-square flag. -/
theorem qCube_triangle_dimensions (t : (strictOrderCx (QCube A)).F)
    (ht : t.1.2.2.spx.card ≤ 2) :
    t.1.1.spx.card = 0 ∧ t.1.2.1.spx.card = 1 ∧ t.1.2.2.spx.card = 2 := by
  have h01 := qCube_card_lt_of_lt t.2.1
  have h12 := qCube_card_lt_of_lt t.2.2
  omega

/-- A genuine tetrahedron below dimension three has all four successive cube dimensions. -/
theorem qCube_tetrahedron_dimensions (t : StrictOrdTet (QCube A))
    (ht : t.1.2.2.2.spx.card ≤ 3) :
    t.1.1.spx.card = 0 ∧ t.1.2.1.spx.card = 1 ∧
    t.1.2.2.1.spx.card = 2 ∧ t.1.2.2.2.spx.card = 3 := by
  have h01 := qCube_card_lt_of_lt t.2.1
  have h12 := qCube_card_lt_of_lt t.2.2.1
  have h23 := qCube_card_lt_of_lt t.2.2.2
  omega

end FiniteChains.Davis

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

def squarePositiveFlag (c : QCube A) (a b : V) (hne : a ≠ b)
    (hs : c.spx = {a, b}) (s : ZMod 2) : (strictOrderCx (QCube A)).F :=
  ⟨(cubePositiveVertex (qCubeFacet c a s), qCubeFacet c a s, c),
    cubePositiveVertex_lt _ b (by rw [squareFacet_w_spx c hne hs s]; simp),
    qCubeFacet_lt c a s (by rw [hs]; simp)⟩

def squareNegativeFlag (c : QCube A) (a b : V) (hne : a ≠ b)
    (hs : c.spx = {a, b}) (s : ZMod 2) : (strictOrderCx (QCube A)).F :=
  ⟨(cubeNegativeVertex (qCubeFacet c a s) b, qCubeFacet c a s, c),
    cubeNegativeVertex_lt _ b (by rw [squareFacet_w_spx c hne hs s]; simp),
    qCubeFacet_lt c a s (by rw [hs]; simp)⟩

/-- The actual cone filling is the signed sum of its eight genuine square flags. -/
theorem cubeSquareSubdivision_flags (c : QCube A) (v w : V) (hne : v ≠ w)
    (hs : c.spx = {v, w}) :
    cubeSquareSubdivision c v w hne hs =
      Finsupp.single (squareNegativeFlag c w v (Ne.symm hne)
        (by simpa [Finset.pair_comm] using hs) 0) 1 -
      Finsupp.single (squarePositiveFlag c w v (Ne.symm hne)
        (by simpa [Finset.pair_comm] using hs) 0) 1 -
      (Finsupp.single (squareNegativeFlag c w v (Ne.symm hne)
        (by simpa [Finset.pair_comm] using hs) 1) 1 -
       Finsupp.single (squarePositiveFlag c w v (Ne.symm hne)
        (by simpa [Finset.pair_comm] using hs) 1) 1) -
      (Finsupp.single (squareNegativeFlag c v w hne hs 0) 1 -
       Finsupp.single (squarePositiveFlag c v w hne hs 0) 1) +
      (Finsupp.single (squareNegativeFlag c v w hne hs 1) 1 -
       Finsupp.single (squarePositiveFlag c v w hne hs 1) 1) := by
  simp [cubeSquareSubdivision, lowerSquareEdgeBoundary, lowerFacetEdgeChain,
    strictTopConeEdgeChain, strictTopConeEdgeTriangle, squarePositiveFlag, squareNegativeFlag]

/-- Every strict triangle with this square as its top cell is one of the eight actual flags. -/
theorem squareFlags_exhaustive (c : QCube A) (v w : V) (hne : v ≠ w)
    (hs : c.spx = {v, w}) (t : (strictOrderCx (QCube A)).F) (ht : t.1.2.2 = c) :
    ∃ s : ZMod 2,
      t = squarePositiveFlag c v w hne hs s ∨
      t = squareNegativeFlag c v w hne hs s ∨
      t = squarePositiveFlag c w v (Ne.symm hne) (by simpa [Finset.pair_comm] using hs) s ∨
      t = squareNegativeFlag c w v (Ne.symm hne) (by simpa [Finset.pair_comm] using hs) s := by
  obtain ⟨⟨x, y, z⟩, hxy, hyz⟩ := t
  change z = c at ht
  subst z
  change x < y at hxy
  change y < c at hyz
  have hc : c.spx.card = 2 := by rw [hs]; simp [hne]
  have hy : y.spx.card = 1 := by
    have hx := qCube_card_lt_of_lt hxy
    have hy := qCube_card_lt_of_lt hyz
    omega
  obtain ⟨a, ha, hface⟩ := exists_qCube_zero_or_one_facet y c hyz.le (by omega)
  rw [hs, Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl
  · rcases hface with rfl | rfl
    · rcases qCube_vertex_below_edge x _ hxy w (squareFacet_w_spx c hne hs 0) with rfl | rfl
      · exact ⟨0, Or.inl rfl⟩
      · exact ⟨0, Or.inr (Or.inl rfl)⟩
    · rcases qCube_vertex_below_edge x _ hxy w (squareFacet_w_spx c hne hs 1) with rfl | rfl
      · exact ⟨1, Or.inl rfl⟩
      · exact ⟨1, Or.inr (Or.inl rfl)⟩
  · rcases hface with rfl | rfl
    · rcases qCube_vertex_below_edge x _ hxy v (squareFacet_v_spx c hne hs 0) with rfl | rfl
      · exact ⟨0, Or.inr (Or.inr (Or.inl rfl))⟩
      · exact ⟨0, Or.inr (Or.inr (Or.inr rfl))⟩
    · rcases qCube_vertex_below_edge x _ hxy v (squareFacet_v_spx c hne hs 1) with rfl | rfl
      · exact ⟨1, Or.inr (Or.inr (Or.inl rfl))⟩
      · exact ⟨1, Or.inr (Or.inr (Or.inr rfl))⟩

end FiniteChains.Davis
end

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

def squareEndpointFlag (c : QCube A) (a b : V) (hne : a ≠ b)
    (hs : c.spx = {a, b}) (i : ZMod 2 × Bool) : (strictOrderCx (QCube A)).F :=
  if i.2 then squarePositiveFlag c a b hne hs i.1 else squareNegativeFlag c a b hne hs i.1

theorem squareEndpointFlag_injective (c : QCube A) (a b : V) (hne : a ≠ b)
    (hs : c.spx = {a, b}) : Function.Injective (squareEndpointFlag c a b hne hs) := by
  intro ⟨s, e⟩ ⟨t, f⟩ h
  have hm := congrArg (fun z : (strictOrderCx (QCube A)).F => z.1.2.1.sgn a) h
  have hv := congrArg (fun z : (strictOrderCx (QCube A)).F => z.1.1.sgn b) h
  have hb r : (qCubeFacet c a r).sgn b = 0 :=
    (qCubeFacet c a r).sgn_eq_zero b (by rw [squareFacet_w_spx c hne hs r]; simp)
  cases e <;> cases f
  · have hst : s = t := by simpa [squareEndpointFlag, squareNegativeFlag] using hm
    exact Prod.ext hst rfl
  · simp [squareEndpointFlag, squareNegativeFlag, squarePositiveFlag,
      cubeNegativeVertex, cubePositiveVertex, hb] at hv
  · simp [squareEndpointFlag, squareNegativeFlag, squarePositiveFlag,
      cubeNegativeVertex, cubePositiveVertex, hb] at hv
  · have hst : s = t := by simpa [squareEndpointFlag, squarePositiveFlag] using hm
    exact Prod.ext hst rfl

theorem squareEndpointFlag_middle (c : QCube A) (a b : V) (hne : a ≠ b)
    (hs : c.spx = {a, b}) (i : ZMod 2 × Bool) :
    (squareEndpointFlag c a b hne hs i).1.2.1 = qCubeFacet c a i.1 := by
  obtain ⟨s, e⟩ := i
  cases e <;> rfl

/-- A finite index for all eight actual flags: facet direction, fixed sign, endpoint. -/
def squareFlag (c : QCube A) (a b : V) (hne : a ≠ b)
    (hs : c.spx = {a, b}) (i : Bool × ZMod 2 × Bool) : (strictOrderCx (QCube A)).F :=
  if i.1 then squareEndpointFlag c a b hne hs i.2 else
    squareEndpointFlag c b a (Ne.symm hne) (by simpa [Finset.pair_comm] using hs) i.2

theorem squareFlag_injective (c : QCube A) (a b : V) (hne : a ≠ b)
    (hs : c.spx = {a, b}) : Function.Injective (squareFlag c a b hne hs) := by
  intro ⟨e, i⟩ ⟨f, j⟩ h
  have hcross (i j : ZMod 2 × Bool) :
      squareEndpointFlag c a b hne hs i ≠
        squareEndpointFlag c b a (Ne.symm hne) (by simpa [Finset.pair_comm] using hs) j := by
    intro he
    have hm := congrArg (fun t : (strictOrderCx (QCube A)).F => t.1.2.1.spx) he
    rw [squareEndpointFlag_middle, squareEndpointFlag_middle,
      squareFacet_w_spx c hne hs, squareFacet_v_spx c hne hs] at hm
    exact hne (Finset.singleton_inj.mp hm).symm
  cases e <;> cases f
  · have hij := squareEndpointFlag_injective c b a (Ne.symm hne)
      (by simpa [Finset.pair_comm] using hs) h
    exact Prod.ext rfl hij
  · exact False.elim (hcross j i h.symm)
  · exact False.elim (hcross i j h)
  · exact Prod.ext rfl (squareEndpointFlag_injective c a b hne hs h)

/-- The finite index covers every strict triangle topped by the chosen square. -/
theorem squareFlag_surjective_on_top (c : QCube A) (a b : V) (hne : a ≠ b)
    (hs : c.spx = {a, b}) (t : (strictOrderCx (QCube A)).F) (ht : t.1.2.2 = c) :
    ∃ i : Bool × ZMod 2 × Bool, squareFlag c a b hne hs i = t := by
  obtain ⟨s, hp | hn | hp | hn⟩ := squareFlags_exhaustive c a b hne hs t ht
  · exact ⟨(true, s, true), hp.symm⟩
  · exact ⟨(true, s, false), hn.symm⟩
  · exact ⟨(false, s, true), hp.symm⟩
  · exact ⟨(false, s, false), hn.symm⟩

/-- Extract the eight actual integer flag coefficients of a square. -/
def squareFlagCoordinates (c : QCube A) (a b : V) (hne : a ≠ b)
    (hs : c.spx = {a, b}) : ((strictOrderCx (QCube A)).F →₀ ℤ) →ₗ[ℤ]
      ((Bool × ZMod 2 × Bool) →₀ ℤ) :=
  Finsupp.lcomapDomain (squareFlag c a b hne hs) (squareFlag_injective c a b hne hs)

theorem squareFlagCoordinates_apply (c : QCube A) (a b : V) (hne : a ≠ b)
    (hs : c.spx = {a, b}) (z : (strictOrderCx (QCube A)).F →₀ ℤ)
    (i : Bool × ZMod 2 × Bool) :
    squareFlagCoordinates c a b hne hs z i = z (squareFlag c a b hne hs i) := rfl

/-- Every actual chain supported on this square is recovered from its eight coefficients. -/
theorem squareFlagCoordinates_reconstruct (c : QCube A) (a b : V) (hne : a ≠ b)
    (hs : c.spx = {a, b}) (z : (strictOrderCx (QCube A)).F →₀ ℤ)
    (hz : ∀ t ∈ z.support, t.1.2.2 = c) :
    Finsupp.mapDomain (squareFlag c a b hne hs)
      (squareFlagCoordinates c a b hne hs z) = z := by
  apply Finsupp.mapDomain_comapDomain _ (squareFlag_injective c a b hne hs)
  intro t ht
  exact squareFlag_surjective_on_top c a b hne hs t (hz t ht)

theorem squareFlagCoordinates_single (c : QCube A) (a b : V) (hne : a ≠ b)
    (hs : c.spx = {a, b}) (i : Bool × ZMod 2 × Bool) (n : ℤ) :
    squareFlagCoordinates c a b hne hs (Finsupp.single (squareFlag c a b hne hs i) n) =
      Finsupp.single i n :=
  Finsupp.comapDomain_single _ _ _ (squareFlag_injective c a b hne hs).injOn

/-- The signed coefficient vector of the genuine square subdivision. -/
theorem squareFlagCoordinates_subdivision (c : QCube A) (a b : V) (hne : a ≠ b)
    (hs : c.spx = {a, b}) :
    squareFlagCoordinates c a b hne hs (cubeSquareSubdivision c a b hne hs) =
      Finsupp.single (false, 0, false) 1 - Finsupp.single (false, 0, true) 1 -
      (Finsupp.single (false, 1, false) 1 - Finsupp.single (false, 1, true) 1) -
      (Finsupp.single (true, 0, false) 1 - Finsupp.single (true, 0, true) 1) +
      (Finsupp.single (true, 1, false) 1 - Finsupp.single (true, 1, true) 1) := by
  rw [cubeSquareSubdivision_flags]
  change squareFlagCoordinates c a b hne hs
    (Finsupp.single (squareFlag c a b hne hs (false, 0, false)) 1 -
     Finsupp.single (squareFlag c a b hne hs (false, 0, true)) 1 -
     (Finsupp.single (squareFlag c a b hne hs (false, 1, false)) 1 -
      Finsupp.single (squareFlag c a b hne hs (false, 1, true)) 1) -
     (Finsupp.single (squareFlag c a b hne hs (true, 0, false)) 1 -
      Finsupp.single (squareFlag c a b hne hs (true, 0, true)) 1) +
     (Finsupp.single (squareFlag c a b hne hs (true, 1, false)) 1 -
      Finsupp.single (squareFlag c a b hne hs (true, 1, true)) 1)) = _
  simp only [map_add, map_sub, squareFlagCoordinates_single]

end FiniteChains.Davis

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

def squareFlagSign (i : Bool × ZMod 2 × Bool) : ℤ :=
  (if i.1 then -1 else 1) * (if i.2.1 = 0 then 1 else -1) *
    (if i.2.2 then -1 else 1)

theorem squareSubdivision_flag_coefficient (c : QCube A) (a b : V) (hne : a ≠ b)
    (hs : c.spx = {a, b}) (i : Bool × ZMod 2 × Bool) :
    cubeSquareSubdivision c a b hne hs (squareFlag c a b hne hs i) = squareFlagSign i := by
  rw [← squareFlagCoordinates_apply, squareFlagCoordinates_subdivision]
  obtain ⟨e, s, f⟩ := i
  cases e <;> fin_cases s <;> cases f <;>
    norm_num [squareFlagSign, Finsupp.single_apply, Prod.mk.injEq]

end FiniteChains.Davis
end

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

def squareCorner (c : QCube A) (a b : V) (s t : ZMod 2) : QCube A :=
  qCubeFacet (qCubeFacet c a s) b t

@[simp] theorem squareCorner_sgn_left (c : QCube A) (a b : V) (hne : a ≠ b)
    (s t : ZMod 2) : (squareCorner c a b s t).sgn a = s := by
  simp [squareCorner, qCubeFacet, hne]

@[simp] theorem squareCorner_sgn_right (c : QCube A) (a b : V)
    (s t : ZMod 2) : (squareCorner c a b s t).sgn b = t := by
  simp [squareCorner]

theorem squareCorner_spx (c : QCube A) (a b : V) (hne : a ≠ b)
    (hs : c.spx = {a, b}) (s t : ZMod 2) : (squareCorner c a b s t).spx = ∅ := by
  change (c.spx.erase a).erase b = ∅
  simp [hs, hne]

theorem squareCorner_lt (c : QCube A) (a b : V) (hne : a ≠ b)
    (hs : c.spx = {a, b}) (s t : ZMod 2) : squareCorner c a b s t < c :=
  (qCubeFacet_lt _ b t (by rw [squareFacet_w_spx c hne hs s]; simp)).trans
    (qCubeFacet_lt c a s (by rw [hs]; simp))

theorem squareCorner_injective (c : QCube A) (a b : V) (hne : a ≠ b) :
    Function.Injective (fun i : ZMod 2 × ZMod 2 => squareCorner c a b i.1 i.2) := by
  intro ⟨s, t⟩ ⟨u, v⟩ h
  have hl := congrArg (fun x : QCube A => x.sgn a) h
  have hr := congrArg (fun x : QCube A => x.sgn b) h
  simp only [squareCorner_sgn_left _ _ _ hne] at hl
  simp at hr
  exact Prod.ext hl hr

theorem squareCorner_positive (c : QCube A) (a b : V) (hne : a ≠ b)
    (hs : c.spx = {a, b}) (s : ZMod 2) :
    squareCorner c a b s 0 = cubePositiveVertex (qCubeFacet c a s) :=
  qCubeFacet_zero_of_singleton _ b (squareFacet_w_spx c hne hs s)

theorem squareCorner_negative (c : QCube A) (a b : V) (hne : a ≠ b)
    (hs : c.spx = {a, b}) (s : ZMod 2) :
    squareCorner c a b s 1 = cubeNegativeVertex (qCubeFacet c a s) b :=
  qCubeFacet_one_of_singleton _ b (squareFacet_w_spx c hne hs s)

theorem squareCorner_swap (c : QCube A) (a b : V) (hne : a ≠ b) (s t : ZMod 2) :
    squareCorner c a b s t = squareCorner c b a t s :=
  qCubeFacet_comm c hne s t

end FiniteChains.Davis

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

def squareFacetIndex (c : QCube A) (a b : V) (i : Bool × ZMod 2) : QCube A :=
  if i.1 then qCubeFacet c a i.2 else qCubeFacet c b i.2

theorem squareFacetIndex_spx (c : QCube A) (a b : V) (hne : a ≠ b)
    (hs : c.spx = {a, b}) (i : Bool × ZMod 2) :
    (squareFacetIndex c a b i).spx = if i.1 then {b} else {a} := by grind [squareFacet_v_spx, squareFacet_w_spx, squareFacetIndex]

theorem squareFacetIndex_lt (c : QCube A) (a b : V) (hs : c.spx = {a, b})
    (i : Bool × ZMod 2) : squareFacetIndex c a b i < c := by
  obtain ⟨e, s⟩ := i
  cases e
  · exact qCubeFacet_lt c b s (by rw [hs]; simp)
  · exact qCubeFacet_lt c a s (by rw [hs]; simp)

theorem squareFacetIndex_injective (c : QCube A) (a b : V) (hne : a ≠ b)
    (hs : c.spx = {a, b}) : Function.Injective (squareFacetIndex c a b) := by
  intro ⟨e, s⟩ ⟨f, t⟩ h
  have hf := congrArg QCube.spx h
  rw [squareFacetIndex_spx c a b hne hs, squareFacetIndex_spx c a b hne hs] at hf
  cases e <;> cases f
  · have he := congrArg (fun d : QCube A => d.sgn b) h
    have hst : s = t := by simpa [squareFacetIndex] using he
    exact Prod.ext rfl hst
  · simp_all
  · simp_all
  · have he := congrArg (fun d : QCube A => d.sgn a) h
    have hst : s = t := by simpa [squareFacetIndex] using he
    exact Prod.ext rfl hst

abbrev SquareRadialIndex := (Bool × ZMod 2) ⊕ (ZMod 2 × ZMod 2)

def squareRadialCell (c : QCube A) (a b : V) : SquareRadialIndex → QCube A
  | .inl i => squareFacetIndex c a b i
  | .inr i => squareCorner c a b i.1 i.2

theorem squareRadialCell_injective (c : QCube A) (a b : V) (hne : a ≠ b)
    (hs : c.spx = {a, b}) : Function.Injective (squareRadialCell c a b) := by
  intro i j h
  have hf := congrArg (fun d : QCube A => d.spx.card) h
  cases i with
  | inl i =>
    cases j with
    | inl j => exact congrArg Sum.inl (squareFacetIndex_injective c a b hne hs h)
    | inr j =>
      simp only [squareRadialCell, squareFacetIndex_spx c a b hne hs,
        squareCorner_spx c a b hne hs, Finset.card_empty] at hf
      split_ifs at hf <;> simp at hf
  | inr i =>
    cases j with
    | inl j =>
      simp only [squareRadialCell, squareFacetIndex_spx c a b hne hs,
        squareCorner_spx c a b hne hs, Finset.card_empty] at hf
      split_ifs at hf <;> simp at hf
    | inr j => exact congrArg Sum.inr (squareCorner_injective c a b hne h)

def squareRadialEdge (c : QCube A) (a b : V) (hne : a ≠ b)
    (hs : c.spx = {a, b}) (i : SquareRadialIndex) : (strictOrderCx (QCube A)).E :=
  ⟨(squareRadialCell c a b i, c), by
    cases i with
    | inl i => exact squareFacetIndex_lt c a b hs i
    | inr i => exact squareCorner_lt c a b hne hs i.1 i.2⟩

theorem squareRadialEdge_injective (c : QCube A) (a b : V) (hne : a ≠ b)
    (hs : c.spx = {a, b}) : Function.Injective (squareRadialEdge c a b hne hs) := by
  intro i j h
  exact squareRadialCell_injective c a b hne hs
    (congrArg (fun e : (strictOrderCx (QCube A)).E => e.1.1) h)

end FiniteChains.Davis

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

def squareFlagCornerIndex (i : Bool × ZMod 2 × Bool) : ZMod 2 × ZMod 2 :=
  if i.1 then (i.2.1, if i.2.2 then 0 else 1) else
    (if i.2.2 then 0 else 1, i.2.1)

theorem squareFlag_middle (c : QCube A) (a b : V) (hne : a ≠ b)
    (hs : c.spx = {a, b}) (i : Bool × ZMod 2 × Bool) :
    (squareFlag c a b hne hs i).1.2.1 = squareFacetIndex c a b (i.1, i.2.1) := by
  obtain ⟨e, s, f⟩ := i
  cases e <;> cases f <;> rfl

theorem squareFlag_top (c : QCube A) (a b : V) (hne : a ≠ b)
    (hs : c.spx = {a, b}) (i : Bool × ZMod 2 × Bool) :
    (squareFlag c a b hne hs i).1.2.2 = c := by
  obtain ⟨e, s, f⟩ := i
  cases e <;> cases f <;> rfl


def squareRadialCoordinates (c : QCube A) (a b : V) (hne : a ≠ b)
    (hs : c.spx = {a, b}) : ((strictOrderCx (QCube A)).E →₀ ℤ) →ₗ[ℤ]
      (SquareRadialIndex →₀ ℤ) :=
  Finsupp.lcomapDomain (squareRadialEdge c a b hne hs)
    (squareRadialEdge_injective c a b hne hs)

theorem squareRadialCoordinates_single (c : QCube A) (a b : V) (hne : a ≠ b)
    (hs : c.spx = {a, b}) (i : SquareRadialIndex) (n : ℤ) :
    squareRadialCoordinates c a b hne hs (Finsupp.single (squareRadialEdge c a b hne hs i) n) =
      Finsupp.single i n :=
  Finsupp.comapDomain_single _ _ _ (squareRadialEdge_injective c a b hne hs).injOn

theorem squareRadialCoordinates_off_top (c : QCube A) (a b : V) (hne : a ≠ b)
    (hs : c.spx = {a, b}) (e : (strictOrderCx (QCube A)).E) (he : e.1.2 ≠ c) (n : ℤ) :
    squareRadialCoordinates c a b hne hs (Finsupp.single e n) = 0 := by
  ext i
  change Finsupp.single e n (squareRadialEdge c a b hne hs i) = 0
  have hne : e ≠ squareRadialEdge c a b hne hs i := by
    intro h
    exact he (congrArg (fun e : (strictOrderCx (QCube A)).E => e.1.2) h)
  simp [hne]

def squareInternalBoundary : ((Bool × ZMod 2 × Bool) →₀ ℤ) →ₗ[ℤ]
    (SquareRadialIndex →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun i => Finsupp.single (.inl (i.1, i.2.1)) 1 -
    Finsupp.single (.inr (squareFlagCornerIndex i)) 1)

/-- Each actual flag contributes its facet radial edge minus its corner radial edge. -/
theorem squareFlag_internal_boundary (c : QCube A) (a b : V) (hne : a ≠ b)
    (hs : c.spx = {a, b}) (i : Bool × ZMod 2 × Bool) :
    squareRadialCoordinates c a b hne hs
      (Comb.bdry2 (strictOrderCx (QCube A))
        (Finsupp.single (squareFlag c a b hne hs i) 1)) =
      Finsupp.single (.inl (i.1, i.2.1)) 1 -
        Finsupp.single (.inr (squareFlagCornerIndex i)) 1 := by
  let t := squareFlag c a b hne hs i
  let e01 : (strictOrderCx (QCube A)).E := ⟨(t.1.1, t.1.2.1), t.2.1⟩
  let e12 : (strictOrderCx (QCube A)).E := ⟨(t.1.2.1, t.1.2.2), t.2.2⟩
  let e02 : (strictOrderCx (QCube A)).E := ⟨(t.1.1, t.1.2.2), t.2.1.trans t.2.2⟩
  have h12 : e12 = squareRadialEdge c a b hne hs (.inl (i.1, i.2.1)) := by
    apply Subtype.ext
    exact Prod.ext (squareFlag_middle c a b hne hs i) (squareFlag_top c a b hne hs i)
  have h02 : e02 = squareRadialEdge c a b hne hs (.inr (squareFlagCornerIndex i)) := by
    apply Subtype.ext
    exact Prod.ext (by
      obtain ⟨e, s, f⟩ := i
      cases e <;> cases f
      · exact (squareCorner_negative c b a (Ne.symm hne)
          (by simpa [Finset.pair_comm] using hs) s).symm.trans
          (squareCorner_swap c b a (Ne.symm hne) s 1)
      · exact (squareCorner_positive c b a (Ne.symm hne)
          (by simpa [Finset.pair_comm] using hs) s).symm.trans
          (squareCorner_swap c b a (Ne.symm hne) s 0)
      · exact (squareCorner_negative c a b hne hs s).symm
      · exact (squareCorner_positive c a b hne hs s).symm) (squareFlag_top c a b hne hs i)
  have h01 : e01.1.2 ≠ c := by
    change t.1.2.1 ≠ c
    rw [squareFlag_middle]
    exact (squareFacetIndex_lt c a b hs (i.1, i.2.1)).ne
  have hb : Comb.bdry2 (strictOrderCx (QCube A)) (Finsupp.single t 1) =
      Finsupp.single e01 1 + Finsupp.single e12 1 - Finsupp.single e02 1 := by
    rw [Comb.bdry2_single, one_smul]
    simp [strictOrderCx, pathChain, e01, e12, e02]
    abel
  rw [hb, map_sub, map_add, squareRadialCoordinates_off_top c a b hne hs e01 h01 1,
    h12, h02, squareRadialCoordinates_single, squareRadialCoordinates_single, zero_add]

/-- The finite radial matrix is obtained by the actual strict cellular boundary. -/
theorem squareInternalBoundary_naturality (c : QCube A) (a b : V) (hne : a ≠ b)
    (hs : c.spx = {a, b}) (z : (Bool × ZMod 2 × Bool) →₀ ℤ) :
    squareRadialCoordinates c a b hne hs
      (Comb.bdry2 (strictOrderCx (QCube A))
        (Finsupp.mapDomain (squareFlag c a b hne hs) z)) = squareInternalBoundary z := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => rw [Finsupp.mapDomain_add, map_add, map_add, hz, hw, map_add]
  | single i n =>
      rw [Finsupp.mapDomain_single]
      have hn : Finsupp.single (squareFlag c a b hne hs i) n =
          n • Finsupp.single (squareFlag c a b hne hs i) 1 := by simp
      rw [hn, map_smul, map_smul, squareFlag_internal_boundary, squareInternalBoundary,
        Finsupp.linearCombination_single]

end FiniteChains.Davis
end

section
set_option maxHeartbeats 1000000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Davis
open RACG Mirror Comb

theorem squareInternalBoundary_facet (z : (Bool × ZMod 2 × Bool) →₀ ℤ)
    (e : Bool) (s : ZMod 2) :
    squareInternalBoundary z (.inl (e, s)) = z (e, s, false) + z (e, s, true) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => simp only [map_add, Finsupp.add_apply, hz, hw]; abel
  | single i n =>
      obtain ⟨f, t, b⟩ := i
      cases e <;> cases f <;> fin_cases s <;> fin_cases t <;> cases b <;>
        simp [squareInternalBoundary, Prod.mk.injEq]

theorem squareInternalBoundary_vertex (z : (Bool × ZMod 2 × Bool) →₀ ℤ)
    (s t : ZMod 2) :
    squareInternalBoundary z (.inr (s, t)) =
      -(z (true, s, decide (t = 0)) + z (false, t, decide (s = 0))) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => simp only [map_add, Finsupp.add_apply, hz, hw]; abel
  | single i n =>
      obtain ⟨e, r, b⟩ := i
      cases e <;> fin_cases r <;> cases b <;> fin_cases s <;> fin_cases t <;>
        simp [squareInternalBoundary, squareFlagCornerIndex, Prod.mk.injEq]

theorem squareInternalBoundary_kernel (z : (Bool × ZMod 2 × Bool) →₀ ℤ)
    (hz : squareInternalBoundary z = 0) :
    ∀ i, z i = z (false, 0, false) * squareFlagSign i := by
  have hf00 := congrArg (fun w : SquareRadialIndex →₀ ℤ => w (.inl (false, 0))) hz
  have hf01 := congrArg (fun w : SquareRadialIndex →₀ ℤ => w (.inl (false, 1))) hz
  have hf10 := congrArg (fun w : SquareRadialIndex →₀ ℤ => w (.inl (true, 0))) hz
  have hf11 := congrArg (fun w : SquareRadialIndex →₀ ℤ => w (.inl (true, 1))) hz
  have hv00 := congrArg (fun w : SquareRadialIndex →₀ ℤ => w (.inr (0, 0))) hz
  have hv10 := congrArg (fun w : SquareRadialIndex →₀ ℤ => w (.inr (1, 0))) hz
  have hv01 := congrArg (fun w : SquareRadialIndex →₀ ℤ => w (.inr (0, 1))) hz
  simp only [squareInternalBoundary_facet, Finsupp.zero_apply] at hf00 hf01 hf10 hf11
  simp only [squareInternalBoundary_vertex, Finsupp.zero_apply] at hv00 hv10 hv01
  norm_num at hv00 hv10 hv01
  rintro ⟨e, s, f⟩
  cases e <;> fin_cases s <;> cases f <;> simp only [squareFlagSign] <;> norm_num <;> omega

/-- An actual square-supported chain with zero internal boundary is its coefficient times
that square's genuine strict subdivision. -/
theorem squareChain_eq_scalar_subdivision {V : Type} [DecidableEq V] {A : CommRel V}
    (c : QCube A) (a b : V) (hne : a ≠ b) (hs : c.spx = {a, b})
    (z : (strictOrderCx (QCube A)).F →₀ ℤ)
    (hz : ∀ t ∈ z.support, t.1.2.2 = c)
    (hint : squareRadialCoordinates c a b hne hs
      (Comb.bdry2 (strictOrderCx (QCube A)) z) = 0) :
    z = z (squareFlag c a b hne hs (false, 0, false)) • cubeSquareSubdivision c a b hne hs := by
  let r := squareFlagCoordinates c a b hne hs z
  have hr : squareInternalBoundary r = 0 := by
    rw [← squareInternalBoundary_naturality c a b hne hs r]
    rw [squareFlagCoordinates_reconstruct c a b hne hs z hz]
    exact hint
  have he : r = r (false, 0, false) •
      squareFlagCoordinates c a b hne hs (cubeSquareSubdivision c a b hne hs) := by
    ext i
    rw [Finsupp.smul_apply, squareFlagCoordinates_apply c a b hne hs
      (cubeSquareSubdivision c a b hne hs) i, squareSubdivision_flag_coefficient, smul_eq_mul]
    exact squareInternalBoundary_kernel r hr i
  let f := Finsupp.lmapDomain ℤ ℤ (squareFlag c a b hne hs)
  have hzr  := squareFlagCoordinates_reconstruct c a b hne hs z hz
  have hsr : f (squareFlagCoordinates c a b hne hs (cubeSquareSubdivision c a b hne hs)) =
      cubeSquareSubdivision c a b hne hs := by
    apply squareFlagCoordinates_reconstruct
    intro t ht
    by_contra htop
    exact (Finsupp.mem_support_iff.mp ht)
      (cubeSquareSubdivision_eq_zero_off_top c a b hne hs t htop)
  calc
    z = f r := hzr.symm
    _ = f (r (false, 0, false) •
        squareFlagCoordinates c a b hne hs (cubeSquareSubdivision c a b hne hs)) := congrArg f he
    _ = r (false, 0, false) • cubeSquareSubdivision c a b hne hs := by rw [map_smul, hsr]
    _ = _ := rfl

end FiniteChains.Davis
end

section
open scoped Classical
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

theorem squareRadialBoundary_off_square (c : QCube A) (a b : V) (hne : a ≠ b)
    (hs : c.spx = {a, b}) (t : (strictOrderCx (QCube A)).F)
    (hm : t.1.2.1 ≠ c) (ht : t.1.2.2 ≠ c) (n : ℤ) :
    squareRadialCoordinates c a b hne hs
      (Comb.bdry2 (strictOrderCx (QCube A)) (Finsupp.single t n)) = 0 := by
  let e01 : (strictOrderCx (QCube A)).E := ⟨(t.1.1, t.1.2.1), t.2.1⟩
  let e12 : (strictOrderCx (QCube A)).E := ⟨(t.1.2.1, t.1.2.2), t.2.2⟩
  let e02 : (strictOrderCx (QCube A)).E := ⟨(t.1.1, t.1.2.2), t.2.1.trans t.2.2⟩
  have hb : Comb.bdry2 (strictOrderCx (QCube A)) (Finsupp.single t 1) =
      Finsupp.single e01 1 + Finsupp.single e12 1 - Finsupp.single e02 1 := by
    simp [Comb.bdry2, strictOrderCx, pathChain, e01, e12, e02]
    abel
  have hn : Finsupp.single t n = n • Finsupp.single t 1 := by simp
  rw [hn, map_smul, map_smul, hb, map_sub, map_add,
    squareRadialCoordinates_off_top c a b hne hs e01 hm,
    squareRadialCoordinates_off_top c a b hne hs e12 ht,
    squareRadialCoordinates_off_top c a b hne hs e02 ht]
  simp


/-- Every genuine two-dimensional cycle has on each square exactly its cubical coefficient
 times the actual strict square subdivision. -/
theorem cubeTwoCycle_square_component (c : QCube A) (a b : V) (hne : a ≠ b)
    (hs : c.spx = {a, b}) (z : (strictOrderCx (QCube A)).F →₀ ℤ)
    (hz : ∀ t ∈ z.support, t.1.2.2.spx.card ≤ 2)
    (hcycle : Comb.bdry2 (strictOrderCx (QCube A)) z = 0) :
    z.filter (fun t => t.1.2.2 = c) =
      z (squareFlag c a b hne hs (false, 0, false)) • cubeSquareSubdivision c a b hne hs := by
  have hsupp : ∀ t ∈ (z.filter (fun t => t.1.2.2 = c)).support, t.1.2.2 = c := by
    intro t ht
    exact (Finset.mem_filter.mp ht).2
  have hint : squareRadialCoordinates c a b hne hs
      (Comb.bdry2 (strictOrderCx (QCube A)) (z.filter (fun t => t.1.2.2 = c))) = 0 := by
    rw [← (show squareRadialCoordinates c a b hne hs (Comb.bdry2 (strictOrderCx (QCube A)) z) =
    squareRadialCoordinates c a b hne hs (Comb.bdry2 (strictOrderCx (QCube A))
      (z.filter (fun t => t.1.2.2 = c))) by
      have hc : c.spx.card = 2 := by rw [hs]; simp [hne]
      conv_lhs => rw [← z.sum_single]
      conv_rhs => rw [← z.sum_single]
      simp only [Finsupp.sum, map_sum, Finsupp.filter_sum]
      apply Finset.sum_congr rfl
      intro t ht
      by_cases he : t.1.2.2 = c
      · simp_all
      · rw [Finsupp.filter_single_of_neg (fun t : (strictOrderCx (QCube A)).F => t.1.2.2 = c) he]
        have hm : t.1.2.1 ≠ c := by
          intro hm
          have hdim := (qCube_triangle_dimensions t (hz t ht)).2.1
          rw [hm, hc] at hdim
          omega
        rw [squareRadialBoundary_off_square c a b hne hs t hm he, map_zero, map_zero]), hcycle, map_zero]
  have he := squareChain_eq_scalar_subdivision c a b hne hs _ hsupp hint
  simpa only [Finsupp.filter_apply, squareFlag_top, if_true] using he

end FiniteChains.Davis
end

section
open scoped Classical
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

theorem cubeSquareSubdivision_filter_top (d c : QCube A) (v w : V) (hne : v ≠ w)
    (hs : d.spx = {v, w}) :
    (cubeSquareSubdivision d v w hne hs).filter
      (fun t : (strictOrderCx (QCube A)).F => t.1.2.2 = c) =
      if d = c then cubeSquareSubdivision d v w hne hs else 0 := by
  by_cases hdc : d = c
  · rw [if_pos hdc]
    apply (Finsupp.filter_eq_self_iff _ _).mpr
    intro t ht
    by_contra h
    apply ht
    exact cubeSquareSubdivision_eq_zero_off_top d v w hne hs t (by simpa [hdc] using h)
  · rw [if_neg hdc]
    apply (Finsupp.filter_eq_zero_iff _ _).mpr
    intro t ht
    apply cubeSquareSubdivision_eq_zero_off_top
    intro he
    exact hdc (he.symm.trans ht)

end FiniteChains.Davis

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V C : Type} [DecidableEq V] {A : CommRel V}
  (cell : C → QCube A) (left right : C → V)
  (hne : ∀ i, left i ≠ right i) (hspx : ∀ i, (cell i).spx = {left i, right i})

def squareChainSubdivision : (C →₀ ℤ) →ₗ[ℤ]
    ((strictOrderCx (QCube A)).F →₀ ℤ) :=
  Finsupp.linearCombination ℤ
    (fun i => cubeSquareSubdivision (cell i) (left i) (right i) (hne i) (hspx i))

theorem squareChainSubdivision_filter_top (hcell : Function.Injective cell)
    (z : C →₀ ℤ) (i : C) :
    (squareChainSubdivision cell left right hne hspx z).filter
      (fun t : (strictOrderCx (QCube A)).F => t.1.2.2 = cell i) =
      z i • cubeSquareSubdivision (cell i) (left i) (right i) (hne i) (hspx i) := by
  induction z using Finsupp.induction_linear with
  | zero => simp [Finsupp.filter_zero]
  | add z w hz hw =>
      rw [map_add, Finsupp.filter_add, hz, hw, Finsupp.add_apply, add_smul]
  | single j n =>
      rw [squareChainSubdivision, Finsupp.linearCombination_single,
        Finsupp.filter_smul, cubeSquareSubdivision_filter_top]
      by_cases hji : j = i
      · subst j
        simp
      · have hci : cell j ≠ cell i := fun h => hji (hcell h)
        simp [hci, hji]

end FiniteChains.Davis
end

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V C : Type} [DecidableEq V] {A : CommRel V}
  (cell : C → QCube A) (left right : C → V)
  (hne : ∀ i, left i ≠ right i) (hspx : ∀ i, (cell i).spx = {left i, right i})

def squareChainEdgeBoundary : (C →₀ ℤ) →ₗ[ℤ]
    ((strictOrderCx (QCube A)).E →₀ ℤ) :=
  Finsupp.linearCombination ℤ
    (fun i => cubeSquareEdgeBoundary (cell i) (left i) (right i) (hne i) (hspx i))

theorem squareChainSubdivision_boundary (z : C →₀ ℤ) :
    Comb.bdry2 (strictOrderCx (QCube A))
      (squareChainSubdivision cell left right hne hspx z) =
      squareChainEdgeBoundary cell left right hne hspx z := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => simp_all
  | single i n =>
      rw [squareChainSubdivision, Finsupp.linearCombination_single, map_smul,
        cubeSquareSubdivision_boundary, squareChainEdgeBoundary,
        Finsupp.linearCombination_single]

end FiniteChains.Davis

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V C : Type} [DecidableEq V] {A : CommRel V}
  (cell : C → QCube A) (left right : C → V)
  (hne : ∀ i, left i ≠ right i) (hspx : ∀ i, (cell i).spx = {left i, right i})

def squareCoefficientFlag (i : C) : (strictOrderCx (QCube A)).F :=
  squareFlag (cell i) (left i) (right i) (hne i) (hspx i) (false, 0, false)


def squareCycleCoefficients (hcell : Function.Injective cell) :
    ((strictOrderCx (QCube A)).F →₀ ℤ) →ₗ[ℤ] (C →₀ ℤ) :=
  Finsupp.lcomapDomain (squareCoefficientFlag cell left right hne hspx)
    (by
      intro i j h
      have ht := congrArg (fun t : (strictOrderCx (QCube A)).F => t.1.2.2) h
      simp only [squareCoefficientFlag, squareFlag_top] at ht
      exact hcell ht)

theorem squareChainSubdivision_off_cells (r : C →₀ ℤ)
    (t : (strictOrderCx (QCube A)).F) (ht : ∀ i, t.1.2.2 ≠ cell i) :
    squareChainSubdivision cell left right hne hspx r t = 0 := by
  induction r using Finsupp.induction_linear with
  | zero => simp
  | add r s hr hs => simp_all
  | single i n =>
      rw [squareChainSubdivision, Finsupp.linearCombination_single, Finsupp.smul_apply,
        cubeSquareSubdivision_eq_zero_off_top _ _ _ _ _ _ (ht i), smul_zero]

/-- Every actual strict two-cycle of dimension at most two is the subdivision of its
finite recovered cubical coefficient chain. -/
theorem cubeTwoCycle_is_squareSubdivision (hcell : Function.Injective cell)
    (hcover : ∀ c : QCube A, c.spx.card = 2 → ∃ i, cell i = c)
    (z : (strictOrderCx (QCube A)).F →₀ ℤ)
    (hz : ∀ t ∈ z.support, t.1.2.2.spx.card ≤ 2)
    (hcycle : Comb.bdry2 (strictOrderCx (QCube A)) z = 0) :
    z = squareChainSubdivision cell left right hne hspx
      (squareCycleCoefficients cell left right hne hspx hcell z) := by
  ext t
  by_cases hdim : t.1.2.2.spx.card = 2
  · obtain ⟨i, hi⟩ := hcover t.1.2.2 hdim
    have hti  := hi.symm
    have hl := congrArg (fun w : (strictOrderCx (QCube A)).F →₀ ℤ => w t)
      (cubeTwoCycle_square_component (cell i) (left i) (right i) (hne i) (hspx i)
        z hz hcycle)
    have hr := congrArg (fun w : (strictOrderCx (QCube A)).F →₀ ℤ => w t)
      (squareChainSubdivision_filter_top cell left right hne hspx hcell
        (squareCycleCoefficients cell left right hne hspx hcell z) i)
    simp only [Finsupp.filter_apply, hti, Finsupp.smul_apply] at hl hr
    exact hl.trans hr.symm
  · have hzt : z t = 0 := by
      by_contra hzt
      exact hdim (qCube_triangle_dimensions t (hz t (Finsupp.mem_support_iff.mpr hzt))).2.2
    rw [hzt]
    symm
    apply squareChainSubdivision_off_cells
    intro i he
    apply hdim
    rw [he, hspx i]
    simp [hne i]

/-- The recovered cubical coefficients are genuine cycles for the facet boundary map. -/
theorem cubeTwoCycle_coefficients_cycle (hcell : Function.Injective cell)
    (hcover : ∀ c : QCube A, c.spx.card = 2 → ∃ i, cell i = c)
    (z : (strictOrderCx (QCube A)).F →₀ ℤ)
    (hz : ∀ t ∈ z.support, t.1.2.2.spx.card ≤ 2)
    (hcycle : Comb.bdry2 (strictOrderCx (QCube A)) z = 0) :
    squareChainEdgeBoundary cell left right hne hspx
      (squareCycleCoefficients cell left right hne hspx hcell z) = 0 := by
  rw [← squareChainSubdivision_boundary,
    ← cubeTwoCycle_is_squareSubdivision cell left right hne hspx hcell hcover z hz hcycle]
  exact hcycle

end FiniteChains.Davis

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [LinearOrder V] {A : CommRel V}

abbrev QSquare (A : CommRel V) := {c : QCube A // c.spx.card = 2}

def qSquareFrame (c : QSquare A) :
    {p : V × V // p.2 < p.1 ∧ c.1.spx = {p.1, p.2}} := by
  apply Classical.choice
  obtain ⟨a, b, hne, hs⟩ := Finset.card_eq_two.mp c.2
  rcases lt_or_gt_of_ne hne with hab | hba
  · exact ⟨⟨(b, a), hab, by simpa [Finset.pair_comm] using hs⟩⟩
  · exact ⟨⟨(a, b), hba, hs⟩⟩

def qSquareLeft (c : QSquare A) : V := (qSquareFrame c).1.1
def qSquareRight (c : QSquare A) : V := (qSquareFrame c).1.2

theorem qSquare_directions_ne (c : QSquare A) : qSquareLeft c ≠ qSquareRight c :=
  Ne.symm (qSquareFrame c).2.1.ne

theorem qSquare_directions_decreasing (c : QSquare A) : qSquareRight c < qSquareLeft c :=
  (qSquareFrame c).2.1

theorem qSquare_free_directions (c : QSquare A) : c.1.spx = {qSquareLeft c, qSquareRight c} :=
  (qSquareFrame c).2.2

def qSquareChainSubdivision : (QSquare A →₀ ℤ) →ₗ[ℤ]
    ((strictOrderCx (QCube A)).F →₀ ℤ) :=
  squareChainSubdivision Subtype.val qSquareLeft qSquareRight
    qSquare_directions_ne qSquare_free_directions

def qSquareCycleCoefficients : ((strictOrderCx (QCube A)).F →₀ ℤ) →ₗ[ℤ]
    (QSquare A →₀ ℤ) :=
  squareCycleCoefficients Subtype.val qSquareLeft qSquareRight
    qSquare_directions_ne qSquare_free_directions Subtype.val_injective

def qSquareFacetBoundary : (QSquare A →₀ ℤ) →ₗ[ℤ]
    ((strictOrderCx (QCube A)).E →₀ ℤ) :=
  squareChainEdgeBoundary Subtype.val qSquareLeft qSquareRight
    qSquare_directions_ne qSquare_free_directions

/-- Every actual strict two-cycle supported in cube dimension at most two is exactly the
subdivision of its finite integer chain on the actual square cells. -/
theorem qCube_twoCycle_reconstruction (z : (strictOrderCx (QCube A)).F →₀ ℤ)
    (hz : ∀ t ∈ z.support, t.1.2.2.spx.card ≤ 2)
    (hcycle : Comb.bdry2 (strictOrderCx (QCube A)) z = 0) :
    qSquareChainSubdivision (qSquareCycleCoefficients z) = z :=
  (cubeTwoCycle_is_squareSubdivision Subtype.val qSquareLeft qSquareRight
    qSquare_directions_ne qSquare_free_directions Subtype.val_injective
    (fun c hc => ⟨⟨c, hc⟩, rfl⟩) z hz hcycle).symm

theorem qCube_twoCycle_coefficients_cycle (z : (strictOrderCx (QCube A)).F →₀ ℤ)
    (hz : ∀ t ∈ z.support, t.1.2.2.spx.card ≤ 2)
    (hcycle : Comb.bdry2 (strictOrderCx (QCube A)) z = 0) :
    qSquareFacetBoundary (qSquareCycleCoefficients z) = 0 :=
  cubeTwoCycle_coefficients_cycle Subtype.val qSquareLeft qSquareRight
    qSquare_directions_ne qSquare_free_directions Subtype.val_injective
    (fun c hc => ⟨⟨c, hc⟩, rfl⟩) z hz hcycle

/-- Recovering coefficients is a left inverse on all finite chains of actual square cells. -/
theorem qSquare_coefficients_subdivision (r : QSquare A →₀ ℤ) :
    qSquareCycleCoefficients (qSquareChainSubdivision r) = r := by
  ext c
  change qSquareChainSubdivision r
    (squareFlag c.1 (qSquareLeft c) (qSquareRight c) (qSquare_directions_ne c)
      (qSquare_free_directions c) (false, 0, false)) = r c
  have he := congrArg (fun z : (strictOrderCx (QCube A)).F →₀ ℤ =>
      z (squareFlag c.1 (qSquareLeft c) (qSquareRight c) (qSquare_directions_ne c)
        (qSquare_free_directions c) (false, 0, false)))
    (squareChainSubdivision_filter_top Subtype.val qSquareLeft qSquareRight
      qSquare_directions_ne qSquare_free_directions Subtype.val_injective r c)
  have hc := squareSubdivision_flag_coefficient c.1 (qSquareLeft c) (qSquareRight c)
    (qSquare_directions_ne c) (qSquare_free_directions c) (false, 0, false)
  simp only [squareFlagSign] at hc
  norm_num at hc
  simpa only [if_true, qSquareChainSubdivision, Finsupp.filter_apply, squareFlag_top, Finsupp.smul_apply, hc,
    smul_eq_mul, mul_one] using he

end FiniteChains.Davis

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

def qCubeFacetIndex (c : QCube A) (i : {v : V // v ∈ c.spx} × ZMod 2) : QCube A :=
  qCubeFacet c i.1.1 i.2

theorem qCubeFacetIndex_injective (c : QCube A) : Function.Injective (qCubeFacetIndex c) := by
  intro ⟨⟨v, hv⟩, s⟩ ⟨⟨w, hw⟩, t⟩ h
  have he : c.spx.erase v = c.spx.erase w := congrArg QCube.spx h
  have hvw : v = w := by
    by_contra hvw
    have hm  := Finset.mem_erase.mpr ⟨hvw, hv⟩
    rw [← he] at hm
    exact (Finset.notMem_erase v c.spx) hm
  subst w
  have hst := congrArg (fun d : QCube A => d.sgn v) h
  simp only [qCubeFacetIndex, qCubeFacet_sgn_self] at hst
  exact Prod.ext (Subtype.ext rfl) hst

def qThreeFacetSquare (c : QCube A) (hc : c.spx.card = 3)
    (i : {v : V // v ∈ c.spx} × ZMod 2) : QSquare A :=
  ⟨qCubeFacetIndex c i, by
    change (c.spx.erase i.1.1).card = 2
    rw [Finset.card_erase_of_mem i.1.2, hc]⟩

theorem qThreeFacetSquare_injective (c : QCube A) (hc : c.spx.card = 3) :
    Function.Injective (qThreeFacetSquare c hc) := by
  intro i j h
  exact qCubeFacetIndex_injective c (congrArg Subtype.val h)

end FiniteChains.Davis

section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Davis

def fixedCoordinateSign (s : ZMod 2) : ℤ := if s = 0 then 1 else -1

def threeFacetBoundaryColumn (i : Fin 3 × ZMod 2) :
    (Fin 3 × ZMod 2 × ZMod 2) →₀ ℤ :=
  if i.1 = 0 then
    -Finsupp.single (0, i.2, 0) 1 + Finsupp.single (0, i.2, 1) 1 +
      Finsupp.single (1, i.2, 0) 1 - Finsupp.single (1, i.2, 1) 1
  else if i.1 = 1 then
    -Finsupp.single (0, 0, i.2) 1 + Finsupp.single (0, 1, i.2) 1 +
      Finsupp.single (2, i.2, 0) 1 - Finsupp.single (2, i.2, 1) 1
  else
    -Finsupp.single (1, 0, i.2) 1 + Finsupp.single (1, 1, i.2) 1 +
      Finsupp.single (2, 0, i.2) 1 - Finsupp.single (2, 1, i.2) 1

def threeFacetBoundaryMatrix : ((Fin 3 × ZMod 2) →₀ ℤ) →ₗ[ℤ]
    ((Fin 3 × ZMod 2 × ZMod 2) →₀ ℤ) :=
  Finsupp.linearCombination ℤ threeFacetBoundaryColumn

set_option maxHeartbeats 1000000

theorem threeFacetBoundaryMatrix_row0 (r : (Fin 3 × ZMod 2) →₀ ℤ) (s t : ZMod 2) :
    threeFacetBoundaryMatrix r (0, s, t) =
      -fixedCoordinateSign t * r (0, s) - fixedCoordinateSign s * r (1, t) := by
  induction r using Finsupp.induction_linear with
  | zero => simp
  | add r q hr hq => simp only [map_add, Finsupp.add_apply, hr, hq]; ring
  | single i n =>
      obtain ⟨e, u⟩ := i
      fin_cases e <;> fin_cases u <;> fin_cases s <;> fin_cases t <;>
        norm_num [threeFacetBoundaryMatrix, threeFacetBoundaryColumn, fixedCoordinateSign,
          Finsupp.single_apply, Prod.mk.injEq]

theorem threeFacetBoundaryMatrix_row1 (r : (Fin 3 × ZMod 2) →₀ ℤ) (s t : ZMod 2) :
    threeFacetBoundaryMatrix r (1, s, t) =
      fixedCoordinateSign t * r (0, s) - fixedCoordinateSign s * r (2, t) := by
  induction r using Finsupp.induction_linear with
  | zero => simp
  | add r q hr hq => simp only [map_add, Finsupp.add_apply, hr, hq]; ring
  | single i n =>
      obtain ⟨e, u⟩ := i
      fin_cases e <;> fin_cases u <;> fin_cases s <;> fin_cases t <;>
        norm_num [threeFacetBoundaryMatrix, threeFacetBoundaryColumn, fixedCoordinateSign,
          Finsupp.single_apply, Prod.mk.injEq]

def threeFacetOrientation (i : Fin 3 × ZMod 2) : ℤ :=
  (if i.1 = 1 then -1 else 1) * fixedCoordinateSign i.2

theorem threeFacetBoundaryMatrix_kernel (r : (Fin 3 × ZMod 2) →₀ ℤ)
    (hr : threeFacetBoundaryMatrix r = 0) :
    ∀ i, r i = r (0, 0) * threeFacetOrientation i := by
  have h00 := congrArg (fun z : (Fin 3 × ZMod 2 × ZMod 2) →₀ ℤ => z (0, 0, 0)) hr
  have h10 := congrArg (fun z : (Fin 3 × ZMod 2 × ZMod 2) →₀ ℤ => z (1, 0, 0)) hr
  have h01 := congrArg (fun z : (Fin 3 × ZMod 2 × ZMod 2) →₀ ℤ => z (0, 1, 0)) hr
  have h02 := congrArg (fun z : (Fin 3 × ZMod 2 × ZMod 2) →₀ ℤ => z (0, 0, 1)) hr
  have h12 := congrArg (fun z : (Fin 3 × ZMod 2 × ZMod 2) →₀ ℤ => z (1, 0, 1)) hr
  simp only [threeFacetBoundaryMatrix_row0, threeFacetBoundaryMatrix_row1,
    Finsupp.zero_apply] at h00 h10 h01 h02 h12
  norm_num [fixedCoordinateSign] at h00 h10 h01 h02 h12
  rintro ⟨e, s⟩
  fin_cases e
  · fin_cases s
    · change r (0, 0) = r (0, 0) * (1 : ℤ)
      norm_num
    · change r (0, 1) = r (0, 0) * (-1 : ℤ)
      norm_num
      omega
  · fin_cases s
    · change r (1, 0) = r (0, 0) * (-1 : ℤ)
      norm_num
      omega
    · change r (1, 1) = r (0, 0) * (1 : ℤ)
      norm_num
      omega
  · fin_cases s
    · change r (2, 0) = r (0, 0) * (1 : ℤ)
      norm_num
      omega
    · change r (2, 1) = r (0, 0) * (-1 : ℤ)
      norm_num
      omega

end FiniteChains.Davis

namespace FiniteChains.Davis

def threeOrientedFaces : (Fin 3 × ZMod 2) →₀ ℤ :=
  Finsupp.single (0, 0) 1 - Finsupp.single (0, 1) 1 -
  Finsupp.single (1, 0) 1 + Finsupp.single (1, 1) 1 +
  Finsupp.single (2, 0) 1 - Finsupp.single (2, 1) 1

theorem threeOrientedFaces_apply (i : Fin 3 × ZMod 2) :
    threeOrientedFaces i = threeFacetOrientation i := by
  obtain ⟨e, s⟩ := i
  fin_cases e <;> fin_cases s <;>
    norm_num [threeOrientedFaces, threeFacetOrientation, fixedCoordinateSign, Fin.ext_iff,
      Finsupp.single_apply, Prod.mk.injEq]

end FiniteChains.Davis
end

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [Fintype V] {A : CommRel V}

theorem qCubeToCoordinate_injective : Function.Injective (qCubeToCoordinate (A := A)) := by
  intro c d h
  apply qCubeCoordinateEquiv.injective
  exact Subtype.ext h

omit [Fintype V] in
/-- Freeing the fixed coordinate of an actual facet recovers its actual cube. -/
theorem qCubeFacet_coordinate_free (c : QCube A) (v : V) (hv : v ∈ c.spx)
    (s : ZMod 2) :
    Function.update (qCubeToCoordinate (qCubeFacet c v s)) v CubeCoord.free =
      qCubeToCoordinate c := by
  funext x
  by_cases hx : x = v
  · subst x
    simp [qCubeToCoordinate, hv]
  · simp [qCubeToCoordinate, qCubeFacet, hx]

/-- A nonfree coordinate that frees to a given cube lies in that cube's free set. -/
theorem coordinate_update_free_mem (g : Cube V) (c : QCube A) (v : V)
    (he : Function.update g v CubeCoord.free = qCubeToCoordinate c) : v ∈ c.spx := by
  have hval := congrFun he v
  have hfree : qCubeToCoordinate c v = CubeCoord.free := by simpa using hval.symm
  exact (freeSet_qCubeToCoordinate c) ▸ mem_freeSet.mpr hfree

omit [Fintype V] in
/-- Every nonfree coordinate cube that frees to an actual cube is its actual fixed facet. -/
theorem coordinate_update_free_facet (g : Cube V) (c : QCube A) (v : V)
    (hv : g v ≠ CubeCoord.free)
    (he : Function.update g v CubeCoord.free = qCubeToCoordinate c) :
    ∃ s : ZMod 2, g = qCubeToCoordinate (qCubeFacet c v s) := by
  have hother x (hx : x ≠ v) : g x = qCubeToCoordinate c x := by
    have h := congrFun he x
    simpa [Function.update_of_ne hx] using h
  cases hgv : g v with
  | free => simp_all
  | pos =>
      refine ⟨0, ?_⟩
      rw [qCubeFacet_coordinate_zero]
      funext x
      by_cases hx : x = v
      · simp_all
      · simp_all
  | neg =>
      refine ⟨1, ?_⟩
      rw [qCubeFacet_coordinate_one]
      funext x
      by_cases hx : x = v
      · simp_all
      · simp_all

variable [LinearOrder V]

/-- The coefficient of any actual fixed facet in the collapse's cubical boundary is
exactly its coordinate incidence. -/
theorem cubeBdry_actual_facet (c : QCube A) (v : V) (hv : v ∈ c.spx) (s : ZMod 2) :
    cubeBdry (qCubeToCoordinate c) (Sum.inl (qCubeToCoordinate (qCubeFacet c v s))) =
      incid (qCubeToCoordinate (qCubeFacet c v s)) v := by
  let g := qCubeToCoordinate (qCubeFacet c v s)
  have hfixed : g v ≠ CubeCoord.free := by
    by_cases hs : s = 0 <;> simp [g, qCubeToCoordinate, qCubeFacet, hs]
  have hmem : v ∈ Finset.univ.filter (fun x => g x ≠ CubeCoord.free) := by simp [hfixed]
  have he := qCubeFacet_coordinate_free c v hv s
  rw [cubeBdry_inl, Finset.sum_eq_single v]
  · simp_all
  · intro k hk hkv
    have hkfixed  := (Finset.mem_filter.mp hk).2
    rw [if_neg, mul_zero]
    intro hkfree
    exact hkv (update_free_injective hkfixed (hkfree.trans he.symm))
  · grind

/-- The collapse's ordinary cubical boundary has no coefficient outside actual facets. -/
theorem cubeBdry_zero_off_actual_facets (c : QCube A) (g : Cube V)
    (hg : ∀ v ∈ c.spx, ∀ s : ZMod 2, g ≠ qCubeToCoordinate (qCubeFacet c v s)) :
    cubeBdry (qCubeToCoordinate c) (Sum.inl g) = 0 := by
  rw [cubeBdry_inl]
  apply Finset.sum_eq_zero
  intro v hv
  rw [if_neg, mul_zero]
  intro he
  obtain ⟨s, hs⟩ := coordinate_update_free_facet g c v (Finset.mem_filter.mp hv).2 he
  exact hg v (coordinate_update_free_mem g c v he) s hs

end FiniteChains.Davis

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [Fintype V] [LinearOrder V] {A : CommRel V}

def qCubeCoordinateFacetChain (c : QCube A) : Cube V →₀ ℤ :=
  ∑ i : {v : V // v ∈ c.spx} × ZMod 2,
    Finsupp.single (qCubeToCoordinate (qCubeFacetIndex c i))
      (incid (qCubeToCoordinate (qCubeFacetIndex c i)) i.1.1)

/-- Every coefficient of the genuine finite coordinate facet chain is the ordinary
cubical boundary coefficient used by the truncated collapse. -/
theorem qCubeCoordinateFacetChain_apply (c : QCube A) (g : Cube V) :
    qCubeCoordinateFacetChain c g = cubeBdry (qCubeToCoordinate c) (Sum.inl g) := by
  have hinj  :=
    qCubeToCoordinate_injective.comp (qCubeFacetIndex_injective c)
  simp only [qCubeCoordinateFacetChain, Finsupp.finset_sum_apply]
  by_cases hg : ∃ i : {v : V // v ∈ c.spx} × ZMod 2,
      qCubeToCoordinate (qCubeFacetIndex c i) = g
  · obtain ⟨i, rfl⟩ := hg
    rw [Finset.sum_eq_single i]
    · simp
      exact (cubeBdry_actual_facet c i.1.1 i.1.2 i.2).symm
    · intro j _ hji
      have hne : qCubeToCoordinate (qCubeFacetIndex c j) ≠
          qCubeToCoordinate (qCubeFacetIndex c i) := fun h => hji (hinj h)
      simp [hne]
    · simp
  · have hzero : cubeBdry (qCubeToCoordinate c) (Sum.inl g) = 0 := by
      apply cubeBdry_zero_off_actual_facets
      intro v hv s he
      exact hg ⟨(⟨v, hv⟩, s), he.symm⟩
    rw [hzero]
    apply Finset.sum_eq_zero
    intro i _
    have hne : qCubeToCoordinate (qCubeFacetIndex c i) ≠ g := fun h => hg ⟨i, h⟩
    simp [hne]

end FiniteChains.Davis

namespace FiniteChains
open CategoryTheory CategoryTheory.Limits

/-- The actual free integral module agrees with the categorical coproduct of copies of ℤ. -/
def freeIntegerCoproductIso (ι : Type) :
    (ModuleCat.free ℤ).obj ι ≅
      (sigmaConst.obj (ModuleCat.of ℤ ℤ)).obj ι :=
  by
  classical
  exact (finsuppLequivDFinsupp ℤ).toModuleIso ≪≫
    (ModuleCat.coprodIsoDirectSum (fun _ : ι => ModuleCat.of ℤ ℤ)).symm

/-- Each actual coproduct injection corresponds to the actual finitely supported generator. -/
theorem freeIntegerCoproductIso_inv_ι (ι : Type) (i : ι) (n : ℤ) :
    (freeIntegerCoproductIso ι).inv (Sigma.ι (fun _ : ι => ModuleCat.of ℤ ℤ) i n) =
      Finsupp.single i n := by
  classical
  change (finsuppLequivDFinsupp ℤ).symm
    ((ModuleCat.coprodIsoDirectSum (fun _ : ι => ModuleCat.of ℤ ℤ)).hom
      (Sigma.ι (fun _ : ι => ModuleCat.of ℤ ℤ) i n)) = _
  have h := congrArg (fun k : ModuleCat.of ℤ ℤ ⟶
      ModuleCat.of ℤ (Π₀ _ : ι, ℤ) => k n)
    (ModuleCat.ι_coprodIsoDirectSum_hom (fun _ : ι => ModuleCat.of ℤ ℤ) i)
  change (ModuleCat.coprodIsoDirectSum (fun _ : ι => ModuleCat.of ℤ ℤ)).hom
    (Sigma.ι (fun _ : ι => ModuleCat.of ℤ ℤ) i n) =
      DirectSum.lof ℤ ι (fun _ : ι => ℤ) i n at h
  rw [h]
  exact DFinsupp.toFinsupp_single i n

/-- The inverse coefficient comparison is natural under arbitrary maps of index sets. -/
theorem freeIntegerCoproductIso_inv_natural {ι κ : Type} (f : ι → κ) :
    (sigmaConst.obj (ModuleCat.of ℤ ℤ)).map (TypeCat.ofHom f) ≫ (freeIntegerCoproductIso κ).inv =
      (freeIntegerCoproductIso ι).inv ≫ (ModuleCat.free ℤ).map (TypeCat.ofHom f) := by
  apply Sigma.hom_ext
  intro i
  apply ModuleCat.hom_ext
  ext
  simp [ModuleCat.free, sigmaConst]
  change (freeIntegerCoproductIso κ).inv
      (Sigma.ι (fun _ : κ => ModuleCat.of ℤ ℤ) (f i) 1) =
    Finsupp.mapDomain f ((freeIntegerCoproductIso ι).inv
      (Sigma.ι (fun _ : ι => ModuleCat.of ℤ ℤ) i 1))
  rw [freeIntegerCoproductIso_inv_ι, freeIntegerCoproductIso_inv_ι,
    Finsupp.mapDomain_single]

/-- The coefficient comparison is a genuine natural isomorphism of functors. -/
def freeIntegerCoproductNatIso :
    ModuleCat.free ℤ ≅ sigmaConst.obj (ModuleCat.of ℤ ℤ) :=
  NatIso.ofComponents freeIntegerCoproductIso (by
    intro ι κ f
    apply (cancel_mono (freeIntegerCoproductIso κ).inv).mp
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [show f = TypeCat.ofHom f.hom from rfl, freeIntegerCoproductIso_inv_natural, ← Category.assoc,
      Iso.hom_inv_id, Category.id_comp])

end FiniteChains

namespace FiniteChains
open CategoryTheory

/-- Free integral chains on the actual singular simplicial set are naturally
isomorphic to the actual Mathlib singular chain complex with integral coefficients. -/
def freeSingularChainComplexIso (X : TopCat.{0}) :
    AlgebraicTopology.AlternatingFaceMapComplex.obj (TopCat.toSSet.obj X ⋙ ModuleCat.free ℤ) ≅
      ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
        (ModuleCat.of ℤ ℤ)).obj X :=
  (AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{0} ℤ)).mapIso
    (CategoryTheory.Functor.isoWhiskerLeft (TopCat.toSSet.obj X) freeIntegerCoproductNatIso)

/-- Categorical homology of the free singular chains is genuine integral singular homology. -/
def freeSingularHomologyIso (X : TopCat.{0}) (n : ℕ) :
    (AlgebraicTopology.AlternatingFaceMapComplex.obj
      (TopCat.toSSet.obj X ⋙ ModuleCat.free ℤ)).homology n ≅
        (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
          (ModuleCat.of ℤ ℤ)).obj X) :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n).mapIso
    (freeSingularChainComplexIso X)

/-- The coefficient identification commutes with every actual continuous map. -/
theorem freeSingularChainComplexIso_natural {X Y : TopCat.{0}} (f : X ⟶ Y) :
    AlgebraicTopology.AlternatingFaceMapComplex.map
        (Functor.whiskerRight (TopCat.toSSet.map f) (ModuleCat.free ℤ)) ≫
      (freeSingularChainComplexIso Y).hom =
    (freeSingularChainComplexIso X).hom ≫
      (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
        (ModuleCat.of ℤ ℤ)).map f) := by
  change (AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{0} ℤ)).map _ ≫
      (AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{0} ℤ)).map _ =
    (AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{0} ℤ)).map _ ≫
      (AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{0} ℤ)).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  apply NatTrans.ext
  funext i
  exact freeIntegerCoproductNatIso.hom.naturality ((TopCat.toSSet.map f).app i)

/-- Naturality of the identification with integral singular homology in every degree. -/
theorem freeSingularHomologyIso_natural {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) :
    (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n).map
      (AlgebraicTopology.AlternatingFaceMapComplex.map
        (Functor.whiskerRight (TopCat.toSSet.map f) (ModuleCat.free ℤ))) ≫
      (freeSingularHomologyIso Y n).hom =
    (freeSingularHomologyIso X n).hom ≫
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
        (ModuleCat.of ℤ ℤ)).map f) := by
  change (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).map _ ≫
      (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).map _ =
    (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).map _ ≫
      (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).map _
  rw [← Functor.map_comp, ← Functor.map_comp, freeSingularChainComplexIso_natural]

end FiniteChains

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P]

def strictLowerIncl (c : P) : Hom (strictOrderCx (Set.Iio c)) (strictOrderCx P) :=
  strictOrderCxMap Subtype.val (fun _ _ h => h)

end FiniteChains.Comb

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

theorem threeFacet_uv_spx (c : QCube A) {u v w : V}
    (huw : u ≠ w) (hvw : v ≠ w) (hs : c.spx = {u, v, w}) (s : ZMod 2) :
    (qCubeFacet c w s).spx = {u, v} := by
  ext x
  simp only [qCubeFacet, hs, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
  grind

theorem threeFacet_uw_spx (c : QCube A) {u v w : V}
    (huv : u ≠ v) (hvw : v ≠ w) (hs : c.spx = {u, v, w}) (s : ZMod 2) :
    (qCubeFacet c v s).spx = {u, w} := by grind [threeFacet_uv_spx]

theorem threeFacet_vw_spx (c : QCube A) {u v w : V}
    (huv : u ≠ v) (huw : u ≠ w) (hs : c.spx = {u, v, w}) (s : ZMod 2) :
    (qCubeFacet c u s).spx = {v, w} := by grind [threeFacet_uv_spx]

def cubeThreeSquareBoundary (c : QCube A) (u v w : V)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (hs : c.spx = {u, v, w}) :
    (strictOrderCx (QCube A)).F →₀ ℤ :=
  cubeSquareSubdivision (qCubeFacet c w 0) u v huv (threeFacet_uv_spx c huw hvw hs 0) -
  cubeSquareSubdivision (qCubeFacet c w 1) u v huv (threeFacet_uv_spx c huw hvw hs 1) -
  cubeSquareSubdivision (qCubeFacet c v 0) u w huw (threeFacet_uw_spx c huv hvw hs 0) +
  cubeSquareSubdivision (qCubeFacet c v 1) u w huw (threeFacet_uw_spx c huv hvw hs 1) +
  cubeSquareSubdivision (qCubeFacet c u 0) v w hvw (threeFacet_vw_spx c huv huw hs 0) -
  cubeSquareSubdivision (qCubeFacet c u 1) v w hvw (threeFacet_vw_spx c huv huw hs 1)

end FiniteChains.Davis

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [Fintype V] [LinearOrder V] {A : CommRel V}

theorem qCubeFacet_incidence_zero (c : QCube A) (v : V) :
    incid (qCubeToCoordinate (qCubeFacet c v 0)) v =
      (-1 : ℤ) ^ ((c.spx.erase v).filter (fun i => i < v)).card := by
  simp [incid, freeSet_qCubeToCoordinate, qCubeToCoordinate, qCubeFacet, CubeCoord.sgn]

theorem qCubeFacet_incidence_one (c : QCube A) (v : V) :
    incid (qCubeToCoordinate (qCubeFacet c v 1)) v =
      -((-1 : ℤ) ^ ((c.spx.erase v).filter (fun i => i < v)).card) := by
  simp [incid, freeSet_qCubeToCoordinate, qCubeToCoordinate, qCubeFacet, CubeCoord.sgn]

/-- The six signs of an actual three-cube in decreasing coordinate order. -/
theorem threeFacet_incidence_zero (c : QCube A) {u v w : V}
    (huv : v < u) (hvw : w < v) (hs : c.spx = {u, v, w}) :
    incid (qCubeToCoordinate (qCubeFacet c w 0)) w = 1 ∧
    incid (qCubeToCoordinate (qCubeFacet c v 0)) v = -1 ∧
    incid (qCubeToCoordinate (qCubeFacet c u 0)) u = 1 := by
  have huw := hvw.trans huv
  have he : ({v, w} : Finset V).erase u = {v, w} :=
    Finset.erase_eq_of_notMem (by simp [Ne.symm huv.ne, Ne.symm huw.ne])
  simp [qCubeFacet_incidence_zero, hs, Finset.filter_erase, Finset.filter_insert, Finset.filter_singleton,
    huv, hvw, huw, not_lt_of_ge huv.le, not_lt_of_ge hvw.le, not_lt_of_ge huw.le,
    he, Ne.symm hvw.ne]

theorem threeFacet_incidence_one (c : QCube A) {u v w : V}
    (huv : v < u) (hvw : w < v) (hs : c.spx = {u, v, w}) :
    incid (qCubeToCoordinate (qCubeFacet c w 1)) w = -1 ∧
    incid (qCubeToCoordinate (qCubeFacet c v 1)) v = 1 ∧
    incid (qCubeToCoordinate (qCubeFacet c u 1)) u = -1 := by
  obtain ⟨hw, hv, hu⟩ := threeFacet_incidence_zero c huv hvw hs
  simp only [qCubeFacet_incidence_zero] at hw hv hu
  simp only [qCubeFacet_incidence_one, hw, hv, hu]
  norm_num

end FiniteChains.Davis

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [LinearOrder V] {A : CommRel V}

theorem qSquare_frame_unique (c : QSquare A) {a b : V}
    (h : b < a) (hs : c.1.spx = {a, b}) : qSquareLeft c = a ∧ qSquareRight c = b := by
  have hl : qSquareLeft c ∈ ({a, b} : Finset V) := by
    rw [← hs, qSquare_free_directions]
    simp
  have hr : qSquareRight c ∈ ({a, b} : Finset V) := by
    rw [← hs, qSquare_free_directions]
    simp
  simp at hl hr
  have horder := qSquare_directions_decreasing c
  grind


theorem qSquare_subdivision_single (c : QSquare A) (n : ℤ) {a b : V}
    (h : b < a) (hs : c.1.spx = {a, b}) :
    qSquareChainSubdivision (Finsupp.single c n) =
      n • cubeSquareSubdivision c.1 a b (Ne.symm h.ne) hs := by grind [qSquareChainSubdivision, squareChainSubdivision, Finsupp.linearCombination_single, qSquare_frame_unique]

end FiniteChains.Davis

section
open scoped Classical
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

abbrev QEdge (A : CommRel V) := {c : QCube A // c.spx.card = 1}

def qEdgeDirection (c : QEdge A) : V :=
  Classical.choose (Finset.card_eq_one.mp c.2)

omit [DecidableEq V] in
theorem qEdge_free_direction (c : QEdge A) : c.1.spx = {qEdgeDirection c} :=
  Classical.choose_spec (Finset.card_eq_one.mp c.2)


def qEdgeSubdivision (c : QEdge A) : (strictOrderCx (QCube A)).E →₀ ℤ :=
  oneCubeSubdivision c.1 (qEdgeDirection c) (qEdge_free_direction c)

theorem qEdgeSubdivision_eq (c : QEdge A) (v : V) (hs : c.1.spx = {v}) :
    qEdgeSubdivision c = oneCubeSubdivision c.1 v hs := by
  have he := (Finset.singleton_inj.mp ((qEdge_free_direction c).symm.trans hs))
  subst v
  rfl

def qEdgeChainSubdivision : (QEdge A →₀ ℤ) →ₗ[ℤ]
    ((strictOrderCx (QCube A)).E →₀ ℤ) :=
  Finsupp.linearCombination ℤ qEdgeSubdivision


theorem qEdgeChainSubdivision_filter_top (r : QEdge A →₀ ℤ) (c : QEdge A) :
    (qEdgeChainSubdivision r).filter
      (fun e : (strictOrderCx (QCube A)).E => e.1.2 = c.1) = r c • qEdgeSubdivision c := by
  induction r using Finsupp.induction_linear with
  | zero => simp [Finsupp.filter_zero]
  | add r s hr hs => rw [map_add, Finsupp.filter_add, hr, hs, Finsupp.add_apply, add_smul]
  | single d n =>
      rw [qEdgeChainSubdivision, Finsupp.linearCombination_single, Finsupp.filter_smul]
      change n • (cubeEdgeSubdivision d.1 (qEdgeDirection d)
        (by rw [qEdge_free_direction]; simp)).filter _ = _
      rw [cubeEdgeSubdivision_filter_tgt]
      by_cases hd : d = c
      · subst d
        simp [qEdgeSubdivision, oneCubeSubdivision]
      · have hdc : d.1 ≠ c.1 := fun h => hd (Subtype.ext h)
        simp [hd, hdc]

theorem qEdgeChainSubdivision_injective : Function.Injective (qEdgeChainSubdivision (A := A)) := by
  intro r s h
  have hz : qEdgeChainSubdivision (r - s) = 0 := by rw [map_sub, h, sub_self]
  have hr : r - s = 0 := by
    ext c
    have he := congrArg (Finsupp.filter
      (fun e : (strictOrderCx (QCube A)).E => e.1.2 = c.1)) hz
    rw [qEdgeChainSubdivision_filter_top, Finsupp.filter_zero] at he
    exact (smul_eq_zero.mp he).resolve_right (cubeEdgeSubdivision_ne_zero c.1 (qEdgeDirection c) (by rw [qEdge_free_direction]; simp))
  exact sub_eq_zero.mp hr

end FiniteChains.Davis
end

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [LinearOrder V] {A : CommRel V}

def qSquareSmallFacet (c : QSquare A) (s : ZMod 2) : QEdge A :=
  ⟨qCubeFacet c.1 (qSquareRight c) s, by
    rw [squareFacet_v_spx c.1 (qSquare_directions_ne c) (qSquare_free_directions c) s]
    simp⟩

def qSquareLargeFacet (c : QSquare A) (s : ZMod 2) : QEdge A :=
  ⟨qCubeFacet c.1 (qSquareLeft c) s, by
    rw [squareFacet_w_spx c.1 (qSquare_directions_ne c) (qSquare_free_directions c) s]
    simp⟩

def qSquareCubicalFaceBoundary (c : QSquare A) : QEdge A →₀ ℤ :=
  Finsupp.single (qSquareSmallFacet c 0) 1 - Finsupp.single (qSquareSmallFacet c 1) 1 -
    Finsupp.single (qSquareLargeFacet c 0) 1 + Finsupp.single (qSquareLargeFacet c 1) 1

def qSquareCubicalBoundary : (QSquare A →₀ ℤ) →ₗ[ℤ] (QEdge A →₀ ℤ) :=
  Finsupp.linearCombination ℤ qSquareCubicalFaceBoundary

omit [LinearOrder V] in
theorem qEdgeChainSubdivision_single (c : QEdge A) (n : ℤ) :
    qEdgeChainSubdivision (Finsupp.single c n) = n • qEdgeSubdivision c := by
  rw [qEdgeChainSubdivision, Finsupp.linearCombination_single]

theorem qEdgeSubdivision_smallFacet (c : QSquare A) (s : ZMod 2) :
    qEdgeSubdivision (qSquareSmallFacet c s) =
      oneCubeSubdivision (qCubeFacet c.1 (qSquareRight c) s) (qSquareLeft c)
        (squareFacet_v_spx c.1 (qSquare_directions_ne c) (qSquare_free_directions c) s) :=
  qEdgeSubdivision_eq _ _ _

theorem qEdgeSubdivision_largeFacet (c : QSquare A) (s : ZMod 2) :
    qEdgeSubdivision (qSquareLargeFacet c s) =
      oneCubeSubdivision (qCubeFacet c.1 (qSquareLeft c) s) (qSquareRight c)
        (squareFacet_w_spx c.1 (qSquare_directions_ne c) (qSquare_free_directions c) s) :=
  qEdgeSubdivision_eq _ _ _


/-- The actual cubical boundary commutes with the proved edge and square subdivisions. -/
theorem qSquareCubicalBoundary_subdivision (r : QSquare A →₀ ℤ) :
    qEdgeChainSubdivision (qSquareCubicalBoundary r) = qSquareFacetBoundary r := by
  induction r using Finsupp.induction_linear with
  | zero => simp
  | add r s hr hs => simp_all
  | single c n =>
      rw [qSquareCubicalBoundary, Finsupp.linearCombination_single, map_smul,
        (show qEdgeChainSubdivision (qSquareCubicalFaceBoundary c) =
      cubeSquareEdgeBoundary c.1 (qSquareLeft c) (qSquareRight c)
        (qSquare_directions_ne c) (qSquare_free_directions c) by
          rw [qSquareCubicalFaceBoundary, map_add, map_sub, map_sub]
          simp only [qEdgeChainSubdivision_single, one_smul,
            qEdgeSubdivision_smallFacet, qEdgeSubdivision_largeFacet]
          rfl), qSquareFacetBoundary,
        squareChainEdgeBoundary, Finsupp.linearCombination_single]

/-- Faithful edge subdivision reflects the actual cubical square-cycle equations. -/
theorem qSquareCubicalBoundary_zero_iff (r : QSquare A →₀ ℤ) :
    qSquareCubicalBoundary r = 0 ↔ qSquareFacetBoundary r = 0 := by
  constructor
  · intro h
    rw [← qSquareCubicalBoundary_subdivision, h, map_zero]
  · intro h
    apply qEdgeChainSubdivision_injective
    rwa [map_zero, qSquareCubicalBoundary_subdivision]

end FiniteChains.Davis

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [LinearOrder V] {A : CommRel V}

theorem qSquareSmallFacet_ordered (c : QSquare A) {a b : V}
    (h : b < a) (hs : c.1.spx = {a, b}) (s : ZMod 2) :
    (qSquareSmallFacet c s).1 = qCubeFacet c.1 b s := by
  obtain ⟨_, hr⟩ := qSquare_frame_unique c h hs
  change qCubeFacet c.1 (qSquareRight c) s = _
  rw [hr]

theorem qSquareLargeFacet_ordered (c : QSquare A) {a b : V}
    (h : b < a) (hs : c.1.spx = {a, b}) (s : ZMod 2) :
    (qSquareLargeFacet c s).1 = qCubeFacet c.1 a s := by
  obtain ⟨hl, _⟩ := qSquare_frame_unique c h hs
  change qCubeFacet c.1 (qSquareLeft c) s = _
  rw [hl]

end FiniteChains.Davis

section
open scoped Classical
namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

theorem strictTopConeEdgeChain_filter_top (f : P → Q) (hf : StrictMono f)
    (c : Q) (hc : ∀ x, f x < c) (z : (strictOrderCx P).E →₀ ℤ) :
    (strictTopConeEdgeChain f hf c hc z).filter
      (fun t : (strictOrderCx Q).F => t.1.2.2 = c) = strictTopConeEdgeChain f hf c hc z := by
  apply (Finsupp.filter_eq_self_iff _ _).mpr
  intro t ht
  by_contra htop
  exact ht (strictTopConeEdgeChain_eq_zero_off_top f hf c hc z t htop)

theorem strictLowerChain_filter_top (c : P) (z : (strictOrderCx (Set.Iio c)).F →₀ ℤ) :
    (chain2 (strictLowerIncl c) z).filter
      (fun t : (strictOrderCx P).F => t.1.2.2 = c) = 0 := by
  induction z using Finsupp.induction_linear with
  | zero => simp [Finsupp.filter_zero]
  | add z w hz hw => erw [map_add, Finsupp.filter_add, hz, hw, add_zero]
  | single t n =>
      change (Finsupp.mapDomain (strictLowerIncl c).onF (Finsupp.single t n)).filter _ = 0
      erw [Finsupp.mapDomain_single]
      apply Finsupp.filter_single_of_neg
      exact t.1.2.2.2.ne

/-- An actual tetrahedral fan has zero internal top boundary only if its base is a two-cycle. -/
theorem strictLowerCone_internal_boundary_reflects_cycle (c : P)
    (z : (strictOrderCx (Set.Iio c)).F →₀ ℤ)
    (hz : (strictOrdBoundary3
      (strictTopConeTriangleChain Subtype.val (fun _ _ h => h) c
        (fun x : Set.Iio c => x.2) z)).filter
          (fun t : (strictOrderCx P).F => t.1.2.2 = c) = 0) :
    bdry2 (strictOrderCx (Set.Iio c)) z = 0 := by
  have hzero := strictLowerChain_filter_top c z
  simp at hzero
  erw [strictTopConeTriangleChain_boundary, Finsupp.filter_sub,
    strictTopConeEdgeChain_filter_top, hzero, sub_zero] at hz
  apply strictTopConeEdgeChain_injective Subtype.val (fun _ _ h => h) c
    (fun x : Set.Iio c => x.2) Subtype.val_injective
  rwa [map_zero]

/-- Every genuine tetrahedron chain with this top vertex is the cone of an actual interval chain. -/
theorem exists_strictLowerConeChain (c : P) (y : StrictOrdTet P →₀ ℤ)
    (hy : ∀ t ∈ y.support, t.1.2.2.2 = c) :
    ∃ z : (strictOrderCx (Set.Iio c)).F →₀ ℤ,
      strictTopConeTriangleChain Subtype.val (fun _ _ h => h) c
        (fun x : Set.Iio c => x.2) z = y := by
  let f := strictTopConeTriangleTetrahedron Subtype.val (fun _ _ h => h) c
    (fun x : Set.Iio c => x.2)
  have hf : Function.Injective f := strictTopConeTriangleTetrahedron_injective _ _ _ _
    Subtype.val_injective
  refine ⟨y.comapDomain f hf.injOn, ?_⟩
  apply Finsupp.mapDomain_comapDomain _ hf
  intro t ht
  have he := hy t ht
  obtain ⟨⟨a, b, d, e⟩, hab, hbd, hde⟩ := t
  change e = c at he
  subst e
  refine ⟨⟨(⟨a, hab.trans (hbd.trans hde)⟩, ⟨b, hbd.trans hde⟩, ⟨d, hde⟩), hab, hbd⟩, ?_⟩
  rfl

/-- A top-supported tetrahedron chain without internal boundary has an actual lower two-cycle. -/
theorem exists_strictLowerConeCycle (c : P) (y : StrictOrdTet P →₀ ℤ)
    (hy : ∀ t ∈ y.support, t.1.2.2.2 = c)
    (hint : (strictOrdBoundary3 y).filter
      (fun t : (strictOrderCx P).F => t.1.2.2 = c) = 0) :
    ∃ z : (strictOrderCx (Set.Iio c)).F →₀ ℤ,
      bdry2 (strictOrderCx (Set.Iio c)) z = 0 ∧
      strictTopConeTriangleChain Subtype.val (fun _ _ h => h) c
        (fun x : Set.Iio c => x.2) z = y := by
  obtain ⟨z, hz⟩ := exists_strictLowerConeChain c y hy
  refine ⟨z, strictLowerCone_internal_boundary_reflects_cycle c z ?_, hz⟩
  rwa [hz]

end FiniteChains.Comb
end

section
open scoped Classical
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}



/-- In dimension at most three, only tetrahedra topped by this cube contribute to its
internal triangle boundary. -/
theorem qCube_boundary3_filter_top (c : QCube A) (hc : c.spx.card = 3)
    (y : StrictOrdTet (QCube A) →₀ ℤ)
    (hy : ∀ t ∈ y.support, t.1.2.2.2.spx.card ≤ 3) :
    (strictOrdBoundary3 y).filter
      (fun s : (strictOrderCx (QCube A)).F => s.1.2.2 = c) =
    (strictOrdBoundary3 (y.filter (fun t => t.1.2.2.2 = c))).filter
      (fun s : (strictOrderCx (QCube A)).F => s.1.2.2 = c) := by
  conv_lhs => erw [← y.sum_single]
  conv_rhs => erw [← y.sum_single]
  simp only [Finsupp.sum, map_sum, Finsupp.filter_sum]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases he : t.1.2.2.2 = c
  · simp_all
  · erw [Finsupp.filter_single_of_neg (fun t : StrictOrdTet (QCube A) => t.1.2.2.2 = c) he,
      map_zero, Finsupp.filter_zero]
    have hm : t.1.2.2.1 ≠ c := by
      intro hm
      have hd := (qCube_tetrahedron_dimensions t (hy t ht)).2.2.1
      erw [hm, hc] at hd
      omega
    exact (by
      erw [strictOrdBoundary3, Finsupp.linearCombination_single, Finsupp.filter_smul,
        (show (strictOrdTetBoundary t).filter
      (fun s : (strictOrderCx (QCube A)).F => s.1.2.2 = c) = 0 by
          simp only [strictOrdTetBoundary, Finsupp.filter_sub, Finsupp.filter_add]
          simp_all), smul_zero])

/-- A boundary supported in dimensions at most two has zero internal component at a three-cube. -/
theorem qCube_boundary3_internal_zero (c : QCube A) (hc : c.spx.card = 3)
    (y : StrictOrdTet (QCube A) →₀ ℤ)
    (hy : ∀ t ∈ y.support, t.1.2.2.2.spx.card ≤ 3)
    (hb : ∀ s ∈ (strictOrdBoundary3 y).support, s.1.2.2.spx.card ≤ 2) :
    (strictOrdBoundary3 (y.filter (fun t => t.1.2.2.2 = c))).filter
      (fun s : (strictOrderCx (QCube A)).F => s.1.2.2 = c) = 0 := by
  erw [← qCube_boundary3_filter_top c hc y hy]
  apply (Finsupp.filter_eq_zero_iff _ _).mpr
  intro s hs
  by_contra hsz
  have hd := hb s (Finsupp.mem_support_iff.mpr hsz)
  erw [hs, hc] at hd
  omega

/-- Every three-cube component of such a chain is a fan over a proved actual lower two-cycle. -/
theorem qCube_three_component_lower_cycle (c : QCube A) (hc : c.spx.card = 3)
    (y : StrictOrdTet (QCube A) →₀ ℤ)
    (hy : ∀ t ∈ y.support, t.1.2.2.2.spx.card ≤ 3)
    (hb : ∀ s ∈ (strictOrdBoundary3 y).support, s.1.2.2.spx.card ≤ 2) :
    ∃ z : (strictOrderCx (Set.Iio c)).F →₀ ℤ,
      Comb.bdry2 (strictOrderCx (Set.Iio c)) z = 0 ∧
      strictTopConeTriangleChain Subtype.val (fun _ _ h => h) c
        (fun x : Set.Iio c => x.2) z = y.filter (fun t => t.1.2.2.2 = c) := by
  apply exists_strictLowerConeCycle
  · simp
  · exact qCube_boundary3_internal_zero c hc y hy hb

end FiniteChains.Davis
end

section
open scoped Classical
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [LinearOrder V] {A : CommRel V}

omit [LinearOrder V] in
theorem qCubeLowerChain_dimension (c : QCube A) (hc : c.spx.card = 3)
    (z : (strictOrderCx (Set.Iio c)).F →₀ ℤ)
    (t : (strictOrderCx (QCube A)).F) (ht : t ∈ (chain2 (strictLowerIncl c) z).support) :
    t.1.2.2.spx.card ≤ 2 := by
  obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support ht)
  change s.1.2.2.1.spx.card ≤ 2
  have hd := qCube_card_lt_of_lt s.1.2.2.2
  erw [hc] at hd
  omega

/-- Recovered square coefficients of a lower-interval chain are supported on actual facets. -/
theorem qSquare_lower_coefficients_support (c : QCube A) (hc : c.spx.card = 3)
    (z : (strictOrderCx (Set.Iio c)).F →₀ ℤ) (s : QSquare A)
    (hs : s ∈ (qSquareCycleCoefficients (chain2 (strictLowerIncl c) z)).support) :
    ∃ v ∈ c.spx, s.1 = qCubeFacet c v 0 ∨ s.1 = qCubeFacet c v 1 := by
  have hn := Finsupp.mem_support_iff.mp hs
  change (chain2 (strictLowerIncl c) z)
    (squareFlag s.1 (qSquareLeft s) (qSquareRight s) (qSquare_directions_ne s)
      (qSquare_free_directions s) (false, 0, false)) ≠ 0 at hn
  have hmem := Finsupp.mem_support_iff.mpr hn
  obtain ⟨t, _, he⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hmem)
  have htop : t.1.2.2.1 = s.1 := by
    have h := congrArg (fun t : (strictOrderCx (QCube A)).F => t.1.2.2) he
    simpa only [strictLowerIncl, strictOrderCxMap, squareFlag_top] using h
  have hlt := t.1.2.2.2
  rw (config := { transparency := .default }) [htop] at hlt
  exact exists_qCube_zero_or_one_facet s.1 c hlt.le (by rw (config := { transparency := .default }) [hc, s.2])

/-- The isolated three-cube boundary is the negative subdivision of an actual finite
square cycle supported on that cube's six coordinate facets. -/
theorem qCube_three_component_facet_boundary (c : QCube A) (hc : c.spx.card = 3)
    (y : StrictOrdTet (QCube A) →₀ ℤ)
    (hy : ∀ t ∈ y.support, t.1.2.2.2.spx.card ≤ 3)
    (hb : ∀ s ∈ (strictOrdBoundary3 y).support, s.1.2.2.spx.card ≤ 2) :
    ∃ r : QSquare A →₀ ℤ,
      qSquareFacetBoundary r = 0 ∧
      (∀ s ∈ r.support, ∃ v ∈ c.spx, s.1 = qCubeFacet c v 0 ∨ s.1 = qCubeFacet c v 1) ∧
      qSquareChainSubdivision r = -strictOrdBoundary3 (y.filter (fun t => t.1.2.2.2 = c)) := by
  obtain ⟨z, hz, hfan⟩ := qCube_three_component_lower_cycle c hc y hy hb
  have hcycle : Comb.bdry2 (strictOrderCx (QCube A)) (chain2 (strictLowerIncl c) z) = 0 := by
    erw [bdry2_chain2, hz, map_zero]
  refine ⟨qSquareCycleCoefficients (chain2 (strictLowerIncl c) z),
    qCube_twoCycle_coefficients_cycle _ (qCubeLowerChain_dimension c hc z) hcycle,
    qSquare_lower_coefficients_support c hc z, ?_⟩
  erw [qCube_twoCycle_reconstruction _ (qCubeLowerChain_dimension c hc z) hcycle,
    ← hfan, strictTopConeTriangleChain_boundary, hz, map_zero, zero_sub, neg_neg]
  rfl

end FiniteChains.Davis
end

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

def qCubeDoubleFacet (c : QCube A) (a b : V) (s t : ZMod 2) : QCube A :=
  qCubeFacet (qCubeFacet c a s) b t

@[simp] theorem qCubeDoubleFacet_sgn_first (c : QCube A) (a b : V) (hne : a ≠ b)
    (s t : ZMod 2) : (qCubeDoubleFacet c a b s t).sgn a = s := by
  simp [qCubeDoubleFacet, qCubeFacet, hne]

@[simp] theorem qCubeDoubleFacet_sgn_second (c : QCube A) (a b : V)
    (s t : ZMod 2) : (qCubeDoubleFacet c a b s t).sgn b = t := by
  simp [qCubeDoubleFacet]

theorem qCubeDoubleFacet_signs_injective (c : QCube A) (a b : V) (hne : a ≠ b) :
    Function.Injective (fun i : ZMod 2 × ZMod 2 => qCubeDoubleFacet c a b i.1 i.2) := by
  intro ⟨s, t⟩ ⟨u, v⟩ h
  have hs := congrArg (fun d : QCube A => d.sgn a) h
  have ht := congrArg (fun d : QCube A => d.sgn b) h
  simp only [qCubeDoubleFacet_sgn_first _ _ _ hne] at hs
  simp at ht
  exact Prod.ext hs ht

theorem qCubeDoubleFacet_spx (c : QCube A) (a b : V) (s t : ZMod 2) :
    (qCubeDoubleFacet c a b s t).spx = (c.spx.erase a).erase b := rfl

def qThreeEdgeCell (c : QCube A) (u v w : V) (i : Fin 3 × ZMod 2 × ZMod 2) : QCube A :=
  if i.1 = 0 then qCubeDoubleFacet c u v i.2.1 i.2.2
  else if i.1 = 1 then qCubeDoubleFacet c u w i.2.1 i.2.2
  else qCubeDoubleFacet c v w i.2.1 i.2.2

theorem qThreeEdgeCell_spx (c : QCube A) (u v w : V)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (hs : c.spx = {u, v, w})
    (i : Fin 3 × ZMod 2 × ZMod 2) :
    (qThreeEdgeCell c u v w i).spx = if i.1 = 0 then {w} else if i.1 = 1 then {v} else {u} := by grind [qThreeEdgeCell, qCubeDoubleFacet_spx]

theorem qThreeEdgeCell_injective (c : QCube A) (u v w : V)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (hs : c.spx = {u, v, w}) :
    Function.Injective (qThreeEdgeCell c u v w) := by
  intro ⟨e, s, t⟩ ⟨f, a, b⟩ h
  have he := congrArg QCube.spx h
  rw [qThreeEdgeCell_spx c u v w huv huw hvw hs,
    qThreeEdgeCell_spx c u v w huv huw hvw hs] at he
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  fin_cases e <;> fin_cases f
  · have hp := qCubeDoubleFacet_signs_injective c u v huv h
    exact Prod.ext rfl hp
  · simp_all
  · simp_all
  · simp_all
  · have hp := qCubeDoubleFacet_signs_injective c u w huw h
    exact Prod.ext rfl hp
  · simp_all
  · simp_all
  · simp_all
  · have hp : (s, t) = (a, b) := qCubeDoubleFacet_signs_injective c v w hvw
      (by simpa [qThreeEdgeCell, h21] using h)
    exact Prod.ext rfl hp

/-- Each indexed codimension-two face is an actual edge cube. -/
def qThreeEdge (c : QCube A) (u v w : V)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (hs : c.spx = {u, v, w})
    (i : Fin 3 × ZMod 2 × ZMod 2) : QEdge A :=
  ⟨qThreeEdgeCell c u v w i, by
    rw [qThreeEdgeCell_spx c u v w huv huw hvw hs i]
    split_ifs <;> simp⟩

theorem qThreeEdge_injective (c : QCube A) (u v w : V)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (hs : c.spx = {u, v, w}) :
    Function.Injective (qThreeEdge c u v w huv huw hvw hs) := by
  intro i j h
  exact qThreeEdgeCell_injective c u v w huv huw hvw hs (congrArg Subtype.val h)

end FiniteChains.Davis

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

def qThreeDirection (u v w : V) (e : Fin 3) : V :=
  if e = 0 then u else if e = 1 then v else w

omit [DecidableEq V] in
theorem qThreeDirection_injective (u v w : V) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    Function.Injective (qThreeDirection u v w) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [qThreeDirection, Fin.ext_iff]

theorem qThreeDirection_mem (c : QCube A) (u v w : V) (hs : c.spx = {u, v, w})
    (e : Fin 3) : qThreeDirection u v w e ∈ c.spx := by
  fin_cases e <;> simp [qThreeDirection, hs, Fin.ext_iff]

theorem qCube_three_card (c : QCube A) (u v w : V)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (hs : c.spx = {u, v, w}) :
    c.spx.card = 3 := by simp [hs, huv, huw, hvw]

def qThreeFaceSquare (c : QCube A) (u v w : V)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (hs : c.spx = {u, v, w})
    (i : Fin 3 × ZMod 2) : QSquare A :=
  qThreeFacetSquare c (qCube_three_card c u v w huv huw hvw hs)
    (⟨qThreeDirection u v w i.1, qThreeDirection_mem c u v w hs i.1⟩, i.2)

theorem qThreeFaceSquare_injective (c : QCube A) (u v w : V)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (hs : c.spx = {u, v, w}) :
    Function.Injective (qThreeFaceSquare c u v w huv huw hvw hs) := by
  intro ⟨e, s⟩ ⟨f, t⟩ h
  have hp := qThreeFacetSquare_injective c (qCube_three_card c u v w huv huw hvw hs) h
  have hd := congrArg (fun i : {v : V // v ∈ c.spx} × ZMod 2 => i.1.1) hp
  have hsign := congrArg (fun i : {v : V // v ∈ c.spx} × ZMod 2 => i.2) hp
  exact Prod.ext (qThreeDirection_injective u v w huv huw hvw hd) hsign

/-- Every actual square facet occurs in the six-entry coordinate index. -/
theorem qThreeFaceSquare_exhaustive (c : QCube A) (u v w : V)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (hs : c.spx = {u, v, w})
    (s : QSquare A) (hslt : s.1 < c) :
    ∃ i : Fin 3 × ZMod 2, qThreeFaceSquare c u v w huv huw hvw hs i = s := by
  obtain ⟨a, ha, he⟩ := exists_qCube_facet_of_card s.1 c hslt.le
    (by rw [qCube_three_card c u v w huv huw hvw hs, s.2])
  rw [hs, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with ha | ha | ha
  · subst a
    exact ⟨(0, s.1.sgn u), Subtype.ext he.symm⟩
  · subst a
    exact ⟨(1, s.1.sgn v), Subtype.ext he.symm⟩
  · subst a
    refine ⟨(2, s.1.sgn w), Subtype.ext ?_⟩
    have h21 : (2 : Fin 3) ≠ 1 := by decide
    simpa [qThreeFaceSquare, qThreeFacetSquare, qCubeFacetIndex, qThreeDirection, h21] using he.symm

end FiniteChains.Davis
