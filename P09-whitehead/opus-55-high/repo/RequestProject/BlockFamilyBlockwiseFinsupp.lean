import RequestProject.BlockFamilySubst
import RequestProject.FoxFinsupp


/-!
Arbitrary-family assembly of the block-local surface-generation statement.

The block family, retained relators, and the relators of an individual block
may all be infinite. Every chain below is finitely supported in its cell
indices as well as in its group coefficients. In particular, the polygon
coefficients are chosen to be zero outside the blocks occupied by the input
chain. This is the support argument missing from the finite-family assembly.

The geometric block-local B2 statement remains an explicit hypothesis. The
results here construct its global chain preimage and the cancelling-cylinder
relative filling; they do not assume global generation or relative exactness.

This new source has not been compiled under the current no-checkpoint workflow.
-/

noncomputable section

namespace FiniteChains.BlockFamily

universe u

section Chains

variable {Jr Sx R : Type u} {Mt : Sx → Type u} [Ring R]

/-- The part of a two-chain supported on the substituted blocks. -/
def fsBlockPart (x : (Jr ⊕ (Σ s, Mt s)) →₀ R) :=
  x.comapDomain Sum.inr Sum.inr_injective.injOn

/-- The actual finitely supported chain in one block. -/
def fsBlockSlice (x : (Jr ⊕ (Σ s, Mt s)) →₀ R) s :=
  (fsBlockPart x).split s

@[simp] theorem fsBlockSlice_apply (x : (Jr ⊕ (Σ s, Mt s)) →₀ R)
    s m : fsBlockSlice x s m = x (Sum.inr ⟨s, m⟩) := rfl

/-- Only the finitely many occupied block labels are needed for coefficients. -/
def fsBlockSupport (x : (Jr ⊕ (Σ s, Mt s)) →₀ R) :=
  (fsBlockPart x).splitSupport

theorem fsBlockSlice_eq_zero_of_not_mem (x : (Jr ⊕ (Σ s, Mt s)) →₀ R)
    {s} (hs : s ∉ fsBlockSupport x) : fsBlockSlice x s = 0 := by
  by_contra h
  exact hs ((Finsupp.mem_splitSupport_iff_nonzero _ s).mpr h)

/-- A finitely supported family of polygon coefficients expands along the
actual finitely supported surface chains. -/
def fsFillBlocks (c : ∀ s, Mt s →₀ R) (w : Sx →₀ R) : (Σ s, Mt s) →₀ R := by
  classical
  refine Finsupp.onFinset (w.support.sigma fun s => (c s).support)
    (fun p => w p.1 * c p.1 p.2) ?_
  grind

@[simp] theorem fsFillBlocks_apply c (w : Sx →₀ R)
    (p : Σ s, Mt s) : fsFillBlocks c w p = w p.1 * c p.1 p.2 := rfl

/-- The substituted two-chain map after extending coefficients to the target
ring: retain old cells and replace each polygon by its chosen surface chain. -/
def fsCellsBase (c : ∀ s, Mt s →₀ R) :
    ((Jr ⊕ Sx) →₀ R) →ₗ[R] ((Jr ⊕ (Σ s, Mt s)) →₀ R) where
  toFun y := Finsupp.sumElim
    (y.comapDomain Sum.inl Sum.inl_injective.injOn)
    (fsFillBlocks c (y.comapDomain Sum.inr Sum.inr_injective.injOn))
  map_add' y z := by
    aesop
  map_smul' a y := by
    ext k
    cases k with
    | inl j => rfl
    | inr p =>
        exact mul_assoc _ _ _

@[simp] theorem fsCellsBase_inl (c : ∀ s, Mt s →₀ R)
    y (j : Jr) :
    fsCellsBase c y (Sum.inl j) = y (Sum.inl j) := rfl

@[simp] theorem fsCellsBase_inr c
    (y : (Jr ⊕ Sx) →₀ R) s (m : Mt s) :
    fsCellsBase c y (Sum.inr ⟨s, m⟩) = y (Sum.inr s) * c s m := rfl

/-- Local witnesses can be selected with finite support, even if zero blocks
admit nonzero scalar witnesses. Thus no injectivity of a surface chain is
needed to obtain finitely supported polygon coefficients. -/
theorem exists_fsBlockCoefficients (c : ∀ s, Mt s →₀ R)
    (x : (Jr ⊕ (Σ s, Mt s)) →₀ R)
    (h : ∀ s, ∃ a, ∀ m, x (Sum.inr ⟨s, m⟩) = a * c s m) :
    ∃ w : Sx →₀ R, w.support ⊆ fsBlockSupport x ∧
      ∀ s m, x (Sum.inr ⟨s, m⟩) = w s * c s m := by
  classical
  choose a ha using h
  let w := Finsupp.onFinset (fsBlockSupport x)
    (fun s => if s ∈ fsBlockSupport x then a s else 0)
    (by simp_all)
  refine ⟨w, Finsupp.support_onFinset_subset, ?_⟩
  intro s m
  by_cases hs : s ∈ fsBlockSupport x
  · grind
  · have hz := congrArg (· m)
      (fsBlockSlice_eq_zero_of_not_mem x hs)
    aesop

/-- Assemble the local surface coefficients and the retained coefficients into
an actual preimage of the full substituted two-chain. -/
theorem exists_fsCellsBase_preimage c
    (x : (Jr ⊕ (Σ s, Mt s)) →₀ R)
    (h : ∀ s, ∃ a, ∀ m, x (Sum.inr ⟨s, m⟩) = a * c s m) :
    ∃ y, fsCellsBase c y = x ∧
      (∀ j, y (Sum.inl j) = x (Sum.inl j)) ∧
      (y.comapDomain Sum.inr Sum.inr_injective.injOn).support ⊆ fsBlockSupport x := by
  obtain ⟨w, hw, he⟩ := exists_fsBlockCoefficients c x h
  let y :=
    Finsupp.sumElim (x.comapDomain Sum.inl Sum.inl_injective.injOn) w
  refine ⟨y, ?_, fun _ => rfl, ?_⟩
  · aesop
  aesop

end Chains

section Fox

variable {α Jr Sx : Type u} {Zt Mt : Sx → Type u}
  [DecidableEq α] [DecidableEq Sx] [∀ s, DecidableEq (Zt s)]
  (ρ : Jr ⊕ Sx → FreeGroup α)
  (bsub : ∀ s, Mt s → FreeGroup (α ⊕ Zt s))

local notation "R'" => MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub))

/-- The existing genuine finitely supported Fox boundary, in matrix coordinates. -/
theorem fsCoverSecondBoundary_apply {A J : Type u} [DecidableEq A]
    σ (x : J →₀ MonoidAlgebra ℤ (PresGroup σ)) (i : A) :
    coverSecondBoundary (relSub σ) σ x i =
      x.sum (fun j a => a * foxMatrixPres σ i j) := by
  classical
  simp [coverSecondBoundary, Finsupp.linearCombination_apply, Finsupp.sum,
    Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul]
  rfl

/-- Internal coordinates of the actual substituted Fox boundary see exactly
one block, with a finite sum even for an infinite block-relator set. -/
theorem fsCoverSecondBoundary_inr
    (x : (Jr ⊕ (Σ s, Mt s)) →₀ R') s z :
    coverSecondBoundary (relSub (substPresF ρ bsub)) (substPresF ρ bsub) x
        (Sum.inr ⟨s, z⟩) =
      (fsBlockSlice x s).sum (fun m a => a *
        foxMatrixPres (substPresF ρ bsub) (Sum.inr ⟨s, z⟩) (Sum.inr ⟨s, m⟩)) := by
  classical
  rw [fsCoverSecondBoundary_apply]
  let old := x.comapDomain Sum.inl Sum.inl_injective.injOn
  let blocks := fsBlockPart x
  have hx : x = old.sumElim blocks := by
    aesop
  have ho : old.sum (fun j a => a *
      foxMatrixPres _ (Sum.inr ⟨s, z⟩) (Sum.inl j)) = 0 := by
    simp [foxMatrix_inr_inl ρ bsub]
  calc
    x.sum (fun k a => a * foxMatrixPres _ (Sum.inr ⟨s, z⟩) k) =
        old.sum (fun j a => a *
          foxMatrixPres _ (Sum.inr ⟨s, z⟩) (Sum.inl j)) +
        blocks.sum (fun p a => a *
          foxMatrixPres _ (Sum.inr ⟨s, z⟩) (Sum.inr p)) := by
      rw [hx, Finsupp.sum_sumElim]
      rfl
    _ = blocks.sum (fun p a => a *
        foxMatrixPres _ (Sum.inr ⟨s, z⟩) (Sum.inr p)) := by
      simp_all
    _ = (fsBlockSlice x s).sum (fun m a => a *
        foxMatrixPres _ (Sum.inr ⟨s, z⟩) (Sum.inr ⟨s, m⟩)) := by
      rw [Finsupp.sigma_sum]
      apply Finset.sum_eq_single s
      · intro t _ hts
        simp [foxMatrix_inr_inr_of_ne ρ bsub hts z]
      · intro hs
        have hz : blocks.split s = 0 := by
          by_contra h
          exact hs ((blocks.mem_splitSupport_iff_nonzero s).mpr h)
        simp_all

/-- The geometric block-local B2 input, with genuine finite support in the
block relators and coefficients in the whole substituted presentation group. -/
def BlockSurfaceGeneratesFS (c : ∀ s, Mt s →₀ R') :=
  ∀ (s : Sx) (β : Mt s →₀ R'),
    (∀ z, β.sum (fun m a => a *
      foxMatrixPres _ (Sum.inr ⟨s, z⟩) (Sum.inr ⟨s, m⟩)) = 0) →
    ∃ w : R', ∀ m, β m = w * c s m

/-- A finite-block geometric B2 calculation feeds the arbitrary-family
assembly directly. Only each individual block's relator set is finite;
the ambient family and the retained presentation have no finiteness bound. -/
theorem blockSurfaceGeneratesFS_of_finite_blocks [∀ s, Fintype (Mt s)]
    c
    (hblock : ∀ s (β : Mt s → R'),
      (∀ z, ∑ m : Mt s, β m *
        foxMatrixPres (substPresF ρ bsub) (Sum.inr ⟨s, z⟩) (Sum.inr ⟨s, m⟩) = 0) →
      ∃ w, ∀ m, β m = w * c s m) :
    BlockSurfaceGeneratesFS ρ bsub c := by
  intro s β hβ
  apply hblock s β
  intro z
  rw [← Finsupp.sum_fintype β
    (fun m a => a * foxMatrixPres (substPresF ρ bsub)
      (Sum.inr ⟨s, z⟩) (Sum.inr ⟨s, m⟩)) (by simp)]
  exact hβ z

/-- Block-local B2 supplies a finite global preimage for every chain whose
actual Fox boundary lies entirely on the old generators. No finite-family
assumption and no global generation hypothesis is used. -/
theorem fsCellsBase_preimage_of_internal_zero c
    (hblock : BlockSurfaceGeneratesFS ρ bsub c)
    (x : (Jr ⊕ (Σ s, Mt s)) →₀ R')
    (hx : ∀ s z,
      coverSecondBoundary (relSub (substPresF ρ bsub)) (substPresF ρ bsub) x
        (Sum.inr ⟨s, z⟩) = 0) :
    ∃ y : (Jr ⊕ Sx) →₀ R', fsCellsBase c y = x ∧
      (∀ j, y (Sum.inl j) = x (Sum.inl j)) ∧
      (y.comapDomain Sum.inr Sum.inr_injective.injOn).support ⊆ fsBlockSupport x := by
  apply exists_fsCellsBase_preimage c x
  intro s
  apply hblock s (fsBlockSlice x s)
  simp_all [← fsCoverSecondBoundary_inr ρ bsub]

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
