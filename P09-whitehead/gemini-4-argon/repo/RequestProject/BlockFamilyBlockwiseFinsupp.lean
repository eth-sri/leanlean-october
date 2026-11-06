module

public import RequestProject.BlockFamilySubst
public import RequestProject.FoxFinsupp

@[expose] public section

noncomputable section

namespace FiniteChains.BlockFamily

universe u

section

variable {Jr Sx R : Type u} {Mt : Sx → Type u} [Ring R]

def fsBlockPart (x : (Jr ⊕ (Σ s, Mt s)) →₀ R) : (Σ s, Mt s) →₀ R :=
  x.comapDomain Sum.inr Sum.inr_injective.injOn

def fsBlockSupport (x : (Jr ⊕ (Σ s, Mt s)) →₀ R) : Finset Sx :=
  (fsBlockPart x).splitSupport

def fsFillBlocks (c : ∀ s, Mt s →₀ R) (w : Sx →₀ R) : (Σ s, Mt s) →₀ R := by
  classical
  refine Finsupp.onFinset (w.support.sigma fun s => (c s).support)
    (fun p => w p.1 * c p.1 p.2) fun p hp => Finset.mem_sigma.mpr
      ⟨Finsupp.mem_support_iff.mpr fun hw => hp (by change w p.1 * c p.1 p.2 = 0; rw [hw, zero_mul]),
       Finsupp.mem_support_iff.mpr fun hc => hp (by change w p.1 * c p.1 p.2 = 0; rw [hc, mul_zero])⟩

def fsCellsBase (c : ∀ s, Mt s →₀ R) :
    ((Jr ⊕ Sx) →₀ R) →ₗ[R] ((Jr ⊕ (Σ s, Mt s)) →₀ R) where
  toFun y := Finsupp.sumElim
    (y.comapDomain Sum.inl Sum.inl_injective.injOn)
    (fsFillBlocks c (y.comapDomain Sum.inr Sum.inr_injective.injOn))
  map_add' y z := by
    ext (j | p)
    · rfl
    · exact add_mul (y (Sum.inr p.1)) (z (Sum.inr p.1)) (c p.1 p.2)
  map_smul' a y := by
    ext (j | p)
    · rfl
    · exact mul_assoc a (y (Sum.inr p.1)) (c p.1 p.2)

@[simp] theorem fsCellsBase_inl (c : ∀ s, Mt s →₀ R) (y : (Jr ⊕ Sx) →₀ R) (j : Jr) :
    fsCellsBase c y (Sum.inl j) = y (Sum.inl j) := rfl

@[simp] theorem fsCellsBase_inr (c : ∀ s, Mt s →₀ R) (y : (Jr ⊕ Sx) →₀ R) (s : Sx) (m : Mt s) :
    fsCellsBase c y (Sum.inr ⟨s, m⟩) = y (Sum.inr s) * c s m := rfl

end

variable {α Jr Sx : Type u} {Zt Mt : Sx → Type u}
  [DecidableEq α] [DecidableEq Sx] [∀ s, DecidableEq (Zt s)]
  (ρ : Jr ⊕ Sx → FreeGroup α)
  (bsub : ∀ s, Mt s → FreeGroup (α ⊕ Zt s))

local notation "R'" => MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub))

theorem fsCoverSecondBoundary_apply {A J : Type u} [DecidableEq A]
    (σ : J → FreeGroup A) (x : J →₀ MonoidAlgebra ℤ (PresGroup σ)) (i : A) :
    coverSecondBoundary (relSub σ) σ x i = x.sum (fun j a => a * foxMatrixPres σ i j) := by
  classical
  simp only [coverSecondBoundary, Finsupp.linearCombination_apply, Finsupp.sum,
    Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul]; rfl

def BlockSurfaceGeneratesFS (c : ∀ s, Mt s →₀ R') : Prop :=
  ∀ (s : Sx) (β : Mt s →₀ R'),
    (∀ z : Zt s, β.sum (fun m a => a *
      foxMatrixPres (substPresF ρ bsub) (Sum.inr ⟨s, z⟩) (Sum.inr ⟨s, m⟩)) = 0) →
    ∃ w : R', ∀ m, β m = w * c s m

theorem blockSurfaceGeneratesFS_of_finite_blocks [∀ s, Fintype (Mt s)]
    (c : ∀ s, Mt s →₀ R')
    (hblock : ∀ (s : Sx) (β : Mt s → R'),
      (∀ z : Zt s, ∑ m : Mt s, β m *
        foxMatrixPres (substPresF ρ bsub) (Sum.inr ⟨s, z⟩) (Sum.inr ⟨s, m⟩) = 0) →
      ∃ w : R', ∀ m, β m = w * c s m) :
    BlockSurfaceGeneratesFS ρ bsub c :=
  fun s β hβ => hblock s β fun z => by
    rw [← Finsupp.sum_fintype β
      (fun m a => a * foxMatrixPres (substPresF ρ bsub) (Sum.inr ⟨s, z⟩) (Sum.inr ⟨s, m⟩))
      (fun _ => zero_mul _)]
    exact hβ z

theorem fsCellsBase_preimage_of_internal_zero (c : ∀ s, Mt s →₀ R')
    (hblock : BlockSurfaceGeneratesFS ρ bsub c)
    (x : (Jr ⊕ (Σ s, Mt s)) →₀ R')
    (hx : ∀ (s : Sx) (z : Zt s),
      coverSecondBoundary (relSub (substPresF ρ bsub)) (substPresF ρ bsub) x
        (Sum.inr ⟨s, z⟩) = 0) :
    ∃ y : (Jr ⊕ Sx) →₀ R', fsCellsBase c y = x ∧
      (∀ j, y (Sum.inl j) = x (Sum.inl j)) ∧
      (y.comapDomain Sum.inr Sum.inr_injective.injOn).support ⊆ fsBlockSupport x := by
  classical
  have hex (s : Sx) : ∃ a : R', ∀ m, x (Sum.inr ⟨s, m⟩) = a * c s m := by
    refine hblock s ((fsBlockPart x).split s) fun z => ?_
    let old := x.comapDomain Sum.inl Sum.inl_injective.injOn
    let blocks := fsBlockPart x
    have hx' : x = Finsupp.sumElim old blocks := by ext (k | k) <;> rfl
    have hsum : x.sum (fun k a => a * foxMatrixPres (substPresF ρ bsub) (Sum.inr ⟨s, z⟩) k) =
        blocks.sum (fun p a => a * foxMatrixPres (substPresF ρ bsub) (Sum.inr ⟨s, z⟩) (Sum.inr p)) := by
      have ho : old.sum (fun j a => a *
          foxMatrixPres (substPresF ρ bsub) (Sum.inr ⟨s, z⟩) (Sum.inl j)) = 0 := by
        simp [foxMatrix_inr_inl ρ bsub]
      rw [hx', Finsupp.sum_sumElim]
      change old.sum (fun j a => a * foxMatrixPres (substPresF ρ bsub) (Sum.inr ⟨s, z⟩) (Sum.inl j)) + _ = _
      rw [ho, zero_add]; rfl
    rw [← hx s z, fsCoverSecondBoundary_apply, hsum, Finsupp.sigma_sum]
    change (blocks.split s).sum (fun m a => a *
        foxMatrixPres (substPresF ρ bsub) (Sum.inr ⟨s, z⟩) (Sum.inr ⟨s, m⟩)) =
      ∑ t ∈ blocks.splitSupport, (blocks.split t).sum (fun m a => a *
        foxMatrixPres (substPresF ρ bsub) (Sum.inr ⟨s, z⟩) (Sum.inr ⟨t, m⟩))
    symm
    refine Finset.sum_eq_single s (fun t _ hts => by simp [foxMatrix_inr_inr_of_ne ρ bsub hts z])
      fun hs => ?_
    have hz : blocks.split s = 0 := by
      by_contra h; exact hs ((Finsupp.mem_splitSupport_iff_nonzero blocks s).mpr h)
    simp [hz]
  choose a ha using hex
  let w : Sx →₀ R' := Finsupp.onFinset (fsBlockSupport x)
    (fun s => if s ∈ fsBlockSupport x then a s else 0)
    (fun s hs => by by_contra hn; exact hs (if_neg hn))
  let y : (Jr ⊕ Sx) →₀ R' := Finsupp.sumElim (x.comapDomain Sum.inl Sum.inl_injective.injOn) w
  refine ⟨y, ?_, fun _ => rfl, ?_⟩
  · ext (j | ⟨s, m⟩) : 1
    · rfl
    · by_cases hs : s ∈ fsBlockSupport x
      · simpa only [y, fsCellsBase_inr, Finsupp.sumElim_inr, w, Finsupp.onFinset_apply, if_pos hs] using (ha s m).symm
      · have hz : (fsBlockPart x).split s = 0 := by
          by_contra h; exact hs ((Finsupp.mem_splitSupport_iff_nonzero (fsBlockPart x) s).mpr h)
        have hzm : x (Sum.inr ⟨s, m⟩) = 0 := congrArg (fun b : Mt s →₀ R' => b m) hz
        simp [y, w, hs, hzm]
  · rw [show y.comapDomain Sum.inr Sum.inr_injective.injOn = w by ext; rfl]
    exact Finsupp.support_onFinset_subset

def fsCellsF (hfill : FilledF ρ bsub) (c : ∀ s, Mt s →₀ R')
    (y : (Jr ⊕ Sx) →₀ MonoidAlgebra ℤ (PresGroup ρ)) :
    (Jr ⊕ (Σ s, Mt s)) →₀ R' :=
  fsCellsBase c (y.mapRange (coeffF ρ bsub hfill) (map_zero _))
