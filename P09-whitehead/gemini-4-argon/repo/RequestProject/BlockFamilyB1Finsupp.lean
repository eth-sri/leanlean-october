module

public import RequestProject.BlockFamilyBlockwiseFinsupp
public import RequestProject.BaseChangeExactFinsupp

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains

section

variable {R S : Type*} [Ring R] [Ring S] {J I : Type*}

def fsRingMapBoundary (φ : R →+* S) (A : J → I →₀ R) : (J →₀ S) →ₗ[S] (I →₀ S) :=
  Finsupp.linearCombination S (fun j => (A j).mapRange φ (map_zero _))

theorem fsRingMapBoundary_mapRange (φ : R →+* S) (A : J → I →₀ R) (y : J →₀ R) :
    fsRingMapBoundary φ A (y.mapRange φ (map_zero _)) =
      (Finsupp.linearCombination R A y).mapRange φ (map_zero _) := by
  induction y using Finsupp.induction_linear with
  | zero => simp [fsRingMapBoundary]
  | add y z hy hz =>
      rw [Finsupp.mapRange_add, map_add, map_add, Finsupp.mapRange_add, hy, hz] <;>
        exact fun a b => map_add φ a b
  | single j a =>
      simp only [Finsupp.mapRange_single, fsRingMapBoundary, Finsupp.linearCombination_single]
      ext i; exact (map_mul φ a (A j i)).symm

end

section

variable {G G' : Type*} [Group G] [Group G'] {J I : Type*}

theorem fs_cycle_mem_span_groupMap_cycles (f : G →* G') (hf : Function.Injective f)
    (A : J → I →₀ MonoidAlgebra ℤ G) (x : J →₀ MonoidAlgebra ℤ G')
    (hx : fsRingMapBoundary (MonoidAlgebra.mapDomainRingHom ℤ f) A x = 0) :
    x ∈ Submodule.span (MonoidAlgebra ℤ G')
      {v : J →₀ MonoidAlgebra ℤ G' | ∃ y : J →₀ MonoidAlgebra ℤ G,
        Finsupp.linearCombination (MonoidAlgebra ℤ G) A y = 0 ∧
        v = y.mapRange (MonoidAlgebra.mapDomainRingHom ℤ f) (map_zero _)} := by
  classical
  let H := f.range
  let e : G ≃* H := MonoidHom.ofInjective hf
  let φ : MonoidAlgebra ℤ G →+* MonoidAlgebra ℤ H := MonoidAlgebra.mapDomainRingHom ℤ e.toMonoidHom
  let ψ : MonoidAlgebra ℤ H →+* MonoidAlgebra ℤ G := MonoidAlgebra.mapDomainRingHom ℤ e.symm.toMonoidHom
  let θ : MonoidAlgebra ℤ G →+* MonoidAlgebra ℤ G' := MonoidAlgebra.mapDomainRingHom ℤ f
  have hφ (a) : subRingHom H (φ a) = θ a := by
    change MonoidAlgebra.mapDomain _ (MonoidAlgebra.mapDomain _ a) = MonoidAlgebra.mapDomain _ a
    rw [← MonoidAlgebra.mapDomain_comp]; rfl
  have hφψ (a) : φ (ψ a) = a := by
    change MonoidAlgebra.mapDomain _ (MonoidAlgebra.mapDomain _ a) = a
    rw [← MonoidAlgebra.mapDomain_comp,
      show (e.toMonoidHom : G → H) ∘ (e.symm.toMonoidHom : H → G) = id from funext e.apply_symm_apply,
      MonoidAlgebra.mapDomain_id]
  have hφinj : Function.Injective φ := fun _ _ h =>
    MonoidAlgebra.coeff_injective (Finsupp.mapDomain_injective e.injective (congrArg MonoidAlgebra.coeff h))
  let A' : J → I →₀ MonoidAlgebra ℤ H := fun j => (A j).mapRange φ (map_zero _)
  have hboundary : fsExtendedBoundary H A' = fsRingMapBoundary θ A := by
    refine Finsupp.lhom_ext fun j a => ?_
    simp only [fsExtendedBoundary, fsRingMapBoundary, Finsupp.linearCombination_single]
    congr 1; ext i : 1; exact hφ (A j i)
  refine Submodule.span_mono ?_ (fs_cycle_mem_span_subgroup_cycles H A' x (hboundary.symm ▸ hx))
  rintro v ⟨w, hw, rfl⟩
  let y := w.mapRange ψ (map_zero _)
  have hy : y.mapRange φ (map_zero _) = w := by ext j : 1; exact hφψ (w j)
  refine ⟨y, ?_, by ext j : 1; change subRingHom H (w j) = θ (ψ (w j)); rw [← hφ, hφψ]⟩
  have hb : (Finsupp.linearCombination (MonoidAlgebra ℤ G) A y).mapRange φ (map_zero _) = 0 := by
    rw [← fsRingMapBoundary_mapRange]
    change Finsupp.linearCombination (MonoidAlgebra ℤ H) A' (y.mapRange φ (map_zero _)) = 0
    rwa [hy]
  ext i : 1
  exact hφinj (by
    simpa only [Finsupp.mapRange_apply, Finsupp.zero_apply, map_zero] using
      congrArg (fun z : I →₀ MonoidAlgebra ℤ H => z i) hb)

end

namespace BlockFamily

universe u

section

variable {Jr Sx R : Type u} {Mt : Sx → Type u} [Ring R]

def fsSurfaceChain (c : ∀ s, Mt s →₀ R) (s : Sx) : (Jr ⊕ (Σ s, Mt s)) →₀ R :=
  (c s).mapDomain (fun m => Sum.inr ⟨s, m⟩)

@[simp] theorem fsSurfaceChain_inl (c : ∀ s, Mt s →₀ R) (s : Sx) (j : Jr) :
    fsSurfaceChain c s (Sum.inl j) = 0 :=
  Finsupp.mapDomain_notin_range _ _ fun ⟨_, h⟩ => Sum.inr_ne_inl h

@[simp] theorem fsSurfaceChain_inr (c : ∀ s, Mt s →₀ R) (s : Sx) (m : Mt s) :
    fsSurfaceChain (Jr := Jr) c s (Sum.inr ⟨s, m⟩) = c s m :=
  Finsupp.mapDomain_apply_of_injective (fun _ _ h => eq_of_heq (Sigma.mk.inj (Sum.inr_injective h)).2) _ _

@[simp] theorem fsCellsBase_single_inl (c : ∀ s, Mt s →₀ R) (j : Jr) :
    fsCellsBase c (Finsupp.single (Sum.inl j) 1) = Finsupp.single (Sum.inl j) 1 := by
  classical
  ext (i | ⟨s, m⟩)
  · simp only [fsCellsBase_inl, Finsupp.single_apply, Sum.inl.injEq]
  · simp

@[simp] theorem fsCellsBase_single_inr (c : ∀ s, Mt s →₀ R) (s : Sx) :
    fsCellsBase (Jr := Jr) c (Finsupp.single (Sum.inr s) 1) = fsSurfaceChain c s := by
  classical
  ext (j | ⟨t, m⟩)
  · simp
  · by_cases hst : s = t
    · subst t; simp
    · simp [hst, show fsSurfaceChain (Jr := Jr) c s (Sum.inr ⟨t, m⟩) = 0 from
        Finsupp.mapDomain_notin_range _ _ fun ⟨_, h⟩ => hst (congrArg Sigma.fst (Sum.inr_injective h))]

def fsOldOneIncl {α Z : Type u} : (α →₀ R) →ₗ[R] ((α ⊕ Z) →₀ R) where
  toFun x := Finsupp.sumElim x 0
  map_add' x y := by ext (k | k) <;> simp [Finsupp.sumElim_apply]
  map_smul' a x := by ext (k | k) <;> simp [Finsupp.sumElim_apply]

@[simp] theorem fsOldOneIncl_inl {α Z : Type u} (x : α →₀ R) (i : α) :
    fsOldOneIncl (Z := Z) x (Sum.inl i) = x i := rfl

@[simp] theorem fsOldOneIncl_inr {α Z : Type u} (x : α →₀ R) (z : Z) :
    fsOldOneIncl x (Sum.inr z) = 0 := rfl

end

variable {α Jr Sx : Type u} {Zt Mt : Sx → Type u}
  [DecidableEq α] [DecidableEq Sx] [∀ s, DecidableEq (Zt s)]
  (ρ : Jr ⊕ Sx → FreeGroup α)
  (bsub : ∀ s, Mt s → FreeGroup (α ⊕ Zt s))
  (hfill : FilledF ρ bsub)

local notation "R'" => MonoidAlgebra ℤ (PresGroup (substPresF ρ bsub))
local notation "R₀" => MonoidAlgebra ℤ (PresGroup ρ)

def fsFoxPushBoundary : ((Jr ⊕ Sx) →₀ R') →ₗ[R'] (α →₀ R') :=
  fsRingMapBoundary (coeffF ρ bsub hfill) (fun k => coverFoxGradient (relSub ρ) (ρ k))

omit [DecidableEq Sx] [∀ s, DecidableEq (Zt s)] in
@[simp] theorem fsFoxPushBoundary_single (k : Jr ⊕ Sx) (i : α) :
    fsFoxPushBoundary ρ bsub hfill (Finsupp.single k 1) i =
      coeffF ρ bsub hfill (foxMatrixPres ρ i k) := by
  simp only [fsFoxPushBoundary, fsRingMapBoundary, Finsupp.linearCombination_single,
    one_smul, Finsupp.mapRange_apply]; rfl

structure IsFillingFS (c : ∀ s, Mt s →₀ R') : Prop where
  base : ∀ (s : Sx) (i : α),
    (c s).sum (fun m a => a * foxMatrixPres (substPresF ρ bsub) (Sum.inl i) (Sum.inr ⟨s, m⟩)) =
      coeffF ρ bsub hfill (foxMatrixPres ρ i (Sum.inr s))
  internal : ∀ (s : Sx) (z : Zt s),
    (c s).sum (fun m a => a * foxMatrixPres (substPresF ρ bsub) (Sum.inr ⟨s, z⟩) (Sum.inr ⟨s, m⟩)) = 0

theorem isFillingFS_of_finite_blocks [∀ s, Fintype (Mt s)] (c : ∀ s, Mt s →₀ R')
    (hbase : ∀ (s : Sx) (i : α), ∑ m : Mt s, c s m *
      foxMatrixPres (substPresF ρ bsub) (Sum.inl i) (Sum.inr ⟨s, m⟩) =
        coeffF ρ bsub hfill (foxMatrixPres ρ i (Sum.inr s)))
    (hinternal : ∀ (s : Sx) (z : Zt s), ∑ m : Mt s, c s m *
      foxMatrixPres (substPresF ρ bsub) (Sum.inr ⟨s, z⟩) (Sum.inr ⟨s, m⟩) = 0) :
    IsFillingFS ρ bsub hfill c where
  base s i := by rw [Finsupp.sum_fintype _ _ (fun _ => zero_mul _)]; exact hbase s i
  internal s z := by rw [Finsupp.sum_fintype _ _ (fun _ => zero_mul _)]; exact hinternal s z

theorem fsSurfaceChain_boundary_apply (c : ∀ s, Mt s →₀ R') (s : Sx) (i : α ⊕ (Σ s, Zt s)) :
    coverSecondBoundary (relSub (substPresF ρ bsub)) (substPresF ρ bsub) (fsSurfaceChain c s) i =
      (c s).sum (fun m a => a * foxMatrixPres (substPresF ρ bsub) i (Sum.inr ⟨s, m⟩)) := by
  rw [fsCoverSecondBoundary_apply]
  exact Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

theorem fsCellsBase_chainMap (c : ∀ s, Mt s →₀ R') (hc : IsFillingFS ρ bsub hfill c) :
    (coverSecondBoundary (relSub (substPresF ρ bsub)) (substPresF ρ bsub)).comp (fsCellsBase c) =
      fsOldOneIncl.comp (fsFoxPushBoundary ρ bsub hfill) := by
  classical
  refine Finsupp.lhom_ext fun k a => ?_
  rw [← Finsupp.smul_single_one k a, map_smul, map_smul]; congr 1
  simp only [LinearMap.comp_apply]
  rcases k with j | s
  · rw [fsCellsBase_single_inl]; ext (i | p) : 1
    · rw [fsOldOneIncl_inl, fsFoxPushBoundary_single, fsCoverSecondBoundary_apply]
      simp [foxMatrix_inl_inl ρ bsub hfill]
    · rw [fsOldOneIncl_inr, fsCoverSecondBoundary_apply]; simp [foxMatrix_inr_inl ρ bsub]
  · rw [fsCellsBase_single_inr]; ext (i | ⟨t, z⟩) : 1
    · rw [fsOldOneIncl_inl, fsFoxPushBoundary_single, fsSurfaceChain_boundary_apply]
      exact hc.base s i
    · rw [fsOldOneIncl_inr, fsSurfaceChain_boundary_apply]
      by_cases hst : s = t
      · subst t; exact hc.internal s z
      · simp [foxMatrix_inr_inr_of_ne ρ bsub hst z]

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
  rwa [fsFoxPushBoundary, fsRingMapBoundary_mapRange] at h

theorem fsGenerates_familySubst (c : ∀ s, Mt s →₀ R')
    (hc : IsFillingFS ρ bsub hfill c)
    (hblock : BlockSurfaceGeneratesFS ρ bsub c)
    (hinj : Function.Injective (substHomF ρ bsub hfill))
    (x : (Jr ⊕ (Σ s, Mt s)) →₀ R')
    (hx : coverSecondBoundary (relSub (substPresF ρ bsub)) (substPresF ρ bsub) x = 0) :
    x ∈ Submodule.span R'
      {v : (Jr ⊕ (Σ s, Mt s)) →₀ R' | ∃ y : (Jr ⊕ Sx) →₀ R₀,
        coverSecondBoundary (relSub ρ) ρ y = 0 ∧ v = fsCellsF ρ bsub hfill c y} := by
  obtain ⟨y, rfl, -, -⟩ := fsCellsBase_preimage_of_internal_zero ρ bsub c hblock x
    (fun s z => congrArg (fun v => v (Sum.inr ⟨s, z⟩)) hx)
  have hy : fsFoxPushBoundary ρ bsub hfill y = 0 := by
    ext i : 1
    have h := congrArg (fun z : (α ⊕ (Σ s, Zt s)) →₀ R' => z (Sum.inl i))
      (LinearMap.congr_fun (fsCellsBase_chainMap ρ bsub hfill c hc) y)
    simpa [hx] using h.symm
  have hmem := fs_cycle_mem_span_groupMap_cycles (substHomF ρ bsub hfill) hinj
    (fun k => coverFoxGradient (relSub ρ) (ρ k)) y hy
  clear hx hy
  induction hmem using Submodule.span_induction with
  | mem v hv => obtain ⟨a, ha, rfl⟩ := hv; exact Submodule.subset_span ⟨a, ha, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add _ _ _ _ hv' hw' => rw [map_add]; exact Submodule.add_mem _ hv' hw'
  | smul a _ _ hv' => rw [map_smul]; exact Submodule.smul_mem _ a hv'
