import RequestProject.TopologicalSingular.SmallRefinementStep
import RequestProject.Tac
noncomputable section


namespace FiniteChains.SingularSubdivision
open TopologicalSingular
universe u v
variable {X : Type u} [TopologicalSpace X] {ι : Type v}

def smallRefinementNextMap (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) {n} (s : SmallRefinementStage U n) :
    Chain X (n + 1) →ₗ[ℤ] Chain X (n + 1) :=
  Finsupp.linearCombination ℤ (fun σ => (smallRefinementStep_exists U hU hcover s σ).choose)

def smallRefinementNextHomotopy (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) {n} (s : SmallRefinementStage U n) :
    Chain X (n + 1) →ₗ[ℤ] Chain X (n + 2) :=
  Finsupp.linearCombination ℤ
    (fun σ => (smallRefinementStep_exists U hU hcover s σ).choose_spec.choose)

theorem smallRefinementNextHomotopy_identity (U : ι → Set X) hU
    hcover {n} s
    c :
    boundary (n + 1) (smallRefinementNextHomotopy U hU hcover s c) =
      c - smallRefinementNextMap U hU hcover s c - s.homotopyMap (boundary n c) := by
  have he : (boundary _).comp (smallRefinementNextHomotopy U hU hcover s) =
      LinearMap.id - smallRefinementNextMap U hU hcover s -
        s.homotopyMap.comp (boundary n) := by
    apply Finsupp.lhom_ext'
    intro σ
    apply LinearMap.ext_ring
    grind [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, smallRefinementNextHomotopy, smallRefinementNextMap, Finsupp.lsingle_apply, Finsupp.linearCombination_single, one_smul]
  exact DFunLike.congr_fun he c

def smallRefinementStageNext (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) {n} (s : SmallRefinementStage U n) :
    SmallRefinementStage U (n + 1) where
  smallMap := smallRefinementNextMap U hU hcover s
  homotopyMap := smallRefinementNextHomotopy U hU hcover s
  small c := by
    lin_ind c σ r using aesop =>
      dsimp [smallRefinementNextMap]
      rw [Finsupp.linearCombination_single]
      exact Submodule.smul_mem _ r
        (smallRefinementStep_exists U hU hcover s σ).choose_spec.choose_spec.1
  small_support σ := by
    grind [smallRefinementNextMap, Finsupp.linearCombination_single, one_smul]
  homotopy_support σ := by
    grind [smallRefinementNextHomotopy, Finsupp.linearCombination_single, one_smul]
  on_boundary c := by
    rw [smallRefinementNextHomotopy_identity, boundary_boundary, map_zero, sub_zero]

def smallRefinementStage (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) : (n : ℕ) → SmallRefinementStage U n
  | 0 => smallRefinementStageZero U hcover
  | n + 1 => smallRefinementStageNext U hU hcover (smallRefinementStage U hU hcover n)

def smallRefinement (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) n :=
  (smallRefinementStage U hU hcover n).smallMap

def smallRefinementHomotopy (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) n :=
  (smallRefinementStage U hU hcover n).homotopyMap

theorem smallRefinementHomotopy_identity (U : ι → Set X) hU
    hcover n c :
    boundary (n + 1) (smallRefinementHomotopy U hU hcover (n + 1) c) =
      c - smallRefinement U hU hcover (n + 1) c -
        smallRefinementHomotopy U hU hcover n (boundary n c) :=
  smallRefinementNextHomotopy_identity U hU hcover _ c

theorem smallRefinement_boundary (U : ι → Set X) hU
    hcover n c :
    boundary n (smallRefinement U hU hcover (n + 1) c) =
      smallRefinement U hU hcover n (boundary n c) := by
  have he := congrArg (boundary n) (smallRefinementHomotopy_identity U hU hcover n c)
  rw [boundary_boundary, map_sub, map_sub, smallRefinementHomotopy,
    (smallRefinementStage U hU hcover n).on_boundary] at he
  change 0 = boundary n c - boundary n (smallRefinement U hU hcover _ c) -
    (boundary n c - smallRefinement U hU hcover n (boundary n c)) at he
  linear_combination (norm := abel) he

theorem smallRefinement_mem_small (U : ι → Set X) hU
    hcover n c :
    smallRefinement U hU hcover n c ∈ smallChains U n :=
  (smallRefinementStage U hU hcover n).small c

/-- Refinement preserves every subspace, even though the subdivision count may
depend on the individual simplex. -/
theorem smallRefinement_support (U : ι → Set X) hU
    hcover n A {c}
    (hc : c ∈ subChains A n) : smallRefinement U hU hcover n c ∈ subChains A n :=
  carried_linearMap_mem_subChains _ (smallRefinementStage U hU hcover n).small_support A hc
