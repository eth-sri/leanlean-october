module

public import RequestProject.TopologicalSingular.SmallRefinementStep

@[expose] public section

noncomputable section

namespace FiniteChains.SingularSubdivision
open TopologicalSingular
universe u v
variable {X : Type u} [TopologicalSpace X] {ι : Type v}

def smallRefinementNextMap (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) {n : ℕ} (s : SmallRefinementStage U n) :=
  Finsupp.linearCombination ℤ (fun σ => (smallRefinementStep_exists U hU hcover s σ).choose)

def smallRefinementNextHomotopy (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) {n : ℕ} (s : SmallRefinementStage U n) :=
  Finsupp.linearCombination ℤ
    (fun σ => (smallRefinementStep_exists U hU hcover s σ).choose_spec.choose)

theorem smallRefinementNextHomotopy_identity (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) {n : ℕ} (s : SmallRefinementStage U n)
    (c : Chain X _) :
    boundary _ (smallRefinementNextHomotopy U hU hcover s c) =
      c - smallRefinementNextMap U hU hcover s c - s.homotopyMap (boundary n c) := by
  have he : (boundary (n + 1)).comp (smallRefinementNextHomotopy U hU hcover s) =
      LinearMap.id - smallRefinementNextMap U hU hcover s -
        s.homotopyMap.comp (boundary n) := by
    apply Finsupp.lhom_ext'
    intro σ
    apply LinearMap.ext_ring
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
      smallRefinementNextHomotopy, smallRefinementNextMap,
      Finsupp.lsingle_apply, Finsupp.linearCombination_single, one_smul]
    grind
  exact DFunLike.congr_fun he c

def smallRefinementStageNext (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) {n : ℕ} (s : SmallRefinementStage U n) :
    SmallRefinementStage U (n + 1) where
  smallMap := smallRefinementNextMap U hU hcover s
  homotopyMap := smallRefinementNextHomotopy U hU hcover s
  small c := by
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add c d hc hd => aesop
    | single σ r =>
      dsimp only [smallRefinementNextMap]
      rw [Finsupp.linearCombination_single]
      exact Submodule.smul_mem _ r
        (smallRefinementStep_exists U hU hcover s σ).choose_spec.choose_spec.1
  small_support σ := by
    dsimp only [smallRefinementNextMap]
    rw [Finsupp.linearCombination_single, one_smul] <;> grind
  homotopy_support σ := by
    dsimp only [smallRefinementNextHomotopy]
    rw [Finsupp.linearCombination_single, one_smul] <;> grind
  on_boundary c := by
    rw [smallRefinementNextHomotopy_identity, boundary_boundary, map_zero, sub_zero]

def smallRefinementStage (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) : (n : ℕ) → SmallRefinementStage U n
  | 0 => smallRefinementStageZero U hcover
  | n + 1 => smallRefinementStageNext U hU hcover (smallRefinementStage U hU hcover n)

def smallRefinement (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) (n : ℕ) :=
  (smallRefinementStage U hU hcover n).smallMap

def smallRefinementHomotopy (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) (n : ℕ) :=
  (smallRefinementStage U hU hcover n).homotopyMap

theorem smallRefinementHomotopy_identity (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) (n : ℕ) (c : Chain X _) :
    boundary _ (smallRefinementHomotopy U hU hcover _ c) =
      c - smallRefinement U hU hcover _ c -
        smallRefinementHomotopy U hU hcover n (boundary n c) :=
  by solve_by_elim [smallRefinementNextHomotopy_identity]

theorem smallRefinement_boundary (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) (n : ℕ) (c : Chain X _) :
    boundary n (smallRefinement U hU hcover _ c) =
      smallRefinement U hU hcover n (boundary n c) := by
  have he := congrArg (boundary n) (smallRefinementHomotopy_identity U hU hcover n c)
  rw [boundary_boundary, map_sub, map_sub, smallRefinementHomotopy,
    (smallRefinementStage U hU hcover n).on_boundary] at he
  change 0 = boundary n c - boundary n (smallRefinement U hU hcover _ c) -
    (boundary n c - smallRefinement U hU hcover n _) at he
  linear_combination (norm := abel) he

theorem smallRefinement_mem_small (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) (n : ℕ) (c : Chain X n) :
    smallRefinement U hU hcover n c ∈ smallChains U n :=
  (smallRefinementStage U hU hcover n).small c

/-- Refinement preserves every subspace, even though the subdivision count may
depend on the individual simplex. -/
theorem smallRefinement_support (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) (n : ℕ) (A : Set X) {c : Chain X n}
    (hc : c ∈ subChains A n) : smallRefinement U hU hcover n c ∈ subChains A n :=
  carried_linearMap_mem_subChains _ (smallRefinementStage U hU hcover n).small_support A hc

end FiniteChains.SingularSubdivision
