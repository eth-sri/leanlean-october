module

public import Glennie.Compact.Flows
public import Glennie.Compact.NativeDictionary
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
@[expose] public section

namespace Glennie.Compact.FlowFamily
open NativeDictionary Flows ContinuousLinearMap NormedSpace

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

local instance : NormedSpace ℝ Albert := inferInstance
local instance : NormedRing End := ContinuousLinearMap.toNormedRing
local instance : IsTopologicalRing End := inferInstance
local instance : NormedAlgebra ℚ End := .restrictScalars ℚ ℝ _

def spanGen {k : ℕ} (D : Fin k → Albert →ₗ[ℝ] Albert) : (Fin k → ℝ) →L[ℝ] End :=
  ∑ n, (proj n : (Fin k → ℝ) →L[ℝ] ℝ).smulRight ((D n).toContinuousLinearMap)

private theorem spanGen_apply {k : ℕ} (D : Fin k → Albert →ₗ[ℝ] Albert) (s : Fin k → ℝ)
    (x : Albert) : spanGen D s x = ∑ n, s n • D n x := by simp [spanGen, sum_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, smul_apply]

private theorem spanGen_single {k : ℕ} (D : Fin k → Albert →ₗ[ℝ] Albert) (n : Fin k) (x : Albert) :
    spanGen D (Pi.single n 1) x = D n x := by simp [spanGen_apply]

private theorem spanGen_toLinearMap {k : ℕ} (D : Fin k → Albert →ₗ[ℝ] Albert) (s : Fin k → ℝ) :
    (spanGen D s).toLinearMap = ∑ n, s n • D n := by apply LinearMap.ext <;> simp [spanGen_apply, LinearMap.sum_apply]

variable {k : ℕ}
variable (D : Fin 3 → Fin k → Albert →ₗ[ℝ] Albert) (T : Fin 3 → Fin 3 → Albert)

def movedFrame (a : Fin 3) (s : Fin k → ℝ) (i : Fin 3) : Albert :=
  exp (spanGen (D a) s) (T a i)

@[simp] theorem movedFrame_zero (a : Fin 3) : movedFrame D T a 0 = T a := by
  funext i
  simp [movedFrame, one_apply_eq_self]

theorem movedFrame_frame (hD : ∀ a n, IsJordanDerivation (D a n)) (hT : ∀ a n, TraceFree (D a n))
    (a : Fin 3) (hF : Frame (T a)) (s : Fin k → ℝ) : Frame (movedFrame D T a s) := by
  have hd : IsJordanDerivation (spanGen (D a) s).toLinearMap := by
    rw [spanGen_toLinearMap]
    exact IsJordanDerivation.sum _ _ fun n _ => (hD a n).smul (s n)
  have ht : TraceFree (spanGen (D a) s).toLinearMap := by
    rw [spanGen_toLinearMap]
    exact TraceFree.sum _ _ fun n _ => (hT a n).smul (s n)
  exact (expAut _ hd ht).map_frame _ hF

theorem continuous_movedFrame (a i : Fin 3) : Continuous fun s => movedFrame D T a s i :=
  (exp_continuous.comp (spanGen (D a)).continuous).clm_apply continuous_const

def δ (a i : Fin 3) := (spanGen (D a)).flip (T a i)

private theorem hasStrictFDerivAt_movedFrame (a i : Fin 3) :
    HasStrictFDerivAt (fun s => movedFrame D T a s i) (δ D T a i) 0 := by
  have h : HasStrictFDerivAt exp (1 : End →L[ℝ] End) (spanGen (D a) 0) := by
    rw [map_zero]
    exact hasStrictFDerivAt_exp_zero
  refine ((h.comp 0 (spanGen (D a)).hasStrictFDerivAt).clm_apply
    (hasStrictFDerivAt_const (T a i) (0 : Fin k → ℝ))).congr_fderiv ?_
  apply ContinuousLinearMap.ext
  intro s
  simp [δ, one_apply_eq_self]

def ledgerDeriv (i j l : Fin 3) : (Fin k → ℝ) →L[ℝ] ℝ :=
  traceCLM.comp ((jordanContinuous.flip (T 2 l)).comp
    ((jordanContinuous.flip (T 1 j)).comp (δ D T 0 i) +
     (jordanContinuous (T 0 i)).comp (δ D T 1 j)) +
    (jordanContinuous (jordan (T 0 i) (T 1 j))).comp (δ D T 2 l))

private theorem hasStrictFDerivAt_ledger_movedFrame (i j l : Fin 3) :
    HasStrictFDerivAt (fun s => ledger (movedFrame D T 0 s) (movedFrame D T 1 s)
      (movedFrame D T 2 s) i j l) (ledgerDeriv D T i j l) 0 := by
  let h := hasStrictFDerivAt_movedFrame D T
  have hp := (jordanContinuous.hasStrictFDerivAt.comp 0 (h 0 i)).clm_apply (h 1 j)
  have hq := (jordanContinuous.hasStrictFDerivAt.comp 0 hp).clm_apply (h 2 l)
  refine (traceCLM.hasStrictFDerivAt.comp 0 hq).congr_fderiv ?_
  ext s
  simp [ledgerDeriv, δ, add_comm, add_left_comm]

/-! ## The twenty directions, read through the dictionary -/

/-- The partner full27 indices, in the minor-column order. -/
def partnerIndex : Fin 20 → Fin 27 :=
  ![3, 4, 5, 6, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20,
    11, 12, 13, 14]

/-- Sixteen first-frame and four second-frame directions; none third-frame. -/
def contextIndex : Fin 20 → Fin 3 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1]

/-- The twenty selected ordered triple-ledger rows. -/
def rowIndex : Fin 20 → Fin 3 × Fin 3 × Fin 3 :=
  ![(0,0,0), (0,0,1), (0,0,2), (0,1,0), (0,1,1), (0,1,2),
    (0,2,0), (0,2,1), (1,0,0), (1,0,1), (1,0,2), (1,1,0),
    (1,1,1), (1,1,2), (1,2,0), (1,2,1), (2,0,0), (2,0,1),
    (2,1,0), (2,1,1)]

/-- [L_t, L_b] with t = basis 1 and b = basis (partnerIndex n), halved native product,
no factor 4. Basis vectors are `nativeVector m`. -/
def direction (n : Fin 20) : Albert →ₗ[ℝ] Albert :=
  innerDerLinear (nativeVector 1) (nativeVector (partnerIndex n))

/-- The direction family of frame a: direction n if it belongs to frame a, else 0. -/
def contextDirection (a : Fin 3) (n : Fin 20) : Albert →ₗ[ℝ] Albert :=
  if a = contextIndex n then direction n else 0

theorem contextDirection_isJordanDerivation (a : Fin 3) (n : Fin 20) :
    IsJordanDerivation (contextDirection a n) := by
  unfold contextDirection
  split_ifs
  · exact isJordanDerivation_innerDerLinear _ _
  · exact IsJordanDerivation.zero

theorem contextDirection_traceFree (a : Fin 3) (n : Fin 20) :
    TraceFree (contextDirection a n) := by
  unfold contextDirection
  split_ifs
  · exact traceFree_innerDerLinear _ _
  · exact TraceFree.zero

theorem contextDirection_apply (a : Fin 3) (n : Fin 20) (x : Albert) :
    contextDirection a n x = if a = contextIndex n then direction n x else 0 := by
  unfold contextDirection
  split_ifs <;> rfl

theorem context_cases (n : Fin 20) : contextIndex n = 0 ∨ contextIndex n = 1 := by
  fin_cases n <;> decide

/-- The differentiated slot, paired with the product of the two fixed slots.
The exact-arithmetic certificate uses the same indexing. -/
def ledgerColumn {A B : Type*} (pair : A → A → B) (mul : A → A → A)
    (D : Fin 20 → Fin 3 → A) (T : Fin 3 → Fin 3 → A) (r n : Fin 20) : B :=
  let (i,j,k) := rowIndex r
  if contextIndex n = 0 then pair (D n i) (mul (T 1 j) (T 2 k))
  else pair (D n j) (mul (T 0 i) (T 2 k))

def jacobianEntry (T : Fin 3 → Fin 3 → Albert) : Fin 20 → Fin 20 → ℝ :=
  ledgerColumn inner jordan (fun n i => direction n (T (contextIndex n) i)) T

def rowLedger (T : Fin 3 → Fin 3 → Albert) (s : Fin 20 → ℝ) : Fin 20 → ℝ := fun r =>
  ledger (movedFrame contextDirection T 0 s) (movedFrame contextDirection T 1 s)
    (movedFrame contextDirection T 2 s) (rowIndex r).1 (rowIndex r).2.1 (rowIndex r).2.2

def rowLedgerDeriv (T : Fin 3 → Fin 3 → Albert) : (Fin 20 → ℝ) →L[ℝ] (Fin 20 → ℝ) :=
  ContinuousLinearMap.pi fun r => ledgerDeriv contextDirection T (rowIndex r).1 (rowIndex r).2.1 (rowIndex r).2.2

theorem hasStrictFDerivAt_rowLedger (T : Fin 3 → Fin 3 → Albert) :
    HasStrictFDerivAt (rowLedger T) (rowLedgerDeriv T) 0 :=
  hasStrictFDerivAt_pi'.2 fun r => by exact hasStrictFDerivAt_ledger_movedFrame _ _ _ _ _

theorem rowLedgerDeriv_single (T : Fin 3 → Fin 3 → Albert) (r n : Fin 20) :
    rowLedgerDeriv T (Pi.single n 1) r = jacobianEntry T r n := by
  rcases h : rowIndex r with ⟨i,j,k⟩
  rcases context_cases n with hn | hn <;>
    simp [rowLedgerDeriv, ledgerDeriv, δ, spanGen_single, contextDirection_apply,
      jacobianEntry, ledgerColumn, h, hn,  jordan_zero_right]
  · exact inner_jordan_associative _ _ _
  · rw [jordan_comm (T 0 i) (direction n (T 1 j))]
    exact inner_jordan_associative _ _ _

end
end Glennie.Compact.FlowFamily
