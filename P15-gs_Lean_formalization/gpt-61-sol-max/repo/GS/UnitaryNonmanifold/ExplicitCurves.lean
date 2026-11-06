module

public import GS.UnitaryNonmanifold.TangentObstruction
public import GS.Unitary.RealEmbedding
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Two explicit feasible unitary three-factor curves

The matrices have rational base points and rational change of two-dimensional
basis. Only the scalar sine and cosine curves are used.
-/

noncomputable section
open Matrix Filter GS.UnitaryGeometry
open scoped Topology
namespace GS.UnitaryNonmanifold
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def witnessQ : Mat 3 :=
  !![1/3, -2/3, -2/3; -2/3, 1/3, -2/3; -2/3, -2/3, 1/3]

def rotate01 (t : ℝ) : Mat 3 :=
  !![Real.cos t, -Real.sin t, 0; Real.sin t, Real.cos t, 0; 0, 0, 1]

def rotate02 (t : ℝ) : Mat 3 :=
  !![Real.cos t, 0, -Real.sin t; 0, 1, 0; Real.sin t, 0, Real.cos t]

@[simp] theorem rotate01_zero : rotate01 0 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rotate01]
@[simp] theorem rotate02_zero : rotate02 0 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rotate02]

def sandwichMatrix {q : ℕ} (H : CMat 2) (A B : CMat q) : CMat (q*2) :=
  fun i j =>
    let x : Fin q × Fin 2 := finProdFinEquiv.symm i
    let y : Fin q × Fin 2 := finProdFinEquiv.symm j
    (H * diagTwo (A x.1 y.1) (B x.1 y.1) * Hᴴ) x.2 y.2

@[simp] theorem cBlock_sandwichMatrix {q : ℕ} (H : CMat 2) (A B : CMat q)
    (i j : Fin q) : cBlock (sandwichMatrix H A B) i j =
    H * diagTwo (A i j) (B i j) * Hᴴ := by
  ext a b
  simp [cBlock, sandwichMatrix]

def witnessBase : CMat 6 := fun i j =>
  let x : Fin 3 × Fin 2 := finProdFinEquiv.symm i
  let y : Fin 3 × Fin 2 := finProdFinEquiv.symm j
  ofRealMatrix witnessQ x.1 y.1 * (1 : CMat 2) x.2 y.2

@[simp] theorem cBlock_witnessBase (i j : Fin 3) :
    cBlock witnessBase i j = ofRealMatrix witnessQ i j • 1 := by
  ext a b
  simp only [cBlock,witnessBase,Equiv.symm_apply_apply,Matrix.smul_apply,smul_eq_mul]
  congr 1
  exact congrArg₂ (fun a b : Fin 2 => (1 : CMat 2) a b)
    (congrArg Prod.snd ((finProdFinEquiv : Fin 3 × Fin 2 ≃ Fin 6).symm_apply_apply (i,a)))
    (congrArg Prod.snd ((finProdFinEquiv : Fin 3 × Fin 2 ≃ Fin 6).symm_apply_apply (j,b)))

end GS.UnitaryNonmanifold
