module

public import GS.M4Data
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Exact m=4 example from the manuscript

Polynomial certificates are expressed as
Lean `linear_combination` proofs, not accepted as external numerical oracles.

The generic necessity proof and non-membership theorem are in M4Necessary.lean.
-/

noncomputable section
open Matrix GS.Isometric
open scoped BigOperators Real
namespace GS.M4
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

def mixer (a b c : ℝ) := load fun i => !![1,1;1,(![a,b,c] i)]
def core := route (mixer (1/3) (-1/3) (-3)) (mixer (-3) (-1/3) (1/3))

def tri (a b c : ℝ) := !![a,0;b,c]
def rightEnd (x y z : ℝ) := load ![tri (z/2) (-6*z/7) (y*z/14), tri (1/2) (2/3) (x/6), tri (y/2) (-2*y/3) (x*y/6)]
def leftEnd (x y z : ℝ) := load ![tri (x/2) 2 (3/2), tri (y/2) (-x*y) (3*x*y/2), tri (3*z/14) (6*y*z/7) (y*z/2)]
def witness (x y z : ℝ) := leftEnd x y z * core * rightEnd x y z
def Q := witness (√2) (√3) (√7)

lemma Q_mem_A4 : InA4 2 2 2 2 P P P Q :=
  ⟨rightEnd (√2) (√3) (√7),mixer (-3) (-1/3) (1/3),mixer (1/3) (-1/3) (-3),leftEnd (√2) (√3) (√7),load_supported _,load_supported _,load_supported _,load_supported _,by
    unfold Q witness product4 core route; simp only [wiring_real,mul_assoc]⟩

/-- Precompute the rational core once, before multiplying by the Cholesky ends. -/
private lemma core_value : core = !![1,1,1,0,1,0; 1,0,-3,1,0,1; 0,-1/3,0,1,1,1/3;
    1,1/3,1,0,1/3,0; -1/3,0,1,1,0,1; 0,-1/3,0,-3,1,-1] := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [core,route_apply,rowWire,colWire,mixer,load_apply,Fin.divNat,Fin.modNat,Fin.sum_univ_succ]

local macro "computeEntries" : tactic => `(tactic| (norm_num [witness,leftEnd,rightEnd,tri,core_value,Matrix.transpose_apply,
  Matrix.mul_apply,Matrix.vecMul,dotProduct,load_apply,Fin.divNat,Fin.modNat,Fin.sum_univ_succ,Matrix.one_apply] <;> grind only))
private lemma orth (x y z : ℝ) (hx : x^2=2) (hy : y^2=3) (hz : z^2=7) : Orthogonal (witness x y z) := by
  suffices h : witness x y z * (witness x y z)ᵀ = 1 from ⟨mul_eq_one_comm.mp h,h⟩
  ext i j; fin_cases i <;> fin_cases j <;> computeEntries
lemma Q_orthogonal : Orthogonal Q := orth _ _ _ (by norm_num) (by norm_num) (by norm_num)

private lemma values (x y z : ℝ) (hx : x^2=2) (hy : y^2=3) (hz : z^2=7) :
    let m := minor (witness x y z)
    m 0 0 = -3*x*y/16 ∧ m 2 2 = -3*x*y/16 ∧ m 1 1 = -3/8 ∧ m 0 2 = 3/8 := by
  dsimp only; refine ⟨?_,?_,?_,?_⟩ <;> simp only [minor_apply] <;> computeEntries
lemma violates : ¬Bound (minors Q) := by
  obtain ⟨a,b,c,d⟩ := values (√2) (√3) (√7) (by norm_num) (by norm_num) (by norm_num)
  norm_num [Bound,minors,Q,a,b,c,d,← sq,div_pow,mul_pow]
end GS.M4
