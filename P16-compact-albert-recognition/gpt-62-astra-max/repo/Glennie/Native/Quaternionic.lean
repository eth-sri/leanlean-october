module
public import Glennie.Compact.CyclicTraceNullR01
public import Glennie.Native.AlgebraLaws
public import Mathlib.LinearAlgebra.Matrix.Trace
/-! The first quaternion in each octonion gives a special subalgebra. Its
vanishing theorem uses the same associative cyclic trace as the defect test. -/
@[expose] public section
namespace Glennie.Quaternionic
open Compact.CyclicTraceNullR01
noncomputable section
set_option maxHeartbeats 2500000
private abbrev M := Matrix (Fin 3) (Fin 3) (Quaternion ℝ)
def space : Submodule ℝ Albert where
  carrier := {x | x.o01.2 = 0 ∧ x.o02.2 = 0 ∧ x.o12.2 = 0}
  zero_mem' := by simp
  add_mem' := by rintro x y ⟨a,b,c⟩ ⟨d,e,f⟩; simp_all
  smul_mem' := by rintro r y ⟨a,b,c⟩; simp_all

private def prodQ (x y : space) : space := ⟨jordan x y,by
  rcases x.2 with ⟨a,b,c⟩; rcases y.2 with ⟨d,e,f⟩
  simp [space,jordan_o01,jordan_o02,jordan_o12,octMul,octConj, *]⟩
private def ρ : space →ₗ[ℝ] M where
  toFun x := fun i j => (toMatrix x i j).1
  map_add' x y := by
    funext i j; change (toMatrix (x+y:space) i j).1 = (toMatrix x i j).1 + (toMatrix y i j).1
    fin_cases i <;> fin_cases j <;> ext <;> simp [toMatrix,octScalar,octConj]
  map_smul' r y := by
    funext i j; change (toMatrix (r • y) i j).1 = r • (toMatrix y i j).1
    fin_cases i <;> fin_cases j <;> ext <;> simp [toMatrix,octScalar,octConj,smul_eq_mul]
private theorem ρ_apply (a : space) (i j) : ρ a i j = (toMatrix a i j).1 := rfl
private def τ : M →ₗ[ℝ] ℝ := (QuaternionAlgebra.reₗ (-1:ℝ) 0 (-1)).comp (Matrix.traceLinearMap (Fin 3) ℝ (Quaternion ℝ))
local macro "qcalc" : tactic => `(tactic| simp [ρ_apply,τ,prodQ,symmProd,Matrix.mul_apply,Matrix.trace,Matrix.diag,Fin.sum_univ_three,
  toMatrix,octScalar,octConj,octMul,jordan_o01,jordan_o02,jordan_o12,jordan_d0,jordan_d1,jordan_d2,octDot_coordinates,
  smul_eq_mul,Quaternion.re_mul,Quaternion.imI_mul,Quaternion.imJ_mul,Quaternion.imK_mul, *] <;> ring)
private theorem homQ (x y : space) : ρ (prodQ x y) = symmProd (ρ x) (ρ y) := by
  rcases x.2 with ⟨a,b,c⟩; rcases y.2 with ⟨d,e,f⟩
  ext i j <;> fin_cases i <;> fin_cases j <;> qcalc
private theorem realPair (x y : space) : inner x y = τ (ρ x * ρ y) := by
  rcases x.2 with ⟨a,b,c⟩; rcases y.2 with ⟨d,e,f⟩
  change inner _ _ = (ρ x * ρ y).trace.re
  simp only [inner_coordinates]; qcalc
private theorem cyclic (a b : M) : τ (a*b) = τ (b*a) := by
  change (a*b).trace.re = (b*a).trace.re; qcalc

private theorem coeQ (a b : space) : ((quadraticWith prodQ a b : space) : Albert) = U a b := rfl
private theorem coeP (a b : space) : ((prodQ a b : space) : Albert) = jordan a b := rfl

theorem vanishes {x y z : Albert} (hx : x ∈ space) (hy : y ∈ space) (hz : z ∈ space) : phi x y z = 0 := by
  have h := phiWith_eq_zero_of_compatible_trace prodQ (fun a b : space => inner a b) ρ τ homQ realPair cyclic ⟨x,hx⟩ ⟨y,hy⟩ ⟨z,hz⟩
  simp only [phiWith, Submodule.coe_sub, coeQ, coeP] at h; exact h
end
end Glennie.Quaternionic
