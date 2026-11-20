module

public import HypoellipticAleksandrov.Parabolic.Hypoellipticity.Tests
import Mathlib

/-! # The convex chain rule on the adjoint test space

For a field `X`, its unsigned formal adjoint is `X + div X`. In the chain rule
for a sum of such squares, all zeroth-order terms have the single coefficient
`L*1`. The remaining quadratic correction is nonnegative.
-/

@[expose] public noncomputable section
namespace HypoellipticAleksandrov.Parabolic.Transposition
open Hypoellipticity MeasureTheory Set
open scoped ContDiff

abbrev Vector (d : ℕ) := Fin (d+1) → Field d
variable {d k : ℕ} {U : Domain d}

section
variable (v : Vector d) (X : Fin (k+1) → Vector d) (P : ℝ → ℝ) {f g : TimeVelocity d → ℝ}
    (hP : Sm P) (hf : Sm f) (h0 : P 0 = 0) (hg : Sm g) (φ : Test U)

include v in
def along (f : TimeVelocity d → ℝ) (z : TimeVelocity d) := ∑ i, (v i).val z * pd i f z

include v in
def divergence (z : TimeVelocity d) := ∑ i, pd i (v i).val z

theorem along_sm {f : TimeVelocity d → ℝ} (hf : Sm f) : Sm (along v f) :=
  ContDiff.sum (fun i _ => (v i).prop.mul (pd_sm i hf))

theorem divergence_sm : Sm (divergence v) := ContDiff.sum (fun i _ => pd_sm i (v i).prop)

include hf hg in
theorem along_add (z) :
    along v (fun z => f z + g z) z = along v f z + along v g z := by
  simp only [along,pd,fderiv_fun_add (hf.differentiable (by simp) _) (hg.differentiable (by simp) _),
    add_apply,mul_add,Finset.sum_add_distrib]

include hf hg in
theorem along_mul (z) :
    along v (fun z => f z * g z) z = f z * along v g z + g z * along v f z := by
  simp only [along,pd,fderiv_fun_mul (hf.differentiable (by simp) _) (hg.differentiable (by simp) _),
    add_apply,smul_apply,smul_eq_mul,mul_add,Finset.sum_add_distrib,mul_left_comm,Finset.mul_sum]

theorem along_comp {f : TimeVelocity d → ℝ} {P : ℝ → ℝ}
    (hf : Sm f) (hP : Sm P) (z) : along v (P ∘ f) z = deriv P (f z) * along v f z := by
  have h := ((hP.differentiable (by simp) _).hasDerivAt.comp_hasFDerivAt z
    (hf.differentiable (by simp) z).hasFDerivAt).fderiv
  simp only [along,pd,h,smul_apply,smul_eq_mul,Finset.mul_sum,mul_left_comm]

include v in
def divT : Test U →ₗ[ℝ] Test U := ∑ i, (part i).toLinearMap.comp (times (v i))

include X in
def adjoint : Test U →ₗ[ℝ] Test U :=
  -(divT (X 0)) + ∑ i : Fin k, (divT (X i.succ)).comp (divT (X i.succ))

@[simp] theorem adjoint_apply :
    adjoint X φ = -adj (X 0) φ + ∑ i : Fin k, adj (X i.succ) (adj (X i.succ) φ) := by
  simp [adjoint,divT,adj,LinearMap.sum_apply]

private theorem adj_val (z) : adj v φ z = along v φ z + divergence v z * φ z := by
  simp [adj,along,divergence,add_mul,mul_add,Finset.sum_add_distrib,Finset.sum_mul]

include v in
def zerothSq (z) := along v (divergence v) z + divergence v z ^ 2

private theorem adj_sq (z) : adj v (adj v φ) z =
    along v (along v φ) z + 2 * divergence v z * along v φ z + zerothSq v z * φ z := by
  rw [adj_val,show (adj v φ : TimeVelocity d → ℝ) = _ from funext (adj_val v φ),
    along_add v (along_sm v φ.contDiff) ((divergence_sm v).mul φ.contDiff), along_mul v (divergence_sm v) φ.contDiff]
  dsimp [zerothSq]; ring

include hP h0 φ in
/-- Act by a smooth scalar function that preserves zero; the support cannot increase. -/
def compTest : Test U :=
  ⟨P ∘ φ,hP.comp φ.contDiff,φ.hasCompactSupport.comp_left h0,
    (tsupport_comp_subset h0 φ).trans φ.tsupport_subset⟩

include X in
def potential z := -divergence (X 0) z + ∑ i : Fin k, zerothSq (X i.succ) z

theorem potential_sm : Sm (potential X) :=
  (divergence_sm _).neg.add (ContDiff.sum fun i _ => (along_sm _ (divergence_sm _)).add ((divergence_sm _).pow 2))

end

theorem adjoint_chain (X : Fin (k+1) → Vector d) (φ : Test U) {P : ℝ → ℝ} (hP : Sm P) (h0 : P 0 = 0) (z) :
    adjoint X (compTest P hP h0 φ) z = deriv P (φ z) * adjoint X φ z +
      deriv (deriv P) (φ z) * ∑ i : Fin k, (along (X i.succ) φ z)^2 +
      potential X z * (P (φ z) - deriv P (φ z) * φ z) := by
  have hd := (contDiff_infty_iff_deriv.mp hP).2
  have eq : (compTest P hP h0 φ : TimeVelocity d → ℝ) = P ∘ φ := rfl
  have sq (v : Vector d) : adj v (adj v (compTest P hP h0 φ)) z =
      deriv P (φ z) * adj v (adj v φ) z + deriv (deriv P) (φ z) * (along v φ z)^2 +
      (P (φ z) - deriv P (φ z)*φ z) * zerothSq v z := by
    rw [adj_sq,adj_sq,eq,show along v (P ∘ ⇑φ) = _ from funext (along_comp v φ.contDiff hP)]
    erw [along_mul v (hd.comp φ.contDiff) (along_sm v φ.contDiff), along_comp v φ.contDiff hd]
    dsimp; ring
  simp only [adjoint_apply,FunLike.coe_add,Pi.add_apply,FunLike.coe_neg,Pi.neg_apply,
    FunLike.coe_sum,Finset.sum_apply,sq,Finset.sum_add_distrib,← Finset.mul_sum,
    adj_val,eq,along_comp _ φ.contDiff hP,Function.comp_apply,potential] <;> ring

theorem adjoint_congr {V : Domain d} (X : Fin (k+1) → Vector d) {φ : Test U} {ψ : Test V}
    (h : (φ : TimeVelocity d → ℝ) = ψ) : (adjoint X φ : TimeVelocity d → ℝ) = adjoint X ψ := by
  have a (v : Vector d) : (adj v φ : TimeVelocity d → ℝ) = adj v ψ := funext fun x => by simp only [adj_val,h]
  funext z
  simp only [adjoint_apply,FunLike.coe_add, Pi.add_apply, FunLike.coe_neg,Pi.neg_apply, FunLike.coe_sum,Finset.sum_apply,adj_val,a,h]

end HypoellipticAleksandrov.Parabolic.Transposition
