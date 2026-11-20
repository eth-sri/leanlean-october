module

public import HypoellipticAleksandrov.Parabolic.Transposition.Envelope
import Mathlib

/-! # The adjoint estimate under a supersolution envelope

Apply the generator inequality to a smooth approximation to the modulus of a
test. Integration by parts cancels the only terms without a pointwise sign.
-/

@[expose] public noncomputable section
namespace HypoellipticAleksandrov.Parabolic.Transposition
open Hypoellipticity Set Filter MeasureTheory
open scoped Topology

theorem discard_error {a b C : ℝ} (h : ∀ ε : ℝ, 0 < ε → a ≤ b + ε*C) : a ≤ b := by
  have hc : Continuous (fun ε : ℝ => b + ε*C) := by fun_prop
  have he := ge_of_tendsto (hc.continuousWithinAt (s := Ioi 0) (x := 0)) (mem_of_superset self_mem_nhdsWithin h)
  simpa using he

variable {d k : ℕ} {U : Domain d}

theorem int_cont (K : IsCompact (closure (U : Set (TimeVelocity d)))) {f : TimeVelocity d → ℝ}
    (hf : Continuous f) : IntegrableOn f U := hf.continuousOn.integrableOn_compact K |>.mono_set subset_closure

private theorem kato_point {X : Fin (k+1) → Vector d} (φ : Test U) {B : Field d} {ε M : ℝ} (he : 0 < ε)
    (hM : 0 ≤ M) (z : TimeVelocity d) (hB : 0 ≤ B.val z) (hL : generator X B.val z ≤ -M) :
    let ψ := compTest (modulus ε) (sm_modulus he) (modulus_zero he) φ
    M*|φ z| ≤ (B.val z * |adjoint X φ z| + ε*(M+B.val z * |potential X z|)) +
      (B.val z * adjoint X ψ z - generator X B.val z * ψ z) := by
  dsimp only
  let s := φ z; let A := adjoint X φ z; let c := potential X z
  let t := modulus ε s; let t' := deriv (modulus ε) s
  have hb := modulus_bounds he s
  have ha : -|A| ≤ t'*A := (neg_le_of_abs_le (abs_mul t' A ▸
    (mul_le_mul_of_nonneg_right (slope_bound he s) (abs_nonneg A)).trans_eq (one_mul _)))
  have hd : -(ε*|c|) ≤ c*(t-t'*s) := neg_le_of_abs_le (by
    rw [abs_mul,mul_comm ε]; exact mul_le_mul_of_nonneg_left (defect_bound he _) (abs_nonneg _))
  have hh := mul_nonneg (modulus_convex he s) (Finset.sum_nonneg (s := Finset.univ)
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) => sq_nonneg (along (X i.succ) φ z)))
  have hA : -|A|-ε*|c| ≤ adjoint X (compTest (modulus ε) (sm_modulus he) (modulus_zero he) φ) z := by
    rw [adjoint_chain]; change _ ≤ t'*A + deriv (deriv (modulus ε)) s * _ + c*(t-t'*s)
    linarith only [ha,hd,hh]
  change M*|s| ≤ (B.val z*|A|+ε*(M+B.val z*|c|))+ (B.val z*_ - generator X B.val z*t)
  nlinarith only [mul_le_mul_of_nonneg_left hA hB,mul_le_mul_of_nonneg_right hL hb.1,
    mul_le_mul_of_nonneg_left hb.2.2 hM]

theorem adjoint_estimate (K : IsCompact (closure (U : Set (TimeVelocity d)))) (X : Fin (k+1) → Vector d)
    (B : Field d) {M : TimeVelocity d → ℝ} (cm : Continuous M) (hM : ∀ z ∈ U, 0 ≤ M z) (hB : ∀ z ∈ U, 0 ≤ B.val z)
    (hL : ∀ z ∈ U, generator X B.val z ≤ -M z) (φ : Test U) :
    (∫ z in U, M z*|φ z|) ≤ ∫ z in U, B.val z * |adjoint X φ z| := by
  let C := ∫ z in U, M z+B.val z*|potential X z|
  apply discard_error (C := C); intro ε he
  let ψ := compTest (modulus ε) (sm_modulus he) (modulus_zero he) φ
  have cM := φ.contDiff.continuous; have cB := B.prop.continuous; have cA := (adjoint X φ).contDiff.continuous
  have cA' := (adjoint X ψ).contDiff.continuous; have cψ := ψ.contDiff.continuous
  have cL := (generator_sm X B.prop).continuous; have cc := (potential_sm X).continuous
  have inter : (∫ z in U, B.val z * adjoint X ψ z) = ∫ z in U, generator X B.val z * ψ z := by
    have H := generator_pair X (onDomain U B) ψ
    rw [pair_eq,local_apply,local_apply] at H
    simpa only [applied_val] using! H
  have h := setIntegral_mono_on (s := (U : Set _)) (int_cont K (cm.mul cM.abs))
    (int_cont K (((cB.mul cA.abs).add (continuous_const.mul (cm.add (cB.mul cc.abs)))).add
      ((cB.mul cA').sub (cL.mul cψ)))) U.isOpen.measurableSet
    (fun z hz => kato_point φ he (hM z hz) z (hB z hz) (hL z hz))
  change _ ≤ ∫ z in U, (B.val z * |adjoint X φ z| + ε*(M z + B.val z*|potential X z|)) +
    (B.val z * adjoint X ψ z - generator X B.val z * ψ z) at h
  have i1 : IntegrableOn (fun z => B.val z * |adjoint X φ z|) U := int_cont K (cB.mul cA.abs)
  have i2 : IntegrableOn (fun z => ε*(M z+B.val z*|potential X z|)) U := int_cont K (continuous_const.mul (cm.add (cB.mul cc.abs)))
  have i3 : IntegrableOn (fun z => B.val z * adjoint X ψ z) U := int_cont K (cB.mul cA')
  have i4 : IntegrableOn (fun z => generator X B.val z * ψ z) U := int_cont K (cL.mul cψ)
  erw [integral_add (i1.add i2) (i3.sub i4), integral_add' i1 i2, integral_sub' i3 i4, inter, sub_self, add_zero] at h
  simpa only [integral_const_mul, C] using h

theorem min_adjoint_estimate (K : IsCompact (closure (U : Set (TimeVelocity d)))) (X : Fin (k+1) → Vector d)
    (f g : Field d) {M : TimeVelocity d → ℝ} (cm : Continuous M) (hM : ∀ z ∈ U, 0 ≤ M z) (hf : ∀ z ∈ U, 0 ≤ f.val z ∧ generator X f.val z ≤ -M z)
    (hg : ∀ z ∈ U, 0 ≤ g.val z ∧ generator X g.val z ≤ -M z) (φ : Test U) :
    (∫ z in U, M z*|φ z|) ≤ ∫ z in U, min (f.val z) (g.val z) * |adjoint X φ z| := by
  let A (z) := |adjoint X φ z|
  have hc : Continuous A := (adjoint X φ).contDiff.continuous.abs
  have hm := f.prop.continuous.min g.prop.continuous
  apply discard_error (C := ∫ z in U, A z); intro ε he
  let B : Field d := ⟨_,envelope_sm he f.prop g.prop⟩
  apply (adjoint_estimate K X B cm hM (fun z hz => (le_min (hf z hz).1 (hg z hz).1).trans (envelope_bounds he _ _ z).1)
    (fun z hz => generator_envelope X he f.prop g.prop z (hf z hz).2 (hg z hz).2) φ).trans
  rw [← integral_const_mul]
  erw [← integral_add (int_cont K (hm.mul hc)) (int_cont K ((continuous_const (y := ε)).mul hc))]
  exact setIntegral_mono_on (int_cont K (B.prop.continuous.mul hc)) (int_cont K ((hm.mul hc).add (continuous_const.mul hc)))
    U.isOpen.measurableSet (fun z _ => (mul_le_mul_of_nonneg_right (envelope_bounds he _ _ z).2 (abs_nonneg _)).trans_eq (add_mul ..))

end HypoellipticAleksandrov.Parabolic.Transposition
