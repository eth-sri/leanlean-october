module

public import Glennie.Native.CubicIdentity
public import Glennie.SectorModel
public import Glennie.Automorphism
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace Glennie.Compact.InnerDerivation

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

def defect (mul : V →ₗ[ℝ] V →ₗ[ℝ] V) (x y : V) : V :=
  mul (mul x y) (mul x x) - mul x (mul y (mul x x))

def polar (mul : V →ₗ[ℝ] V →ₗ[ℝ] V) (x₁ x₂ x₃ y : V) : V :=
  (mul (mul x₁ y) (mul x₂ x₃) - mul x₁ (mul y (mul x₂ x₃))) +
    (mul (mul x₂ y) (mul x₃ x₁) - mul x₂ (mul y (mul x₃ x₁))) +
    (mul (mul x₃ y) (mul x₁ x₂) - mul x₃ (mul y (mul x₁ x₂)))

def der (mul : V →ₗ[ℝ] V →ₗ[ℝ] V) (a b z : V) : V :=
  mul a (mul b z) - mul b (mul a z)

theorem polar_eq_half (mul : V →ₗ[ℝ] V →ₗ[ℝ] V) (comm : ∀ x y, mul x y = mul y x)
    (x₁ x₂ x₃ y : V) :
    polar mul x₁ x₂ x₃ y = (1 / 2 : ℝ) •
      (defect mul (x₁ + x₂ + x₃) y - defect mul (x₁ + x₂) y - defect mul (x₁ + x₃) y -
        defect mul (x₂ + x₃) y + defect mul x₁ y + defect mul x₂ y + defect mul x₃ y) := by
  simp only [polar, defect, map_add, LinearMap.add_apply]
  simp only [comm x₂ x₁, comm x₃ x₁, comm x₃ x₂]; module

theorem polar_eq_zero (mul : V →ₗ[ℝ] V →ₗ[ℝ] V) (comm : ∀ x y, mul x y = mul y x)
    (hJ : ∀ x y, defect mul x y = 0) (x₁ x₂ x₃ y : V) :
    polar mul x₁ x₂ x₃ y = 0 := by
  rw [polar_eq_half mul comm]; simp [hJ]

theorem der_leibniz (mul : V →ₗ[ℝ] V →ₗ[ℝ] V) (comm : ∀ x y, mul x y = mul y x)
    (hJ : ∀ x y, defect mul x y = 0) (a b z x : V) :
    der mul a b (mul z x) = mul (der mul a b z) x + mul z (der mul a b x) := by
  have E1 := polar_eq_zero mul comm hJ x a z b
  have E2 := polar_eq_zero mul comm hJ x b z a
  simp only [polar, der, map_sub, LinearMap.sub_apply] at E1 E2 ⊢
  simp only [comm x a, comm x b, comm z a, comm z b, comm b a,
    comm (mul b z) (mul a x), comm (mul a z) (mul b x),
    comm (mul a (mul b z)) x, comm (mul b (mul a z)) x] at E1 E2 ⊢
  linear_combination (norm := module) E2 - E1

end
end Glennie.Compact.InnerDerivation

namespace Glennie.Compact

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

theorem jordanLinear_comm (x y : Albert) : jordanLinear x y = jordanLinear y x := by
  simpa only [jordanLinear_apply] using jordan_comm x y

theorem defect_jordanLinear (x y : Albert) : InnerDerivation.defect jordanLinear x y = 0 := by
  simp only [InnerDerivation.defect, jordanLinear_apply, jordan_identity, sub_self]

def innerDer (a b z : Albert) : Albert := jordan a (jordan b z) - jordan b (jordan a z)

theorem innerDer_jordan (a b z x : Albert) :
    innerDer a b (jordan z x) = jordan (innerDer a b z) x + jordan z (innerDer a b x) := by
  simpa only [InnerDerivation.der, jordanLinear_apply, innerDer] using
    InnerDerivation.der_leibniz jordanLinear jordanLinear_comm defect_jordanLinear a b z x

theorem trace_innerDer (a b z : Albert) : trace (innerDer a b z) = 0 := by
  have h1 := inner_jordan_associative a b z
  have h2 := inner_jordan_associative b a z
  simp only [inner] at h1 h2
  rw [innerDer, trace_sub, ← h1, ← h2, jordan_comm b a, sub_self]

def innerDerLinear (a b : Albert) : Albert →ₗ[ℝ] Albert :=
  (jordanLinear a).comp (jordanLinear b) - (jordanLinear b).comp (jordanLinear a)

@[simp] theorem innerDerLinear_apply (a b z : Albert) :
    innerDerLinear a b z = innerDer a b z := rfl

def IsJordanDerivation (D : Albert →ₗ[ℝ] Albert) : Prop :=
  ∀ x y, D (jordan x y) = jordan (D x) y + jordan x (D y)

def TraceFree (D : Albert →ₗ[ℝ] Albert) : Prop := ∀ x, trace (D x) = 0

theorem isJordanDerivation_innerDerLinear (a b : Albert) :
    IsJordanDerivation (innerDerLinear a b) := fun x y => by
  simp only [innerDerLinear_apply]; exact innerDer_jordan a b x y

theorem traceFree_innerDerLinear (a b : Albert) : TraceFree (innerDerLinear a b) := fun z => by
  rw [innerDerLinear_apply]; exact trace_innerDer a b z

theorem IsJordanDerivation.zero : IsJordanDerivation 0 := fun _ _ => by simp

theorem IsJordanDerivation.add {D E : Albert →ₗ[ℝ] Albert} (hD : IsJordanDerivation D)
    (hE : IsJordanDerivation E) : IsJordanDerivation (D + E) := fun x y => by
  simp only [LinearMap.add_apply, hD x y, hE x y, jordan_add_left, jordan_add_right]; module

theorem IsJordanDerivation.smul (r : ℝ) {D : Albert →ₗ[ℝ] Albert}
    (hD : IsJordanDerivation D) : IsJordanDerivation (r • D) := fun x y => by
  simp only [LinearMap.smul_apply, hD x y, jordan_smul_left, jordan_smul_right, smul_add]

theorem IsJordanDerivation.sum {ι : Type*} (s : Finset ι) (D : ι → Albert →ₗ[ℝ] Albert)
    (hD : ∀ i ∈ s, IsJordanDerivation (D i)) : IsJordanDerivation (∑ i ∈ s, D i) :=
  Finset.sum_induction D IsJordanDerivation (fun _ _ h₁ h₂ => h₁.add h₂)
    IsJordanDerivation.zero hD

theorem TraceFree.zero : TraceFree 0 := fun _ => by simp [trace]

theorem TraceFree.add {D E : Albert →ₗ[ℝ] Albert} (hD : TraceFree D) (hE : TraceFree E) :
    TraceFree (D + E) := fun x => by
  simp only [LinearMap.add_apply, trace_add, hD x, hE x, add_zero]

theorem TraceFree.smul (r : ℝ) {D : Albert →ₗ[ℝ] Albert} (hD : TraceFree D) :
    TraceFree (r • D) := fun x => by
  simp only [LinearMap.smul_apply, trace_smul, hD x, mul_zero]

theorem TraceFree.sum {ι : Type*} (s : Finset ι) (D : ι → Albert →ₗ[ℝ] Albert)
    (hD : ∀ i ∈ s, TraceFree (D i)) : TraceFree (∑ i ∈ s, D i) :=
  Finset.sum_induction D TraceFree (fun _ _ h₁ h₂ => h₁.add h₂) TraceFree.zero hD

end
end Glennie.Compact

namespace Glennie.Compact.NativeDictionary

noncomputable section

set_option autoImplicit false

def extDecode (a : Fin 27 → ℝ) : Albert :=
  ⟨a 0, a 1, a 2,
    (⟨a 3, a 4, a 5, a 6⟩, ⟨a 7, a 8, a 9, a 10⟩),
    (⟨a 11, a 12, a 13, a 14⟩, ⟨a 15, a 16, a 17, a 18⟩),
    (⟨a 19, a 20, a 21, a 22⟩, ⟨a 23, a 24, a 25, a 26⟩)⟩

def extEncode (x : Albert) : Fin 27 → ℝ :=
  ![x.d0, x.d1, x.d2,
    x.o01.1.re, x.o01.1.imI, x.o01.1.imJ, x.o01.1.imK,
    x.o01.2.re, x.o01.2.imI, x.o01.2.imJ, x.o01.2.imK,
    x.o02.1.re, x.o02.1.imI, x.o02.1.imJ, x.o02.1.imK,
    x.o02.2.re, x.o02.2.imI, x.o02.2.imJ, x.o02.2.imK,
    x.o12.1.re, x.o12.1.imI, x.o12.1.imJ, x.o12.1.imK,
    x.o12.2.re, x.o12.2.imI, x.o12.2.imJ, x.o12.2.imK]

def extEquiv : (Fin 27 → ℝ) ≃ₗ[ℝ] Albert where
  toFun := extDecode
  invFun := extEncode
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv a := by funext i; fin_cases i <;> rfl
  right_inv _ := rfl

def archivalHiddenBasis (r c : Fin 3) (w : ℂ) : Albert :=
  hiddenAlbert (fun i j => if i = r ∧ j = c then w else 0)

end
end Glennie.Compact.NativeDictionary

namespace Glennie.Compact.Flows

open Glennie.Compact.NativeDictionary

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

def toCoord (D : Albert →ₗ[ℝ] Albert) : (Fin 27 → ℝ) →L[ℝ] (Fin 27 → ℝ) :=
  LinearMap.toContinuousLinearMap
    (extEquiv.symm.toLinearMap ∘ₗ D ∘ₗ extEquiv.toLinearMap)

theorem toCoord_apply (D : Albert →ₗ[ℝ] Albert) (a : Fin 27 → ℝ) :
    toCoord D a = extEquiv.symm (D (extEquiv a)) := rfl

def prodC : (Fin 27 → ℝ) →L[ℝ] (Fin 27 → ℝ) →L[ℝ] (Fin 27 → ℝ) :=
  LinearMap.toContinuousLinearMap
    (LinearMap.toContinuousLinearMap.toLinearMap.comp
      ((jordanLinear.compl₁₂ extEquiv.toLinearMap extEquiv.toLinearMap).compr₂
        extEquiv.symm.toLinearMap))

theorem prodC_apply (a b : Fin 27 → ℝ) :
    prodC a b = extEquiv.symm (jordan (extEquiv a) (extEquiv b)) := rfl

theorem prodC_symm (x y : Albert) :
    prodC (extEquiv.symm x) (extEquiv.symm y) = extEquiv.symm (jordan x y) := by
  simp only [prodC_apply, LinearEquiv.apply_symm_apply]

def traceC : (Fin 27 → ℝ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (traceLinear ∘ₗ extEquiv.toLinearMap)

theorem traceC_apply (a : Fin 27 → ℝ) : traceC a = trace (extEquiv a) := rfl

theorem toCoord_prodC (D : Albert →ₗ[ℝ] Albert) (hD : IsJordanDerivation D)
    (a b : Fin 27 → ℝ) :
    toCoord D (prodC a b) = prodC (toCoord D a) b + prodC a (toCoord D b) := by
  have h := hD (extEquiv a) (extEquiv b)
  simp only [toCoord_apply, prodC_apply, LinearEquiv.apply_symm_apply, h, map_add]

def flowC (D : Albert →ₗ[ℝ] Albert) (t : ℝ) : (Fin 27 → ℝ) →L[ℝ] (Fin 27 → ℝ) :=
  NormedSpace.exp (t • toCoord D)

def flowInvC (D : Albert →ₗ[ℝ] Albert) (t : ℝ) : (Fin 27 → ℝ) →L[ℝ] (Fin 27 → ℝ) :=
  NormedSpace.exp (t • -toCoord D)

theorem flowC_zero (D : Albert →ₗ[ℝ] Albert) : flowC D 0 = 1 := by simp [flowC]

theorem flowInvC_zero (D : Albert →ₗ[ℝ] Albert) : flowInvC D 0 = 1 := by simp [flowInvC]

theorem flowC_mul_flowInvC (D : Albert →ₗ[ℝ] Albert) (t : ℝ) :
    flowC D t * flowInvC D t = 1 := by
  let +nondep : NormedAlgebra ℚ ((Fin 27 → ℝ) →L[ℝ] (Fin 27 → ℝ)) := .restrictScalars ℚ ℝ _
  have h : Commute (t • toCoord D) (t • -toCoord D) :=
    (((Commute.refl (toCoord D)).neg_right).smul_left t).smul_right t
  rw [flowC, flowInvC, ← NormedSpace.exp_add_of_commute h, ← smul_add, add_neg_cancel,
    smul_zero, NormedSpace.exp_zero]

theorem flowInvC_mul_flowC (D : Albert →ₗ[ℝ] Albert) (t : ℝ) :
    flowInvC D t * flowC D t = 1 := by
  let +nondep : NormedAlgebra ℚ ((Fin 27 → ℝ) →L[ℝ] (Fin 27 → ℝ)) := .restrictScalars ℚ ℝ _
  have h : Commute (t • -toCoord D) (t • toCoord D) :=
    (((Commute.refl (toCoord D)).neg_left).smul_left t).smul_right t
  rw [flowC, flowInvC, ← NormedSpace.exp_add_of_commute h, ← smul_add, neg_add_cancel,
    smul_zero, NormedSpace.exp_zero]

theorem flowC_flowInvC_apply (D : Albert →ₗ[ℝ] Albert) (t : ℝ) (c : Fin 27 → ℝ) :
    flowC D t (flowInvC D t c) = c := by
  rw [← mul_apply_eq_comp, flowC_mul_flowInvC, one_apply_eq_self]

theorem flowInvC_flowC_apply (D : Albert →ₗ[ℝ] Albert) (t : ℝ) (c : Fin 27 → ℝ) :
    flowInvC D t (flowC D t c) = c := by
  rw [← mul_apply_eq_comp, flowInvC_mul_flowC, one_apply_eq_self]

theorem hasDerivAt_flowC_apply (D : Albert →ₗ[ℝ] Albert) (c : Fin 27 → ℝ) (t : ℝ) :
    HasDerivAt (fun s => flowC D s c) (toCoord D (flowC D t c)) t := by
  have h : HasDerivAt (fun s => flowC D s c) ((toCoord D * flowC D t) c + flowC D t 0) t :=
    (hasDerivAt_exp_smul_const' (toCoord D) t).clm_apply (hasDerivAt_const t c)
  exact h.congr_deriv (by rw [mul_apply_eq_comp, map_zero, add_zero])

theorem hasDerivAt_flowInvC (D : Albert →ₗ[ℝ] Albert) (t : ℝ) :
    HasDerivAt (fun s => flowInvC D s) (flowInvC D t * -toCoord D) t := by
  simpa [flowInvC] using hasDerivAt_exp_smul_const (-toCoord D) t

theorem flowC_prodC (D : Albert →ₗ[ℝ] Albert) (hD : IsJordanDerivation D)
    (a b : Fin 27 → ℝ) (t : ℝ) :
    flowC D t (prodC a b) = prodC (flowC D t a) (flowC D t b) := by
  have hderiv (s : ℝ) : HasDerivAt
      (fun r => flowInvC D r (prodC (flowC D r a) (flowC D r b))) 0 s := by
    have hu := hasDerivAt_flowC_apply D a s
    have hv := hasDerivAt_flowC_apply D b s
    have hpu : HasDerivAt (fun r => prodC (flowC D r a))
        (prodC (toCoord D (flowC D s a))) s := prodC.hasFDerivAt.comp_hasDerivAt s hu
    have hall := (hasDerivAt_flowInvC D s).clm_apply (hpu.clm_apply hv)
    exact hall.congr_deriv (by
      rw [mul_apply_eq_comp, neg_apply, ← map_add, ← toCoord_prodC D hD, neg_add_cancel, map_zero])
  have hconst := is_const_of_deriv_eq_zero
    (fun s => (hderiv s).differentiableAt) (fun s => (hderiv s).deriv) t 0
  simp only [flowC_zero, flowInvC_zero, one_apply_eq_self] at hconst
  have h2 := congrArg (flowC D t) hconst
  rw [flowC_flowInvC_apply] at h2
  exact h2.symm

theorem flowC_traceC (D : Albert →ₗ[ℝ] Albert) (hT : TraceFree D)
    (a : Fin 27 → ℝ) (t : ℝ) :
    traceC (flowC D t a) = traceC a := by
  have hderiv (s : ℝ) : HasDerivAt (fun r => traceC (flowC D r a)) 0 s := by
    refine (traceC.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_flowC_apply D a s)).congr_deriv ?_
    rw [traceC_apply, toCoord_apply, LinearEquiv.apply_symm_apply, hT (extEquiv (flowC D s a))]
  have hconst := is_const_of_deriv_eq_zero
    (fun s => (hderiv s).differentiableAt) (fun s => (hderiv s).deriv) t 0
  simpa only [flowC_zero, one_apply_eq_self] using hconst

def flowL (D : Albert →ₗ[ℝ] Albert) (t : ℝ) : Albert →ₗ[ℝ] Albert :=
  extEquiv.toLinearMap ∘ₗ (flowC D t : (Fin 27 → ℝ) →ₗ[ℝ] (Fin 27 → ℝ)) ∘ₗ
    extEquiv.symm.toLinearMap

def flowInvL (D : Albert →ₗ[ℝ] Albert) (t : ℝ) : Albert →ₗ[ℝ] Albert :=
  extEquiv.toLinearMap ∘ₗ (flowInvC D t : (Fin 27 → ℝ) →ₗ[ℝ] (Fin 27 → ℝ)) ∘ₗ
    extEquiv.symm.toLinearMap

def flow (D : Albert →ₗ[ℝ] Albert) (t : ℝ) : Albert ≃ₗ[ℝ] Albert :=
  LinearEquiv.ofLinearMap (flowL D t) (flowInvL D t)
    (LinearMap.ext fun _ => by simp [flowL, flowInvL, flowC_flowInvC_apply])
    (LinearMap.ext fun _ => by simp [flowL, flowInvL, flowInvC_flowC_apply])

theorem flow_apply (D : Albert →ₗ[ℝ] Albert) (t : ℝ) (x : Albert) :
    flow D t x = extEquiv (flowC D t (extEquiv.symm x)) := rfl

theorem flow_jordan (D : Albert →ₗ[ℝ] Albert) (hD : IsJordanDerivation D) (t : ℝ)
    (x y : Albert) : flow D t (jordan x y) = jordan (flow D t x) (flow D t y) := by
  simp only [flow_apply]
  rw [← prodC_symm, flowC_prodC D hD, prodC_apply, LinearEquiv.apply_symm_apply]

theorem flow_trace (D : Albert →ₗ[ℝ] Albert) (hT : TraceFree D) (t : ℝ) (x : Albert) :
    trace (flow D t x) = trace x := by
  have h := flowC_traceC D hT (extEquiv.symm x) t
  simp only [traceC_apply, LinearEquiv.apply_symm_apply] at h
  rw [flow_apply]; exact h

def flowAut (D : Albert →ₗ[ℝ] Albert) (hD : IsJordanDerivation D) (hT : TraceFree D)
    (t : ℝ) : CompactAutomorphism where
  equiv := flow D t
  map_jordan := flow_jordan D hD t
  map_trace := flow_trace D hT t

theorem flowAut_apply (D : Albert →ₗ[ℝ] Albert) (hD : IsJordanDerivation D)
    (hT : TraceFree D) (t : ℝ) (x : Albert) :
    (flowAut D hD hT t).equiv x = flow D t x := rfl

end
end Glennie.Compact.Flows

namespace Glennie.Compact.FlowFamily

open Glennie.Compact.NativeDictionary Glennie.Compact.Flows

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] extEquiv toCoord prodC traceC

def spanCoord {k : ℕ} (D : Fin k → Albert →ₗ[ℝ] Albert) :
    (Fin k → ℝ) →L[ℝ] ((Fin 27 → ℝ) →L[ℝ] (Fin 27 → ℝ)) :=
  ∑ n, (ContinuousLinearMap.proj n : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (toCoord (D n))

theorem spanCoord_apply {k : ℕ} (D : Fin k → Albert →ₗ[ℝ] Albert) (s : Fin k → ℝ) :
    spanCoord D s = ∑ n, s n • toCoord (D n) := by
  simp only [spanCoord, sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply]

def spanDer {k : ℕ} (D : Fin k → Albert →ₗ[ℝ] Albert) (s : Fin k → ℝ) :
    Albert →ₗ[ℝ] Albert := ∑ n, s n • D n

theorem spanDer_apply {k : ℕ} (D : Fin k → Albert →ₗ[ℝ] Albert) (s : Fin k → ℝ)
    (x : Albert) : spanDer D s x = ∑ n, s n • D n x := by
  simp only [spanDer, LinearMap.sum_apply, LinearMap.smul_apply]

theorem toCoord_spanDer {k : ℕ} (D : Fin k → Albert →ₗ[ℝ] Albert) (s : Fin k → ℝ) :
    toCoord (spanDer D s) = spanCoord D s := by
  refine ContinuousLinearMap.ext fun a => ?_
  simp only [toCoord_apply, spanDer_apply, map_sum, map_smul, spanCoord_apply, sum_apply, smul_apply]

theorem spanDer_single {k : ℕ} (D : Fin k → Albert →ₗ[ℝ] Albert) (n : Fin k) (x : Albert) :
    spanDer D (Pi.single n 1) x = D n x := by
  rw [spanDer_apply, Finset.sum_eq_single n]
  · rw [Pi.single_eq_same, one_smul]
  · intro m _ hm; rw [Pi.single_eq_of_ne hm, zero_smul]
  · intro hn; exact absurd (Finset.mem_univ n) hn

theorem spanDer_isJordanDerivation {k : ℕ} {D : Fin k → Albert →ₗ[ℝ] Albert}
    (hD : ∀ n, IsJordanDerivation (D n)) (s : Fin k → ℝ) :
    IsJordanDerivation (spanDer D s) :=
  IsJordanDerivation.sum Finset.univ (fun n => s n • D n) (fun n _ => (hD n).smul (s n))

theorem spanDer_traceFree {k : ℕ} {D : Fin k → Albert →ₗ[ℝ] Albert}
    (hT : ∀ n, TraceFree (D n)) (s : Fin k → ℝ) : TraceFree (spanDer D s) :=
  TraceFree.sum Finset.univ (fun n => s n • D n) (fun n _ => (hT n).smul (s n))

def familyC {k : ℕ} (D : Fin k → Albert →ₗ[ℝ] Albert) (s : Fin k → ℝ) :
    (Fin 27 → ℝ) →L[ℝ] (Fin 27 → ℝ) := NormedSpace.exp (spanCoord D s)

theorem flowC_spanDer {k : ℕ} (D : Fin k → Albert →ₗ[ℝ] Albert) (s : Fin k → ℝ) :
    flowC (spanDer D s) 1 = familyC D s := by
  rw [flowC, one_smul, toCoord_spanDer, familyC]

theorem familyC_zero {k : ℕ} (D : Fin k → Albert →ₗ[ℝ] Albert) : familyC D 0 = 1 := by
  rw [familyC, map_zero, NormedSpace.exp_zero]

theorem familyC_zero_apply {k : ℕ} (D : Fin k → Albert →ₗ[ℝ] Albert) (v : Fin 27 → ℝ) :
    familyC D 0 v = v := by rw [familyC_zero, one_apply_eq_self]

theorem hasStrictFDerivAt_familyC {k : ℕ} (D : Fin k → Albert →ₗ[ℝ] Albert) :
    HasStrictFDerivAt (familyC D) (spanCoord D) 0 := by
  have h0 : spanCoord D 0 = 0 := map_zero _
  have hexp : HasStrictFDerivAt
      (NormedSpace.exp : ((Fin 27 → ℝ) →L[ℝ] (Fin 27 → ℝ)) → ((Fin 27 → ℝ) →L[ℝ] (Fin 27 → ℝ)))
      (1 : ((Fin 27 → ℝ) →L[ℝ] (Fin 27 → ℝ)) →L[ℝ] ((Fin 27 → ℝ) →L[ℝ] (Fin 27 → ℝ)))
      (spanCoord D 0) := by rw [h0]; exact hasStrictFDerivAt_exp_zero
  refine (hexp.comp (0 : Fin k → ℝ) (spanCoord D).hasStrictFDerivAt).congr_fderiv ?_
  exact ContinuousLinearMap.ext fun h => by rw [ContinuousLinearMap.comp_apply, one_apply_eq_self]

theorem hasStrictFDerivAt_familyC_apply {k : ℕ} (D : Fin k → Albert →ₗ[ℝ] Albert)
    (v : Fin 27 → ℝ) :
    HasStrictFDerivAt (fun s => familyC D s v) ((spanCoord D).flip v) 0 := by
  refine ((hasStrictFDerivAt_familyC D).clm_apply
    (hasStrictFDerivAt_const v (0 : Fin k → ℝ))).congr_fderiv ?_
  rw [ContinuousLinearMap.comp_zero, zero_add]

theorem continuous_familyC {k : ℕ} (D : Fin k → Albert →ₗ[ℝ] Albert) :
    Continuous (familyC D) := by
  let +nondep : NormedAlgebra ℚ ((Fin 27 → ℝ) →L[ℝ] (Fin 27 → ℝ)) := .restrictScalars ℚ ℝ _
  exact NormedSpace.exp_continuous.comp (spanCoord D).continuous

theorem continuous_familyC_apply {k : ℕ} (D : Fin k → Albert →ₗ[ℝ] Albert)
    (v : Fin 27 → ℝ) : Continuous fun s => familyC D s v :=
  (continuous_familyC D).clm_apply continuous_const

def familyAut {k : ℕ} (D : Fin k → Albert →ₗ[ℝ] Albert)
    (hD : ∀ n, IsJordanDerivation (D n)) (hT : ∀ n, TraceFree (D n)) (s : Fin k → ℝ) :
    CompactAutomorphism :=
  flowAut (spanDer D s) (spanDer_isJordanDerivation hD s) (spanDer_traceFree hT s) 1

theorem familyAut_apply {k : ℕ} (D : Fin k → Albert →ₗ[ℝ] Albert)
    (hD : ∀ n, IsJordanDerivation (D n)) (hT : ∀ n, TraceFree (D n)) (s : Fin k → ℝ)
    (x : Albert) :
    (familyAut D hD hT s).equiv x = extEquiv (familyC D s (extEquiv.symm x)) := by
  rw [familyAut, flowAut_apply, flow_apply, flowC_spanDer]

def movedFrame {k : ℕ} (D : Fin 3 → Fin k → Albert →ₗ[ℝ] Albert)
    (hD : ∀ a n, IsJordanDerivation (D a n)) (hT : ∀ a n, TraceFree (D a n))
    (T : Fin 3 → Fin 3 → Albert) (a : Fin 3) (s : Fin k → ℝ) : Fin 3 → Albert :=
  fun i => (familyAut (D a) (hD a) (hT a) s).equiv (T a i)

theorem movedFrame_frame {k : ℕ} (D : Fin 3 → Fin k → Albert →ₗ[ℝ] Albert)
    (hD : ∀ a n, IsJordanDerivation (D a n)) (hT : ∀ a n, TraceFree (D a n))
    (T : Fin 3 → Fin 3 → Albert) (a : Fin 3) (hF : Frame (T a)) (s : Fin k → ℝ) :
    Frame (movedFrame D hD hT T a s) :=
  (familyAut (D a) (hD a) (hT a) s).map_frame (T a) hF

theorem movedFrame_zero {k : ℕ} (D : Fin 3 → Fin k → Albert →ₗ[ℝ] Albert)
    (hD : ∀ a n, IsJordanDerivation (D a n)) (hT : ∀ a n, TraceFree (D a n))
    (T : Fin 3 → Fin 3 → Albert) (a : Fin 3) : movedFrame D hD hT T a 0 = T a := by
  funext i; show (familyAut (D a) (hD a) (hT a) 0).equiv (T a i) = T a i
  rw [familyAut_apply, familyC_zero_apply, LinearEquiv.apply_symm_apply]

theorem movedFrame_coord {k : ℕ} (D : Fin 3 → Fin k → Albert →ₗ[ℝ] Albert)
    (hD : ∀ a n, IsJordanDerivation (D a n)) (hT : ∀ a n, TraceFree (D a n))
    (T : Fin 3 → Fin 3 → Albert) (a : Fin 3) (s : Fin k → ℝ) (i : Fin 3) :
    extEquiv.symm (movedFrame D hD hT T a s i) = familyC (D a) s (extEquiv.symm (T a i)) := by
  show extEquiv.symm ((familyAut (D a) (hD a) (hT a) s).equiv (T a i)) = _
  rw [familyAut_apply, LinearEquiv.symm_apply_apply]

theorem continuous_movedFrame_coord {k : ℕ} (D : Fin 3 → Fin k → Albert →ₗ[ℝ] Albert)
    (hD : ∀ a n, IsJordanDerivation (D a n)) (hT : ∀ a n, TraceFree (D a n))
    (T : Fin 3 → Fin 3 → Albert) (a i : Fin 3) :
    Continuous fun s : Fin k → ℝ => extEquiv.symm (movedFrame D hD hT T a s i) := by
  simp only [movedFrame_coord]; exact continuous_familyC_apply (D a) _

theorem ledger_movedFrame {k : ℕ} (D : Fin 3 → Fin k → Albert →ₗ[ℝ] Albert)
    (hD : ∀ a n, IsJordanDerivation (D a n)) (hT : ∀ a n, TraceFree (D a n))
    (T : Fin 3 → Fin 3 → Albert) (s : Fin k → ℝ) (i j l : Fin 3) :
    ledger (movedFrame D hD hT T 0 s) (movedFrame D hD hT T 1 s) (movedFrame D hD hT T 2 s)
        i j l =
      traceC (prodC (prodC (familyC (D 0) s (extEquiv.symm (T 0 i)))
        (familyC (D 1) s (extEquiv.symm (T 1 j)))) (familyC (D 2) s (extEquiv.symm (T 2 l)))) := by
  simp only [ledger, movedFrame, familyAut_apply, traceC_apply, prodC_apply,
    LinearEquiv.apply_symm_apply]

theorem hasStrictFDerivAt_ledgerC {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f0 f1 f2 : E → (Fin 27 → ℝ)} {f0' f1' f2' : E →L[ℝ] (Fin 27 → ℝ)} {x : E}
    (h0 : HasStrictFDerivAt f0 f0' x) (h1 : HasStrictFDerivAt f1 f1' x)
    (h2 : HasStrictFDerivAt f2 f2' x) :
    HasStrictFDerivAt (fun y => traceC (prodC (prodC (f0 y) (f1 y)) (f2 y)))
      (traceC.comp ((prodC (prodC (f0 x) (f1 x))).comp f2' +
        (prodC.comp ((prodC (f0 x)).comp f1' + (prodC.comp f0').flip (f1 x))).flip (f2 x))) x :=
  traceC.hasStrictFDerivAt.comp x
    ((prodC.hasStrictFDerivAt.comp x
      ((prodC.hasStrictFDerivAt.comp x h0).clm_apply h1)).clm_apply h2)

theorem ledgerDerivC_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p q r : Fin 27 → ℝ) (f0' f1' f2' : E →L[ℝ] (Fin 27 → ℝ)) (h : E) :
    (traceC.comp ((prodC (prodC p q)).comp f2' +
        (prodC.comp ((prodC p).comp f1' + (prodC.comp f0').flip q)).flip r)) h =
      traceC (prodC (prodC (f0' h) q) r) + traceC (prodC (prodC p (f1' h)) r) +
        traceC (prodC (prodC p q) (f2' h)) := by
  simp only [ContinuousLinearMap.comp_apply, add_apply, ContinuousLinearMap.flip_apply, map_add]
  ring

def movedLedgerDeriv {k : ℕ} (D : Fin 3 → Fin k → Albert →ₗ[ℝ] Albert)
    (T : Fin 3 → Fin 3 → Albert) (i j l : Fin 3) : (Fin k → ℝ) →L[ℝ] ℝ :=
  traceC.comp ((prodC (prodC (extEquiv.symm (T 0 i)) (extEquiv.symm (T 1 j)))).comp
      ((spanCoord (D 2)).flip (extEquiv.symm (T 2 l))) +
    (prodC.comp ((prodC (extEquiv.symm (T 0 i))).comp
        ((spanCoord (D 1)).flip (extEquiv.symm (T 1 j))) +
      (prodC.comp ((spanCoord (D 0)).flip (extEquiv.symm (T 0 i)))).flip
        (extEquiv.symm (T 1 j)))).flip (extEquiv.symm (T 2 l)))

theorem hasStrictFDerivAt_ledger_movedFrame {k : ℕ} (D : Fin 3 → Fin k → Albert →ₗ[ℝ] Albert)
    (hD : ∀ a n, IsJordanDerivation (D a n)) (hT : ∀ a n, TraceFree (D a n))
    (T : Fin 3 → Fin 3 → Albert) (i j l : Fin 3) :
    HasStrictFDerivAt
      (fun s => ledger (movedFrame D hD hT T 0 s) (movedFrame D hD hT T 1 s)
        (movedFrame D hD hT T 2 s) i j l)
      (movedLedgerDeriv D T i j l) 0 := by
  have h := hasStrictFDerivAt_ledgerC
    (hasStrictFDerivAt_familyC_apply (D 0) (extEquiv.symm (T 0 i)))
    (hasStrictFDerivAt_familyC_apply (D 1) (extEquiv.symm (T 1 j)))
    (hasStrictFDerivAt_familyC_apply (D 2) (extEquiv.symm (T 2 l)))
  simp only [familyC_zero_apply] at h
  have hfun : (fun s => ledger (movedFrame D hD hT T 0 s) (movedFrame D hD hT T 1 s)
      (movedFrame D hD hT T 2 s) i j l) = fun s =>
      traceC (prodC (prodC (familyC (D 0) s (extEquiv.symm (T 0 i)))
        (familyC (D 1) s (extEquiv.symm (T 1 j)))) (familyC (D 2) s (extEquiv.symm (T 2 l)))) :=
    funext fun s => ledger_movedFrame D hD hT T s i j l
  rw [hfun]; exact h

theorem movedLedgerDeriv_apply {k : ℕ} (D : Fin 3 → Fin k → Albert →ₗ[ℝ] Albert)
    (T : Fin 3 → Fin 3 → Albert) (i j l : Fin 3) (h : Fin k → ℝ) :
    movedLedgerDeriv D T i j l h =
      trace (jordan (jordan (spanDer (D 0) h (T 0 i)) (T 1 j)) (T 2 l)) +
        trace (jordan (jordan (T 0 i) (spanDer (D 1) h (T 1 j))) (T 2 l)) +
        trace (jordan (jordan (T 0 i) (T 1 j)) (spanDer (D 2) h (T 2 l))) := by
  rw [movedLedgerDeriv, ledgerDerivC_apply]
  simp only [ContinuousLinearMap.flip_apply, ← toCoord_spanDer, toCoord_apply, traceC_apply,
    prodC_apply, LinearEquiv.apply_symm_apply]

def partnerBasis : Fin 20 → Albert :=
  ![complexAlbert 0 0 0 1 0 0, complexAlbert 0 0 0 Complex.I 0 0,
    complexAlbert 0 0 0 0 1 0, complexAlbert 0 0 0 0 Complex.I 0,
    archivalHiddenBasis 0 0 1, archivalHiddenBasis 0 0 Complex.I,
    archivalHiddenBasis 0 1 1, archivalHiddenBasis 0 1 Complex.I,
    archivalHiddenBasis 0 2 1, archivalHiddenBasis 0 2 Complex.I,
    archivalHiddenBasis 1 0 1, archivalHiddenBasis 1 0 Complex.I,
    archivalHiddenBasis 1 1 1, archivalHiddenBasis 1 1 Complex.I,
    archivalHiddenBasis 1 2 1, archivalHiddenBasis 1 2 Complex.I,
    archivalHiddenBasis 0 1 1, archivalHiddenBasis 0 1 Complex.I,
    archivalHiddenBasis 0 2 1, archivalHiddenBasis 0 2 Complex.I]

def contextIndex : Fin 20 → Fin 3 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1]

def rowIndex : Fin 20 → Fin 3 × Fin 3 × Fin 3 :=
  ![(0,0,0), (0,0,1), (0,0,2), (0,1,0), (0,1,1), (0,1,2),
    (0,2,0), (0,2,1), (1,0,0), (1,0,1), (1,0,2), (1,1,0),
    (1,1,1), (1,1,2), (1,2,0), (1,2,1), (2,0,0), (2,0,1),
    (2,1,0), (2,1,1)]

def direction (n : Fin 20) : Albert →ₗ[ℝ] Albert :=
  innerDerLinear (diagonalAlbert 1 (-1) 0) (partnerBasis n)

def contextDirection (a : Fin 3) (n : Fin 20) : Albert →ₗ[ℝ] Albert :=
  if a = contextIndex n then direction n else 0

theorem contextDirection_isJordanDerivation (a : Fin 3) (n : Fin 20) :
    IsJordanDerivation (contextDirection a n) := by
  unfold contextDirection; split_ifs
  · exact isJordanDerivation_innerDerLinear _ _
  · exact IsJordanDerivation.zero

theorem contextDirection_traceFree (a : Fin 3) (n : Fin 20) :
    TraceFree (contextDirection a n) := by
  unfold contextDirection; split_ifs
  · exact traceFree_innerDerLinear _ _
  · exact TraceFree.zero

theorem contextDirection_apply (a : Fin 3) (n : Fin 20) (x : Albert) :
    contextDirection a n x = if a = contextIndex n then direction n x else 0 := by
  unfold contextDirection; split_ifs <;> rfl

def atomTangent (T : Fin 3 → Fin 3 → Albert) (n : Fin 20) (a i : Fin 3) : Albert :=
  if a = contextIndex n then direction n (T a i) else 0

def jacobianEntry (T : Fin 3 → Fin 3 → Albert) (r n : Fin 20) : ℝ :=
  trace (jordan (jordan (atomTangent T n 0 (rowIndex r).1) (T 1 (rowIndex r).2.1))
      (T 2 (rowIndex r).2.2) +
    jordan (jordan (T 0 (rowIndex r).1) (atomTangent T n 1 (rowIndex r).2.1))
      (T 2 (rowIndex r).2.2) +
    jordan (jordan (T 0 (rowIndex r).1) (T 1 (rowIndex r).2.1))
      (atomTangent T n 2 (rowIndex r).2.2))

def rowLedger (T : Fin 3 → Fin 3 → Albert) (s : Fin 20 → ℝ) : Fin 20 → ℝ := fun r =>
  ledger (movedFrame contextDirection contextDirection_isJordanDerivation
      contextDirection_traceFree T 0 s)
    (movedFrame contextDirection contextDirection_isJordanDerivation
      contextDirection_traceFree T 1 s)
    (movedFrame contextDirection contextDirection_isJordanDerivation
      contextDirection_traceFree T 2 s)
    (rowIndex r).1 (rowIndex r).2.1 (rowIndex r).2.2

def rowLedgerDeriv (T : Fin 3 → Fin 3 → Albert) : (Fin 20 → ℝ) →L[ℝ] (Fin 20 → ℝ) :=
  ContinuousLinearMap.pi fun r =>
    movedLedgerDeriv contextDirection T (rowIndex r).1 (rowIndex r).2.1 (rowIndex r).2.2

theorem hasStrictFDerivAt_rowLedger (T : Fin 3 → Fin 3 → Albert) :
    HasStrictFDerivAt (rowLedger T) (rowLedgerDeriv T) 0 := by
  refine hasStrictFDerivAt_pi'.2 fun r => ?_
  rw [rowLedgerDeriv, ContinuousLinearMap.proj_pi]
  exact hasStrictFDerivAt_ledger_movedFrame contextDirection contextDirection_isJordanDerivation
    contextDirection_traceFree T _ _ _

theorem rowLedgerDeriv_single (T : Fin 3 → Fin 3 → Albert) (r n : Fin 20) :
    rowLedgerDeriv T (Pi.single n 1) r = jacobianEntry T r n := by
  rw [rowLedgerDeriv, ContinuousLinearMap.pi_apply, movedLedgerDeriv_apply, jacobianEntry,
    trace_add, trace_add]
  simp only [spanDer_single, contextDirection_apply, atomTangent]

end
end Glennie.Compact.FlowFamily
