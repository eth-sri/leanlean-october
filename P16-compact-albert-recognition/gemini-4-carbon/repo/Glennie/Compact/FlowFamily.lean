module
public import Glennie.Compactness
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace Glennie.Compact.NativeDictionary
noncomputable section
open Glennie
set_option autoImplicit false

def extDecode (a : Fin 27 → ℝ) : Albert :=
  let b (i : Fin 26) : ℝ := a i.succ
  a 0 • (1 : Albert) +
    ⟨b 0 + b 1, -b 0 + b 1, -2 * b 1,
      (⟨b 2, b 3, -b 12, -b 13⟩, ⟨-b 18, -b 19, -b 24, b 25⟩),
      (⟨b 4, b 5, b 10, b 11⟩, ⟨b 16, b 17, b 22, -b 23⟩),
      (⟨b 6, b 7, -b 8, -b 9⟩, ⟨-b 14, -b 15, -b 20, b 21⟩)⟩

def extUnit (n : Fin 27) : Fin 27 → ℝ := fun i => if i = n then 1 else 0

end
end Glennie.Compact.NativeDictionary

namespace Glennie.Compact
noncomputable section
open Glennie
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
attribute [-instance] FloorSemiring.instCharZero RCLike.charZero_rclike

def innerDer (a b z : Albert) : Albert := jordan a (jordan b z) - jordan b (jordan a z)

def innerDerLinear (a b : Albert) : Albert →ₗ[ℝ] Albert :=
  (jordanLinear a).comp (jordanLinear b) - (jordanLinear b).comp (jordanLinear a)

@[simp] theorem innerDerLinear_apply (a b z : Albert) : innerDerLinear a b z = innerDer a b z := rfl

def IsJordanDerivation (D : Albert →ₗ[ℝ] Albert) : Prop :=
  ∀ x y, D (jordan x y) = jordan (D x) y + jordan x (D y)

def TraceFree (D : Albert →ₗ[ℝ] Albert) : Prop := ∀ x, trace (D x) = 0

theorem isJordanDerivation_innerDerLinear (a b : Albert) : IsJordanDerivation (innerDerLinear a b) := fun z x => by
  let defJ (u v : Albert) : Albert := jordanLinear (jordanLinear u v) (jordanLinear u u) - jordanLinear u (jordanLinear v (jordanLinear u u))
  let pol (x₁ x₂ x₃ y : Albert) : Albert :=
    (jordanLinear (jordanLinear x₁ y) (jordanLinear x₂ x₃) - jordanLinear x₁ (jordanLinear y (jordanLinear x₂ x₃))) +
      (jordanLinear (jordanLinear x₂ y) (jordanLinear x₃ x₁) - jordanLinear x₂ (jordanLinear y (jordanLinear x₃ x₁))) +
      (jordanLinear (jordanLinear x₃ y) (jordanLinear x₁ x₂) - jordanLinear x₃ (jordanLinear y (jordanLinear x₁ x₂)))
  have hcomm (u v : Albert) : jordanLinear u v = jordanLinear v u := by simp only [jordanLinear_apply, jordan_comm]
  have hp0 (x₁ x₂ x₃ y : Albert) : pol x₁ x₂ x₃ y = 0 := by
    rw [show pol x₁ x₂ x₃ y = (1 / 2 : ℝ) •
      (defJ (x₁ + x₂ + x₃) y - defJ (x₁ + x₂) y - defJ (x₁ + x₃) y -
        defJ (x₂ + x₃) y + defJ x₁ y + defJ x₂ y + defJ x₃ y) by
      simp only [pol, defJ, map_add, LinearMap.add_apply, hcomm x₂ x₁, hcomm x₃ x₁, hcomm x₃ x₂]; module]
    simp [defJ, jordan_identity]
  have E1 := hp0 x a z b; have E2 := hp0 x b z a
  have h : jordanLinear a (jordanLinear b (jordanLinear z x)) - jordanLinear b (jordanLinear a (jordanLinear z x)) =
      jordanLinear (jordanLinear a (jordanLinear b z) - jordanLinear b (jordanLinear a z)) x +
        jordanLinear z (jordanLinear a (jordanLinear b x) - jordanLinear b (jordanLinear a x)) := by
    simp only [pol, map_sub, LinearMap.sub_apply] at E1 E2 ⊢
    simp only [hcomm x a, hcomm x b, hcomm z a, hcomm z b, hcomm b a,
      hcomm (jordanLinear b z) (jordanLinear a x), hcomm (jordanLinear a z) (jordanLinear b x),
      hcomm (jordanLinear a (jordanLinear b z)) x, hcomm (jordanLinear b (jordanLinear a z)) x] at E1 E2 ⊢
    linear_combination (norm := module) E2 - E1
  simpa only [innerDerLinear_apply, jordanLinear_apply, innerDer] using h

theorem traceFree_innerDerLinear (a b : Albert) : TraceFree (innerDerLinear a b) := fun z => by
  change trace (jordan a (jordan b z) - jordan b (jordan a z)) = 0
  rw [trace_sub]; change inner a (jordan b z) - inner b (jordan a z) = 0
  rw [← inner_jordan_associative, ← inner_jordan_associative, jordan_comm b a, sub_self]

end
end Glennie.Compact

namespace Glennie.Compact.FlowFamily
open Glennie Glennie.Compact.NativeDictionary
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
attribute [-instance] FloorSemiring.instCharZero RCLike.charZero_rclike

def e27 : (Fin 27 → ℝ) ≃ₗ[ℝ] Albert := automorphismBasis.equivFun.symm

def toCoord (D : Albert →ₗ[ℝ] Albert) : (Fin 27 → ℝ) →L[ℝ] (Fin 27 → ℝ) :=
  LinearMap.toContinuousLinearMap (e27.symm.toLinearMap ∘ₗ D ∘ₗ e27.toLinearMap)

theorem toCoord_neg (D : Albert →ₗ[ℝ] Albert) : toCoord (-D) = -toCoord D := by ext c i; simp [toCoord]

def prodC : (Fin 27 → ℝ) →L[ℝ] (Fin 27 → ℝ) →L[ℝ] (Fin 27 → ℝ) :=
  LinearMap.toContinuousLinearMap
    (LinearMap.toContinuousLinearMap.toLinearMap.comp
      ((jordanLinear.compl₁₂ e27.toLinearMap e27.toLinearMap).compr₂ e27.symm.toLinearMap))

def traceC : (Fin 27 → ℝ) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (traceLinear ∘ₗ e27.toLinearMap)

def flowC (D : Albert →ₗ[ℝ] Albert) (t : ℝ) : (Fin 27 → ℝ) →L[ℝ] (Fin 27 → ℝ) := NormedSpace.exp (t • toCoord D)

def flowAut (D : Albert →ₗ[ℝ] Albert) (hD : IsJordanDerivation D) (hT : TraceFree D) (t : ℝ) : CompactAutomorphism := by
  let +nondep : NormedAlgebra ℚ ((Fin 27 → ℝ) →L[ℝ] (Fin 27 → ℝ)) := .restrictScalars ℚ ℝ _
  have hm1 : flowC D t * flowC (-D) t = 1 := by
    rw [flowC, flowC, toCoord_neg, ← NormedSpace.exp_add_of_commute ((((Commute.refl (toCoord D)).neg_right).smul_left t).smul_right t),
      ← smul_add, add_neg_cancel, smul_zero, NormedSpace.exp_zero]
  have hm2 : flowC (-D) t * flowC D t = 1 := by
    rw [flowC, flowC, toCoord_neg, ← NormedSpace.exp_add_of_commute ((((Commute.refl (toCoord D)).neg_left).smul_left t).smul_right t),
      ← smul_add, neg_add_cancel, smul_zero, NormedSpace.exp_zero]
  have hl (c : Fin 27 → ℝ) : flowC D t (flowC (-D) t c) = c := by rw [← mul_apply_eq_comp, hm1, one_apply_eq_self]
  have hr (c : Fin 27 → ℝ) : flowC (-D) t (flowC D t c) = c := by rw [← mul_apply_eq_comp, hm2, one_apply_eq_self]
  have hf0 (E : Albert →ₗ[ℝ] Albert) (c : Fin 27 → ℝ) : flowC E 0 c = c := by simp [flowC]
  have hd_app (E : Albert →ₗ[ℝ] Albert) (c : Fin 27 → ℝ) (s : ℝ) :
      HasDerivAt (fun r => flowC E r c) (toCoord E (flowC E s c)) s :=
    (((hasDerivAt_exp_smul_const' (toCoord E) s).clm_apply (hasDerivAt_const s c)).congr_deriv
      (by rw [mul_apply_eq_comp, map_zero, add_zero]; rfl))
  let fl : Albert ≃ₗ[ℝ] Albert := LinearEquiv.ofLinearMap
    (e27.toLinearMap ∘ₗ (flowC D t).toLinearMap ∘ₗ e27.symm.toLinearMap)
    (e27.toLinearMap ∘ₗ (flowC (-D) t).toLinearMap ∘ₗ e27.symm.toLinearMap)
    (LinearMap.ext fun _ => by simp [hl]) (LinearMap.ext fun _ => by simp [hr])
  refine ⟨fl, fun x y => ?_, fun x => ?_⟩
  · let a := e27.symm x; let b := e27.symm y
    have hder (s : ℝ) : HasDerivAt (fun r => flowC (-D) r (prodC (flowC D r a) (flowC D r b))) 0 s := by
      have hw := (prodC.hasFDerivAt.comp_hasDerivAt s (hd_app D a s)).clm_apply (hd_app D b s)
      refine ((hasDerivAt_exp_smul_const (toCoord (-D)) s).clm_apply hw).congr_deriv ?_
      have hleib (u v : Fin 27 → ℝ) : toCoord D (prodC u v) = prodC (toCoord D u) v + prodC u (toCoord D v) := by
        change e27.symm (D (e27 (e27.symm (jordan (e27 u) (e27 v))))) = _
        rw [e27.apply_symm_apply, hD, map_add]; simp [toCoord, prodC]
      dsimp only [Function.comp_def]
      rw [mul_apply_eq_comp, toCoord_neg, neg_apply, ← map_add, ← hleib, neg_add_cancel, map_zero]
    have hc := is_const_of_deriv_eq_zero (fun s => (hder s).differentiableAt) (fun s => (hder s).deriv) t 0
    simp only [hf0] at hc
    have h2 := congrArg (flowC D t) hc; rw [hl] at h2
    simpa [fl, a, b, show ∀ u v, prodC u v = e27.symm (jordan (e27 u) (e27 v)) from fun _ _ => rfl] using congrArg e27 h2.symm
  · let a := e27.symm x
    have hder (s : ℝ) : HasDerivAt (fun r => traceC (flowC D r a)) 0 s :=
      (traceC.hasFDerivAt.comp_hasDerivAt s (hd_app D a s)).congr_deriv
        (by change trace (e27 (e27.symm (D _))) = 0; rw [e27.apply_symm_apply]; exact hT _)
    simpa [fl, hf0, traceC, a] using is_const_of_deriv_eq_zero (fun s => (hder s).differentiableAt) (fun s => (hder s).deriv) t 0

def spanCoord {k : ℕ} (D : Fin k → Albert →ₗ[ℝ] Albert) :
    (Fin k → ℝ) →L[ℝ] ((Fin 27 → ℝ) →L[ℝ] (Fin 27 → ℝ)) :=
  ∑ n, (ContinuousLinearMap.proj n : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (toCoord (D n))

def spanDer {k : ℕ} (D : Fin k → Albert →ₗ[ℝ] Albert) (s : Fin k → ℝ) : Albert →ₗ[ℝ] Albert := ∑ n, s n • D n

theorem spanDer_der {k : ℕ} {D : Fin k → Albert →ₗ[ℝ] Albert}
    (hD : ∀ n, IsJordanDerivation (D n)) (s : Fin k → ℝ) : IsJordanDerivation (spanDer D s) :=
  Finset.sum_induction (fun n => s n • D n) IsJordanDerivation
    (fun _ _ h1 h2 x y => by simp only [LinearMap.add_apply, h1 x y, h2 x y, jordan_add_left, jordan_add_right]; module)
    (fun _ _ => by simp)
    (fun n _ x y => by simp only [LinearMap.smul_apply, hD n x y, jordan_smul_left, jordan_smul_right, smul_add])

theorem spanDer_tf {k : ℕ} {D : Fin k → Albert →ₗ[ℝ] Albert}
    (hT : ∀ n, TraceFree (D n)) (s : Fin k → ℝ) : TraceFree (spanDer D s) :=
  Finset.sum_induction (fun n => s n • D n) TraceFree
    (fun _ _ h1 h2 x => by simp [h1 x, h2 x]) (fun _ => by simp [trace]) (fun n _ x => by simp [hT n x])

def familyC {k : ℕ} (D : Fin k → Albert →ₗ[ℝ] Albert) (s : Fin k → ℝ) : (Fin 27 → ℝ) →L[ℝ] (Fin 27 → ℝ) :=
  NormedSpace.exp (spanCoord D s)

def movedFrame {k : ℕ} (D : Fin 3 → Fin k → Albert →ₗ[ℝ] Albert)
    (hD : ∀ a n, IsJordanDerivation (D a n)) (hT : ∀ a n, TraceFree (D a n))
    (T : Fin 3 → Fin 3 → Albert) (a : Fin 3) (s : Fin k → ℝ) : Fin 3 → Albert :=
  fun i => (flowAut (spanDer (D a) s) (spanDer_der (hD a) s) (spanDer_tf (hT a) s) 1).equiv (T a i)

theorem movedFrame_eq {k : ℕ} (D : Fin 3 → Fin k → Albert →ₗ[ℝ] Albert)
    (hD : ∀ a n, IsJordanDerivation (D a n)) (hT : ∀ a n, TraceFree (D a n))
    (T : Fin 3 → Fin 3 → Albert) (a : Fin 3) (s : Fin k → ℝ) (i : Fin 3) :
    movedFrame D hD hT T a s i = e27 (familyC (D a) s (e27.symm (T a i))) := by
  change e27 (flowC (spanDer (D a) s) 1 (e27.symm (T a i))) = _
  rw [flowC, one_smul, show toCoord (spanDer (D a) s) = spanCoord (D a) s from
    ContinuousLinearMap.ext fun _ => by simp [toCoord, spanDer, spanCoord, sum_apply], familyC]

theorem movedFrame_frame {k : ℕ} (D : Fin 3 → Fin k → Albert →ₗ[ℝ] Albert)
    (hD : ∀ a n, IsJordanDerivation (D a n)) (hT : ∀ a n, TraceFree (D a n))
    (T : Fin 3 → Fin 3 → Albert) (a : Fin 3) (hF : Frame (T a)) (s : Fin k → ℝ) :
    Frame (movedFrame D hD hT T a s) := CompactAutomorphism.map_frame _ (T a) hF

theorem movedFrame_zero {k : ℕ} (D : Fin 3 → Fin k → Albert →ₗ[ℝ] Albert)
    (hD : ∀ a n, IsJordanDerivation (D a n)) (hT : ∀ a n, TraceFree (D a n))
    (T : Fin 3 → Fin 3 → Albert) (a : Fin 3) : movedFrame D hD hT T a 0 = T a := by
  funext i; rw [movedFrame_eq, familyC, map_zero, NormedSpace.exp_zero, one_apply_eq_self, e27.apply_symm_apply]

theorem continuous_movedFrame {k : ℕ} (D : Fin 3 → Fin k → Albert →ₗ[ℝ] Albert)
    (hD : ∀ a n, IsJordanDerivation (D a n)) (hT : ∀ a n, TraceFree (D a n))
    (T : Fin 3 → Fin 3 → Albert) (a i : Fin 3) :
    Continuous fun s : Fin k → ℝ => movedFrame D hD hT T a s i := by
  let +nondep : NormedAlgebra ℚ ((Fin 27 → ℝ) →L[ℝ] (Fin 27 → ℝ)) := .restrictScalars ℚ ℝ _
  simp only [movedFrame_eq, familyC]
  exact e27.toLinearMap.continuous_of_finiteDimensional.comp
    ((NormedSpace.exp_continuous.comp (spanCoord (D a)).continuous).clm_apply continuous_const)

def partnerIndex : Fin 20 → Fin 27 :=
  ![3, 4, 5, 6, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 11, 12, 13, 14]

def contextIndex : Fin 20 → Fin 3 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1]

def rowIndex : Fin 20 → Fin 3 × Fin 3 × Fin 3 :=
  ![(0,0,0), (0,0,1), (0,0,2), (0,1,0), (0,1,1), (0,1,2),
    (0,2,0), (0,2,1), (1,0,0), (1,0,1), (1,0,2), (1,1,0),
    (1,1,1), (1,1,2), (1,2,0), (1,2,1), (2,0,0), (2,0,1),
    (2,1,0), (2,1,1)]

def direction (n : Fin 20) : Albert →ₗ[ℝ] Albert :=
  innerDerLinear (extDecode (extUnit 1)) (extDecode (extUnit (partnerIndex n)))

def contextDirection (a : Fin 3) (n : Fin 20) : Albert →ₗ[ℝ] Albert :=
  if a = contextIndex n then direction n else 0

theorem contextDirection_isJordanDerivation (a : Fin 3) (n : Fin 20) :
    IsJordanDerivation (contextDirection a n) := by
  unfold contextDirection; split_ifs <;> [exact isJordanDerivation_innerDerLinear _ _; exact fun _ _ => by simp]

theorem contextDirection_traceFree (a : Fin 3) (n : Fin 20) :
    TraceFree (contextDirection a n) := by
  unfold contextDirection; split_ifs <;> [exact traceFree_innerDerLinear _ _; exact fun _ => by simp [trace]]

def atomTangent (T : Fin 3 → Fin 3 → Albert) (n : Fin 20) (a i : Fin 3) : Albert :=
  if a = contextIndex n then direction n (T a i) else 0

def jacobianEntry (T : Fin 3 → Fin 3 → Albert) (r n : Fin 20) : ℝ :=
  trace (jordan (jordan (atomTangent T n 0 (rowIndex r).1) (T 1 (rowIndex r).2.1)) (T 2 (rowIndex r).2.2) +
    jordan (jordan (T 0 (rowIndex r).1) (atomTangent T n 1 (rowIndex r).2.1)) (T 2 (rowIndex r).2.2) +
    jordan (jordan (T 0 (rowIndex r).1) (T 1 (rowIndex r).2.1)) (atomTangent T n 2 (rowIndex r).2.2))

def rowLedger (T : Fin 3 → Fin 3 → Albert) (s : Fin 20 → ℝ) : Fin 20 → ℝ := fun r =>
  ledger (movedFrame contextDirection contextDirection_isJordanDerivation contextDirection_traceFree T 0 s)
    (movedFrame contextDirection contextDirection_isJordanDerivation contextDirection_traceFree T 1 s)
    (movedFrame contextDirection contextDirection_isJordanDerivation contextDirection_traceFree T 2 s)
    (rowIndex r).1 (rowIndex r).2.1 (rowIndex r).2.2

def rowLedgerDeriv (T : Fin 3 → Fin 3 → Albert) : (Fin 20 → ℝ) →L[ℝ] (Fin 20 → ℝ) :=
  ContinuousLinearMap.pi fun r =>
    let i := (rowIndex r).1; let j := (rowIndex r).2.1; let l := (rowIndex r).2.2
    traceC.comp ((prodC (prodC (e27.symm (T 0 i)) (e27.symm (T 1 j)))).comp
        ((spanCoord (contextDirection 2)).flip (e27.symm (T 2 l))) +
      (prodC.comp ((prodC (e27.symm (T 0 i))).comp
          ((spanCoord (contextDirection 1)).flip (e27.symm (T 1 j))) +
        (prodC.comp ((spanCoord (contextDirection 0)).flip (e27.symm (T 0 i)))).flip
          (e27.symm (T 1 j)))).flip (e27.symm (T 2 l)))

theorem hasStrictFDerivAt_rowLedger (T : Fin 3 → Fin 3 → Albert) :
    HasStrictFDerivAt (rowLedger T) (rowLedgerDeriv T) 0 :=
  hasStrictFDerivAt_pi'.2 fun r => by
    rw [rowLedgerDeriv, ContinuousLinearMap.proj_pi]
    have hfam (a : Fin 3) (v : Fin 27 → ℝ) :
        HasStrictFDerivAt (fun s => familyC (contextDirection a) s v) ((spanCoord (contextDirection a)).flip v) 0 := by
      have hexp : HasStrictFDerivAt
          (NormedSpace.exp : ((Fin 27 → ℝ) →L[ℝ] (Fin 27 → ℝ)) → ((Fin 27 → ℝ) →L[ℝ] (Fin 27 → ℝ)))
          (1 : ((Fin 27 → ℝ) →L[ℝ] (Fin 27 → ℝ)) →L[ℝ] ((Fin 27 → ℝ) →L[ℝ] (Fin 27 → ℝ)))
          (spanCoord (contextDirection a) 0) := by rw [map_zero]; exact hasStrictFDerivAt_exp_zero
      have hf : HasStrictFDerivAt (familyC (contextDirection a)) (spanCoord (contextDirection a)) 0 :=
        (hexp.comp (0 : Fin 20 → ℝ) (spanCoord (contextDirection a)).hasStrictFDerivAt).congr_fderiv
          (ContinuousLinearMap.ext fun _ => by simp)
      exact (hf.clm_apply (hasStrictFDerivAt_const v 0)).congr_fderiv (by rw [ContinuousLinearMap.comp_zero, zero_add])
    have hf0 (a : Fin 3) (v : Fin 27 → ℝ) : familyC (contextDirection a) 0 v = v := by
      rw [familyC, map_zero, NormedSpace.exp_zero, one_apply_eq_self]
    have h := traceC.hasStrictFDerivAt.comp (0 : Fin 20 → ℝ)
      ((prodC.hasStrictFDerivAt.comp 0
        ((prodC.hasStrictFDerivAt.comp 0 (hfam 0 (e27.symm (T 0 (rowIndex r).1)))).clm_apply
          (hfam 1 (e27.symm (T 1 (rowIndex r).2.1))))).clm_apply (hfam 2 (e27.symm (T 2 (rowIndex r).2.2))))
    simp only [hf0] at h
    rwa [show (fun s => rowLedger T s r) = fun s =>
      traceC (prodC (prodC (familyC (contextDirection 0) s (e27.symm (T 0 (rowIndex r).1)))
        (familyC (contextDirection 1) s (e27.symm (T 1 (rowIndex r).2.1))))
        (familyC (contextDirection 2) s (e27.symm (T 2 (rowIndex r).2.2)))) from
      funext fun s => by simp [rowLedger, ledger, movedFrame_eq, traceC, prodC]]

theorem rowLedgerDeriv_single (T : Fin 3 → Fin 3 → Albert) (r n : Fin 20) :
    rowLedgerDeriv T (Pi.single n 1) r = jacobianEntry T r n := by
  have hsp (a : Fin 3) (x : Albert) :
      e27 (spanCoord (contextDirection a) (Pi.single n 1) (e27.symm x)) =
        if a = contextIndex n then direction n x else 0 := by
    rw [spanCoord, sum_apply, Finset.sum_eq_single n]
    · simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, Pi.single_eq_same,
        one_smul, toCoord, LinearMap.coe_toContinuousLinearMap', LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
        e27.apply_symm_apply, contextDirection]
      split_ifs <;> rfl
    · intro m _ hm; simp [Pi.single_eq_of_ne hm]
    · intro hn; exact absurd (Finset.mem_univ n) hn
  rw [rowLedgerDeriv, ContinuousLinearMap.pi_apply, jacobianEntry, trace_add, trace_add]
  simp only [ContinuousLinearMap.comp_apply, add_apply, ContinuousLinearMap.flip_apply,
    traceC, prodC, LinearMap.coe_toContinuousLinearMap', LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, map_add,
    jordanLinear_apply, traceLinear_apply, e27.apply_symm_apply, hsp, atomTangent]
  ring

end
end Glennie.Compact.FlowFamily
