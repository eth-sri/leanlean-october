module

public import PDEFoundation.Sobolev.H1.Cutoff
public import PDEFoundation.Sobolev.H1.Mean
public import PDEFoundation.Sobolev.H1.Product
public import PDEFoundation.Sobolev.H1.Truncation
public import PDEFoundation.Sobolev.H1.ZeroBoundary
public import PDEFoundation.Sobolev.W1p.ZeroBoundaryCutoff

/-!
# Compactly supported multipliers as concrete `H¹₀` tests

This file is the `p = 2` representative facade for the generic
finite-exponent zero-boundary multiplier theorem. Its constructors return the
LIH-compatible `H10Function`, so weak PDE predicates can consume the result
directly.

The main concrete test is `η² (u - k)₊`, with its value and gradient
representatives kept literal.
-/

@[expose] public section

namespace PDE

namespace H1Function

variable {d : ℕ} {U inner outer : Set (Vec d)} {K : ℝ}

/-- Multiplication by a globally smooth compactly supported function whose
topological support lies in `U` has an explicit supported smooth
approximation. -/
noncomputable def
    supportedSmoothApproximation_mulContDiffHasCompactSupport
    (hU : IsOpenBoundedConvexDomain U) (u : H1Function U)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφCompact : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) :
    (u.mulContDiffHasCompactSupport hφ hφCompact).SupportedSmoothApproximation := by
  exact
    u.toW1pFunction.supportedSmoothApproximation_mulContDiffHasCompactSupport
      hU (by norm_num) (by norm_num) hφ hφCompact hφU

/-- LIH-compatible constructor: a globally smooth compactly supported
multiplier turns an `H1Function` into a concrete `H10Function`. -/
noncomputable def mulContDiffHasCompactSupportToH10
    (u : H1Function U) (hU : IsOpenBoundedConvexDomain U)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφCompact : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) :
    H10Function U :=
  (u.mulContDiffHasCompactSupport hφ hφCompact).toH10Function
    (u.supportedSmoothApproximation_mulContDiffHasCompactSupport
      hU hφ hφCompact hφU)

variable (u : H1Function U) (hU : IsOpenBoundedConvexDomain U) {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφCompact : HasCompactSupport φ) (hφU : tsupport φ ⊆ U)

@[simp]
theorem mulContDiffHasCompactSupportToH10_toH1Function
     :
    (u.mulContDiffHasCompactSupportToH10
      hU hφ hφCompact hφU).toH1Function =
        u.mulContDiffHasCompactSupport hφ hφCompact :=
  rfl

@[simp]
theorem mulContDiffHasCompactSupportToH10_toFun
     :
    (u.mulContDiffHasCompactSupportToH10
      hU hφ hφCompact hφU).toH1Function.toFun =
        fun x => φ x * u x := by
  simp

@[simp]
theorem mulContDiffHasCompactSupportToH10_grad
     :
    (u.mulContDiffHasCompactSupportToH10
      hU hφ hφCompact hφU).toH1Function.grad =
        fun x =>
          φ x • u.grad x + u x • classicalGradient φ x := by
  simp

/-- A quantitative cutoff supported in `U`, packaged as a concrete
LIH-compatible `H10Function`. -/
noncomputable def mulCutoffToH10
    (u : H1Function U) (hU : IsOpenBoundedConvexDomain U)
    (η : QuantitativeSmoothCutoff inner outer K) (houter : outer ⊆ U) :
    H10Function U :=
  u.mulContDiffHasCompactSupportToH10
    hU η.smooth η.hasCompactSupport (η.tsupport_subset.trans houter)

variable (u : H1Function U) (hU : IsOpenBoundedConvexDomain U) (η : QuantitativeSmoothCutoff inner outer K) (houter : outer ⊆ U)

@[simp]
theorem mulCutoffToH10_toH1Function
     :
    (u.mulCutoffToH10 hU η houter).toH1Function = u.mulCutoff η :=
  rfl

@[simp]
theorem mulCutoffToH10_toFun
     :
    (u.mulCutoffToH10 hU η houter).toH1Function.toFun =
      fun x => η x * u x := by
  simp

@[simp]
theorem mulCutoffToH10_grad
     :
    (u.mulCutoffToH10 hU η houter).toH1Function.grad =
      fun x =>
        η x • u.grad x +
          u x • classicalGradient η.toFun x := by
  simp

/-- The exact hole-filling test `η² (u-k)`, packaged as a concrete
LIH-compatible `H10Function`. Unlike the De Giorgi test below, this
constructor does not truncate the value. -/
noncomputable def mulCutoffSqSubConstToH10
    (hU : IsOpenBoundedConvexDomain U) (u : H1Function U) (k : ℝ)
    (η : QuantitativeSmoothCutoff inner outer K) (houter : outer ⊆ U) :
    H10Function U :=
  (u.subConst hU k).mulCutoffToH10 hU η.sq houter

variable (hU : IsOpenBoundedConvexDomain U) (u : H1Function U) (k : ℝ) (η : QuantitativeSmoothCutoff inner outer K) (houter : outer ⊆ U)

@[simp]
theorem mulCutoffSqSubConstToH10_toH1Function
     :
    (mulCutoffSqSubConstToH10
      hU u k η houter).toH1Function =
        (u.subConst hU k).mulCutoff η.sq :=
  rfl

@[simp]
theorem mulCutoffSqSubConstToH10_toFun
     :
    (mulCutoffSqSubConstToH10
      hU u k η houter).toH1Function.toFun =
        fun x => η x ^ 2 * (u.toFun x - k) := by
  simp

@[simp]
theorem mulCutoffSqSubConstToH10_grad
     :
    (mulCutoffSqSubConstToH10
      hU u k η houter).toH1Function.grad =
        fun x =>
          η x ^ 2 • u.grad x +
            (2 * η x * (u.toFun x - k)) •
              classicalGradient η.toFun x := by
  rw [mulCutoffSqSubConstToH10_toH1Function, mulCutoff_sq_grad]
  simp

/-- The exact De Giorgi test `η² (u-k)₊`, packaged as a concrete
LIH-compatible `H10Function`. -/
noncomputable def mulCutoffSqPositivePartSubConstToH10
    (hU : IsOpenBoundedConvexDomain U) (u : H1Function U) (k : ℝ)
    (η : QuantitativeSmoothCutoff inner outer K) (houter : outer ⊆ U) :
    H10Function U :=
  (u.positivePartSubConst hU k).mulCutoffToH10 hU η.sq houter

variable (hU : IsOpenBoundedConvexDomain U) (u : H1Function U) (k : ℝ) (η : QuantitativeSmoothCutoff inner outer K) (houter : outer ⊆ U)

@[simp]
theorem mulCutoffSqPositivePartSubConstToH10_toH1Function
     :
    (mulCutoffSqPositivePartSubConstToH10
      hU u k η houter).toH1Function =
        (u.positivePartSubConst hU k).mulCutoff η.sq :=
  rfl

@[simp]
theorem mulCutoffSqPositivePartSubConstToH10_toFun
     :
    (mulCutoffSqPositivePartSubConstToH10
      hU u k η houter).toH1Function.toFun =
        fun x => η x ^ 2 * max (u.toFun x - k) 0 := by
  simp

@[simp]
theorem mulCutoffSqPositivePartSubConstToH10_grad
     :
    (mulCutoffSqPositivePartSubConstToH10
      hU u k η houter).toH1Function.grad =
        fun x =>
          η x ^ 2 • {y | k < u.toFun y}.indicator u.grad x +
            (2 * η x * max (u.toFun x - k) 0) •
              classicalGradient η.toFun x := by
  rw [mulCutoffSqPositivePartSubConstToH10_toH1Function,
    mulCutoff_sq_grad, positivePartSubConst_toFun,
    positivePartSubConst_grad]

end H1Function

end PDE
