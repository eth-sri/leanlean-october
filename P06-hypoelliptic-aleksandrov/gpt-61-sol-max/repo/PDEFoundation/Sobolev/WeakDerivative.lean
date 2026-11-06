module

public import PDEFoundation.Ambient.Basis
public import PDEFoundation.Measure.RestrictedVolume
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Lean.Elab.Tactic.Grind
public import PDEFoundation.Calculus.RegularityOrder




/-!
# Weak first derivatives on native vector domains

The raw integration-by-parts predicates remain compatible with LIH. A bundled
test-function facade packages smoothness, compact support, and support
containment for later PDE proofs.
-/

@[expose] public section

namespace PDE

/-- A smooth compactly supported test function whose topological support lies
inside `U`. -/
structure WeakTestFunction {d : ℕ} (U : Set (Vec d)) where
  toFun : Vec d → ℝ
  contDiff : ContDiff ℝ PDE.smoothOrder toFun
  hasCompactSupport : HasCompactSupport toFun
  tsupport_subset : tsupport toFun ⊆ U

instance {d : ℕ} {U : Set (Vec d)} :
    CoeFun (WeakTestFunction U) (fun _ => Vec d → ℝ) where
  coe φ := φ.toFun

variable {d : ℕ}

/-- The classical `i`th derivative of a bundled test function. -/
noncomputable def WeakTestFunction.partialDeriv
     {U : Set (Vec d)}
    (φ : WeakTestFunction U) (i : Fin d) (x : Vec d) : ℝ :=
  (fderiv ℝ φ.toFun x) (basisVec i)

variable (U : Set (Vec d))

/-- `gi` is the `i`th weak derivative of `u` on `U`. -/
def HasWeakPartialDerivOn   (i : Fin d)
    (u gi : Vec d → ℝ) : Prop :=
  ∀ φ : Vec d → ℝ,
    ContDiff ℝ PDE.smoothOrder φ →
    HasCompactSupport φ →
    tsupport φ ⊆ U →
    ∫ x in U, u x * (fderiv ℝ φ x) (basisVec i) ∂MeasureTheory.volume =
      -∫ x in U, gi x * φ x ∂MeasureTheory.volume

/-- `Du` is a coordinate weak gradient of `u` on `U`. -/
def HasWeakGradientOn
     (u : Vec d → ℝ) (Du : Vec d → Vec d) : Prop :=
  ∀ i : Fin d, HasWeakPartialDerivOn U i u (fun x => Du x i)

theorem hasWeakPartialDerivOn_iff_forall_testFunction
     {U : Set (Vec d)} {i : Fin d}
    {u gi : Vec d → ℝ} :
    HasWeakPartialDerivOn U i u gi ↔
      ∀ φ : WeakTestFunction U,
        ∫ x in U, u x * φ.partialDeriv i x ∂MeasureTheory.volume =
          -∫ x in U, gi x * φ x ∂MeasureTheory.volume := by
  constructor
  · intro h φ
    exact h φ.toFun φ.contDiff φ.hasCompactSupport φ.tsupport_subset
  · intro h φ hφSmooth hφCompact hφSupport
    exact h
      { toFun := φ
        contDiff := hφSmooth
        hasCompactSupport := hφCompact
        tsupport_subset := hφSupport }

namespace HasWeakPartialDerivOn

/-- Weak partial derivatives that are locally integrable are unique a.e. on an
open set. -/
theorem ae_eq {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    {i : Fin d} {u gi hi : Vec d → ℝ}
    (hgiLoc : MeasureTheory.LocallyIntegrableOn gi U MeasureTheory.volume)
    (hhiLoc : MeasureTheory.LocallyIntegrableOn hi U MeasureTheory.volume)
    (hgi : HasWeakPartialDerivOn U i u gi)
    (hhi : HasWeakPartialDerivOn U i u hi) :
    gi =ᵐ[volumeOn U] hi := by

  rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' hU.measurableSet]
  filter_upwards [(by
      refine hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
        (f := fun x => gi x - hi x) (hgiLoc.sub hhiLoc) ?_
      intro φ hφSmooth hφCompact hφSub
      have hφCont  := hφSmooth.continuous


      have hgiφK :
          MeasureTheory.IntegrableOn (fun x => gi x * φ x) (tsupport φ)
            MeasureTheory.volume := by
        simpa [smul_eq_mul] using
          (hgiLoc.integrableOn_compact_subset hφSub hφCompact.isCompact).smul_continuousOn hφCont.continuousOn hφCompact.isCompact
      have hhiφK :
          MeasureTheory.IntegrableOn (fun x => hi x * φ x) (tsupport φ)
            MeasureTheory.volume := by
        simpa [smul_eq_mul] using
          (hhiLoc.integrableOn_compact_subset hφSub hφCompact.isCompact).smul_continuousOn hφCont.continuousOn hφCompact.isCompact




      have hsetEq :
          ∫ x in U, gi x * φ x ∂MeasureTheory.volume =
            ∫ x in U, hi x * φ x ∂MeasureTheory.volume := by


        apply neg_injective
        rw [← (hgi φ hφSmooth hφCompact hφSub), ← (hhi φ hφSmooth hφCompact hφSub)]


      calc
        ∫ x, φ x • (gi x - hi x) ∂MeasureTheory.volume =
            ∫ x, φ x * (gi x - hi x) ∂MeasureTheory.volume := rfl
        _ = ∫ x in U, φ x * (gi x - hi x) ∂MeasureTheory.volume := by
              rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
                (by
                    intro x hx

                    simp [image_eq_zero_of_notMem_tsupport (fun hx' => hx (hφSub hx'))])]
        _ = 0 := (by
            calc
              ∫ x in U, φ x * (gi x - hi x) ∂MeasureTheory.volume =
                  ∫ x in U, (gi x * φ x - hi x * φ x)
                    ∂MeasureTheory.volume := by
                      grind
              _ = ∫ x in U, gi x * φ x ∂MeasureTheory.volume -
                    ∫ x in U, hi x * φ x ∂MeasureTheory.volume := by
                      rw [MeasureTheory.integral_sub (by
                          simpa [MeasureTheory.IntegrableOn, volumeOn] using
                            hgiφK.of_forall_sdiff_eq_zero hU.measurableSet (by
                                intro x hx
                                simp [image_eq_zero_of_notMem_tsupport hx.2])) (by
                          simpa [MeasureTheory.IntegrableOn, volumeOn] using
                            hhiφK.of_forall_sdiff_eq_zero hU.measurableSet (by
                                intro x hx
                                simp [image_eq_zero_of_notMem_tsupport hx.2]))]
              _ = 0 := by rw [hsetEq, sub_self]))] with x hx hxu
  exact sub_eq_zero.mp (hx hxu)

end HasWeakPartialDerivOn

variable {d : ℕ}

variable {U V : Set (Vec d)}

theorem HasWeakPartialDerivOn.restrict
     (_hVOpen : IsOpen V) (hVU : V ⊆ U)
    {i : Fin d} {u gi : Vec d → ℝ}
    (h : HasWeakPartialDerivOn U i u gi) :
    HasWeakPartialDerivOn V i u gi := by
  intro φ hφSmooth hφCompact hφSupport


  have hValueZero :
      ∀ x, x ∉ V → u x * (fderiv ℝ φ x) (basisVec i) = 0 := by
    intro x hx

    have hφEq  :=
      (isClosed_tsupport (f := φ)).isOpen_compl.eventually_mem (fun hx' => hx (hφSupport hx')) |>.mono
        (fun y hy => image_eq_zero_of_notMem_tsupport hy)
    rw [Filter.EventuallyEq.fderiv_eq hφEq]
    simp
  have hGradZero :
      ∀ x, x ∉ V → gi x * φ x = 0 := by
    intro x hx
    simp [image_eq_zero_of_notMem_tsupport
      (fun hx' => hx (hφSupport hx'))]


  rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        hValueZero,
    MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hGradZero,
    ← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => hValueZero x (fun hx' => hx (hVU hx'))),
    ← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => hGradZero x (fun hx' => hx (hVU hx'))),
    (h φ hφSmooth hφCompact (hφSupport.trans hVU))]

theorem HasWeakGradientOn.restrict
     (hVOpen : IsOpen V) (hVU : V ⊆ U)
    {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (h : HasWeakGradientOn U u Du) :
    HasWeakGradientOn V u Du := by
  intro i
  exact (h i).restrict hVOpen hVU

variable {U : Set (Vec d)}

theorem HasWeakPartialDerivOn.of_contDiff
     {i : Fin d} {f : Vec d → ℝ}
    (hf : ContDiff ℝ 1 f) :
    HasWeakPartialDerivOn U i f
      (fun x => (fderiv ℝ f x) (basisVec i)) := by
  intro φ hφSmooth hφSupport hφSubset
  let ei : Vec d := basisVec i
  have hfDiff : Differentiable ℝ f := hf.differentiable (by simp)
  have hφDiff : Differentiable ℝ φ :=
    hφSmooth.differentiable (by simp)
  have hfCont  := hfDiff.continuous
  have hφCont  := hφDiff.continuous

  have hfderivfCont :
      Continuous (fun x => (fderiv ℝ f x) ei) := by
    simpa [ei] using
      (hf.continuous_fderiv (by simp)).clm_apply continuous_const

  rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero,
    MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
  · simpa [ei] using
      integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
        ((hfderivfCont.mul hφCont).integrable_of_hasCompactSupport
          hφSupport.mul_left)
        ((hfCont.mul (by
            simpa [ei] using
              (hφSmooth.continuous_fderiv (by simp)).clm_apply continuous_const)).integrable_of_hasCompactSupport
          (show HasCompactSupport (fun x => (fderiv ℝ φ x) ei) by
              exact hφSupport.fderiv_apply (𝕜 := ℝ) ei).mul_left)
        ((hfCont.mul hφCont).integrable_of_hasCompactSupport
          hφSupport.mul_left)
        (fun x _ => hfDiff x) (fun x _ => hφDiff x)
  · intro x hx

    simp [image_eq_zero_of_notMem_tsupport (fun hx' => hx (hφSubset hx'))]
  · intro x hx

    have hφEq  :=
      (isClosed_tsupport (f := φ)).isOpen_compl.eventually_mem (fun hx' => hx (hφSubset hx')) |>.mono
        (fun y hy => image_eq_zero_of_notMem_tsupport hy)
    rw [Filter.EventuallyEq.fderiv_eq hφEq]
    simp

theorem HasWeakGradientOn.of_contDiff
     {f : Vec d → ℝ}
    (hf : ContDiff ℝ 1 f) :
    HasWeakGradientOn U f
      (fun x i => (fderiv ℝ f x) (basisVec i)) := by
  intro i
  exact HasWeakPartialDerivOn.of_contDiff hf

end PDE
