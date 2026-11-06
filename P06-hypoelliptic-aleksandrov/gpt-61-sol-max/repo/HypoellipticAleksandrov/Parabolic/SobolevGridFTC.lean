module

public import HypoellipticAleksandrov.Parabolic.TimeVelocityMultiIndexLocalCalculus
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementSmoothResidual
import all HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamilyPairing
public import HypoellipticAleksandrov.Measure.TimeVelocity
public import PDEFoundation.Calculus.RegularityOrder



open private HypoellipticAleksandrov.Parabolic.coordinateIteratedFDeriv_hasCompactSupport from HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamilyPairing


/-!
# The all-coordinate grid fundamental theorem of calculus

This file records the ordinary multi-index having one derivative in each
time--velocity coordinate and the corresponding compact-support grid estimate.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.TimeVelocityMultiIndex

/-- One derivative in every time--velocity coordinate. -/
def allOnes (d : ℕ) : TimeVelocityMultiIndex d :=
  fun _ => 1

@[simp] theorem order_allOnes (d : ℕ) :
    (allOnes d).order = d + 1 := by
  simp [allOnes, order, timeOrder, velocity, VelocityMultiIndex.order]
  omega

end HypoellipticAleksandrov.Parabolic.TimeVelocityMultiIndex

namespace HypoellipticAleksandrov.Parabolic



private theorem enorm_le_lmarginal_coordinateFTC
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : Finset ι → (ι → ℝ) → ℝ)
    (hg : ∀ s, ContDiff ℝ 1 (g s))
    (hgsupp : ∀ s, HasCompactSupport (g s))
    (hstep : ∀ (s : Finset ι) (i : ι), i ∉ s → ∀ x,
      g (insert i s) x = fderiv ℝ (g s) x (Pi.single i 1))
    (s : Finset ι) (x : ι → ℝ) :
    ‖g ∅ x‖ₑ ≤ (∫⋯∫⁻_s, fun y => ‖g s y‖ₑ ∂fun _ => volume) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      refine ih.trans ?_
      rw [lmarginal_insert' (fun y => ‖g (insert i s) y‖ₑ)
        ((hg _).continuous.enorm.measurable) hi]
      apply lmarginal_mono
      intro y
      let q  := fun t => g s (Function.update y i t)



      have hderiv : ∀ t, deriv q t = g (insert i s) (Function.update y i t) := by
        intro t
        rw [hstep s i hi]
        have hd := ((hg s).differentiable (by norm_num) _).hasFDerivAt.comp t
          (hasDerivAt_update y i t).hasFDerivAt
        simpa only [q, Function.comp_def, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.toSpanSingleton_apply, one_smul] using hd.hasDerivAt.deriv
      simpa only [Function.comp_def,q, Function.update_eq_self, hderiv] using
        (((hgsupp s).comp_isClosedEmbedding (isClosedEmbedding_update y i)).enorm_le_lintegral_Ici_deriv ((hg s).comp (contDiff_update 1 y i)) (y i)).trans (MeasureTheory.setLIntegral_le_lintegral _ _)

variable (d : ℕ)

private def timeVelocityPiEquiv  :
    (TimeVelocityCoord d → ℝ) ≃L[ℝ] TimeVelocity d :=
  (ContinuousLinearEquiv.sumPiEquivProdPi ℝ Unit (Fin d) (fun _ => ℝ)).trans
    ((ContinuousLinearEquiv.funUnique Unit ℝ ℝ).prodCongr
      (ContinuousLinearEquiv.refl ℝ (Fin d → ℝ)))





private theorem timeVelocityPiEquiv_single (d : ℕ) (c : TimeVelocityCoord d) :
    timeVelocityPiEquiv d (Pi.single c 1) = timeVelocityBasis c := by
  rcases c with (_ | i)
  · rfl
  · ext <;> simp [timeVelocityPiEquiv, ContinuousLinearEquiv.sumPiEquivProdPi,
      LinearEquiv.sumPiEquivProdPi, timeVelocityBasis, PDE.basisVec, Pi.single_apply]







variable (d : ℕ)

private theorem timeVelocityPiEquiv_measurePreserving  :
    MeasurePreserving (timeVelocityPiEquiv d)
      (volume )
       := by
  have hsum := volume_measurePreserving_sumPiEquivProdPi
    (fun _ : Unit ⊕ Fin d => ℝ)
  have hprod := (volume_preserving_funUnique Unit ℝ).prod
    (MeasurePreserving.id (volume : Measure (Fin d → ℝ)))
  simpa [timeVelocityPiEquiv, ContinuousLinearEquiv.sumPiEquivProdPi,
    LinearEquiv.sumPiEquivProdPi, ContinuousLinearEquiv.funUnique,
    LinearEquiv.funUnique, Function.comp_def, Prod.map_def,
    ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.trans,
    ContinuousLinearEquiv.prodCongr] using! hprod.comp hsum

/-- A compactly supported smooth function is bounded pointwise by the `L¹`
norm of the derivative which differentiates once in every coordinate. -/
theorem abs_le_integral_abs_coordinateIteratedFDeriv_allOnes

    (f : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hf : ContDiff ℝ PDE.smoothOrder f)
    (hfsupp : HasCompactSupport f)
    (z : TimeVelocity d) :
    |f z| ≤
      ∫ x : TimeVelocity d,
        |TimeVelocityMultiIndex.coordinateIteratedFDeriv
          (TimeVelocityMultiIndex.allOnes d) f x|
        ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d) := by
  classical
  let beta : Finset (TimeVelocityCoord d) → TimeVelocityMultiIndex d :=
    fun s c => if c ∈ s then 1 else 0
  let g  :=
    fun s x => TimeVelocityMultiIndex.coordinateIteratedFDeriv (beta s) f
      (timeVelocityPiEquiv d x)
  have hbeta_insert (s : Finset (TimeVelocityCoord d)) (c : TimeVelocityCoord d)
      (hc : c ∉ s) : beta (insert c s) = beta s + Pi.single c 1 := by
    funext a
    by_cases hca : a = c
    · subst a
      simp [beta, hc]
    · simp [beta, hca]



  let xz := (timeVelocityPiEquiv d).symm z
  have hgrid := enorm_le_lmarginal_coordinateFTC g (by
      intro s
      exact (_root_.HypoellipticAleksandrov.Parabolic.LocalHolder.contDiff_coordinateIteratedFDeriv_infty (beta s) f hf).of_le
        (by simp) |>.comp (timeVelocityPiEquiv d).contDiff) (by
      intro s
      exact (_root_.HypoellipticAleksandrov.Parabolic.coordinateIteratedFDeriv_hasCompactSupport (beta s) f hfsupp).comp_homeomorph
        (timeVelocityPiEquiv d).toHomeomorph) (by
      intro s c hc x
      rw [show g (insert c s) x =
        TimeVelocityMultiIndex.coordinateIteratedFDeriv
          (beta s + Pi.single c 1) f (timeVelocityPiEquiv d x) by
            simp only [g, hbeta_insert s c hc]]
      rw [TimeVelocityMultiIndex.coordinateIteratedFDeriv_add_single]
      change (fderiv ℝ (TimeVelocityMultiIndex.coordinateIteratedFDeriv (beta s) f)
        (timeVelocityPiEquiv d x)) (timeVelocityBasis c) =
        (fderiv ℝ ((TimeVelocityMultiIndex.coordinateIteratedFDeriv (beta s) f) ∘
          timeVelocityPiEquiv d) x) (Pi.single c 1)
      rw [fderiv_comp x
        ((_root_.HypoellipticAleksandrov.Parabolic.LocalHolder.contDiff_coordinateIteratedFDeriv_infty (beta s) f hf).differentiable (by simp) _)
        (timeVelocityPiEquiv d).differentiableAt]
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.fderiv]
      have hb := timeVelocityPiEquiv_single d c
      change ((timeVelocityPiEquiv d : (TimeVelocityCoord d → ℝ) → TimeVelocity d)
        (Pi.single c 1)) = timeVelocityBasis c at hb
      exact congrArg
        (fun v => (fderiv ℝ (TimeVelocityMultiIndex.coordinateIteratedFDeriv (beta s) f)
          (timeVelocityPiEquiv d x)) v) hb.symm
      apply hf.of_le
      exact_mod_cast (show (beta s).order + 1 ≤ PDE.smoothOrder by simp))
    Finset.univ xz
  rw [lmarginal_univ] at hgrid
  have hzero : beta ∅ = 0 := by ext c; simp [beta]
  have hone : beta Finset.univ = TimeVelocityMultiIndex.allOnes d := by
    ext c
    simp [beta, TimeVelocityMultiIndex.allOnes]
  simp only [g, hzero, hone, TimeVelocityMultiIndex.coordinateIteratedFDeriv_zero] at hgrid
  have hlin :
      (∫⁻ x : TimeVelocity d,
        ‖TimeVelocityMultiIndex.coordinateIteratedFDeriv
          (TimeVelocityMultiIndex.allOnes d) f x‖ₑ) =
      (∫⁻ x : TimeVelocityCoord d → ℝ,
        ‖TimeVelocityMultiIndex.coordinateIteratedFDeriv
          (TimeVelocityMultiIndex.allOnes d) f (timeVelocityPiEquiv d x)‖ₑ
          ∂(Measure.pi fun _ => volume)) := by
    exact (timeVelocityPiEquiv_measurePreserving d).lintegral_map_equiv _
      (timeVelocityPiEquiv d).toHomeomorph.toMeasurableEquiv
  rw [← hlin] at hgrid
  simp only [xz, ContinuousLinearEquiv.apply_symm_apply] at hgrid
  have hint : Integrable (fun x  =>
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv
        (TimeVelocityMultiIndex.allOnes d) f x|) :=
    (_root_.HypoellipticAleksandrov.Parabolic.LocalHolder.contDiff_coordinateIteratedFDeriv_infty _ f hf).continuous.abs
      |>.integrable_of_hasCompactSupport
        (_root_.HypoellipticAleksandrov.Parabolic.coordinateIteratedFDeriv_hasCompactSupport _ f hfsupp).abs
  rw [← ofReal_norm_eq_enorm] at hgrid
  rw [← ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun _ => abs_nonneg _)]
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all _ fun _ => abs_nonneg _)]
  simpa only [← ofReal_norm_eq_enorm, Real.norm_eq_abs] using hgrid

end HypoellipticAleksandrov.Parabolic
