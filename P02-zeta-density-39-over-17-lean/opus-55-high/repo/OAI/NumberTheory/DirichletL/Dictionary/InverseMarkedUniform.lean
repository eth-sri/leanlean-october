module
public import OAI.NumberTheory.DirichletL.Dictionary.InverseRawUniform
public import OAI.NumberTheory.DirichletL.Dictionary.InverseRawFiberSource
public import OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedPadding
import WeylPort.Analytic.RealLaplace

public section

namespace OAI

open scoped Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory

namespace SevenEighths.DetectorDictionaryInverseMarkedUniform
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseMoment
open DetectorDictionaryInverseUniform DetectorDictionaryInverseClippedUniform
open DetectorDictionaryInverseRawFourier InverseInitialClippedColumns
open FourierBridge HeckeDetectorRawFiber

private theorem clipped_one_zero (W : ℝ→ℂ) : clippedTest W 1 0=W := by
  funext x
  simp [clippedTest,childLogTest,logPhase]

theorem moving_finite_energy (J : ℕ) :
    ∃K : ℕ,∃C : ℝ,0<C ∧ ∀{ι : Type*}(rows : Finset ι)
      (χ : ι→ Character)(A : ι→ℂ)(D E : ℝ),0<D→0≤E→
    (∀v : ℝ,(∑u∈rows,‖polynomial (χ u) true (childLogTest referenceWindow v) D 0 0*A u‖^2)
      ≤E*(1+‖v‖)^(2*J))→
    ∀scaled reverse : Bool,∀n : ℕ,n≤2→∀U : ℝ,0<U→
    ∀tstar r : ℝ,∀σ∈Set.Icc (0:ℝ) 1,∀t : ℝ,
    (∑u∈rows,‖polynomial (χ u) true
      (inverseSourceSchwartz scaled reverse n U tstar r σ t) D 0 0*A u‖^2)
      ≤C*E*(1+‖t‖)^K := by
  pm_3698 K B hB hmass familyDensity_moment J
  pm_6975
  intro ι rows χ A D E hD hE href scaled reverse n hn U hU tstar r σ hσ t
  let W:=inverseSourceSchwartz scaled reverse n U tstar r σ t
  have hb:=polynomial_clipped_energy rows χ true A W (1/4) (9/4) (by norm_num)
    (source_support scaled reverse n U tstar r σ t) (W.smooth ⊤)
    referenceWindow (13/4) 1 0 D E J (by norm_num) hD hE
    (fun x hx=>(referenceWindow_support (subset_tsupport _ hx)).2)
    (fun y hy=>referenceWindow_agrees scaled reverse n U tstar r σ t 1 y
      (by norm_num) (by norm_num) hy) href
  rw [clipped_one_zero] at hb
  pm_423 norm_zero add_zero one_pow mul_one hb
  pm_7707 hm
  simp only [familyDensity_norm,logSource_eq_logSchwartz] at hm
  apply hb.trans
  calc
    _≤E*(B*(1+‖t‖)^K)^2:=mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (integral_nonneg (fun _=>by positivity)) hm 2) hE
    _= _:=by rw [mul_pow,←pow_mul];ring_nf

theorem logTest_eq_iterate (W : ℝ→ℂ) (n : ℕ) :
    logTest W n=(HeckeDetectorRowwisePolynomial.logProfile^[n]) W := by
  induction n with
  | zero=>rfl
  | succ n ih=>rw [logTest,Function.iterate_succ_apply',←ih]

section Fiber
variable {M : Ideal O} {H : Subgroup (O⧸M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

section
variable (F : Fiber M H Label Slot U a ε tstar T allowance i)
include F
theorem fiber_inverse_source (n : ℕ) (σ t : ℝ) :
    (inverseSourceSchwartz false false n U tstar F.r σ t : ℝ→ℂ)=
      twistProfile ((HeckeDetectorRowwisePolynomial.logProfile^[n]) F.inverseProfile) σ t := by
  funext x
  simpa only [Bool.false_eq_true,ite_false,HeckeDetectorCoefficientTransfer.orientedProfile,
    logTest_eq_iterate,Fiber.inverseProfile] using
    inverseSourceSchwartz_apply false false n U tstar F.r σ t x

theorem fiber_inverse_polynomial (selected : Finset Slot)
    (n : ℕ) (σ t : ℝ) (u : FreeRow) :
    polynomial (F.family u F.label) true
      (inverseSourceSchwartz false false n U tstar F.r σ t) (U^F.r) 0 0*
        F.physicalProduct selected u=
    polynomial (F.family u F.label) true ((HeckeDetectorRowwisePolynomial.logProfile^[n]) F.inverseProfile)
      (U^F.r) σ t*F.physicalProduct selected u := by
  rw [fiber_inverse_source,polynomial_twistProfile]
end

end Fiber

theorem fiber_inverse_energy_uniform (J : ℕ) :
    ∃K : ℕ,∃C : ℝ,0<C ∧ ∀{M : Ideal O}{H : Subgroup (O⧸M)ˣ}{Label Slot : Type*}
      {U a ε tstar T allowance : ℝ}{i : ℕ}
      (F : Fiber M H Label Slot U a ε tstar T allowance i)(selected : Finset Slot),0<U→
    ∀E : ℝ,0≤E→
    (∀v : ℝ,(∑u∈F.rows,‖polynomial (F.family u F.label) true
      (childLogTest referenceWindow v) (U^F.r) 0 0*F.physicalProduct selected u‖^2)
      ≤E*(1+‖v‖)^(2*J))→
    ∀n : ℕ,n≤2→∀σ∈Set.Icc (0:ℝ) 1,∀t : ℝ,
    (∑u∈F.rows,‖polynomial (F.family u F.label) true
      ((HeckeDetectorRowwisePolynomial.logProfile^[n]) F.inverseProfile)
      (U^F.r) σ t*F.physicalProduct selected u‖^2)≤C*E*(1+‖t‖)^K := by
  pm_3698 K C hC hb moving_finite_energy J
  refine ⟨K,C,hC,?_⟩
  intro M H Label Slot U a ε tstar T allowance i F selected hU E hE href n hn σ hσ t
  have hh:=hb F.rows (fun u=>F.family u F.label) (F.physicalProduct selected)
    (U^F.r) E (Real.rpow_pos_of_pos hU _) hE href false false n hn U hU tstar F.r σ hσ t
  simpa only [fiber_inverse_polynomial] using hh

theorem fiber_inverse_height_uniform (J : ℕ) :
    ∃K : ℕ,∃C : ℝ,0<C ∧ ∀{M : Ideal O}{H : Subgroup (O⧸M)ˣ}{Label Slot : Type*}
      {U a ε tstar T allowance : ℝ}{i : ℕ}
      (F : Fiber M H Label Slot U a ε tstar T allowance i)(selected : Finset Slot),0<U→
    ∀E : ℝ,0≤E→
    (∀v : ℝ,(∑u∈F.rows,‖polynomial (F.family u F.label) true
      (childLogTest referenceWindow v) (U^F.r) 0 0*F.physicalProduct selected u‖^2)
      ≤E*(1+‖v‖)^(2*J))→
    ∀n : ℕ,n≤2→∀σ∈Set.Icc (0:ℝ) 1,∀height t : ℝ,0≤height→ t∈Set.Icc (-height) height→
    (∑u∈F.rows,‖polynomial (F.family u F.label) true
      ((HeckeDetectorRowwisePolynomial.logProfile^[n]) F.inverseProfile)
      (U^F.r) σ t*F.physicalProduct selected u‖^2)≤C*E*(1+height)^K := by
  pm_3698 K C hC hb fiber_inverse_energy_uniform J
  refine ⟨K,C,hC,?_⟩
  intro M H Label Slot U a ε tstar T allowance i F selected hU E hE href n hn σ hσ height t _ ht
  apply (hb F selected hU E hE href n hn σ hσ t).trans
  pm_5679
  gcongr

end SevenEighths.DetectorDictionaryInverseMarkedUniform


end OAI
