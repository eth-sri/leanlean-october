module

public import PDEFoundation.Sobolev.Cutoff.Basic
public import PDEFoundation.Sobolev.WeakDerivative
public import PDEFoundation.Measure.AffineVolume
import Mathlib.Tactic.Ring
public import PDEFoundation.Calculus.RegularityOrder




/-!
# Localized spatial difference-quotient pointwise core

This coefficient-free file packages the literal localized quotient, its
formal energy test, and their discrete integration-by-parts identity.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- The cutoff-weighted forward difference quotient in one native spatial
coordinate, totalized at zero increment. -/
def localizedSpatialDifferenceQuotient
    {d : ℕ} {inner outer : PDE.VelocityRegion d} {K : ℝ}
    (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (f : PDE.ScalarField d) : PDE.ScalarField d :=
  fun y => η y * ((f (y + h • PDE.basisVec k) - f y) / h)

variable {d : ℕ}

variable {inner outer : PDE.VelocityRegion d} {K : ℝ}

variable (η : PDE.QuantitativeSmoothCutoff inner outer K) (k : Fin d) (h : ℝ)

variable (f : PDE.ScalarField d)

/-- The formal localized energy test `-Δ_{k,-h}(η² Δ_{k,h} f)`, totalized
at zero increment. This is a pointwise formula, not an `H10` adjoint. -/
def localizedSpatialDifferenceQuotientEnergyTest

      : PDE.ScalarField d :=
  fun y =>
    (η (y - h • PDE.basisVec k) *
          HypoellipticAleksandrov.Parabolic.Dirichlet.localizedSpatialDifferenceQuotient η k h f
            (y - h • PDE.basisVec k) -
        η y * localizedSpatialDifferenceQuotient η k h f y) / h

variable (y : PDE.Vec d)

/-- The literal value of the localized quotient. -/
@[simp] theorem localizedSpatialDifferenceQuotient_apply

       :
    localizedSpatialDifferenceQuotient η k h f y =
      η y * ((f (y + h • PDE.basisVec k) - f y) / h) :=
  rfl

/-- The literal value of the localized formal energy test. -/
@[simp] theorem localizedSpatialDifferenceQuotientEnergyTest_apply

       :
    localizedSpatialDifferenceQuotientEnergyTest η k h f y =
      (η (y - h • PDE.basisVec k) *
            localizedSpatialDifferenceQuotient η k h f
              (y - h • PDE.basisVec k) -
          η y * localizedSpatialDifferenceQuotient η k h f y) / h :=
  rfl

/-- The localized quotient is additive in its function argument. -/
theorem localizedSpatialDifferenceQuotient_add

     (f g : PDE.ScalarField d) :
    localizedSpatialDifferenceQuotient η k h (f + g) =
      localizedSpatialDifferenceQuotient η k h f +
        localizedSpatialDifferenceQuotient η k h g := by
  ext <;> simp_all [localizedSpatialDifferenceQuotient_apply] <;> ring

/-- The localized quotient commutes with constant scalar multiplication. -/
theorem localizedSpatialDifferenceQuotient_smul

    (c : ℝ) (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (f : PDE.ScalarField d) :
    localizedSpatialDifferenceQuotient η k h (c • f) =
      c • localizedSpatialDifferenceQuotient η k h f := by
  ext <;> simp_all [localizedSpatialDifferenceQuotient_apply] <;> ring

/-- The localized formal energy test is additive in its function argument. -/
theorem localizedSpatialDifferenceQuotientEnergyTest_add

    (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (f g : PDE.ScalarField d) :
    localizedSpatialDifferenceQuotientEnergyTest η k h (f + g) =
      localizedSpatialDifferenceQuotientEnergyTest η k h f +
        localizedSpatialDifferenceQuotientEnergyTest η k h g := by
  ext <;> simp_all [localizedSpatialDifferenceQuotientEnergyTest_apply, localizedSpatialDifferenceQuotient_add] <;> ring

/-- The localized formal energy test commutes with constant scalars. -/
theorem localizedSpatialDifferenceQuotientEnergyTest_smul

    (c : ℝ) (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (f : PDE.ScalarField d) :
    localizedSpatialDifferenceQuotientEnergyTest η k h (c • f) =
      c • localizedSpatialDifferenceQuotientEnergyTest η k h f := by
  ext <;> simp_all [localizedSpatialDifferenceQuotientEnergyTest_apply, localizedSpatialDifferenceQuotient_smul] <;> ring

section
variable {n : ℕ∞} {f : PDE.ScalarField d} (hf : ContDiff ℝ n f) (η : PDE.QuantitativeSmoothCutoff inner outer K) (k : Fin d) (h : ℝ)

include hf
/-- Smoothness is preserved by the localized quotient. -/
theorem ContDiff.localizedSpatialDifferenceQuotient

     :
    ContDiff ℝ n (localizedSpatialDifferenceQuotient η k h f) := by
  change ContDiff ℝ n
    (fun y => η y * ((f (y + h • PDE.basisVec k) - f y) / h))
  exact (η.smooth.of_le (by simp)).mul
    ((hf.comp (contDiff_id.add contDiff_const)).sub hf |>.div_const h)

/-- Smoothness is preserved by the localized formal energy test. -/
theorem ContDiff.localizedSpatialDifferenceQuotientEnergyTest

     :
    ContDiff ℝ n
      (localizedSpatialDifferenceQuotientEnergyTest η k h f) := by
  change ContDiff ℝ n (fun y =>
    (η (y - h • PDE.basisVec k) *
          HypoellipticAleksandrov.Parabolic.Dirichlet.localizedSpatialDifferenceQuotient η k h f
            (y - h • PDE.basisVec k) -
        η y *
          HypoellipticAleksandrov.Parabolic.Dirichlet.localizedSpatialDifferenceQuotient
            η k h f y) / h)
  have hA : ContDiff ℝ n
      (HypoellipticAleksandrov.Parabolic.Dirichlet.localizedSpatialDifferenceQuotient η k h f) := by
    change ContDiff ℝ n
      (fun y => η y * ((f (y + h • PDE.basisVec k) - f y) / h))
    exact (η.smooth.of_le (by simp)).mul
      ((hf.comp (contDiff_id.add contDiff_const)).sub hf |>.div_const h)
  exact (((η.smooth.of_le (by simp)).comp (contDiff_id.sub contDiff_const)).mul
      (hA.comp
        (contDiff_id.sub contDiff_const)) |>.sub
    ((η.smooth.of_le (by simp)).mul
      hA)).div_const h
end


variable (η : PDE.QuantitativeSmoothCutoff inner outer K) (k : Fin d) (h : ℝ) (f : PDE.ScalarField d)

/-- The cutoff factor gives the localized quotient compact support. -/
theorem localizedSpatialDifferenceQuotient_hasCompactSupport

     :
    HasCompactSupport (localizedSpatialDifferenceQuotient η k h f) := (id (HasCompactSupport.mul_right η.hasCompactSupport))

private theorem localizedEnergyFactor_hasCompactSupport

     :
    HasCompactSupport (fun y =>
      η y * localizedSpatialDifferenceQuotient η k h f y) :=
  η.hasCompactSupport.mul_right

/-- The formal energy test has compact support without a premise on `f`. -/
theorem localizedSpatialDifferenceQuotientEnergyTest_hasCompactSupport

     :
    HasCompactSupport
      (localizedSpatialDifferenceQuotientEnergyTest η k h f) := by
  let z  := h • PDE.basisVec k
  let q  := fun y =>
    η y * localizedSpatialDifferenceQuotient η k h f y
  have hq  := localizedEnergyFactor_hasCompactSupport η k h f

  change HasCompactSupport (fun y => (q (y - z) - q y) / h)
  have hdiv : (fun y => (q (y - z) - q y) / h) =
      h⁻¹ • (fun y => q (y - z) - q y) := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
    ring
  rw [hdiv]
  exact ((hq.comp_homeomorph (Homeomorph.subRight z)).sub hq).smul_left

/-- The localized quotient support lies in the cutoff support. -/
theorem tsupport_localizedSpatialDifferenceQuotient_subset

     :
    tsupport (localizedSpatialDifferenceQuotient η k h f) ⊆
      tsupport η.toFun := (id tsupport_mul_subset_left)

/-- The formal energy-test support lies in the cutoff support and its forward
translate by the signed increment. -/
theorem tsupport_localizedSpatialDifferenceQuotientEnergyTest_subset

     :
    tsupport (localizedSpatialDifferenceQuotientEnergyTest η k h f) ⊆
      tsupport η.toFun ∪
        (fun y  => y + h • PDE.basisVec k) ''
          tsupport η.toFun := by
  let z  := h • PDE.basisVec k
  let q  := fun y =>
    η y * localizedSpatialDifferenceQuotient η k h f y
  have hq : tsupport q ⊆ tsupport η.toFun := by
    exact tsupport_mul_subset_left
  change tsupport (fun y => (q (y - z) - q y) / h) ⊆
    tsupport η.toFun ∪ (fun y  => y + z) '' tsupport η.toFun
  have hdiv : (fun y => (q (y - z) - q y) / h) =
      h⁻¹ • (fun y => q (y - z) - q y) := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
    ring
  rw [hdiv]
  change tsupport (h⁻¹ • (fun y => q (y - z) - q y)) ⊆
    tsupport η.toFun ∪ (fun y  => y + z) '' tsupport η.toFun
  refine (tsupport_smul_subset_right (fun _ : PDE.Vec d => h⁻¹)
    (fun y => q (y - z) - q y)).trans ?_
  refine (tsupport_sub _ _).trans ?_
  intro y hy
  rcases hy with hy | hy
  · rw [show (fun x  => q (x - z)) =
      q ∘ (Homeomorph.subRight z) by rfl, tsupport_comp_eq_preimage] at hy
    rcases hq hy with hs
    right
    refine ⟨y - z, hs, ?_⟩
    abel
  · exact Or.inl (hq hy)

/-- Bundle the formal energy test as a compactly supported smooth test on a
raw set using the exact forward signed collar. -/
def localizedSpatialDifferenceQuotientEnergyWeakTest
     {Ω inner outer : PDE.VelocityRegion d} {K : ℝ}
    (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (f : PDE.ScalarField d)
    (hf : ContDiff ℝ PDE.smoothOrder f)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo
      (fun y  => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    PDE.WeakTestFunction Ω where
  toFun := localizedSpatialDifferenceQuotientEnergyTest η k h f
  contDiff := ContDiff.localizedSpatialDifferenceQuotientEnergyTest hf η k h
  hasCompactSupport := localizedSpatialDifferenceQuotientEnergyTest_hasCompactSupport η k h f
  tsupport_subset := by
    intro y hy
    rcases tsupport_localizedSpatialDifferenceQuotientEnergyTest_subset η k h f hy with hy | hy
    · exact hηΩ hy
    · rcases hy with ⟨x, hx, rfl⟩
      exact hηshift hx

/-- The global discrete integration-by-parts identity for continuous inputs. -/
theorem integral_mul_localizedSpatialDifferenceQuotientEnergyTest_eq
     {inner outer : PDE.VelocityRegion d} {K : ℝ}
    (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (f g : PDE.ScalarField d)
    (hf : Continuous f) (hg : Continuous g) :
    (∫ y, f y *
        localizedSpatialDifferenceQuotientEnergyTest η k h g y) =
      ∫ y, localizedSpatialDifferenceQuotient η k h f y *
        localizedSpatialDifferenceQuotient η k h g y := by
  rcases eq_or_ne h 0 with rfl | hh
  · simp_all
  let z  := h • PDE.basisVec k
  let qg  := localizedSpatialDifferenceQuotient η k h g
  let F  := fun y => f (y + z) * η y * qg y
  let G  := fun y => f y * η y * qg y
  have hqg : Continuous qg := by
    change Continuous (fun y => η y * ((g (y + h • PDE.basisVec k) - g y) / h))
    exact η.smooth.continuous.mul
      ((hg.comp (continuous_id.add continuous_const)).sub hg |>.div_const h)
  have hFcont : Continuous F := by
    change Continuous ((fun y => f (y + z)) * η.toFun * qg)
    exact (hf.comp (continuous_id.add continuous_const)).mul η.smooth.continuous |>.mul hqg
  have hGcont : Continuous G := by
    change Continuous (f * η.toFun * qg)
    exact hf.mul η.smooth.continuous |>.mul hqg
  have hFsupport : HasCompactSupport F := by
    change HasCompactSupport ((fun y => f (y + z)) * η.toFun * qg)
    exact (η.hasCompactSupport.mul_left).mul_right


  have hG : Integrable G  := hGcont.integrable_of_hasCompactSupport ((id (HasCompactSupport.mul_right (HasCompactSupport.mul_left η.hasCompactSupport))))
  rw [show (fun y => f y * localizedSpatialDifferenceQuotientEnergyTest η k h g y) =
    fun y => (F (y - z) - G y) / h by
      funext y
      dsimp [F, G, z]
      simp only [qg, localizedSpatialDifferenceQuotient_apply, sub_add_cancel]
      ring]

  have hshift : (∫ y, F (y - z)) = ∫ y, F y := by

    simpa [sub_eq_add_neg] using
      (measurePreserving_add_right volume (-z)).integral_comp (Homeomorph.addRight (-z)).measurableEmbedding F
  rw [integral_div, integral_sub (by
      exact (hFcont.comp (continuous_id.sub continuous_const)).integrable_of_hasCompactSupport
        (hFsupport.comp_homeomorph (Homeomorph.subRight z))) hG, hshift]
  rw [← integral_sub (hFcont.integrable_of_hasCompactSupport hFsupport) hG, ← integral_div]
  have hpoint : (fun y => (F y - G y) / h) =
      fun y => localizedSpatialDifferenceQuotient η k h f y * qg y := by
    funext y
    dsimp [F, G, qg, z]
    field_simp
  rw [hpoint]

/-- The discrete pivot restricted to an arbitrary raw set containing the
forward cutoff collar. -/
theorem setIntegral_mul_localizedSpatialDifferenceQuotientEnergyTest_eq
     {Ω inner outer : PDE.VelocityRegion d} {K : ℝ}
    (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (f g : PDE.ScalarField d)
    (hf : Continuous f) (hg : Continuous g)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo
      (fun y  => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    (∫ y in Ω, f y *
        localizedSpatialDifferenceQuotientEnergyTest η k h g y) =
      ∫ y in Ω, localizedSpatialDifferenceQuotient η k h f y *
        localizedSpatialDifferenceQuotient η k h g y := by
  calc
    (∫ y in Ω, f y * localizedSpatialDifferenceQuotientEnergyTest η k h g y) =
        ∫ y, f y * localizedSpatialDifferenceQuotientEnergyTest η k h g y := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro y hy
      have hs := tsupport_localizedSpatialDifferenceQuotientEnergyTest_subset η k h g

      rw [image_eq_zero_of_notMem_tsupport (show y ∉ tsupport
          (localizedSpatialDifferenceQuotientEnergyTest η k h g) by
          intro hsupport
          rcases hs hsupport with hy' | hy'
          · exact hy (hηΩ hy')
          · rcases hy' with ⟨x, hx, rfl⟩
            exact hy (hηshift hx))]
      ring
    _ = ∫ y, localizedSpatialDifferenceQuotient η k h f y *
        localizedSpatialDifferenceQuotient η k h g y :=
      integral_mul_localizedSpatialDifferenceQuotientEnergyTest_eq η k h f g hf hg
    _ = ∫ y in Ω, localizedSpatialDifferenceQuotient η k h f y *
        localizedSpatialDifferenceQuotient η k h g y := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro y hy

      rw [image_eq_zero_of_notMem_tsupport (show y ∉ tsupport (localizedSpatialDifferenceQuotient η k h f) by
          intro hsupport
          exact hy (hηΩ
            (tsupport_localizedSpatialDifferenceQuotient_subset η k h f hsupport)))]
      ring

end HypoellipticAleksandrov.Parabolic.Dirichlet
