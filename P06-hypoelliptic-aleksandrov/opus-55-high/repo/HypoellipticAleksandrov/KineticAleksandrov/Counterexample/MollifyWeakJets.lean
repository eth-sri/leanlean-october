module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.MollifyApproximateIdentity
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.Ring

/-!
# Commutation of weak directional jets with spatial convolution

The hypothesis is the ordinary distributional integration-by-parts identity against
all smooth compactly supported tests. No classical differentiability of `u` is required.
-/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open MeasureTheory ContinuousLinearMap
open scoped Convolution
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [MeasureSpace G] [BorelSpace G] [FiniteDimensional ℝ G]
  [Measure.IsAddHaarMeasure (volume : Measure G)]

omit [NormedSpace ℝ G] [MeasureSpace G] [BorelSpace G] [FiniteDimensional ℝ G]
  [Measure.IsAddHaarMeasure (volume : Measure G)] in
/-- Reflection and translation preserve compact support of a scalar test. -/
theorem hasCompactSupport_translated_reflection (k : G → ℝ)
    (hk : HasCompactSupport k) (q : G) : HasCompactSupport (fun y => k (q - y)) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (hk.isCompact.image (continuous_const.sub continuous_id))
  intro y hy
  exact ⟨q - y, subset_tsupport k hy, sub_sub_cancel q y⟩

omit [MeasureSpace G] [BorelSpace G] [FiniteDimensional ℝ G]
  [Measure.IsAddHaarMeasure (volume : Measure G)] in
/-- The reflected test has the negative of the original directional derivative. -/
theorem fderiv_translated_reflection (k : G → ℝ) (hk : ContDiff ℝ 1 k)
    (q y w : G) :
    fderiv ℝ (fun z => k (q - z)) y w = -(fderiv ℝ k (q - y) w) := by
  have h := ((hk.differentiable (by simp)) (q - y)).hasFDerivAt.comp y
    ((hasFDerivAt_const q y).sub (hasFDerivAt_id y))
  change HasFDerivAt (fun z => k _) _ y at h
  rw [h.fderiv]
  simp

omit [MeasureSpace G] [BorelSpace G] [FiniteDimensional ℝ G]
  [Measure.IsAddHaarMeasure (volume : Measure G)] in
/-- The two constant directional derivatives of a smooth test commute. -/
theorem smooth_test_second_swap (test : G → ℝ) (ht : ContDiff ℝ 2 test)
    (q w z : G) :
    fderiv ℝ (fun x => fderiv ℝ test x z) q w =
      fderiv ℝ (fun x => fderiv ℝ test x w) q z := by
  have hd : DifferentiableAt ℝ (fderiv ℝ test) q :=
    ((ht.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) q
  rw [fderiv_clm_apply hd (differentiableAt_const _),
    fderiv_clm_apply hd (differentiableAt_const _)]
  simpa using!
      ((ht.contDiffAt (x := q)).isSymmSndFDerivAt (by simp)).eq w z

/-- A locally integrable weak derivative commutes with smoothing by a compact smooth
kernel, pointwise at every base point. -/
theorem mollify_weak_directional_jet (phi : ContDiffBump (0 : G))
    (u g : G → ℝ) (hu : LocallyIntegrable u volume) (w : G)
    (hweak : ∀ test : G → ℝ, ContDiff ℝ (⊤ : ℕ∞) test → HasCompactSupport test →
      (∫ y, u y * fderiv ℝ test y w) = -(∫ y, g y * test y)) (q : G) :
    fderiv ℝ (spatialMollify phi u) q w = spatialMollify phi g q := by
  let k := phi.normed volume
  have hk : ContDiff ℝ (⊤ : ℕ∞) k := phi.contDiff_normed
  have hkc : HasCompactSupport k := phi.hasCompactSupport_normed
  have hs : spatialMollify phi u = u ⋆[lsmul ℝ ℝ, volume] k := by
    unfold spatialMollify
    rw [convolution_symm (lsmul ℝ ℝ)]
    aesop
  rw [hs, (hkc.hasFDerivAt_convolution_right _ hu
    (hk.of_le (by simp)) q).fderiv,
    convolution_precompR_apply (lsmul ℝ ℝ) hu (hkc.fderiv ℝ)
      ((hk.of_le (by simp)).continuous_fderiv one_ne_zero)]
  have ht : ContDiff ℝ _ (fun y => k (q - y)) :=
    hk.comp (contDiff_const.sub contDiff_id)
  have he := hweak _ ht
    (hasCompactSupport_translated_reflection k hkc q)
  simp_rw [fderiv_translated_reflection k (hk.of_le (by simp)), mul_neg,
    integral_neg] at he
  have he' := neg_injective he
  change (∫ y, u y * fderiv ℝ k _ w) = _
  rw [he', spatialMollify, convolution_lsmul_swap]
  apply integral_congr_ae
  filter_upwards [] with y
  ring

/-- A second distributional jet commutes with convolution. The second weak identity
uses the reverse order on test derivatives, as required by two integrations by parts. -/
theorem mollify_weak_second_jet (phi : ContDiffBump (0 : G))
    (u g h : G → ℝ) (hu : LocallyIntegrable u volume) (hg : LocallyIntegrable g volume)
    (w z : G)
    (hfirst : ∀ test : G → ℝ, ContDiff ℝ (⊤ : ℕ∞) test → HasCompactSupport test →
      (∫ y, u y * fderiv ℝ test y w) = -(∫ y, g y * test y))
    (hsecond : ∀ test : G → ℝ, ContDiff ℝ (⊤ : ℕ∞) test → HasCompactSupport test →
      (∫ y, u y * fderiv ℝ (fun x => fderiv ℝ test x z) y w) =
        ∫ y, h y * test y) (q : G) :
    fderiv ℝ (fun x => fderiv ℝ (spatialMollify phi u) x w) q z =
      spatialMollify phi h q := by
  have he : (fun x => fderiv ℝ (spatialMollify phi u) x w) = spatialMollify phi g :=
    funext (mollify_weak_directional_jet phi u g hu w hfirst)
  rw [he]
  apply mollify_weak_directional_jet phi g h hg z
  intro test ht hs
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ test x z) := by
    fun_prop
  have ha := hfirst _ hd (hs.fderiv_apply (𝕜 := ℝ) z)
  simp_all

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
