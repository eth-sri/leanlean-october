/-
From openai/math (https://github.com/openai/math), commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, lean/OAI/Combinatorics/EuclideanRamsey/DifferentialSplitting.lean;
licensed under the Apache License, Version 2.0 (see LICENSES/Apache-2.0.txt and NOTICE).
Modified: ported to the Lean module system and shortened.
-/
module

public import OAI.Combinatorics.EuclideanRamsey.Hessian

@[expose] public section

noncomputable section

open MeasureTheory ContDiff

namespace OAI.EuclideanRamsey
set_option hygiene false
local notation "𝔠" => t^2
local notation "𝔟" => (F ∘ et)
local notation "𝔞" => (et x)
local notation "𝔵" => ‖x‖^2

variable {k d : ℕ}

def secondOperator {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : 𝕄 k ℝ) (v : Fin k → E) f (x : E):=
  (1/2:ℝ)*∑ j, ∑ l, C j l*iteratedFDeriv ℝ 2 f x ![v j, v l]

def stencilDifferential (C : 𝕄 k ℝ) (b : 𝕍 k → ℝ) :=
  secondOperator C (fun j => Pi.single j 1) b

def gradientWeight (U : Matrix (Fin d) (Fin k) ℝ) (x : 𝕍 k):=
  ∑ a, (∑ j, U a j * x j)^2

theorem compact_smoothing (hd : 1 ≤ d) C
    (U : Matrix (Fin d) (Fin k) ℝ) (hC : C.IsSymm) (hU : U * C * U.transpose = 1)
    η (hη : 0 < η) : ∃ b,
      ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧ (∀ x, 0 ≤ b x) ∧ 0 < ∫ x, b x ∧
      (∫ x, max (-(stencilDifferential C b x)) 0 * gradientWeight U x) < η * ∫ x, b x := by
  let R := C * U.transpose
  let Z : 𝕄 k ℝ := 1-R*U
  have hUR : U*R = 1 := by simpa only [R, ← Matrix.mul_assoc] using hU
  have hUZ : U*Z = 0 := by simp [Z, Matrix.mul_sub, ← Matrix.mul_assoc, hUR]
  have hsplit : C = R*R.transpose+Z*C*Z.transpose := by
    have h X : U * (C * (U.transpose * X)) = X := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hU, Matrix.one_mul]
    simp only [Z, R, Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_one,
      Matrix.transpose_transpose, hC.eq, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
      Matrix.mul_one, Matrix.mul_assoc, h]
    abel
  let eH := (EuclideanSpace.equiv (Fin d) ℝ).toLinearEquiv
  let u := eH.symm.toLinearMap.comp (Matrix.toLin' U)
  let r := (Matrix.toLin' R).comp eH.toLinearMap
  have hur : u.comp r = LinearMap.id := by
    ext y
    simp [u, r, hUR]
  let e := (rightInverseSplit u r hur).toContinuousLinearEquiv
  let eh := EuclideanSpace.basisFun (Fin d) ℝ
  have hZv j : (fun l => Z l j) ∈ LinearMap.ker u := by
    simp [u, eH]
    ext a
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply] using congrFun (congrFun hUZ a) j
  have hR j : e (fun l => R l j) = (eh j,0) := by
    have : (fun l => R l j) = r (eh j) := by ext
                                             simp [r, eH, eh, Matrix.mulVec, dotProduct]
    ext <;> simp [this, e, rightInverseSplit, show u (r (eh j)) = eh j from LinearMap.congr_fun hur _]
  let z j : LinearMap.ker u := ⟨fun l => Z l j, hZv j⟩
  have hZ j : e (fun l => Z l j) = (0,z j) := by ext <;> simp [e, z, rightInverseSplit, LinearMap.mem_ker.mp (hZv j)]
  have hw x : ‖(e x).1‖^2 = gradientWeight U x := by
    simp [e, rightInverseSplit, u, eH, gradientWeight, EuclideanSpace.real_norm_sq_eq, Matrix.mulVec, dotProduct]
  let μH : Measure (Space d) := Measure.addHaar
  let μV : Measure (LinearMap.ker u) := Measure.addHaar
  obtain ⟨f,hfs,hfc,hfp,hfm,hfsmall⟩ := exists_radial_smoothing eh μH (by simpa using hd) (η := η/2) (by positivity)
  let g : ContDiffBump (0:LinearMap.ker u) := ⟨1,2,by norm_num,by norm_num⟩
  have hgs : ContDiff ℝ ∞ g := g.contDiff
  have hgm : 0 < ∫ y, g y ∂μV := g.integral_pos
  let a := halfLaplacian eh f
  let bV := secondOperator C z g
  have := hfs.continuous_iteratedFDeriv (m := 2) (by simp)
  have := hgs.continuous_iteratedFDeriv (m := 2) (by simp)
  have hac : Continuous a := by unfold a halfLaplacian
                                fun_prop
  have hbc : Continuous bV := by unfold bV secondOperator
                                 fun_prop
  have haI : Integrable (fun x => max (-a x) 0*𝔵) μH :=
    (by fun_prop : Continuous _).integrable_of_hasCompactSupport ((hfc.mono' fun x hx => support_iteratedFDeriv_subset (𝕜 := ℝ) 2 fun h => hx (by simp [a, halfLaplacian, h])).comp_left (g := fun r => max (-r) 0) (by simp)).mul_right
  have hfI : Integrable (fun x => f x*𝔵) μH :=
    (by fun_prop : Continuous _).integrable_of_hasCompactSupport hfc.mul_right
  have hgI : Integrable g μV := hgs.continuous.integrable_of_hasCompactSupport g.hasCompactSupport
  have hbI : Integrable (fun y => |bV y|) μV := hbc.abs.integrable_of_hasCompactSupport (g.hasCompactSupport.mono' fun x hx =>
    support_iteratedFDeriv_subset (𝕜 := ℝ) 2 fun h => hx (by simp [bV, secondOperator, h])).abs
  let K := (∫ x, f x*𝔵 ∂μH)*(∫ y, |bV y| ∂μV)
  have hK : 0 ≤ K := mul_nonneg (integral_nonneg fun x => mul_nonneg (hfp x) (sq_nonneg _))
    (integral_nonneg fun y => abs_nonneg _)
  obtain ⟨t₀,ht₀,htsmall⟩ := exists_pos_mul_lt
    (mul_pos (mul_pos (show 0 < η/2 by positivity) hfm) hgm) (K+1)
  let t := min t₀ 1
  have ht : 0 < t := lt_min ht₀ one_pos
  have hsmall : 𝔠*K < (η/2)*(∫ x,f x ∂μH)*(∫ y,g y ∂μV) := by
    nlinarith [mul_le_mul_of_nonneg_left (min_le_left t₀ 1) (by linarith),
      mul_le_mul_of_nonneg_right (show 𝔠 ≤ t by nlinarith [min_le_right t₀ 1]) hK]
  let et := e.trans ((LinearEquiv.refl ℝ _).prodCongr
    (LinearEquiv.smulOfNeZero ℝ _ t ht.ne')).toContinuousLinearEquiv
  let F := fun y : Space d × LinearMap.ker u => f y.1*g y.2
  have hF : ContDiff ℝ ∞ F := (hfs.comp contDiff_fst).mul (hgs.comp contDiff_snd)
  let c := (volume.map et).addHaarScalarFactor (μH.prod μV)
  have hc : (0:ℝ) < c := by
    exact_mod_cast Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _
  have hchange (φ : Space d × LinearMap.ker u → ℝ) (hφ : Continuous φ) : ∫ x, φ 𝔞 =
      c * ∫ y, φ y ∂μH.prod μV := by
    rw [← integral_map et.continuous.measurable.aemeasurable hφ.aestronglyMeasurable,
      Measure.isAddLeftInvariant_eq_smul (volume.map et) (μH.prod μV)]
    simp [c, NNReal.smul_def]
  have hdiff x : secondOperator C (fun j => Pi.single j 1) 𝔟 x =
      g 𝔞.2*a 𝔞.1+𝔠*f 𝔞.1*bV 𝔞.2 := by
    simp only [a, bV, secondOperator, halfLaplacian, ← hessianB_eq]
    set H := hessianB 𝔟 x
    have hb v w : H v w = hessianB F 𝔞 (et v) (et w) :=
      hessianB_linear_comp hF et.toContinuousLinearMap x v w
    conv_lhs => rw [hsplit]
    simp only [Matrix.add_apply, add_mul, Finset.sum_add_distrib]
    rw [bilinear_matrix_pushforward H Z C, (by simpa [Matrix.one_apply] using bilinear_matrix_pushforward H R 1 : ∑ j, ∑ l, (R*R.transpose) j l * H _ _ = _)]
    simp [hb, F, et, hR, hZ, hessianB_prod hfs hgs, Finset.mul_sum, mul_add]
    ring_nf
    ring
  have hneg : (∫ x, max (-(stencilDifferential C 𝔟 x)) 0 * gradientWeight U x) =
      c * ∫ y, max (-(g y.2*a y.1+𝔠*f y.1*bV y.2)) 0*‖y.1‖^2 ∂μH.prod μV := by
    simp only [stencilDifferential, hdiff, ← hw]
    exact hchange (fun y => max (-(g y.2*a y.1+𝔠*f y.1*bV y.2)) 0*‖y.1‖^2) (by fun_prop)
  have h1 := haI.mul_prod hgI
  have h2 := (hfI.mul_prod hbI).const_mul (𝔠)
  have hbound := (integral_mono_of_nonneg
    (.of_forall fun z => mul_nonneg (le_max_right _ _) (sq_nonneg _)) (h1.add h2) (.of_forall fun z => by
      have := hfp z.1
      have h3 : max (-(g z.2*a z.1+𝔠*f z.1*bV z.2)) 0 ≤ g z.2*max (-a z.1) 0+𝔠*f z.1*|bV z.2| :=
        max_le (by linarith [mul_le_mul_of_nonneg_left (le_max_left (-a z.1) 0) (g.nonneg' z.2), mul_le_mul_of_nonneg_left (neg_le_abs (bV z.2)) (by positivity : 0 ≤ 𝔠*f z.1)]) (add_nonneg (mul_nonneg (g.nonneg' _) (le_max_right _ _)) (by positivity))
      exact (mul_le_mul_of_nonneg_right h3 (sq_nonneg ‖z.1‖)).trans_eq (by simp; ring))).trans_eq (integral_add h1 h2)
  rw [integral_const_mul, integral_prod_mul (fun x => max (-a x) 0*𝔵) g,
    integral_prod_mul (fun x => f x*𝔵) (fun y => |bV y|)] at hbound
  refine ⟨F ∘ et, hF.comp et.contDiff, HasCompactSupport.comp_homeomorph
    (.of_support_subset_isCompact (hfc.prod g.hasCompactSupport) fun x h =>
      ⟨subset_closure (left_ne_zero_of_mul h), subset_closure (right_ne_zero_of_mul h)⟩)
    et.toHomeomorph, fun x => mul_nonneg (hfp _) (g.nonneg' _), ?_, ?_⟩ <;>
    rw [show ∫ x, 𝔟 x = _ from hchange _ hF.continuous, integral_prod_mul]
  · positivity
  · rw [hneg]
    nlinarith [mul_lt_mul_of_pos_right hfsmall hgm]
