/-
From openai/math (https://github.com/openai/math), commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, lean/OAI/Combinatorics/EuclideanRamsey/SmoothingMatrix.lean;
licensed under the Apache License, Version 2.0 (see LICENSES/Apache-2.0.txt and NOTICE).
Modified: ported to the Lean module system for Lean v4.35.0-rc2 / Mathlib v4.35.0-rc2 (this
notice, a `module` header, `public import`, `@[expose] public section`); subsequently
refactored and proof-compressed while preserving the main results, incorporating
the specialized construction from DifferentialSplitting.lean.
-/
module

public import OAI.Combinatorics.EuclideanRamsey.Hessian

@[expose] public section

open scoped ContDiff
open MeasureTheory

namespace OAI.EuclideanRamsey

noncomputable section




def stencilDifferential {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ)
    (b : (Fin k → ℝ) → ℝ) (x : Fin k → ℝ) : ℝ :=
  (1/2 : ℝ) * ∑ j, ∑ l, C j l *
    iteratedFDeriv ℝ 2 b x ![Pi.single j 1, Pi.single l 1]

def gradientWeight {k d : ℕ} (U : Matrix (Fin d) (Fin k) ℝ) (x : Fin k → ℝ) : ℝ :=
  ∑ a, (∑ j, U a j * x j)^2

theorem compact_smoothing {k d : ℕ} (hd : 1 ≤ d)
    (C : Matrix (Fin k) (Fin k) ℝ) (U : Matrix (Fin d) (Fin k) ℝ)
    (hC : C.IsSymm) (hU : U * C * U.transpose = 1) {η : ℝ} (hη : 0 < η) :
    ∃ b : (Fin k → ℝ) → ℝ, ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧
      0 < ∫ x, b x ∧
      (∫ x, max (-(stencilDifferential C b x)) 0 * gradientWeight U x) < η * ∫ x, b x := by
  let R := C * U.transpose
  let Z  := 1-R*U
  have hu A : U*(C*(U.transpose*A)) = A := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hU, Matrix.one_mul]
  have hUR : U*R=1 := by simpa [R, ← Matrix.mul_assoc] using hU
  have hUZ : U*Z=0 := by simp [Z, Matrix.mul_sub, ← Matrix.mul_assoc, hUR]
  have hsplit : C=R*R.transpose+Z*C*Z.transpose := by
    dsimp [Z, R]
    simp [Matrix.transpose_sub, Matrix.transpose_mul, hC.eq, Matrix.sub_mul,
      Matrix.mul_sub, Matrix.mul_assoc, hu]
  let H := EuclideanSpace ℝ (Fin d)
  let eH  := (EuclideanSpace.equiv (Fin d) ℝ).toLinearEquiv
  let u  := eH.symm.toLinearMap.comp (Matrix.toLin' U)
  let r  := (Matrix.toLin' R).comp eH.toLinearMap
  have hur y : u (r y) = y := by
    simp only [u,r,LinearMap.comp_apply,Matrix.toLin'_apply]
    rw [Matrix.mulVec_mulVec, hUR, Matrix.one_mulVec]
    exact eH.symm_apply_apply y
  let V := LinearMap.ker u
  let e : (Fin k → ℝ) ≃L[ℝ] H×V := ContinuousLinearEquiv.equivOfRightInverse u.toContinuousLinearMap r.toContinuousLinearMap hur
  let eh  := EuclideanSpace.basisFun (Fin d) ℝ
  have hRv j : r (eh j) = fun l => R l j := by
    change R.mulVec ((EuclideanSpace.basisFun (Fin d) ℝ j).ofLp) = _
    simp [EuclideanSpace.basisFun_apply, EuclideanSpace.single, Matrix.mulVec_single]
    rfl
  have hZv j : (fun l => Z l j) ∈ LinearMap.ker u := by
    rw [LinearMap.mem_ker]
    change eH.symm (U.mulVec (fun l => Z l j)) = 0
    have h : U.mulVec (fun l => Z l j) = 0 := by
      ext a
      change (U*Z) a j = 0
      rw [hUZ]; rfl
    rw [h,map_zero]
  let z : Fin k → V := fun j => ⟨fun l => Z l j,hZv j⟩
  have hR j : e (fun l => R l j) = (eh j,0) := by
    rw [← hRv]
    apply Prod.ext
    · exact hur _
    · apply Subtype.ext
      change r (eh j) - r (u (r (eh j))) = 0
      rw [hur, sub_self]
  have hZ j : e (fun l => Z l j) = (0,z j) := by
    apply Prod.ext
    · exact hZv j
    · apply Subtype.ext
      change (fun l => Z l j) - r (u (fun l => Z l j)) = _
      rw [show u (fun l => Z l j) = 0 from hZv j,map_zero,sub_zero]
  have hn : 1 ≤ Module.finrank ℝ H := by simpa [H] using hd
  have hw x : ‖(e x).1‖^2 = gradientWeight U x := by
    change ‖eH.symm (U.mulVec x)‖^2 = _
    rw [EuclideanSpace.real_norm_sq_eq]
    rfl
  let μH : Measure H := Measure.addHaar
  let μV : Measure V := Measure.addHaar
  obtain ⟨f,hfs,hfc,hfp,hfm,hfsmall⟩ := exists_radial_smoothing μH hn (η := η/2) (by positivity)
  let g₀ : ContDiffBump (0:V) := ⟨1,2,by norm_num,by norm_num⟩
  let g : V → ℝ := g₀
  have hgs : ContDiff ℝ ∞ g := g₀.contDiff
  have hgc  := g₀.hasCompactSupport
  have hgp := g₀.nonneg'
  have hgm : 0 < ∫ y, g y ∂μV := g₀.integral_pos
  let a := halfLaplacian f
  let bV x := (1/2:ℝ)*∑ j, ∑ l, C j l*hessianB g x (z j) (z l)
  have hac : Continuous a := by
    have hh := hfs.continuous_iteratedFDeriv (m := 2) (by norm_cast)
    unfold a halfLaplacian
    fun_prop
  have hak : HasCompactSupport a := by
    change HasCompactSupport (fun x => halfLaplacian f x)
    simp only [halfLaplacian,← hessianB_eq]
    apply (hessianB_compact hfc).comp_left
      (g := fun B => (1/2:ℝ)*∑ j, B (stdOrthonormalBasis ℝ H j) (stdOrthonormalBasis ℝ H j))
    simp
  have hbc : Continuous bV := by
    have hh := hgs.continuous_iteratedFDeriv (m := 2) (by norm_cast)
    simp only [bV,hessianB_eq]
    fun_prop
  have hbk : HasCompactSupport bV := by
    apply (hessianB_compact hgc).comp_left (g := fun B => (1/2:ℝ)*∑ j, ∑ l, C j l*B (z j) (z l))
    simp
  have haI : Integrable (fun x => max (-a x) 0*‖x‖^2) μH := by
    have hk : HasCompactSupport (fun x => max (-a x) 0) :=
      hak.comp_left (g := fun r : ℝ => max (-r) 0) (by simp)
    exact ((hac.neg.max continuous_const).mul (continuous_norm.pow 2)).integrable_of_hasCompactSupport hk.mul_right
  have hfI : Integrable (fun x => f x*‖x‖^2) μH :=
    (hfs.continuous.mul (continuous_norm.pow 2)).integrable_of_hasCompactSupport hfc.mul_right
  have hgI : Integrable g μV := hgs.continuous.integrable_of_hasCompactSupport hgc
  have hbI : Integrable (fun y => |bV y|) μV :=
    hbc.abs.integrable_of_hasCompactSupport hbk.abs
  let K := (∫ x, f x*‖x‖^2 ∂μH)*(∫ y, |bV y| ∂μV)
  obtain ⟨t₀,ht₀,htsmall⟩ := exists_pos_mul_lt
    (mul_pos (mul_pos (show 0 < η/2 by positivity) hfm) hgm) K
  let t := Real.sqrt t₀
  have ht : 0 < t := Real.sqrt_pos.mpr ht₀
  have hsmall : t^2*K < (η/2)*(∫ x,f x ∂μH)*(∫ y,g y ∂μV) := by
    dsimp only [t]
    rw [Real.sq_sqrt ht₀.le,mul_comm]
    exact htsmall
  let et := e.trans ((LinearEquiv.refl ℝ H).prodCongr
    (LinearEquiv.smulOfNeZero ℝ V t ht.ne')).toContinuousLinearEquiv
  let b := (fun y : H×V => f y.1*g y.2) ∘ et
  have hfgs : ContDiff ℝ ∞ (fun y : H×V => f y.1*g y.2) :=
    (hfs.comp contDiff_fst).mul (hgs.comp contDiff_snd)
  have hbs := hfgs.comp et.contDiff
  have hprod : HasCompactSupport (fun y : H×V => f y.1*g y.2) := by
    apply HasCompactSupport.of_support_subset_isCompact (hfc.prod hgc)
    rintro ⟨x,y⟩ h
    exact ⟨subset_closure (left_ne_zero_of_mul h), subset_closure (right_ne_zero_of_mul h)⟩
  have hbk'  := hprod.comp_homeomorph et.toHomeomorph
  letI : (volume.map et).IsAddHaarMeasure := et.isAddHaarMeasure_map volume
  let c : ℝ := (volume.map et).addHaarScalarFactor (μH.prod μV)
  have hc : 0 < c := by
    exact_mod_cast Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure (volume.map et) (μH.prod μV)
  have hchange φ (hφ : Continuous φ) :
      (∫ x, φ (et x)) = c * ∫ y, φ y ∂μH.prod μV := by
    rw [← integral_map et.continuous.measurable.aemeasurable hφ.aestronglyMeasurable,
      Measure.isAddLeftInvariant_eq_smul (volume.map et) (μH.prod μV)]
    simp [c, NNReal.smul_def]
  have hmass : (∫ x,b x) = c*((∫ x,f x ∂μH)*(∫ y,g y ∂μV)) := by
    change (∫ x, f (et x).1*g (et x).2) = _
    rw [hchange _ hfgs.continuous, integral_prod_mul]
  have hetfst x : (et x).1 = (e x).1 := rfl
  have hdiff x :
      stencilDifferential C b x =
        g (et x).2 * halfLaplacian f (et x).1 +
        t^2*f (et x).1*bV (et x).2 := by
    have hb v w : hessianB b x v w =
        hessianB (fun y : H×V => f y.1*g y.2) (et x) (et v) (et w) :=
      hessianB_linear_comp hfgs et.toContinuousLinearMap x v w
    have hhr j : et (fun l => R l j) = (eh j,0) := by simp [et,hR]
    have hhz j : et (fun l => Z l j) = (0,t • z j) := by simp [et,hZ]
    have hhor : ∑ j, hessianB b x (fun l => R l j) (fun l => R l j) =
        g (et x).2 * ∑ j, hessianB f (et x).1 (eh j) (eh j) := by
      simp only [hb, hhr, hessianB_prod_horizontal hfs hgs, Finset.mul_sum]
    have hver : ∑ j, ∑ l, C j l*hessianB b x (fun a => Z a j) (fun a => Z a l) =
        t^2*f (et x).1 * ∑ j, ∑ l, C j l*hessianB g (et x).2 (z j) (z l) := by
      simp only [hb, hhz, hessianB_prod_vertical hfs hgs, map_smul,
        _root_.smul_apply, smul_eq_mul, Finset.mul_sum]
      congr! 1 with j hj
      congr! 1 with l hl
      ring
    simp only [stencilDifferential, ← hessianB_eq]
    dsimp only [bV]
    have hcon : ∑ j, ∑ l, C j l*hessianB b x (Pi.single j 1) (Pi.single l 1) =
        (∑ j, hessianB b x (fun l => R l j) (fun l => R l j)) +
        ∑ j, ∑ l, C j l*hessianB b x (fun a => Z a j) (fun a => Z a l) := by
      conv_lhs => rw [hsplit]
      simp only [Matrix.add_apply, add_mul, Finset.sum_add_distrib]
      congr 1
      · have he := bilinear_matrix_pushforward (hessianB b x) R 1
        simpa [Matrix.one_apply] using he
      · exact bilinear_matrix_pushforward (hessianB b x) Z C
    rw [hcon, hhor, hver]
    simp only [halfLaplacian, hessianB_eq]
    rw [← congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f eh),
      ← congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis f)]
    ring
  let φ : H×V → ℝ := fun y => max (-(g y.2*a y.1+t^2*f y.1*bV y.2)) 0*‖y.1‖^2
  have hφ : Continuous φ := by dsimp [φ]; fun_prop
  have hneg : (∫ x, max (-stencilDifferential C b x) 0*‖(e x).1‖^2) =
      c*∫ y, φ y ∂μH.prod μV := by
    conv_lhs => arg 2; intro x; rw [hdiff, ← hetfst]
    exact hchange φ hφ
  have hbound : (∫ y,φ y ∂μH.prod μV) ≤
      (∫ x,max (-a x) 0*‖x‖^2 ∂μH)*(∫ y,g y ∂μV)+t^2*K := by
    have hI := (haI.mul_prod hgI).add ((hfI.mul_prod hbI).const_mul (t^2))
    have hbound (z : H×V) :
        max (-(g z.2*a z.1+t^2*f z.1*bV z.2)) 0*‖z.1‖^2 ≤
        (max (-a z.1) 0*‖z.1‖^2)*g z.2+t^2*((f z.1*‖z.1‖^2)*|bV z.2|) := by
      have hg := hgp z.2
      have hf := hfp z.1
      have h : max (-(g z.2*a z.1+t^2*f z.1*bV z.2)) 0 ≤
          g z.2*max (-a z.1) 0+t^2*f z.1*|bV z.2| := by
        apply max_le
        · have ha := le_max_left (-a z.1) 0
          have hb := neg_le_abs (bV z.2)
          nlinarith [mul_le_mul_of_nonneg_left ha (hgp z.2),
            mul_le_mul_of_nonneg_left hb (mul_nonneg (sq_nonneg t) (hfp z.1))]
        · positivity
      nlinarith [mul_le_mul_of_nonneg_right h (sq_nonneg ‖z.1‖)]
    refine (integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun z => mul_nonneg (le_max_right _ _) (sq_nonneg ‖z.1‖))) hI
      (Filter.Eventually.of_forall hbound)).trans_eq ?_
    change (∫ z : H×V, (max (-a z.1) 0*‖z.1‖^2)*g z.2+
      t^2*((f z.1*‖z.1‖^2)*|bV z.2|) ∂μH.prod μV) = _
    rw [integral_add (haI.mul_prod hgI) ((hfI.mul_prod hbI).const_mul (t^2)),
      integral_const_mul, integral_prod_mul (fun x => max (-a x) 0*‖x‖^2) g,
      integral_prod_mul (fun x => f x*‖x‖^2) (fun y => |bV y|)]
  have hfinal : (∫ y,φ y ∂μH.prod μV) < η*((∫ x,f x ∂μH)*(∫ y,g y ∂μV)) := by
    have hh := mul_lt_mul_of_pos_right hfsmall hgm
    change _ < η/2 * _ * _ at hh
    change _ < _ at hsmall
    dsimp only [φ] at *
    nlinarith
  refine ⟨b,hbs,hbk',?_,?_⟩
  · rw [hmass]; positivity
  · simp_rw [← hw]
    rw [hneg,hmass]
    nlinarith [mul_lt_mul_of_pos_left hfinal hc]

end

end OAI.EuclideanRamsey
