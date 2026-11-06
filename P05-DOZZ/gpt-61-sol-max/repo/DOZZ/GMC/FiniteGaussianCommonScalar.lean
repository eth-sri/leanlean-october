/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FiniteGaussianProduct
public import DOZZ.GMC.FiniteChaosMean
public import Mathlib.Probability.Moments.Covariance

/-! Adding one independent centered Gaussian scalar to every coordinate of a finite Gaussian
family. This is the common-scalar step in Kahane's constant trick. -/

public section

open MeasureTheory ProbabilityTheory
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

private theorem gaussianReal_standard_scale_map (c : ℝ) :
    (gaussianReal 0 (1 : ℝ≥0)).map (fun x : ℝ => c * x) =
      gaussianReal 0 ⟨c ^ 2, sq_nonneg c⟩ := by
  rw [gaussianReal_map_const_mul]
  continuity

variable {Ω ι : Type*} [_inst1 : MeasurableSpace Ω] [_inst2 : Fintype ι] (P : Measure Ω) (Z : Ω → ι → ℝ) (hZ : DOZZ.IsCenteredJointlyGaussian P Z) (c : ℝ)

include Ω ι _inst1 _inst2 P Z hZ c in
/-- The sum of an arbitrary centered jointly Gaussian finite family and an independent common
centered Gaussian coordinate is again centered jointly Gaussian. -/
theorem independent_common_scalar_add_isCenteredJointlyGaussian
     :
    DOZZ.IsCenteredJointlyGaussian (P.prod (gaussianReal 0 1))
      (fun ω i => Z ω.1 i + c * ω.2) := by
  classical
  let Q  := gaussianReal 0 1
  have hQ : IsProbabilityMeasure Q := inferInstance
  have hP  := hZ.1
  let  := hP
  let  := hQ
  refine ⟨inferInstance, ?_, ?_⟩
  · intro i
    have hZi : AEMeasurable (fun ω : Ω × ℝ => Z ω.1 i) (P.prod Q) :=
      (hZ.2.1 i).comp_fst
    have hN : Measurable (fun ω : Ω × ℝ => c * ω.2) := by fun_prop
    exact hZi.add hN.aemeasurable
  · intro a
    let U  := fun ω => ∑ i, a i * Z ω i
    let V  := fun x => (∑ i, a i) * c * x
    let S : Ω × ℝ → ℝ := fun ω => U ω.1 + V ω.2
    obtain ⟨hUmem, ⟨vU, hUmap⟩⟩ := hZ.2.2 a
    have hUmeas  := hUmem.aemeasurable
    have hUlaw : HasLaw U (gaussianReal 0 vU) P := ⟨hUmeas, hUmap⟩
    let d  := (∑ i, a i) * c
    have hVmem : MemLp V 2 Q := (memLp_id_gaussianReal (2 : ℝ≥0)).const_mul ((∑ i, a i) * c)
    have hVlaw : HasLaw V (gaussianReal 0 ⟨d ^ 2, sq_nonneg d⟩) Q := by
      refine ⟨?_, ?_⟩
      · exact (measurable_const_mul d).aemeasurable
      · exact gaussianReal_standard_scale_map d
    have hUprod : HasLaw (fun ω : Ω × ℝ => U ω.1) (gaussianReal 0 vU) (P.prod Q) :=
      hUlaw.comp measurePreserving_fst.hasLaw
    have hVprod : HasLaw (fun ω : Ω × ℝ => V ω.2)
        (gaussianReal 0 ⟨d ^ 2, sq_nonneg d⟩) (P.prod Q) :=
      hVlaw.comp measurePreserving_snd.hasLaw
    have hIndep : (fun ω : Ω × ℝ => U ω.1) ⟂ᵢ[P.prod Q]
        (fun ω => V ω.2) := indepFun_prod₀ hUmeas
          ((measurable_const_mul d).aemeasurable)
    have hSumLaw : HasLaw S (gaussianReal 0 (vU + ⟨d ^ 2, sq_nonneg d⟩)) (P.prod Q) := by
      refine ⟨hUprod.aemeasurable.add hVprod.aemeasurable, ?_⟩
      convert gaussianReal_add_gaussianReal_of_indepFun hIndep hUprod hVprod using 1; simp
    have hSsum (ω : Ω × ℝ) :
        (∑ i, a i * (Z ω.1 i + c * ω.2)) = S ω := by
      dsimp [S, U, V]
      calc
        (∑ i, a i * (Z ω.1 i + c * ω.2)) =
            ∑ i, (a i * Z ω.1 i + a i * (c * ω.2)) := by
              noncomm_ring
        _ = (∑ i, a i * Z ω.1 i) + ∑ i, a i * (c * ω.2) := Finset.sum_add_distrib
        _ = U ω.1 + V ω.2 := by
              simp only [U, V]
              rw [← Finset.sum_mul]
              ring
    refine ⟨?_, ⟨vU + ⟨d ^ 2, sq_nonneg d⟩, ?_⟩⟩
    · have hmemS : MemLp S 2 (P.prod Q) := hSumLaw.memLp (memLp_id_gaussianReal (2 : ℝ≥0))
      simpa only [hSsum] using hmemS
    · simpa only [hSsum] using hSumLaw.map_eq

include Ω ι _inst1 _inst2 P Z hZ c in
/-- The common scalar increases every covariance entry by its variance. -/
theorem gaussianCovariance_independent_common_scalar_add
     (i j : ι) :
    DOZZ.gaussianCovariance (P.prod (gaussianReal 0 1))
      (fun ω => Z ω.1 i + c * ω.2) (fun ω => Z ω.1 j + c * ω.2) =
        DOZZ.gaussianCovariance P (fun ω => Z ω i) (fun ω => Z ω j) + c ^ 2 := by
  classical
  let Q  := gaussianReal 0 1
  let μ  := P.prod Q
  let Xi : Ω × ℝ → ℝ := fun ω => Z ω.1 i
  let Xj : Ω × ℝ → ℝ := fun ω => Z ω.1 j
  let N : Ω × ℝ → ℝ := fun ω => c * ω.2
  let Zi  := fun ω => Z ω i
  let Zj  := fun ω => Z ω j
  let v : ℝ≥0 := ⟨c ^ 2, sq_nonneg c⟩
  have  := hZ.1
  have : IsProbabilityMeasure Q := inferInstance
  have : IsProbabilityMeasure μ := inferInstance
  let hfst : MeasurePreserving Prod.fst μ P := measurePreserving_fst
  let hsnd : MeasurePreserving Prod.snd μ Q := measurePreserving_snd
  have hiMem : MemLp Zi 2 P := by
    obtain ⟨hm, _⟩ := hZ.2.2 (Pi.single i 1)
    simpa [Zi, Pi.single_apply] using hm
  have hjMem : MemLp Zj 2 P := by
    obtain ⟨hm, _⟩ := hZ.2.2 (Pi.single j 1)
    simpa [Zj, Pi.single_apply] using hm
  have hXi2 : MemLp Xi 2 μ := hiMem.comp_measurePreserving hfst
  have hXj2 : MemLp Xj 2 μ := hjMem.comp_measurePreserving hfst
  have hN2 : MemLp N 2 μ := by
    have hcoord : MemLp (fun x : ℝ => c * x) 2 Q := (memLp_id_gaussianReal (2 : ℝ≥0)).const_mul c
    exact hcoord.comp_measurePreserving hsnd
  obtain ⟨_, _, hmeanZi, _⟩ := coordinate_mean_variance P Z hZ i
  obtain ⟨_, _, hmeanZj, _⟩ := coordinate_mean_variance P Z hZ j
  have hmeanXi : (∫ ω, Xi ω ∂μ) = 0 := by
    have hmap := integral_map hfst.aemeasurable
      (by
        rw [hfst.map_eq]
        exact (hiMem.integrable (by norm_num : 1 ≤ (2 : ENNReal))).aestronglyMeasurable)
    rw [hfst.map_eq] at hmap
    grind
  have hmeanXj : (∫ ω, Xj ω ∂μ) = 0 := by
    have hmap := integral_map hfst.aemeasurable
      (by
        rw [hfst.map_eq]
        exact (hjMem.integrable (by norm_num : 1 ≤ (2 : ENNReal))).aestronglyMeasurable)
    rw [hfst.map_eq] at hmap
    grind
  have hNlaw : HasLaw N (gaussianReal 0 v) μ := by
    have hscaled : HasLaw (fun x : ℝ => c * x)
        (gaussianReal 0 v) Q := by
      refine ⟨(measurable_const_mul c).aemeasurable, ?_⟩
      exact gaussianReal_standard_scale_map c
    exact hscaled.comp hsnd.hasLaw
  have hmeanN : (∫ ω, N ω ∂μ) = 0 := by
    calc
      ∫ ω, N ω ∂μ = ∫ x, x ∂gaussianReal 0 v := hNlaw.integral_eq
      _ = 0 := by simp [integral_id_gaussianReal]
  have hvarN : ProbabilityTheory.covariance N N μ = c ^ 2 := by
    calc
      ProbabilityTheory.covariance N N μ = variance N μ :=
        ProbabilityTheory.covariance_self hN2.aemeasurable
      _ = variance id (gaussianReal 0 v) := hNlaw.variance_eq
      _ = c ^ 2 := by rw [variance_id_gaussianReal]; rfl
  have hXi  := hXi2
  have hXj  := hXj2
  have hN  := hN2
  have hXiN : Xi ⟂ᵢ[μ] N := indepFun_prod₀ (hZ.2.1 i)
      (measurable_const_mul c).aemeasurable
  have hXjN : Xj ⟂ᵢ[μ] N := indepFun_prod₀ (hZ.2.1 j)
      (measurable_const_mul c).aemeasurable
  have hNj  := hXjN.symm
  have hsumCov : ProbabilityTheory.covariance (Xi + N) (Xj + N) μ =
      ProbabilityTheory.covariance Xi Xj μ + ProbabilityTheory.covariance N N μ := by
    rw [ProbabilityTheory.covariance_add_left hXi hN (hXj.add hN),
      ProbabilityTheory.covariance_add_right (X := Xi) (Y := Xj) (Z := N) hXi hXj hN,
      ProbabilityTheory.covariance_add_right (X := N) (Y := Xj) (Z := N) hN hXj hN]
    simp [ProbabilityTheory.IndepFun.covariance_eq_zero hXiN hXi hN,
      ProbabilityTheory.IndepFun.covariance_eq_zero hNj hN hXj]
  have hcovXiXj : ProbabilityTheory.covariance Xi Xj μ =
      DOZZ.gaussianCovariance P (fun ω => Z ω i) (fun ω => Z ω j) := by
    have hiMeasMap : AEStronglyMeasurable Zi (μ.map Prod.fst) := by
      rw [hfst.map_eq]
      exact (hZ.2.1 i).aestronglyMeasurable
    have hjMeasMap : AEStronglyMeasurable Zj (μ.map Prod.fst) := by
      rw [hfst.map_eq]
      exact (hZ.2.1 j).aestronglyMeasurable
    have hcovMap  :=
      ProbabilityTheory.covariance_map hiMeasMap hjMeasMap hfst.aemeasurable
    have hcovOrig : ProbabilityTheory.covariance Zi Zj P =
        DOZZ.gaussianCovariance P Zi Zj := by
      rw [ProbabilityTheory.covariance_eq_sub hiMem hjMem, hmeanZi, hmeanZj]
      simp [DOZZ.gaussianCovariance, Zi, Zj]
    continuity
  rw [show (fun ω : Ω × ℝ => Z ω.1 i + c * ω.2) = Xi + N by rfl,
    show (fun ω : Ω × ℝ => Z ω.1 j + c * ω.2) = Xj + N by rfl]
  rw [show DOZZ.gaussianCovariance μ (Xi + N) (Xj + N) =
      ProbabilityTheory.covariance (Xi + N) (Xj + N) μ by
        rw [ProbabilityTheory.covariance_eq_sub (hXi.add hN) (hXj.add hN)]
        have hmeanSumX : (∫ ω, (Xi + N) ω ∂μ) = 0 := by
          calc
            ∫ ω, (Xi + N) ω ∂μ = ∫ ω, Xi ω + N ω ∂μ := rfl
            _ = ∫ ω, Xi ω ∂μ + ∫ ω, N ω ∂μ :=
              integral_add (hXi.integrable (by norm_num)) (hN.integrable (by norm_num))
            _ = 0 := by rw [hmeanXi, hmeanN]; simp
        have hmeanSumY : (∫ ω, (Xj + N) ω ∂μ) = 0 := by
          calc
            ∫ ω, (Xj + N) ω ∂μ = ∫ ω, Xj ω + N ω ∂μ := rfl
            _ = ∫ ω, Xj ω ∂μ + ∫ ω, N ω ∂μ :=
              integral_add (hXj.integrable (by norm_num)) (hN.integrable (by norm_num))
            _ = 0 := by rw [hmeanXj, hmeanN]; simp
        rw [hmeanSumX, hmeanSumY]
        simp [DOZZ.gaussianCovariance]]
  rw [hsumCov, hcovXiXj, hvarN]

end DOZZ.Proofs
