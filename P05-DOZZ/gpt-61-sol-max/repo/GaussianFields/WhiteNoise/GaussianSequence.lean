/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.HasLawExists
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.Moments.Variance

/-!
# GaussianFields.WhiteNoise/GaussianSequence

Port of the corresponding GaussianFields source module.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace GaussianFields

/-- The concrete sample space for a family of independent Gaussian coefficients. -/
abbrev GaussianSequenceSpace (ι : Type*) :=
  ι → ℝ

/-- The standard centered real Gaussian law. -/
@[expose]
noncomputable def standardGaussianReal : Measure ℝ :=
  ProbabilityTheory.gaussianReal 0 (1 : ℝ≥0)

instance instIsProbabilityMeasure_standardGaussianReal :
    IsProbabilityMeasure standardGaussianReal := by
  rw [standardGaussianReal]
  infer_instance

/-- The product law of independent standard centered real Gaussian coefficients. -/
@[expose]
noncomputable def gaussianSequenceMeasure (ι : Type*) :
    Measure (GaussianSequenceSpace ι) :=
  Measure.infinitePi fun _ : ι => standardGaussianReal

instance instIsProbabilityMeasure_gaussianSequenceMeasure (ι : Type*) :
    IsProbabilityMeasure (gaussianSequenceMeasure ι) := by
  rw [gaussianSequenceMeasure]
  infer_instance

variable {ι : Type*}

variable (s : Finset ι) (a : ι → ℝ)

include s a in
include s a in
include s a in
include s a in
include s a in
include s a in
include ι
/-- The `i`-th Gaussian coordinate. -/
@[expose]
def gaussianCoordinate  (i : ι) : GaussianSequenceSpace ι → ℝ :=
  fun ω => ω i


@[fun_prop]
theorem measurable_gaussianCoordinate  (i : ι) :
    Measurable (gaussianCoordinate i) := id (measurable_pi_apply i)


theorem aemeasurable_gaussianCoordinate  (i : ι) :
    AEMeasurable (gaussianCoordinate i) (gaussianSequenceMeasure ι) :=
  (measurable_gaussianCoordinate i).aemeasurable


/-- Each coordinate has the standard Gaussian law. -/
theorem gaussianCoordinate_hasLaw  (i : ι) :
    HasLaw (gaussianCoordinate i) standardGaussianReal (gaussianSequenceMeasure ι) := MeasurePreserving.hasLaw
    (measurePreserving_eval_infinitePi (fun _ : ι => standardGaussianReal) i)


/-- A coordinate under the product law is identically distributed with the identity under the
standard Gaussian law. -/
theorem identDistrib_gaussianCoordinate_id  (i : ι) :
    IdentDistrib (gaussianCoordinate i) id (gaussianSequenceMeasure ι) standardGaussianReal where
  aemeasurable_fst := aemeasurable_gaussianCoordinate i
  aemeasurable_snd := aemeasurable_id'
  map_eq := by
    rw [(gaussianCoordinate_hasLaw i).map_eq]
    exact Measure.map_id.symm


/-- Gaussian coordinates have all finite moments; in particular they are in `L^2`. -/
theorem memLp_gaussianCoordinate  (i : ι) :
    MemLp (gaussianCoordinate i) 2 (gaussianSequenceMeasure ι) := by
  have hdist := identDistrib_gaussianCoordinate_id (ι := ι) i
  exact hdist.symm.memLp_snd
    (ProbabilityTheory.memLp_id_gaussianReal' (μ := 0) (v := (1 : ℝ≥0)) 2 (by norm_num))


/-- Coordinate means are zero. -/
theorem integral_gaussianCoordinate  (i : ι) :
    ∫ ω, gaussianCoordinate i ω ∂gaussianSequenceMeasure ι = 0 := by
  calc
    ∫ ω, gaussianCoordinate i ω ∂gaussianSequenceMeasure ι =
        ∫ x, x ∂standardGaussianReal := (gaussianCoordinate_hasLaw i).integral_eq
    _ = 0 := by
      rw [standardGaussianReal]
      simp


/-- Coordinate variances are one. -/
theorem variance_gaussianCoordinate  (i : ι) :
    Var[gaussianCoordinate i; gaussianSequenceMeasure ι] = 1 := by
  calc
    Var[gaussianCoordinate i; gaussianSequenceMeasure ι] =
        Var[id; standardGaussianReal] := (gaussianCoordinate_hasLaw i).variance_eq
    _ = 1 := by
      rw [standardGaussianReal]
      simp


/-- A deterministic multiple of one Gaussian coordinate is Gaussian. -/
theorem map_const_mul_gaussianCoordinate  (i : ι) (c : ℝ) :
    Measure.map (fun ω => c * gaussianCoordinate i ω) (gaussianSequenceMeasure ι) =
      ProbabilityTheory.gaussianReal 0 (Real.toNNReal (c ^ (2 : Nat))) := by
  change Measure.map ((fun x : ℝ => c * x) ∘ gaussianCoordinate i)
      (gaussianSequenceMeasure ι) =
    ProbabilityTheory.gaussianReal 0 (Real.toNNReal (c ^ (2 : Nat)))
  have hmul_meas :
      AEMeasurable (fun x : ℝ => c * x)
        (Measure.map (gaussianCoordinate i) (gaussianSequenceMeasure ι)) := by
    fun_prop (disch := positivity)
  rw [← AEMeasurable.map_map_of_aemeasurable
    hmul_meas (aemeasurable_gaussianCoordinate i)]
  rw [(gaussianCoordinate_hasLaw i).map_eq, standardGaussianReal,
    ProbabilityTheory.gaussianReal_map_const_mul]
  congr
  · ring
  · apply NNReal.coe_injective
    simp [Real.coe_toNNReal _ (sq_nonneg c)]


/-- The coordinate process is independent. -/
theorem iIndepFun_gaussianCoordinate  :
    iIndepFun (fun i : ι => gaussianCoordinate i) (gaussianSequenceMeasure ι) := by
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (by
    intro i
    exact measurable_gaussianCoordinate i)]
  change Measure.map id (gaussianSequenceMeasure ι) =
    Measure.infinitePi fun i : ι => Measure.map (gaussianCoordinate i) (gaussianSequenceMeasure ι)
  rw [Measure.map_id, gaussianSequenceMeasure]
  congr
  funext i
  exact ((measurePreserving_eval_infinitePi (fun _ : ι => standardGaussianReal) i).map_eq).symm


/-- Distinct Gaussian coordinates are independent. -/
abbrev indepFun_gaussianCoordinate  {i j : ι} (hij : i ≠ j)  :=
  iIndepFun_gaussianCoordinate.indepFun hij


/-- Distinct Gaussian coordinates are uncorrelated. -/
abbrev covariance_gaussianCoordinate_eq_zero  {i j : ι} (hij : i ≠ j)  :=
  (indepFun_gaussianCoordinate hij).covariance_eq_zero
    (memLp_gaussianCoordinate i) (memLp_gaussianCoordinate j)


/-- The covariance of a Gaussian coordinate with itself is one. -/
theorem covariance_gaussianCoordinate_self  (i : ι) :
    cov[gaussianCoordinate i, gaussianCoordinate i; gaussianSequenceMeasure ι] = 1 := by
  rw [covariance_self (aemeasurable_gaussianCoordinate i), variance_gaussianCoordinate i]


/-- Coordinate covariance is the Kronecker delta. -/
theorem covariance_gaussianCoordinate  [DecidableEq ι] (i j : ι) :
    cov[gaussianCoordinate i, gaussianCoordinate j; gaussianSequenceMeasure ι] =
      if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    simp [covariance_gaussianCoordinate_self]
  · simp [hij, covariance_gaussianCoordinate_eq_zero hij]


/-- A finite linear combination of Gaussian coordinates. -/
@[expose]
noncomputable def gaussianLinearCombination   :
    GaussianSequenceSpace ι → ℝ :=
  fun ω => ∑ i ∈ s, a i * gaussianCoordinate i ω


@[simp]
theorem gaussianLinearCombination_apply  
    (ω : GaussianSequenceSpace ι) :
    gaussianLinearCombination s a ω = ∑ i ∈ s, a i * gaussianCoordinate i ω :=
  rfl


@[fun_prop]
theorem measurable_gaussianLinearCombination   :
    Measurable (gaussianLinearCombination s a) := by
  unfold gaussianLinearCombination
  fun_prop


theorem aemeasurable_gaussianLinearCombination   :
    AEMeasurable (gaussianLinearCombination s a) (gaussianSequenceMeasure ι) :=
  (measurable_gaussianLinearCombination s a).aemeasurable


/-- A coordinate outside a finite set is independent of every finite linear combination over that
set. -/
theorem indepFun_gaussianCoordinate_gaussianLinearCombination  [DecidableEq ι]
    {i : ι} {s : Finset ι} (his : i ∉ s) (a : ι → ℝ) :
    gaussianCoordinate i ⟂ᵢ[gaussianSequenceMeasure ι] gaussianLinearCombination s a := by
  let S : Finset ι := {i}
  have hdisjoint : Disjoint S s := by
    continuity
  have htuple  :=
    iIndepFun_gaussianCoordinate.indepFun_finset S s hdisjoint
      (fun j => measurable_gaussianCoordinate j)
  let φ : ((j : S) → ℝ) → ℝ := fun x => x ⟨i, by simp [S]⟩
  let ψ : ((j : s) → ℝ) → ℝ := fun x => ∑ j : s, a j * x j
  have hφ : Measurable φ := by
    fun_prop (disch := positivity)
  have hψ : Measurable ψ := by
    fun_prop (disch := positivity)
  have hcomp := htuple.comp hφ hψ
  refine hcomp.congr ?_ ?_
  · continuity
  · filter_upwards with ω
    change (∑ j : s, a j * ω (j : ι)) = ∑ x ∈ s, a x * ω x
    rw [← Finset.sum_attach s (fun x => a x * ω x)]
    simp


/-- The finite variance parameter associated with a deterministic coefficient family. -/
@[expose]
noncomputable def gaussianLinearCombinationVariance   :
    ℝ≥0 :=
  ∑ i ∈ s, Real.toNNReal ((a i) ^ (2 : Nat))




@[simp]
theorem gaussianLinearCombinationVariance_empty  (a : ι → ℝ) :
    gaussianLinearCombinationVariance (∅ : Finset ι) a = 0 := by
  simp [gaussianLinearCombinationVariance]


theorem gaussianLinearCombinationVariance_insert  [DecidableEq ι]
    {i : ι} {s : Finset ι} (his : i ∉ s) (a : ι → ℝ) :
    gaussianLinearCombinationVariance (insert i s) a =
      Real.toNNReal ((a i) ^ (2 : Nat)) + gaussianLinearCombinationVariance s a := by
  simp [gaussianLinearCombinationVariance, Finset.sum_insert, his]


/-- Every finite Gaussian linear combination is a centered Gaussian with variance equal to the
finite square sum of its coefficients. -/
theorem map_gaussianLinearCombination_eq_gaussianReal  [DecidableEq ι]
    (s : Finset ι) (a : ι → ℝ) :
    Measure.map (gaussianLinearCombination s a) (gaussianSequenceMeasure ι) =
      ProbabilityTheory.gaussianReal 0 (gaussianLinearCombinationVariance s a) := by
  induction s using Finset.induction with
  | empty =>
      change Measure.map (fun _ : GaussianSequenceSpace ι => 0) (gaussianSequenceMeasure ι) =
        ProbabilityTheory.gaussianReal 0 0
      simp_all
  | insert i s his ih =>
      have hsum_fun :
          gaussianLinearCombination (insert i s) a =
            (fun ω => a i * gaussianCoordinate i ω) + gaussianLinearCombination s a := by
        continuity
      have hindep :
          (fun ω => a i * gaussianCoordinate i ω)
            ⟂ᵢ[gaussianSequenceMeasure ι]
          gaussianLinearCombination s a := by
        have h := (indepFun_gaussianCoordinate_gaussianLinearCombination his a).comp
          (by fun_prop : Measurable (fun x : ℝ => a i * x)) measurable_id
        exact h
      have hscaled  :=
        map_const_mul_gaussianCoordinate i (a i)
      have hscaledLaw :
          HasLaw (fun ω => a i * gaussianCoordinate i ω)
            (ProbabilityTheory.gaussianReal 0 (Real.toNNReal ((a i) ^ (2 : Nat))))
            (gaussianSequenceMeasure ι) := ⟨by fun_prop, hscaled⟩
      have htailLaw :
          HasLaw (gaussianLinearCombination s a)
            (ProbabilityTheory.gaussianReal 0 (gaussianLinearCombinationVariance s a))
            (gaussianSequenceMeasure ι) := ⟨aemeasurable_gaussianLinearCombination s a, ih⟩
      have hsum :=
        ProbabilityTheory.gaussianReal_add_gaussianReal_of_indepFun
          hindep hscaledLaw htailLaw
      rw [hsum_fun]
      simpa [gaussianLinearCombinationVariance_insert his a] using hsum


/-- The finite square-sum variance parameter as a real number. -/
theorem coe_gaussianLinearCombinationVariance   :
    (gaussianLinearCombinationVariance s a : ℝ) =
      ∑ i ∈ s, (a i) ^ (2 : Nat) := by
  simp [gaussianLinearCombinationVariance, Real.coe_toNNReal _ (sq_nonneg _)]
omit ι


end GaussianFields

end
