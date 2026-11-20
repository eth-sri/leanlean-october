module

public import QPBT.Combining.DirectLowDegree.Transport.Questions

/-!
# Affine resampling of directly indexed lines

This module identifies the joint directly indexed line-point laws with the
equivalent sampling procedure that first draws their line marginal and then a
uniform affine parameter.  The argument retains zero diagonal directions: it
uses only translations of finite affine spaces and never cancels a direction.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:243-287`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1020-1116`
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

section

variable (D : DirectLdParams)
    (directionOf : Fin D.m → (DirectPoint D) →
      (DirectPoint D))
    (t : DirectScalarQ D)
include D directionOf t

/-- Translate the point coordinate of a direct sample along a direction that
depends only on its stored index and direction coordinates. -/
private def directLdSpacePointTranslateEquiv : DirectLdSpace D ≃ DirectLdSpace D where
  toFun sample :=
    ⟨sample.point + t • directionOf sample.index sample.direction,
      sample.index, sample.direction⟩
  invFun sample :=
    ⟨sample.point + (-t) • directionOf sample.index sample.direction,
      sample.index, sample.direction⟩
  left_inv sample := by simp
  right_inv sample := by simp

@[simp] private theorem directLdSpacePointTranslateEquiv_symm_apply (sample : DirectLdSpace D) :
    (directLdSpacePointTranslateEquiv D directionOf t).symm sample =
      ⟨sample.point + (-t) • directionOf sample.index sample.direction,
        sample.index, sample.direction⟩ := rfl

end

/-- Uniformly resampling a canonical affine line by a scalar parameter
recovers its original joint line-point sample. -/
private theorem avgOver_directLinePoint_resample
    (D : DirectLdParams)
    (directionOf : Fin D.m → (DirectPoint D) →
      (DirectPoint D))
    (lineOf : DirectLdSpace D → DirectLineDesc D)
    (hbase : ∀ sample,
      (lineOf sample).base =
        lineRepMap (directionOf sample.index sample.direction) sample.point)
    (hdirection : ∀ sample,
      (lineOf sample).direction = directionOf sample.index sample.direction)
    (hline : ∀ sample t,
      lineOf (directLdSpacePointTranslateEquiv D directionOf t sample) =
        lineOf sample)
    (F : (DirectLinePointSample D) → Error) :
    avgOver (uniformDistribution (DirectLdSpace D)) (fun sample =>
        avgOver (uniformDistribution (DirectScalarQ D)) (fun t =>
          F (lineOf sample,
            (lineOf sample).base + t • (lineOf sample).direction))) =
      avgOver (uniformDistribution (DirectLdSpace D)) (fun sample =>
        F (lineOf sample, sample.point)) := by
  have hparameter : ∀ sample,
      avgOver (uniformDistribution (DirectScalarQ D)) (fun t =>
          F (lineOf sample,
            (lineOf sample).base + t • (lineOf sample).direction)) =
        avgOver (uniformDistribution (DirectScalarQ D)) (fun t =>
          F (lineOf sample,
            sample.point +
              t • directionOf sample.index sample.direction)) := by
    intro sample
    let direction := directionOf sample.index sample.direction
    let r := directLineRepParameter direction sample.point
    rw [avgOver_uniform_equiv (Equiv.addRight (-r))]
    apply avgOver_congr
    intro t
    congr 2
    rw [hdirection, hbase, show (Equiv.addRight (-r)).symm t = t + r by simp]
    change lineRepMap direction sample.point + (t + r) • direction = _
    rw [add_comm t r, add_smul, ← add_assoc, ← directLineRepParameter_spec]
  have hsample : ∀ t : DirectScalarQ D,
      avgOver (uniformDistribution (DirectLdSpace D)) (fun sample =>
          F (lineOf sample,
            sample.point +
              t • directionOf sample.index sample.direction)) =
        avgOver (uniformDistribution (DirectLdSpace D)) (fun sample =>
          F (lineOf sample, sample.point)) := by
    intro t
    rw [avgOver_uniform_equiv (directLdSpacePointTranslateEquiv D directionOf t)]
    apply avgOver_congr
    intro sample
    congr 2
    · exact hline sample (-t)
    · simp [add_assoc]
  simp_rw [hparameter]
  rw [avgOver_uniform_comm]
  simp_rw [hsample, avgOver_uniform_const]

section

variable (D : DirectLdParams)
    (F : (DirectLinePointSample D) → Error)
include D F

/-- Sampling an axis line with its marginal and then a uniform affine
parameter reproduces the original joint axis-line/point distribution. -/
theorem avgOver_directALinePointDist_resample :
    avgOver ((directALinePointDist D).map Prod.fst) (fun line =>
        avgOver (uniformDistribution (DirectScalarQ D)) (fun t =>
          F (line, line.base + t • line.direction))) =
      avgOver (directALinePointDist D) F := by
  simp [directALinePointDist, Distribution.avgOver_map]
  exact avgOver_directLinePoint_resample D (fun index _ => coordinateDirection index) (directALineDescOf D)
    (fun _ => rfl) (fun _ => rfl) (by simp [directLdSpacePointTranslateEquiv, directALineDescOf, lineRepMap_add_smul]) F

/-- Sampling a prefix-diagonal line with its marginal and then a uniform
affine parameter reproduces the original joint diagonal-line/point
distribution, including samples with zero direction. -/
theorem avgOver_directDLinePointDist_resample :
    avgOver ((directDLinePointDist D).map Prod.fst) (fun line =>
        avgOver (uniformDistribution (DirectScalarQ D)) (fun t =>
          F (line, line.base + t • line.direction))) =
      avgOver (directDLinePointDist D) F := by
  simp [directDLinePointDist, Distribution.avgOver_map]
  exact avgOver_directLinePoint_resample D (directPrefixProjection) (directDLineDescOf D)
    (fun _ => rfl) (fun _ => rfl) (by simp [directLdSpacePointTranslateEquiv, directDLineDescOf, lineRepMap_add_smul]) F

end

end

end MIPStarRE.QPBT
