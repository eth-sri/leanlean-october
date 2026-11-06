module

public import GS.Nonmanifold.RadialCone

@[expose] public section


/-!
# A norm-preserving plane retract of the WHOLE two-row rank-one cone

The old circle retraction is defined only on the link. The maps below extend
it over the vertex. This distinction matters when an additional Euclidean
factor is present: removing the marked point does NOT remove the entire
zero-matrix stratum.

All norms occurring in the identities are the explicit sums of squares below.
They are not identified with the default matrix norm. This module does not
assert a homology computation or a nonmanifold theorem.
-/
noncomputable section
open Matrix GS GS.Extensions GS.GlobalGeometry GS.Nonmanifold Filter
open scoped BigOperators Topology
namespace GS.NonmanifoldObstruction

abbrev RankCone (κ : Type*) [Fintype κ] [DecidableEq κ] :=
  {W : Matrix (Fin 2) κ ℝ // W.rank ≤ 1}

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def coneZero : RankCone κ := ⟨0, by simp⟩

section
variable (v : CircleVector)
def planeSq : ℝ := v 0 ^ 2 + v 1 ^ 2

def planeRadius : ℝ := Real.sqrt (planeSq v)

theorem planeSq_nonneg : 0 ≤ planeSq v :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem planeRadius_sq : planeRadius v ^ 2 = v 0 ^ 2 + v 1 ^ 2 :=
  Real.sq_sqrt (planeSq_nonneg v)

theorem planeRadius_eq_zero_iff : planeRadius v = 0 ↔ v = 0 := by
  rw [planeRadius, Real.sqrt_eq_zero (planeSq_nonneg v)]
  simp [planeSq, funext_iff, Fin.forall_fin_two, add_eq_zero_iff_of_nonneg, sq_nonneg]

end

theorem continuous_planeRadius : Continuous planeRadius := by
  unfold planeRadius planeSq
  fun_prop

/-- The quadratic Gram identity, valid on the actual rank cone. -/
theorem circleCoordinate_sq (W : Matrix (Fin 2) κ ℝ) (hW : W.rank ≤ 1) :
    planeSq (circleCoordinate W) = frobSq W ^ 2 := by
  obtain ⟨u, hu, z, hz⟩ := exists_unit_outer_of_rank_le_one W hW
  rw [← hz, frobSq_outer hu z]
  change (rowGram (outer u z) 0 0 - rowGram (outer u z) 1 1)^2 +
    (2 * rowGram (outer u z) 0 1)^2 = (∑ j, z j^2)^2
  simp only [rowGram_outer]
  have hu : u 0^2 + u 1^2 = 1 := hu
  linear_combination (u 0^2 + u 1^2 + 1) * (∑ j, z j^2)^2 * hu

/-- Division is total in Lean. At W=0 the numerator is zero, hence the value
is zero. Continuity at this point is proved separately, not by div-continuity. -/
def coneToPlane (W : RankCone κ) : CircleVector :=
  fun i => circleCoordinate W.val i / frobeniusRadius W.val

@[simp] theorem coneToPlane_zero : coneToPlane (coneZero : RankCone κ) = 0 := by
  ext i
  simp [coneToPlane, coneZero, circleCoordinate, rowGram, frobeniusRadius, frobSq, frobInner]

section
variable (W : RankCone κ)
/-- Radius preservation is stronger than boundedness; it excludes new zeros. -/
theorem coneToPlane_sq : planeSq (coneToPlane W) = frobSq W.val := by
  by_cases hz : W.val = 0
  · obtain rfl : W = coneZero := Subtype.ext hz
    simp [planeSq, frobSq, frobInner, hz]
  · have hg := circleCoordinate_sq W.val W.property
    have hn := frobeniusRadius_sq W.val
    dsimp [planeSq, coneToPlane] at hg ⊢
    grind

/-- Each component tends to zero with the Frobenius radius. -/
theorem abs_coneToPlane_le (i : Fin 2) :
    |coneToPlane W i| ≤ frobeniusRadius W.val := by
  have hn := coneToPlane_sq W
  unfold planeSq at hn
  exact Real.abs_le_sqrt (by fin_cases i <;> simp <;> nlinarith [sq_nonneg (coneToPlane W 0), sq_nonneg (coneToPlane W 1)])

end

/-- In particular continuous on the zero-matrix stratum of every product. -/
theorem continuous_coneToPlane : Continuous (coneToPlane : RankCone κ → CircleVector) := by
  have hc : Continuous (fun Z : RankCone κ => frobeniusRadius Z.val) :=
    continuous_frobeniusRadius.comp continuous_subtype_val
  refine continuous_iff_continuousAt.mpr fun W => continuousAt_pi.mpr fun i => ?_
  by_cases hz : W.val = 0
  · obtain rfl : W = coneZero := Subtype.ext hz
    simp only [ContinuousAt, coneToPlane_zero, Pi.zero_apply]
    exact squeeze_zero_norm (fun Z => abs_coneToPlane_le Z i)
      (by simpa [coneZero, frobeniusRadius, frobSq, frobInner] using hc.tendsto coneZero)
  · exact ((continuous_apply i).comp (continuous_circleCoordinate.comp continuous_subtype_val)).continuousAt.div
      hc.continuousAt (Real.sqrt_pos.2 (frobSq_pos_of_ne_zero hz)).ne'

section
variable (v : CircleVector)
/-- Homogeneous extension of the projector section: eigenvalues are 0 and |v|.
No direction v/|v| is chosen, so this expression is continuous also at v=0. -/
def planeMatrix : Mat 2 :=
  !![(planeRadius v + v 0)/2, v 1/2;
     v 1/2, (planeRadius v - v 0)/2]

theorem planeMatrix_symmetric : (planeMatrix v)ᵀ = planeMatrix v := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [planeMatrix]

theorem planeMatrix_rank : (planeMatrix v).rank ≤ 1 :=
  rank_le_one_of_two_column_minors (W := planeMatrix v) fun j k => by
    fin_cases j <;> fin_cases k <;> simp [planeMatrix] <;> nlinarith [planeRadius_sq v]

theorem planeMatrix_sq :
    planeMatrix v * planeMatrix v = planeRadius v • planeMatrix v := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planeMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith [planeRadius_sq v]

end

section
variable (d : ℕ)
def planeToCone (v : CircleVector) : RankCone (Fin (d+2)) :=
  ⟨padTwo d (planeMatrix v), padTwo_rank_le_one d (planeMatrix_rank v)⟩

theorem continuous_planeToCone : Continuous (planeToCone d) := by
  have := continuous_planeRadius
  refine Continuous.subtype_mk (continuous_pi fun i => continuous_pi fun j => ?_) _
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun _ => ?_) j) j <;> fin_cases i <;>
    simp only [padTwo, Fin.cases_zero, Fin.cases_succ, planeMatrix, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one] <;> fun_prop

@[simp] theorem planeToCone_zero : planeToCone d 0 = coneZero := by
  ext i j
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun _ => ?_) j) j
  all_goals fin_cases i <;>
    simp [planeToCone, planeMatrix, planeRadius, planeSq, padTwo, coneZero] <;> rfl

end

section
variable (d : ℕ) (v : CircleVector)
theorem planeToCone_sq :
    frobSq (planeToCone d v).val = planeSq v := by
  rw [planeToCone, padTwo_frobSq]
  simp [frobSq, frobInner, planeMatrix, Fin.sum_univ_two, planeSq]
  grind [planeRadius_sq v]

theorem planeToCone_radius :
    frobeniusRadius (planeToCone d v).val = planeRadius v := by
  simp [frobeniusRadius, planeToCone_sq, planeRadius]

theorem circleCoordinate_planeToCone :
    circleCoordinate (planeToCone d v).val = planeRadius v • v := by
  have hg : rowGram (planeToCone d v).val = planeRadius v • planeMatrix v := by
    simp [planeToCone, padTwo_rowGram, planeMatrix_symmetric, planeMatrix_sq]
  ext i
  fin_cases i <;> simp [circleCoordinate, hg, planeMatrix] <;> ring

/-- The retraction identity, including the origin. -/
theorem coneToPlane_planeToCone :
    coneToPlane (planeToCone d v) = v := by
  by_cases hv : v = 0
  · simp_all
  ext i
  simp_all [coneToPlane, circleCoordinate_planeToCone, planeToCone_radius, ← planeRadius_eq_zero_iff v]

end

end GS.NonmanifoldObstruction
