import Mathlib.Tactic

import GS.Nonmanifold.RadialCone
open GS.MatrixBase



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
open Matrix GS.GlobalGeometry GS.Nonmanifold Filter
open scoped Topology
namespace GS.NonmanifoldObstruction

variable (v : CircleVector)

variable (d : ℕ)

variable (v : CircleVector)

abbrev RankCone (κ : Type*) [Fintype κ] [DecidableEq κ] :=
  {W : Matrix (Fin 2) κ ℝ // W.rank ≤ 1}

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def coneZero : RankCone κ := ⟨0, by simp⟩

def planeSq  : ℝ := v 0 ^ 2 + v 1 ^ 2

def planeRadius  : ℝ := Real.sqrt (planeSq v)

theorem planeSq_nonneg  : 0 ≤ planeSq v := add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem planeSq_eq_zero_iff  : planeSq v = 0 ↔ v = 0 := by simp_all [planeSq,Fin.forall_fin_two,funext_iff,add_eq_zero_iff_of_nonneg,sq_nonneg]

theorem planeRadius_sq  : planeRadius v ^ 2 = planeSq v :=
  Real.sq_sqrt (planeSq_nonneg v)

theorem planeRadius_eq_zero_iff  : planeRadius v = 0 ↔ v = 0 := by
  grind [planeRadius_sq,planeSq_eq_zero_iff]



/-- The quadratic Gram identity, valid on the actual rank cone. -/
theorem circleCoordinate_sq (W : Matrix (Fin 2) κ ℝ) (hW : W.rank ≤ 1) :
    planeSq (circleCoordinate W) = cFrobSq W ^ 2 := by
  obtain ⟨u, hu, z, hz⟩ := exists_unit_outer_of_rank_le_one W hW
  rw [← hz, frobSq_outer hu z]
  change (rowGram (outer u z) 0 0 - rowGram (outer u z) 1 1)^2 +
    (2 * rowGram (outer u z) 0 1)^2 = (∑ j, z j^2)^2
  simp only [rowGram,outer]
  calc
    _ = (u 0^2 + u 1^2)^2 * (∑ j, z j^2)^2 := by
      ring_nf
      simp only [← Finset.mul_sum]
      ring
    _ = _ := by rw [show u 0^2 + u 1^2 = 1 from hu]; ring

/-- Division is total in Lean. At W=0 the numerator is zero, hence the value
is zero. Continuity at this point is proved separately, not by div-continuity. -/
def coneToPlane (W : RankCone κ) : CircleVector :=
  fun i => circleCoordinate W.val i / frobeniusRadius W.val

@[simp] theorem coneToPlane_zero : coneToPlane (coneZero : RankCone κ) = 0 := by
  ext i
  simp [coneToPlane, coneZero, circleCoordinate, rowGram, frobeniusRadius, cFrobSq]

/-- Radius preservation is stronger than boundedness; it excludes new zeros. -/
theorem coneToPlane_sq (W : RankCone κ) : planeSq (coneToPlane W) = cFrobSq W.val := by
  grind [coneToPlane,planeSq,GS.Nonmanifold.frobeniusRadius_sq,circleCoordinate_sq]

/-- Each component tends to zero with the Frobenius radius. -/
theorem coneToPlane_zero_iff (W : RankCone κ) : coneToPlane W = 0 ↔ W = coneZero := by
  constructor
  · intro h
    apply Subtype.ext
    apply (cFrobSq_eq_zero_iff _).mp
    rw [← coneToPlane_sq, h]
    simp [planeSq]
  · aesop

theorem abs_coneToPlane_le (W : RankCone κ) (i : Fin 2) :
    |coneToPlane W i| ≤ frobeniusRadius W.val := by
  have hn := coneToPlane_sq W
  have hr := frobeniusRadius_sq W.val
  have hp := frobeniusRadius_nonneg W.val
  have hs : (coneToPlane W i)^2 ≤ cFrobSq W.val := by
    fin_cases i <;> simp only [Fin.mk_zero, Fin.mk_one] <;>
      dsimp [planeSq] at hn <;> nlinarith [sq_nonneg (coneToPlane W 0),
      sq_nonneg (coneToPlane W 1)]
  nlinarith [sq_abs (coneToPlane W i), abs_nonneg (coneToPlane W i)]

/-- In particular continuous on the zero-matrix stratum of every product. -/
theorem continuous_coneToPlane : Continuous (coneToPlane : RankCone κ → CircleVector) := by
  apply continuous_iff_continuousAt.mpr
  intro W
  by_cases hz : W.val = 0
  · have hW : W = coneZero := Subtype.ext hz
    subst W
    rw [ContinuousAt, coneToPlane_zero, tendsto_zero_iff_norm_tendsto_zero]
    have hr : Tendsto (fun Z : RankCone κ => frobeniusRadius Z.val)
        (𝓝 coneZero) (𝓝 0) := by
      have hc : Continuous (fun Z : RankCone κ => frobeniusRadius Z.val) :=
        continuous_frobeniusRadius.comp continuous_subtype_val
      simpa [ContinuousAt, coneZero, frobeniusRadius, cFrobSq, cFrobInner] using hc.continuousAt (x := coneZero)
    apply squeeze_zero (fun _ => norm_nonneg _) _ hr
    intro Z
    exact (pi_norm_le_iff_of_nonneg (frobeniusRadius_nonneg Z.val)).mpr
      (fun i => by simp_all [abs_coneToPlane_le,Real.norm_eq_abs])
  · apply continuousAt_pi.mpr
    intro i
    exact ((continuous_apply i).comp
      (continuous_circleCoordinate.comp continuous_subtype_val)).continuousAt.div
      (continuous_frobeniusRadius.comp continuous_subtype_val).continuousAt
      (frobeniusRadius_ne_zero hz)

/-- Homogeneous extension of the projector section: eigenvalues are 0 and |v|.
No direction v/|v| is chosen, so this expression is continuous also at v=0. -/
def planeMatrix  : Mat 2 :=
  !![(planeRadius v + v 0)/2, v 1/2;
     v 1/2, (planeRadius v - v 0)/2]

theorem planeMatrix_symmetric  : (planeMatrix v)ᵀ = planeMatrix v := by
  ext i j
  fin_cases i,j <;> simp [planeMatrix]

theorem planeMatrix_rank  : (planeMatrix v).rank ≤ 1 := by
  apply rank_le_one_of_two_column_minors
  have h := planeRadius_sq v
  dsimp [planeSq] at h
  intro j k
  fin_cases j,k <;> simp [planeMatrix] <;> nlinarith [h]

theorem planeMatrix_sq  :
    planeMatrix v * planeMatrix v = planeRadius v • planeMatrix v := by
  have h := planeRadius_sq v
  dsimp [planeSq] at h
  ext i j
  fin_cases i,j <;>
    simp [planeMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith [h]

theorem planeMatrix_frobSq  : cFrobSq (planeMatrix v) = planeSq v := by
  have h := planeRadius_sq v
  dsimp [planeSq] at h ⊢
  simp [cFrobSq, cFrobInner, planeMatrix, Fin.sum_univ_two]
  nlinarith [h]

def planeToCone   : RankCone (Fin (d+2)) :=
  ⟨padTwo d (planeMatrix v), padTwo_rank_le_one d (planeMatrix_rank v)⟩

theorem continuous_planeToCone  : Continuous (planeToCone d) := by
  apply Continuous.subtype_mk
  change Continuous (fun v i => (Fin.cons (planeMatrix v i 0)
    (Fin.cons (planeMatrix v i 1) (fun _ : Fin d => 0)) : Fin (d+2) → ℝ))
  unfold planeMatrix planeRadius planeSq
  fun_prop

@[simp] theorem planeToCone_zero  : planeToCone d 0 = coneZero := by
  apply Subtype.ext
  ext i j
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun _ => ?_) j) j
  all_goals fin_cases i <;>
    simp [planeToCone, planeMatrix, planeRadius, planeSq, padTwo, coneZero] <;> rfl

theorem planeToCone_sq   :
    cFrobSq (planeToCone d v).val = planeSq v := by
  change cFrobSq (padTwo d (planeMatrix v)) = planeSq v
  rw [padTwo_frobSq, planeMatrix_frobSq]

theorem planeToCone_radius   :
    frobeniusRadius (planeToCone d v).val = planeRadius v := by
  simp [frobeniusRadius, planeToCone_sq, planeRadius]

theorem circleCoordinate_planeToCone   :
    circleCoordinate (planeToCone d v).val = planeRadius v • v := by
  have hg : rowGram (planeToCone d v).val = planeRadius v • planeMatrix v := by
    change rowGram (padTwo d (planeMatrix v)) = _
    rw [padTwo_rowGram, planeMatrix_symmetric, planeMatrix_sq]
  ext i
  fin_cases i <;> simp [circleCoordinate, hg, planeMatrix] <;> ring

/-- The retraction identity, including the origin. -/
theorem coneToPlane_planeToCone   :
    coneToPlane (planeToCone d v) = v := by
  by_cases hv : v = 0
  · subst v
    simp
  · have hr : planeRadius v ≠ 0 := fun h => hv ((planeRadius_eq_zero_iff v).mp h)
    ext i
    change circleCoordinate (planeToCone d v).val i /
      frobeniusRadius (planeToCone d v).val = v i
    rw [circleCoordinate_planeToCone, planeToCone_radius]
    change planeRadius v * v i / planeRadius v = v i
    field_simp [hr]

end GS.NonmanifoldObstruction
