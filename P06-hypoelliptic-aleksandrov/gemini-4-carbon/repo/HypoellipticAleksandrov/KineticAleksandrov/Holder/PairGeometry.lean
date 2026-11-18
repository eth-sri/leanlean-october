module

public import HypoellipticAleksandrov.KineticAleksandrov.Geometry
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.AffineGeometryTopology
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Setting
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.LeakageGeometry

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder
open Set

/-- The source kinetic quasi-distance is nonnegative. -/
theorem quasiDistance_nonneg {d : ℕ} (P Q : KineticPoint d) : 0 ≤ quasiDistance P Q := by
  unfold quasiDistance
  exact add_nonneg (add_nonneg (Real.sqrt_nonneg _)
    (PDE.vecEuclideanNorm_nonneg _))
    (Real.rpow_nonneg (le_max_of_le_left (PDE.vecEuclideanNorm_nonneg _)) _)

/-- The source maximum of the two transported displacements makes the distance symmetric. -/
theorem quasiDistance_symm {d : ℕ} (P Q : KineticPoint d) :
    quasiDistance P Q = quasiDistance Q P := by
  unfold quasiDistance
  rw [abs_sub_comm P.time Q.time, PDE.vecEuclideanNorm_sub_comm P.velocity Q.velocity,
    max_comm]

/-- The source quasi-distance separates points, including in dimension zero. -/
theorem quasiDistance_eq_zero_iff {d : ℕ} (P Q : KineticPoint d) :
    quasiDistance P Q = 0 ↔ P = Q := by
  constructor
  · intro h
    let B := max
      (PDE.vecEuclideanNorm (Q.position - P.position - (Q.time - P.time) • P.velocity))
      (PDE.vecEuclideanNorm (P.position - Q.position - (P.time - Q.time) • Q.velocity))
    have hB : 0 ≤ B := le_max_of_le_left (PDE.vecEuclideanNorm_nonneg _)
    have hroot := Real.sqrt_nonneg |P.time - Q.time|
    have hvel := PDE.vecEuclideanNorm_nonneg (P.velocity - Q.velocity)
    have hrpow := Real.rpow_nonneg hB (1 / 3 : ℝ)
    change 0 ≤ Real.rpow B (1 / 3 : ℝ) at hrpow
    change Real.sqrt |P.time - Q.time| +
      PDE.vecEuclideanNorm (P.velocity - Q.velocity) + Real.rpow B (1 / 3 : ℝ) = 0 at h
    have ht0 : Real.sqrt |P.time - Q.time| = 0 := by linarith only [h, hroot, hvel, hrpow]
    have hv0 : PDE.vecEuclideanNorm (P.velocity - Q.velocity) = 0 := by
      linarith only [h, hroot, hvel, hrpow]
    have hb0 : Real.rpow B (1 / 3 : ℝ) = 0 := by linarith only [h, hroot, hvel, hrpow]
    have ht : P.time = Q.time := by
      exact sub_eq_zero.mp (abs_nonpos_iff.mp (Real.sqrt_eq_zero'.mp ht0))
    have hv : P.velocity = Q.velocity :=
      sub_eq_zero.mp (PDE.vecEuclideanNorm_eq_zero_iff.mp hv0)
    have hB0 : B = 0 := (Real.rpow_eq_zero hB (by norm_num : (1 / 3 : ℝ) ≠ 0)).mp hb0
    have hxle := le_max_left
      (PDE.vecEuclideanNorm (Q.position - P.position - (Q.time - P.time) • P.velocity))
      (PDE.vecEuclideanNorm (P.position - Q.position - (P.time - Q.time) • Q.velocity))
    change _ ≤ B at hxle
    rw [hB0, ht, sub_self, zero_smul, sub_zero] at hxle
    have hx : P.position = Q.position :=
      (sub_eq_zero.mp (PDE.vecEuclideanNorm_eq_zero_iff.mp
        (le_antisymm hxle (PDE.vecEuclideanNorm_nonneg _)))).symm
    exact KineticPoint.ext ht hx hv
  · rintro rfl
    have hz : PDE.vecEuclideanNorm (0 : PDE.Vec d) = 0 :=
      PDE.vecEuclideanNorm_eq_zero_iff.mpr rfl
    simp [quasiDistance, hz]



/-- A positive affine map takes the closed unit cylinder onto the physical cylinder closure. -/
theorem kineticAffine_image_closedUnitCylinder {d : ℕ} (P : KineticPoint d) {r : ℝ}
    (hr : 0 < r) :
    kineticAffine P r '' closure (backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1) =
      closure (backwardCylinder P r) := by
  have hc := (kineticAffineHomeomorph P r hr.ne').image_closure
    (backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1)
  change kineticAffine P r '' closure _ = closure (kineticAffine P r '' _) at hc
  rw [kineticAffine_image_unitCylinder P hr] at hc
  exact hc


/-- Compact centers and one compact model cylinder give the exact compact neighbourhood closure. -/
theorem holder_neighbourhood_compact {d : ℕ}
    (K : Set (KineticPoint d)) (hK : IsCompact K) (R0 : ℝ) (hR0 : 0 < R0) :
    closure (holderNeighbourhood R0 K) =
        ⋃ P ∈ K, closure (backwardCylinder P (2 * R0)) ∧
      IsCompact (closure (holderNeighbourhood R0 K))  := by
  have continuous_kineticAffine_pair (r : ℝ) :
      Continuous (fun z : KineticPoint d × KineticPoint d => kineticAffine z.1 r z.2) := by
    have ht1 := (continuous_time (d := d)).comp
      (continuous_fst (X := KineticPoint d) (Y := KineticPoint d))
    have ht2 := (continuous_time (d := d)).comp
      (continuous_snd (X := KineticPoint d) (Y := KineticPoint d))
    have hx1 := (continuous_position (d := d)).comp
      (continuous_fst (X := KineticPoint d) (Y := KineticPoint d))
    have hx2 := (continuous_position (d := d)).comp
      (continuous_snd (X := KineticPoint d) (Y := KineticPoint d))
    have hv1 := (continuous_velocity (d := d)).comp
      (continuous_fst (X := KineticPoint d) (Y := KineticPoint d))
    have hv2 := (continuous_velocity (d := d)).comp
      (continuous_snd (X := KineticPoint d) (Y := KineticPoint d))
    exact KineticPoint.continuous_mk
      (ht1.add (ht2.const_mul (r ^ 2)))
      ((hx1.add (hx2.const_smul (r ^ 3))).add ((ht2.const_mul (r ^ 2)).smul hv1))
      (hv1.add (hv2.const_smul r))
  let r := 2 * R0
  have hr : 0 < r := by dsimp only [r]; positivity
  let B := closure (backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1)
  let U := ⋃ P ∈ K, closure (backwardCylinder P r)
  have himage : (fun z : KineticPoint d × KineticPoint d => kineticAffine z.1 r z.2) ''
      (K ×ˢ B) = U := by
    ext Z
    simp only [mem_image, mem_prod, mem_iUnion, U]
    constructor
    · rintro ⟨⟨P, Q⟩, ⟨hP, hQ⟩, rfl⟩
      exact ⟨P, hP, kineticAffine_image_closedUnitCylinder P hr ▸ ⟨Q, hQ, rfl⟩⟩
    · rintro ⟨P, hP, hZ⟩
      rw [← kineticAffine_image_closedUnitCylinder P hr] at hZ
      obtain ⟨Q, hQ, heq⟩ := hZ
      exact ⟨(P, Q), ⟨hP, hQ⟩, heq⟩
  have hUc : IsCompact U := by
    rw [← himage]
    exact (hK.prod (isCompact_closure_backwardCylinder _ 1 zero_lt_one)).image
      (continuous_kineticAffine_pair r)
  have hNsub : holderNeighbourhood R0 K ⊆ U := by
    intro Z hZ
    simp only [holderNeighbourhood, mem_iUnion] at hZ
    obtain ⟨P, hP, hZ⟩ := hZ
    exact mem_iUnion.mpr ⟨P, mem_iUnion.mpr ⟨hP, subset_closure hZ⟩⟩
  have hclosed : closure (holderNeighbourhood R0 K) = U := by
    apply Subset.antisymm (closure_minimal hNsub hUc.isClosed)
    intro Z hZ
    simp only [U, mem_iUnion] at hZ
    obtain ⟨P, hP, hZ⟩ := hZ
    have hs : backwardCylinder P r ⊆ holderNeighbourhood R0 K := by
      intro Y hY
      exact mem_iUnion.mpr ⟨P, mem_iUnion.mpr ⟨hP, hY⟩⟩
    exact closure_mono hs hZ
  exact ⟨hclosed, hclosed ▸ hUc⟩



/-- Every point satisfying the weak unit bounds is an explicit limit of interior points. -/
theorem mem_closure_unitCylinder_of_bounds {d : ℕ} (P : KineticPoint d)
    (htlo : -1 ≤ P.time) (hthi : P.time ≤ 0)
    (hx : PDE.vecEuclideanNorm P.position ≤ 1)
    (hv : PDE.vecEuclideanNorm P.velocity ≤ 1) :
    P ∈ closure (backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1) := by
  let f : ℝ → KineticPoint d := fun e =>
    ⟨(1 - e) * P.time - e / 2, (1 - e) • P.position, (1 - e) • P.velocity⟩
  have hf : Continuous f := KineticPoint.continuous_mk
    ((continuous_const.sub continuous_id).mul continuous_const |>.sub
      (continuous_id.div_const 2))
    ((continuous_const.sub continuous_id).smul continuous_const)
    ((continuous_const.sub continuous_id).smul continuous_const)
  have hsub : f '' Ioo 0 1 ⊆ backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1 := by
    rintro Z ⟨e, he, rfl⟩
    have he1 : 0 < 1 - e := sub_pos.mpr he.2
    refine ⟨?_, ?_, ?_, ?_⟩
    · change 0 - (1 : ℝ) ^ 2 < (1 - e) * P.time - e / 2
      norm_num only [one_pow, zero_sub]
      nlinarith only [mul_le_mul_of_nonneg_left htlo he1.le, he.1]
    · change (1 - e) * P.time - e / 2 < 0
      nlinarith only [mul_nonpos_of_nonneg_of_nonpos he1.le hthi, he.1]
    · apply (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt zero_lt_one).mpr
      change PDE.vecEuclideanNorm ((1 - e) • P.velocity - 0) < 1
      rw [sub_zero, PDE.vecEuclideanNorm_smul, abs_of_pos he1]
      nlinarith only [mul_le_mul_of_nonneg_left hv he1.le, he.1]
    · apply (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt
        (by norm_num : (0 : ℝ) < (1 : ℝ) ^ 3)).mpr
      change PDE.vecEuclideanNorm ((1 - e) • P.position - 0 -
        ((1 - e) * P.time - e / 2 - 0) • 0 - 0) < 1 ^ 3
      rw [smul_zero, sub_zero, sub_zero, sub_zero, PDE.vecEuclideanNorm_smul,
        abs_of_pos he1]
      norm_num only [one_pow]
      nlinarith only [mul_le_mul_of_nonneg_left hx he1.le, he.1]
  have hz : (0 : ℝ) ∈ closure (Ioo 0 1) := by
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact ⟨le_rfl, zero_le_one⟩
  have hp := closure_mono hsub
    (hf.continuousOn.image_closure (mem_image_of_mem f hz))
  simpa only [f, sub_zero, mul_one, one_mul, zero_div, one_smul] using hp

/-- Weak physical time, position and velocity bounds imply cylinder-closure membership. -/
theorem mem_closure_backwardCylinder_of_bounds {d : ℕ} (P0 P : KineticPoint d)
    {r : ℝ} (hr : 0 < r) (htlo : -(r ^ 2) ≤ P.time - P0.time)
    (hthi : P.time - P0.time ≤ 0)
    (hx : PDE.vecEuclideanNorm (relativePosition P0 P) ≤ r ^ 3)
    (hv : PDE.vecEuclideanNorm (relativeVelocity P0 P) ≤ r) :
    P ∈ closure (backwardCylinder P0 r) := by
  have hi : kineticAffineInverse P0 r P ∈
      closure (backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1) := by
    apply mem_closure_unitCylinder_of_bounds
    · change -1 ≤ (P.time - P0.time) / r ^ 2
      exact (le_div_iff₀ (pow_pos hr 2)).mpr (by simpa only [neg_one_mul] using htlo)
    · change (P.time - P0.time) / r ^ 2 ≤ 0
      exact div_nonpos_of_nonpos_of_nonneg hthi (sq_nonneg r)
    · change PDE.vecEuclideanNorm ((r ^ 3)⁻¹ • relativePosition P0 P) ≤ 1
      rw [PDE.vecEuclideanNorm_smul, abs_of_pos (inv_pos.mpr (pow_pos hr 3))]
      exact (mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr (pow_nonneg hr.le 3))).trans_eq
        (inv_mul_cancel₀ (pow_ne_zero 3 hr.ne'))
    · change PDE.vecEuclideanNorm (r⁻¹ • relativeVelocity P0 P) ≤ 1
      rw [PDE.vecEuclideanNorm_smul, abs_of_pos (inv_pos.mpr hr)]
      exact (mul_le_mul_of_nonneg_left hv (inv_nonneg.mpr hr.le)).trans_eq
        (inv_mul_cancel₀ hr.ne')
  have hc := (kineticAffineHomeomorph P0 r hr.ne').image_closure
    (backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1)
  change kineticAffine P0 r '' closure _ = closure (kineticAffine P0 r '' _) at hc
  rw [kineticAffine_image_unitCylinder P0 hr] at hc
  rw [← hc]
  exact ⟨kineticAffineInverse P0 r P, hi, kineticAffine_apply_inverse P0 hr.ne' P⟩




/-- Time-ordered distinct points belong to the closed cylinder at their later endpoint. -/
theorem pair_mem_closed_later_cylinder {d : ℕ}
    (P P' : KineticPoint d) (ht : P.time ≤ P'.time)
    (hpos : 0 < quasiDistance P P') :
    P ∈ closure (backwardCylinder P' (quasiDistance P P')) ∧
      P' ∈ closure (backwardCylinder P' (quasiDistance P P'))  := by
  have quasiDistance_component_bounds :
      |P.time - P'.time| ≤ quasiDistance P P' ^ 2 ∧
      PDE.vecEuclideanNorm (relativeVelocity P' P) ≤ quasiDistance P P' ∧
      PDE.vecEuclideanNorm (relativePosition P' P) ≤ quasiDistance P P' ^ 3 := by
    let A := max (PDE.vecEuclideanNorm (relativePosition P P'))
      (PDE.vecEuclideanNorm (relativePosition P' P))
    have hA : 0 ≤ A := (PDE.vecEuclideanNorm_nonneg _).trans (le_max_left _ _)
    have hs := Real.sqrt_nonneg |P.time - P'.time|
    have hv := PDE.vecEuclideanNorm_nonneg (relativeVelocity P' P)
    have hk := Real.rpow_nonneg hA (1 / 3 : ℝ)
    have hdef : quasiDistance P P' = Real.sqrt |P.time - P'.time| +
        PDE.vecEuclideanNorm (relativeVelocity P' P) + A ^ (1 / 3 : ℝ) := rfl
    have hsD : Real.sqrt |P.time - P'.time| ≤ quasiDistance P P' := by
      rw [hdef]; linarith only [hv, hk]
    have hvD : PDE.vecEuclideanNorm (relativeVelocity P' P) ≤ quasiDistance P P' := by
      rw [hdef]; linarith only [hs, hk]
    have hkD : A ^ (1 / 3 : ℝ) ≤ quasiDistance P P' := by
      rw [hdef]; linarith only [hs, hv]
    have hAeq : (A ^ (1 / 3 : ℝ)) ^ 3 = A := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hA]
      norm_num
    refine ⟨?_, hvD, ?_⟩
    · have he := pow_le_pow_left₀ hs hsD 2
      rw [Real.sq_sqrt (abs_nonneg _)] at he
      exact he
    · have he := pow_le_pow_left₀ hk hkD 3
      rw [hAeq] at he
      exact (le_max_right _ _).trans he
  obtain ⟨htime, hv, hx⟩ := quasiDistance_component_bounds
  refine ⟨mem_closure_backwardCylinder_of_bounds P' P hpos ?_
    (sub_nonpos.mpr ht) hx hv, ?_⟩
  · rw [abs_of_nonpos (sub_nonpos.mpr ht)] at htime
    linarith only [htime]
  · exact Covering.top_mem_closure_cylinder P' hpos
      (PDE.center_mem_euclideanBall _ hpos)

end HypoellipticAleksandrov.KineticAleksandrov.Holder

