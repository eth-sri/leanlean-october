module

public import HypoellipticAleksandrov.Parabolic.LocalClassical
public import HypoellipticAleksandrov.Parabolic.HarnackABP
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.Parabolic
open Matrix Set Filter
open scoped MatrixOrder Topology





namespace HasLowerEllipticityOn

/-- A continuous lower ellipticity bound extends to the closure whenever the
closure stays within the coefficient's continuity set. -/
theorem closure
    {d : ℕ} {lam : ℝ} {A : CoefficientField d}
    {S U : Set (TimeVelocity d)}
    (h : HasLowerEllipticityOn lam A S)
    (hcont : IsContinuousCoefficientOn A U)
    (hclosureU : _root_.closure S ⊆ U) :
    HasLowerEllipticityOn lam A (_root_.closure S)  := by
  have isClosed_setOf_lowerEllipticity :
      IsClosed {M : PDE.Mat d | lam • 1 ≤ M} := by
    have isClosed_posSemidef :
        IsClosed {H : PDE.Mat d | H.PosSemidef} := by
      have isClosed_isHermitian :
          IsClosed {H : PDE.Mat d | H.IsHermitian} := by
        have hset :
            {H : PDE.Mat d | H.IsHermitian} =
              ⋂ i : Fin d, ⋂ j : Fin d, {H : PDE.Mat d | H j i = H i j} := by
          ext H
          simp
          constructor
          · intro h i j
            simpa using h.apply i j
          · intro h
            apply Matrix.IsHermitian.ext
            intro i j
            simpa using h i j
        rw [hset]
        refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
        exact isClosed_eq (continuous_id.matrix_elem j i) (continuous_id.matrix_elem i j)
      have hset :
          {H : PDE.Mat d | H.PosSemidef} =
            {H : PDE.Mat d | H.IsHermitian} ∩
              ⋂ q : PDE.Vec d, {H : PDE.Mat d | 0 ≤ dotProduct q (H *ᵥ q)} := by
        ext H
        simp
        simpa using (Matrix.posSemidef_iff_dotProduct_mulVec (M := H))
      rw [hset]
      refine (isClosed_isHermitian).inter (isClosed_iInter fun q => ?_)
      have hquad : Continuous (fun H : PDE.Mat d => dotProduct q (H *ᵥ q)) :=
        continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)
      exact isClosed_le continuous_const hquad
    have hset : {M : PDE.Mat d | lam • 1 ≤ M} =
        (fun M : PDE.Mat d => M - lam • 1) ⁻¹'
          {H : PDE.Mat d | H.PosSemidef} := by
      ext M
      exact Matrix.le_iff
    rw [hset]
    exact (isClosed_posSemidef).preimage (continuous_id.sub continuous_const)
  have hmaps : MapsTo (coefficientAt A) S
      {M : PDE.Mat d | lam • 1 ≤ M} := h
  intro z hz
  have hzLower := (hmaps.closure_of_continuousOn (hcont.mono hclosureU)) hz
  rwa [(isClosed_setOf_lowerEllipticity).closure_eq] at hzLower

end HasLowerEllipticityOn







/-- The compact local ABP cylinder lies in the supplied unit closed
coordinate box whenever its centre lies in the half cube. -/
theorem localABPClosure_subset_parabolicClosedBox_one {d : ℕ}
    {v₀ : PDE.Vec d} (hv₀ : v₀ ∈ velocityClosedCube 0 (1 / 2 : ℝ)) :
    localABPClosure v₀ ⊆ parabolicClosedBox 1 1 0 0  := by
  have euclideanClosedBall_subset_velocityClosedCube {v₀ : PDE.Vec d} {r : ℝ} (hr : 0 ≤ r) :
      PDE.euclideanClosedBall v₀ r ⊆ velocityClosedCube v₀ r := by
    intro v hv i
    have hcoord : (v i - v₀ i) ^ 2 ≤ r ^ 2 := by
      simpa [PDE.euclideanSqDist, Pi.sub_apply] using
        (PDE.sq_apply_le_vecNormSq (v - v₀) i).trans hv
    exact abs_le_of_sq_le_sq hcoord hr
  rintro z ⟨w, hw, rfl⟩
  rcases mem_closedParabolicCylinder_iff.mp hw with ⟨hw0, hw1, hwv⟩
  apply mem_parabolicClosedBox_iff.mpr
  constructor
  · nlinarith
  constructor
  · nlinarith
  · intro i
    have hwcoord :=
      euclideanClosedBall_subset_velocityClosedCube (by norm_num) hwv i
    have hvcoord := hv₀ i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hwcoord hvcoord ⊢
    have hvabs : |v₀ i| ≤ 1 / 2 := by
      simpa using hvcoord
    rw [sub_zero] at hwcoord
    calc
      |v₀ i + (1 / 2 : ℝ) * w.2 i - (0 : PDE.Vec d) i| =
          |v₀ i + (1 / 2 : ℝ) * w.2 i| := by simp
      _ ≤ |v₀ i| + |(1 / 2 : ℝ) * w.2 i| := abs_add_le _ _
      _ = |v₀ i| + (1 / 2 : ℝ) * |w.2 i| := by
        rw [abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ))]
      _ ≤ 1 / 2 + (1 / 2 : ℝ) * 1 := by gcongr
      _ = 1 := by norm_num

/-- The open local ABP cylinder lies in the unit open coordinate box whenever
its centre lies in the half closed cube. -/
theorem localABPInterior_subset_parabolicBox_one {d : ℕ}
    {v₀ : PDE.Vec d} (hv₀ : v₀ ∈ velocityClosedCube 0 (1 / 2 : ℝ)) :
    localABPInterior v₀ ⊆ parabolicBox 1 1 0 0 := by
  rintro z ⟨w, hw, rfl⟩
  rcases mem_parabolicInterior_iff.mp hw with ⟨hw0, hw1, hwv⟩
  apply mem_parabolicBox_iff.mpr
  constructor
  · nlinarith
  constructor
  · nlinarith
  · intro i
    have hwcoord :=
      euclideanBall_subset_velocityCube (by norm_num) hwv i
    have hvcoord := hv₀ i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hwcoord hvcoord ⊢
    have hvabs : |v₀ i| ≤ 1 / 2 := by
      simpa using hvcoord
    rw [sub_zero] at hwcoord
    calc
      |v₀ i + (1 / 2 : ℝ) * w.2 i - (0 : PDE.Vec d) i| =
          |v₀ i + (1 / 2 : ℝ) * w.2 i| := by simp
      _ ≤ |v₀ i| + |(1 / 2 : ℝ) * w.2 i| := abs_add_le _ _
      _ = |v₀ i| + (1 / 2 : ℝ) * |w.2 i| := by
        rw [abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ))]
      _ < 1 / 2 + (1 / 2 : ℝ) * 1 := by
        have hscaled : (1 / 2 : ℝ) * |w.2 i| < (1 / 2 : ℝ) * 1 :=
          mul_lt_mul_of_pos_left hwcoord (by norm_num)
        linarith
      _ = 1 := by norm_num

/-- Every initial or lateral local ABP boundary point is a limit of points of
the open local ABP cylinder. -/
theorem localABPForwardBoundary_subset_closure_interior {d : ℕ}
    (v₀ : PDE.Vec d) :
    localABPForwardBoundary v₀ ⊆ closure (localABPInterior v₀)  := by
  have forwardParabolicBoundary_one_subset_closure_parabolicInterior :
      forwardParabolicBoundary 1 0 ⊆
      closure (parabolicInterior 1 (0 : PDE.Vec d)) := by
    intro z hz
    have closedParabolicCylinder_one_subset_closure_parabolicInterior :
        closedParabolicCylinder 1 0 ⊆
        closure (parabolicInterior 1 (0 : PDE.Vec d)) := by
      intro z hz
      have euclideanClosedBall_subset_closure_euclideanBall (v₀ : PDE.Vec d) :
          PDE.euclideanClosedBall v₀ 1 ⊆ closure (PDE.euclideanBall v₀ 1) := by
        intro v hv
        let c : ℕ → ℝ := fun n => 1 - 1 / (n + 1 : ℝ)
        have hc : Tendsto c atTop (𝓝 1) := by
          dsimp only [c]
          simpa using tendsto_const_nhds.sub
            (tendsto_one_div_add_atTop_nhds_zero_nat :
              Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) atTop (𝓝 0))
        have hlimit : Tendsto (fun n => c n • (v - v₀) + v₀) atTop (𝓝 v) := by
          simpa using (hc.smul_const (v - v₀)).add (tendsto_const_nhds : Tendsto (fun _ : ℕ => v₀) atTop (𝓝 v₀))
        apply mem_closure_of_tendsto hlimit
        filter_upwards [] with n
        have hdenom : 0 < (n : ℝ) + 1 := by positivity
        have hdenom_one : 1 ≤ (n : ℝ) + 1 := by nlinarith
        have hc_nonneg : 0 ≤ c n := by
          rw [sub_nonneg]
          rw [div_le_iff₀ hdenom]
          nlinarith
        have hc_lt_one : c n < 1 := by
          rw [sub_lt_iff_lt_add]
          exact lt_add_of_pos_right _ (one_div_pos.mpr hdenom)
        have hdist : PDE.euclideanSqDist (v - v₀) 0 = PDE.euclideanSqDist v v₀ := by
          calc
            PDE.euclideanSqDist (v - v₀) 0 =
                PDE.euclideanSqDist ((v - v₀) + v₀) (0 + v₀) := by
              rw [PDE.euclideanSqDist_add_right]
            _ = PDE.euclideanSqDist v v₀ := by simp
        change PDE.euclideanSqDist (c n • (v - v₀) + v₀) v₀ < 1 ^ 2
        rw [PDE.euclideanSqDist_affine_center, hdist]
        calc
          c n ^ 2 * PDE.euclideanSqDist v v₀ ≤ c n ^ 2 * 1 ^ 2 :=
            mul_le_mul_of_nonneg_left hv (sq_nonneg _)
          _ < 1 ^ 2 := by
            have hsq : c n ^ 2 < 1 ^ 2 := by
              exact (sq_lt_sq₀ hc_nonneg zero_le_one).mpr hc_lt_one
            norm_num at hsq ⊢
            exact hsq
      rw [parabolicInterior, closure_prod_eq, closure_Ioo (zero_ne_one : (0 : ℝ) ≠ 1)]
      exact ⟨⟨(mem_closedParabolicCylinder_iff.mp hz).1,
          (mem_closedParabolicCylinder_iff.mp hz).2.1⟩,
        euclideanClosedBall_subset_closure_euclideanBall 0
          (mem_closedParabolicCylinder_iff.mp hz).2.2⟩
    apply closedParabolicCylinder_one_subset_closure_parabolicInterior
    rcases mem_forwardParabolicBoundary_iff.mp hz with hinitial | hlateral
    · rcases hinitial with ⟨ht, hv⟩
      exact mem_closedParabolicCylinder_iff.mpr
        ⟨ht.ge, by rw [ht]; norm_num, hv⟩
    · rcases hlateral with ⟨ht0, ht1, hsphere⟩
      apply mem_closedParabolicCylinder_iff.mpr
      refine ⟨ht0, ht1, ?_⟩
      change PDE.euclideanSqDist z.2 0 = 1 ^ 2 at hsphere
      exact hsphere.le
  unfold localABPForwardBoundary localABPInterior
  calc
    localABPAffine v₀ '' forwardParabolicBoundary 1 0 ⊆
        localABPAffine v₀ '' closure (parabolicInterior 1 0) :=
      Set.image_mono forwardParabolicBoundary_one_subset_closure_parabolicInterior
    _ ⊆ closure (localABPAffine v₀ '' parabolicInterior 1 0) :=
      image_closure_subset_closure_image
        (contDiff_parabolicAffine (3 / 4) v₀ (1 / 2)).continuous



/-- The unit-box lower ellipticity bound extends to every local ABP compact
closure centred in the terminal half-cube. -/
theorem hasLowerEllipticityOn_localABPClosure
    {d : ℕ} {lam : ℝ} {B : CoefficientField d}
    {U : Set (TimeVelocity d)} {v0 : PDE.Vec d}
    (hclosed : parabolicClosedBox 1 1 0 (0 : PDE.Vec d) ⊆ U)
    (hcont : IsContinuousCoefficientOn B U)
    (hlow : HasLowerEllipticityOn lam B
      (parabolicBox 1 1 0 (0 : PDE.Vec d)))
    (hv0 : v0 ∈ velocityClosedCube (0 : PDE.Vec d) (1 / 2 : ℝ)) :
    HasLowerEllipticityOn lam B (localABPClosure v0)  := by
  have closure_parabolicBox_one :
      closure (parabolicBox 1 1 0 (0 : PDE.Vec d)) =
      parabolicClosedBox 1 1 0 0 := by
    have closure_velocityCube_zero_one :
        closure (velocityCube (0 : PDE.Vec d) 1) =
        velocityClosedCube (0 : PDE.Vec d) 1 := by
      rw [velocityCube_eq_pi, closure_pi_set, velocityClosedCube_eq_pi]
      simp [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)]
    simp [parabolicBox, parabolicClosedBox, one_pow]
    rw [closure_prod_eq, closure_Ioo (zero_ne_one : (0 : ℝ) ≠ 1),
      closure_velocityCube_zero_one]
  have hlowClosed : HasLowerEllipticityOn lam B
      (parabolicClosedBox 1 1 0 (0 : PDE.Vec d)) := by
    rw [← closure_parabolicBox_one]
    exact hlow.closure hcont (by rw [closure_parabolicBox_one]; exact hclosed)
  exact hlowClosed.mono (localABPClosure_subset_parabolicClosedBox_one hv0)


end HypoellipticAleksandrov.Parabolic

