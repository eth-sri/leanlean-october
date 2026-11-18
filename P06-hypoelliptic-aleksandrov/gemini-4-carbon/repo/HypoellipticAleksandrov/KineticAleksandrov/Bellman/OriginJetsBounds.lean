module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.HomogeneousTestLiftCalculus
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.BarrierFunctionSpaceLinear
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AnnularNormalizationGeometry

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov
open Set Filter
open scoped Topology






/-- Normalize a punctured point on the literal kinetic unit sphere. -/
def bellmanUnitPoint (q : ℝ × ℝ) : ℝ × ℝ :=
  bellmanPlaneDilation (bellmanGauge q)⁻¹ q

/-- The normalization has gauge one. -/
theorem bellmanUnitPoint_gauge {q : ℝ × ℝ} (hq : q ≠ (0, 0)) :
    bellmanGauge (bellmanUnitPoint q) = 1 := by
  rw [bellmanUnitPoint, bellmanGauge_dilation _ (inv_pos.mpr (bellmanGauge_pos q hq))]
  exact inv_mul_cancel₀ (bellmanGauge_pos q hq).ne'

/-- Positive radial dilation recovers the original point. -/
theorem bellmanUnitPoint_recover {q : ℝ × ℝ} (hq : q ≠ (0, 0)) :
    bellmanPlaneDilation (bellmanGauge q) (bellmanUnitPoint q) = q := by
  rw [bellmanUnitPoint, bellmanPlaneDilation_comp,
    mul_inv_cancel₀ (bellmanGauge_pos q hq).ne']
  simp [bellmanPlaneDilation, one_pow]

/-- Every continuous homogeneous scalar function is bounded by its literal gauge degree. -/
theorem bellman_homogeneous_gauge_bound (beta : ℝ) (f : (ℝ × ℝ) → ℝ)
    (hc : ContinuousOn f bellmanPuncturedSet)
    (hs : ∀ r : ℝ, 0 < r → ∀ q ∈ bellmanPuncturedSet,
      f (bellmanPlaneDilation r q) = r ^ beta * f q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ bellmanPuncturedSet, |f q| ≤ C * bellmanGauge q ^ beta := by
  have hsU : {q : ℝ × ℝ | bellmanGauge q = 1} ⊆ bellmanPuncturedSet :=
    fun q hq => BellmanSphere.ne_zero ⟨q, hq⟩
  obtain ⟨C, hC⟩ := bellmanSphere_isCompact.bddAbove_image (hc.mono hsU).abs
  refine ⟨max C 0, le_max_right _ _, fun q hq => ?_⟩
  have hz := bellmanUnitPoint_gauge hq
  have hb :=
    (hC (mem_image_of_mem _ hz)).trans (le_max_left C 0)
  have he := hs (bellmanGauge q) (bellmanGauge_pos q hq) _ (hsU hz)
  rw [bellmanUnitPoint_recover hq] at he
  rw [he, abs_mul, abs_of_pos (Real.rpow_pos_of_pos (bellmanGauge_pos q hq) beta)]
  exact (mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg (bellmanGauge_nonneg q) beta)).trans_eq
    (mul_comm _ _)

/-- The actual Bellman function and all three jets have their exact source gauge bounds. -/
theorem IsBellmanHomogeneous.origin_jet_bounds {alpha : ℝ} {phi : (ℝ × ℝ) → ℝ}
    (h : IsBellmanHomogeneous alpha phi) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ bellmanPuncturedSet,
      |phi q| ≤ C * bellmanGauge q ^ alpha) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ bellmanPuncturedSet,
      |bellmanDx phi q| ≤ C * bellmanGauge q ^ (alpha - 3)) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ bellmanPuncturedSet,
      |bellmanDv phi q| ≤ C * bellmanGauge q ^ (alpha - 1)) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ bellmanPuncturedSet,
      |bellmanDvv phi q| ≤ C * bellmanGauge q ^ (alpha - 2))     := by
  have eventually_scaling {r : ℝ} (hr : 0 < r) {q : ℝ × ℝ} (hq : q ∈ bellmanPuncturedSet) :
      (fun z => phi (bellmanPlaneDilation r z)) =ᶠ[𝓝 q] fun z => r ^ alpha * phi z := by
    filter_upwards [bellmanPuncturedSet_isOpen.mem_nhds hq] with z hz
    exact h.2 r hr z hz
  have dvv_scaling {r : ℝ} (hr : 0 < r) {q : ℝ × ℝ} (hq : q ∈ bellmanPuncturedSet) :
      bellmanDvv phi (bellmanPlaneDilation r q) = r ^ (alpha - 2) * bellmanDvv phi q := by
    have he : bellmanDv (fun z => phi (bellmanPlaneDilation r z)) =ᶠ[𝓝 q]
        (r ^ alpha) • bellmanDv phi := by
      filter_upwards [bellmanPuncturedSet_isOpen.mem_nhds hq] with z hz
      have hh := congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (0, 1))
        (eventually_scaling hr hz).fderiv_eq
      change bellmanDv (fun z => phi (bellmanPlaneDilation r z)) z =
        (fderiv ℝ ((r ^ alpha) • phi) z) (0, 1) at hh
      rwa [fderiv_const_smul_field] at hh
    have hh := congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (0, 1)) he.fderiv_eq
    change bellmanDvv (fun z => phi (bellmanPlaneDilation r z)) q = _ at hh
    rw [bellmanDvv_comp_dilation r hr phi h.1 q hq, fderiv_const_smul_field] at hh
    apply mul_left_cancel₀ (pow_ne_zero 2 hr.ne')
    calc
      r ^ 2 * bellmanDvv phi (bellmanPlaneDilation r q) =
          r ^ alpha * bellmanDvv phi q := hh
      _ = r ^ 2 * (r ^ (alpha - 2) * bellmanDvv phi q) := by
        rw [← mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add hr]
        congr 2
        ring
  have dv_scaling {r : ℝ} (hr : 0 < r) {q : ℝ × ℝ} (hq : q ∈ bellmanPuncturedSet) :
      bellmanDv phi (bellmanPlaneDilation r q) = r ^ (alpha - 1) * bellmanDv phi q := by
    have hd := (h.1.contDiffAt (bellmanPuncturedSet_isOpen.mem_nhds
      (bellmanPlaneDilation_ne_zero r hr q hq))).differentiableAt (by norm_num)
    have hh := congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (0, 1))
      (eventually_scaling hr hq).fderiv_eq
    change bellmanDv (fun z => phi (bellmanPlaneDilation r z)) q =
      (fderiv ℝ ((r ^ alpha) • phi) q) (0, 1) at hh
    rw [bellmanDv_comp_dilation r phi q hd] at hh
    rw [fderiv_const_smul_field] at hh
    apply mul_left_cancel₀ hr.ne'
    calc
      r * bellmanDv phi (bellmanPlaneDilation r q) = r ^ alpha * bellmanDv phi q := hh
      _ = r * (r ^ (alpha - 1) * bellmanDv phi q) := by
        have he : r * r ^ (alpha - 1) = r ^ alpha := by
          calc
            r * r ^ (alpha - 1) = r ^ 1 * r ^ (alpha - 1) := by
              rw [Real.rpow_one]
            _ = r ^ (1 + (alpha - 1)) := (Real.rpow_add hr _ _).symm
            _ = r ^ alpha := by congr 1; ring
        rw [← mul_assoc, he]
  have dx_scaling {r : ℝ} (hr : 0 < r) {q : ℝ × ℝ} (hq : q ∈ bellmanPuncturedSet) :
      bellmanDx phi (bellmanPlaneDilation r q) = r ^ (alpha - 3) * bellmanDx phi q := by
    have hd := (h.1.contDiffAt (bellmanPuncturedSet_isOpen.mem_nhds
      (bellmanPlaneDilation_ne_zero r hr q hq))).differentiableAt (by norm_num)
    have hh := congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (1, 0))
      (eventually_scaling hr hq).fderiv_eq
    change bellmanDx (fun z => phi (bellmanPlaneDilation r z)) q =
      (fderiv ℝ ((r ^ alpha) • phi) q) (1, 0) at hh
    rw [bellmanDx_comp_dilation r phi q hd] at hh
    rw [fderiv_const_smul_field] at hh
    apply mul_left_cancel₀ (pow_ne_zero 3 hr.ne')
    calc
      r ^ 3 * bellmanDx phi (bellmanPlaneDilation r q) =
          r ^ alpha * bellmanDx phi q := hh
      _ = r ^ 3 * (r ^ (alpha - 3) * bellmanDx phi q) := by
        rw [← mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add hr]
        congr 2
        ring
  refine ⟨bellman_homogeneous_gauge_bound alpha phi h.1.continuousOn h.2, ?_, ?_, ?_⟩
  · exact bellman_homogeneous_gauge_bound (alpha - 3) (bellmanDx phi) h.dx_continuousOn
      (fun _ hr _ hq => dx_scaling hr hq)
  · exact bellman_homogeneous_gauge_bound (alpha - 1) (bellmanDv phi)
      (h.directional_contDiffOn (0, 1)).continuousOn (fun _ hr _ hq => dv_scaling hr hq)
  · exact bellman_homogeneous_gauge_bound (alpha - 2) (bellmanDvv phi) h.dvv_continuousOn
      (fun _ hr _ hq => dvv_scaling hr hq)

end HypoellipticAleksandrov.KineticAleksandrov

