module

public import HypoellipticAleksandrov.Parabolic.Scaling
public import HypoellipticAleksandrov.Parabolic.LocalHarnackGeometry
public import HypoellipticAleksandrov.Parabolic.SourceLocalHarnack
public import HypoellipticAleksandrov.Parabolic.ScalingMeasure
public import HypoellipticAleksandrov.Parabolic.HarnackGeometry
public import Mathlib.Topology.MetricSpace.Thickening
public import HypoellipticAleksandrov.Parabolic.ParabolicMollifierKernel
public import HypoellipticAleksandrov.Parabolic.HarnackUnitCylinder.TimeWeakDerivative
public import HypoellipticAleksandrov.Parabolic.HarnackUnitCylinder.SpatialWeakDerivatives
public import HypoellipticAleksandrov.Parabolic.HarnackUnitCylinder.CompactLp
import HypoellipticAleksandrov.Parabolic.WeakJetExtension
import HypoellipticAleksandrov.Parabolic.WeakJetMollifier
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelDominated
import HypoellipticAleksandrov.LinearAlgebra.LoewnerEntryBound
import Mathlib.Analysis.Calculus.BumpFunction.Convolution

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.Parabolic
open Filter Set Function MeasureTheory
open scoped Convolution ENNReal Pointwise Topology Matrix.Norms.Elementwise

noncomputable section

/-- Continuity within the normalized closed Harnack box gives the terminal-face
limit along the interior-time approximation. -/
theorem ContinuousOn.tendsto_localHarnackTerminalApprox
    {d : ℕ} {q : TimeVelocity d → ℝ} {v : PDE.Vec d}
    (hq : ContinuousOn q (parabolicClosedBox 2 2 0 0))
    (hv : v ∈ velocityCube (0 : PDE.Vec d) 1) :
    Tendsto (fun j : ℕ => q (localHarnackTerminalApprox j, v)) atTop
      (_root_.nhds (q (8, v))) := by
  let K : Set (TimeVelocity d) := parabolicClosedBox 2 2 0 0
  let zj : ℕ → TimeVelocity d := fun j => (localHarnackTerminalApprox j, v)
  have hzj : Tendsto zj atTop (_root_.nhds (8, v)) := by
    exact HypoellipticAleksandrov.Parabolic.tendsto_localHarnackTerminalApprox.prodMk_nhds
      (tendsto_const_nhds : Tendsto (fun _ => v) atTop (_root_.nhds v))
  have hzjMem : ∀ j : ℕ, zj j ∈ K := by
    intro j
    have hj := localHarnackTerminalApprox_mem_normalizedOpenBox j hv
    rw [mem_parabolicBox_iff] at hj
    rw [mem_parabolicClosedBox_iff]
    exact ⟨hj.1.le, hj.2.1.le, fun i => (hj.2.2 i).le⟩
  simpa only [Function.comp_def, zj] using
    (hq (8, v) (normalized_terminal_target_mem_normalizedClosedBox hv)).tendsto.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within zj hzj (Eventually.of_forall hzjMem))

end



private def parabolicAffineHomeomorph
    {d : ℕ} (t0 : ℝ) (v0 : PDE.Vec d) (s : ℝ) (hs : 0 < s) :
    TimeVelocity d ≃ₜ TimeVelocity d where
  toEquiv :=
    { toFun := parabolicAffine t0 v0 s
      invFun := fun z ↦ ((z.1 - t0) / s ^ 2, s⁻¹ • (z.2 - v0))
      left_inv := by
        intro z
        apply Prod.ext
        · change (t0 + s ^ 2 * z.1 - t0) / s ^ 2 = z.1
          field_simp [hs.ne']; ring
        · ext i
          change s⁻¹ * (v0 i + s * z.2 i - v0 i) = z.2 i
          field_simp [hs.ne']; ring
      right_inv := by
        rintro ⟨t, v⟩
        apply Prod.ext
        · change t0 + s ^ 2 * ((t - t0) / s ^ 2) = t
          field_simp [hs.ne']; ring
        · ext i
          change v0 i + s * (s⁻¹ * (v i - v0 i)) = v i
          field_simp [hs.ne']; ring }
  continuous_toFun := (contDiff_infty_parabolicAffine t0 v0 s).continuous
  continuous_invFun := by
    fun_prop


private theorem parabolicAffine_image_preimage_eq
    {d : ℕ} {t0 s : ℝ} {v0 : PDE.Vec d} (hs : 0 < s)
    (K : Set (TimeVelocity d)) :
    parabolicAffine t0 v0 s '' (parabolicAffine t0 v0 s ⁻¹' K) = K := by
  change (parabolicAffineHomeomorph t0 v0 s hs : TimeVelocity d → TimeVelocity d) ''
    ((parabolicAffineHomeomorph t0 v0 s hs : TimeVelocity d → TimeVelocity d) ⁻¹' K) = K
  exact Set.image_preimage_eq _ (parabolicAffineHomeomorph t0 v0 s hs).surjective

private theorem normalized_target_velocity
    {d : ℕ} {r : ℝ} {v v0 : PDE.Vec d} (hr : 0 < r)
    (hv : v ∈ velocityCube v0 (r / 2)) :
    (2 / r) • (v - v0) ∈ velocityCube (0 : PDE.Vec d) 1 := by
  intro i
  have hscale : 0 < 2 / r := div_pos (by norm_num) hr
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.zero_apply, smul_eq_mul, sub_zero]
  rw [abs_mul, abs_of_pos hscale]
  calc
    (2 / r) * |v i - v0 i| < (2 / r) * (r / 2) :=
      mul_lt_mul_of_pos_left (hv i) hscale
    _ = 1 := by field_simp [hr.ne']

private theorem physical_target_from_normalized_velocity
    {d : ℕ} {r : ℝ} {v v0 : PDE.Vec d} (hr : 0 < r) :
    v0 + (r / 2) • ((2 / r) • (v - v0)) = v := by
  ext i
  change v0 i + (r / 2) * ((2 / r) * (v i - v0 i)) = v i
  field_simp [hr.ne']
  ring








/-- A fixed number of links reaches every upper point without crossing the terminal time. -/
theorem unitCylinder_harnack_link_geometry
    (d : ℕ) (hd : 1 ≤ d) (P P' : TimeVelocity d)
    (hP : P ∈ Ioo (1 / 4 : ℝ) (1 / 2 : ℝ) ×ˢ
      PDE.euclideanBall (0 : PDE.Vec d) (1 / 2 : ℝ))
    (hP' : P' ∈ Ioo (3 / 4 : ℝ) 1 ×ˢ
      PDE.euclideanBall (0 : PDE.Vec d) (1 / 2 : ℝ)) :
    let m : ℕ := 256 * d
    let dt : ℝ := (P'.1 - P.1) / (m : ℝ)
    let r : ℝ := Real.sqrt dt
    let t : ℕ → ℝ := fun k => P.1 + (k : ℝ) * dt
    let v : ℕ → PDE.Vec d := fun k =>
      P.2 + ((k : ℝ) / (m : ℝ)) • (P'.2 - P.2)
    0 < m ∧ 0 < r ∧ (t 0, v 0) = P ∧ (t m, v m) = P' ∧
    (∀ k < m, t (k + 1) = t k + r ^ 2) ∧
    (∀ k < m, parabolicClosedBox 2 r (t k - r ^ 2) (v k) ⊆
      Ioo (0 : ℝ) 1 ×ˢ PDE.euclideanBall (0 : PDE.Vec d) 1) ∧
    (∀ k < m, v (k + 1) ∈ velocityCube (v k) (r / 2))    := by
  have normSq_lt_quarter_of_mem_halfBall {d : ℕ} {w : PDE.Vec d} (hw : w ∈ PDE.euclideanBall 0 (1 / 2 : ℝ)) :
      PDE.vecNormSq w < 1 / 4 := by
    norm_num [PDE.euclideanBall, PDE.euclideanSqDist] at hw ⊢
    exact hw
  have vecNormSq_sub_le_natCast_mul_sq_of_mem_velocityClosedCube {v : PDE.Vec d} {v0 : PDE.Vec d} {r : ℝ} (hv : v ∈ velocityClosedCube v0 r) :
      PDE.vecNormSq (v - v0) ≤ (d : ℝ) * r ^ 2 := by
    rw [PDE.vecNormSq_eq_sum_sq]
    calc
      ∑ i, (v - v0) i ^ 2 ≤ ∑ _i : Fin d, r ^ 2 := by
        apply Finset.sum_le_sum
        intro i _hi
        have hr := le_trans (abs_nonneg (v i - v0 i)) (hv i)
        simpa using (sq_le_sq₀ (abs_nonneg (v i - v0 i)) hr).mpr (hv i)
      _ = (d : ℝ) * r ^ 2 := by simp [nsmul_eq_mul]
  have coordinate_lt_half_of_mem_halfBall {d : ℕ} {w : PDE.Vec d} (hw : w ∈ PDE.euclideanBall 0 (1 / 2 : ℝ)) (i : Fin d) :
      |w i| < 1 / 2 := by
    have hs := (PDE.sq_apply_le_vecNormSq w i).trans_lt
      (normSq_lt_quarter_of_mem_halfBall hw)
    apply abs_lt_of_sq_lt_sq (by nlinarith [hs]) (by norm_num)
  let m : ℕ := 256 * d
  let dt : ℝ := (P'.1 - P.1) / (m : ℝ)
  let r : ℝ := Real.sqrt dt
  let t : ℕ → ℝ := fun k => P.1 + (k : ℝ) * dt
  let v : ℕ → PDE.Vec d := fun k =>
    P.2 + ((k : ℝ) / (m : ℝ)) • (P'.2 - P.2)
  change 0 < m ∧ 0 < r ∧ (t 0, v 0) = P ∧ (t m, v m) = P' ∧ _
  have hdreal : 1 ≤ (d : ℝ) := by exact_mod_cast hd
  have hm : 256 ≤ m := by dsimp [m]; omega
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast lt_of_lt_of_le (by decide : 0 < 256) hm
  have hmreal : 256 ≤ (m : ℝ) := by exact_mod_cast hm
  have hmd : (m : ℝ) = 256 * (d : ℝ) := by simp [m]
  have hgap0 : 1 / 4 < P'.1 - P.1 := by linarith [hP.1.2, hP'.1.1]
  have hgap1 : P'.1 - P.1 < 1 := by linarith [hP.1.1, hP'.1.2]
  have hdt : 0 < dt := div_pos (by linarith) hmpos
  have hmul : (m : ℝ) * dt = P'.1 - P.1 := by
    dsimp [dt]
    field_simp
  have hrsq : r ^ 2 = dt := Real.sq_sqrt hdt.le
  have hr := Real.sqrt_pos.mpr hdt
  have hdtSmall : dt < 1 / 256 := by nlinarith
  have hdSmall : (d : ℝ) * dt < 1 / 256 := by rw [hmd] at hmul; nlinarith
  have htstep : ∀ k : ℕ, t (k + 1) = t k + r ^ 2 := by
    intro k
    simp only [t, Nat.cast_add, Nat.cast_one, hrsq]
    ring
  have hvstep : ∀ k : ℕ, v (k + 1) - v k = (1 / (m : ℝ)) • (P'.2 - P.2) := by
    intro k
    ext i
    simp [v, Nat.cast_add, Nat.cast_one]
    ring
  have hcenter : ∀ k ≤ m,
      v k ∈ PDE.euclideanBall 0 (1 / 2 : ℝ) := by
    intro k hk
    have hkreal : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hk
    have ha : 0 ≤ (k : ℝ) / (m : ℝ) := div_nonneg (Nat.cast_nonneg _) hmpos.le
    have hb := (div_le_one₀ hmpos).mpr hkreal
    convert (PDE.convex_euclideanBall 0 (1 / 2 : ℝ)) hP.2 hP'.2 (by linarith : 0 ≤ 1 - (k : ℝ) / (m : ℝ)) ha (by ring : (1 - (k : ℝ) / (m : ℝ)) + (k : ℝ) / (m : ℝ) = 1) using 1
    ext i
    simp [v]
    ring
  have hrecip : 1 / (m : ℝ) < r / 2 := by
    have hsquare : ((m : ℝ) * r) ^ 2 = (m : ℝ) * (P'.1 - P.1) := by
      calc
        ((m : ℝ) * r) ^ 2 = (m : ℝ) * ((m : ℝ) * dt) := by rw [mul_pow, hrsq]; ring
        _ = _ := by rw [hmul]
    have hlarge : 2 < (m : ℝ) * r := by
      nlinarith
    apply (div_lt_iff₀ hmpos).mpr
    nlinarith
  refine ⟨by omega, hr, ?_, ?_, fun k _ => htstep k, ?_, ?_⟩
  · simp [t, v]
  · apply Prod.ext
    · dsimp [t]
      linarith
    · simp [v, div_self hmpos.ne', one_smul]
  · intro k hk w hw
    rcases w with ⟨s, w⟩
    rw [mem_parabolicClosedBox_iff] at hw
    have hkreal : (k : ℝ) ≤ (m : ℝ) - 1 := by
      have hs : ((k + 1 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hk
      push_cast at hs
      linarith
    have htk0 : P.1 ≤ t k := by
      dsimp [t]
      exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hdt.le)
    have htk1 : t k + dt ≤ P'.1 := by
      dsimp [t]
      nlinarith
    have hnorm := normSq_lt_quarter_of_mem_halfBall (hcenter k (Nat.le_of_lt hk))
    have hdisp := vecNormSq_sub_le_natCast_mul_sq_of_mem_velocityClosedCube hw.2.2
    rw [hrsq] at hdisp
    have hsum := PDE.vecNormSq_add_le (v k) (w - v k)
    rw [add_sub_cancel] at hsum
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [hrsq] at hw
      linarith [hP.1.1, hw.1]
    · rw [hrsq] at hw
      linarith [hP'.1.2, hw.2.1]
    · change PDE.euclideanSqDist w 0 < 1 ^ 2
      simpa [PDE.euclideanSqDist] using (show PDE.vecNormSq w < 1 by nlinarith)
  · intro k _ i
    have hcoord0 := coordinate_lt_half_of_mem_halfBall hP.2 i
    have hcoord1 := coordinate_lt_half_of_mem_halfBall hP'.2 i
    have hcoord : |P'.2 i - P.2 i| < 1 := by
      have hab := abs_sub_le (P'.2 i) 0 (P.2 i)
      simp at hab
      linarith
    have hstepi := congrFun (hvstep k) i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hstepi
    rw [hstepi, abs_mul, abs_of_pos (one_div_pos.mpr hmpos)]
    calc
      (1 / (m : ℝ)) * |P'.2 i - P.2 i| < (1 / (m : ℝ)) * 1 :=
        mul_lt_mul_of_pos_left hcoord (one_div_pos.mpr hmpos)
      _ = 1 / (m : ℝ) := mul_one _
      _ < r / 2 := hrecip



/-- Eventually, every point sampled by the translated right mollifier at a
compact carrier lies in the surrounding open set. -/
theorem eventually_translated_parabolicMollifier_support_subset
    (d : Nat) (K U : Set (TimeVelocity d))
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∀ᶠ n in Filter.atTop, ∀ z ∈ K,
      {y | parabolicMollifier d n (z - y) ≠ 0} ⊆ U  := by
  have exists_native_kernel_collar :
      ∃ delta : Real, 0 < delta ∧ Metric.cthickening delta K ⊆ U ∧
      ∀ᶠ n in Filter.atTop, parabolicMollifierScale n < delta := by
    obtain ⟨delta, hdelta_pos, hdeltaU⟩ := hK.exists_cthickening_subset_open hU hKU
    refine ⟨delta, hdelta_pos, hdeltaU, ?_⟩
    exact tendsto_parabolicMollifierScale_zero.eventually_lt_const hdelta_pos
  obtain ⟨delta, hdelta_pos, hdeltaU, hscale⟩ :=
    exists_native_kernel_collar
  filter_upwards [hscale] with n hn
  intro z hz y hy
  apply hdeltaU
  apply Metric.mem_cthickening_of_dist_le y z delta K hz
  have hySupport : z - y ∈ Function.support (parabolicMollifier d n) := hy
  rw [support_parabolicMollifier] at hySupport
  have hdist : dist y z < parabolicMollifierScale n := by
    rw [Metric.mem_ball] at hySupport
    simpa [dist_eq_norm, norm_sub_rev] using hySupport
  exact (hdist.trans hn).le






/-- Every nonnegative C¹,² solution satisfies the unit-cylinder Harnack comparison. -/
theorem parabolic_harnack_unit_cylinder_aux
    (N : ℕ) (hN : 1 ≤ N) (lam : ℝ) (hlam : 0 < lam)
    (Lam : ℝ) (hlamLam : lam ≤ Lam) :
    ∃ h : ℝ, 0 < h ∧
      ∀ (B : CoefficientField N) (u : TimeVelocity N → ℝ),
        IsContinuousCoefficientOn B
          (Set.Ioo (0 : ℝ) 1 ×ˢ PDE.euclideanBall (0 : PDE.Vec N) 1) →
        (∀ z ∈ Set.Ioo (0 : ℝ) 1 ×ˢ PDE.euclideanBall (0 : PDE.Vec N) 1,
          (coefficientAt B z).IsSymm) →
        HasLowerEllipticityOn lam B
          (Set.Ioo (0 : ℝ) 1 ×ˢ PDE.euclideanBall (0 : PDE.Vec N) 1) →
        HasUpperEllipticityOn Lam B
          (Set.Ioo (0 : ℝ) 1 ×ˢ PDE.euclideanBall (0 : PDE.Vec N) 1) →
        IsScalarC12On u
          (Set.Ioo (0 : ℝ) 1 ×ˢ PDE.euclideanBall (0 : PDE.Vec N) 1) →
        IsNonnegativeOn u
          (Set.Ioo (0 : ℝ) 1 ×ˢ PDE.euclideanBall (0 : PDE.Vec N) 1) →
        (∀ z ∈ Set.Ioo (0 : ℝ) 1 ×ˢ PDE.euclideanBall (0 : PDE.Vec N) 1,
          scalarTimeDerivative u z =
            matrixContraction (coefficientAt B z) (scalarSpatialHessian u z)) →
        ∀ P ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2 : ℝ) ×ˢ
            PDE.euclideanBall (0 : PDE.Vec N) (1 / 2 : ℝ),
          ∀ P' ∈ Set.Ioo (3 / 4 : ℝ) 1 ×ˢ
              PDE.euclideanBall (0 : PDE.Vec N) (1 / 2 : ℝ),
            h * u P ≤ u P'     := by
  have exists_source_local_parabolic_harnack :
      ∃ hBox C : Real, 0 < hBox ∧ hBox <= 1 ∧ 0 < C ∧
      ∀ (K U : Set (TimeVelocity N)) (B : CoefficientField N)
        (q F : TimeVelocity N -> Real) (t0 : Real) (v0 : PDE.Vec N) (r : Real),
        0 < r -> IsCompact K -> K ⊆ U -> IsOpen U ->
        parabolicClosedBox 2 r (t0 - r ^ 2) v0 ⊆ K ->
        IsContinuousCoefficientOn B U -> ContDiffOn Real 2 q U ->
        ContinuousOn F U -> IsNonnegativeOn q K ->
        HasLowerEllipticityOn lam B K -> HasUpperEllipticityOn Lam B K ->
        (∀ x ∈ K, parabolicOperator B q x = F x) ->
        ∀ v : PDE.Vec N, v ∈ velocityCube v0 (r / 2) ->
          hBox * q (t0, v0) <= q (t0 + r ^ 2, v) +
            C * r ^ ((N : Real) / ((N : Real) + 1)) *
              parabolicLpNormOn N F K := by
    have isCompact_parabolicAffine_preimage {t0 : ℝ} {s : ℝ} {v0 : PDE.Vec N} (hs : 0 < s) {K : Set (TimeVelocity N)} (hK : IsCompact K) :
        IsCompact (parabolicAffine t0 v0 s ⁻¹' K) := by
      change IsCompact ((parabolicAffineHomeomorph t0 v0 s hs) ⁻¹' K)
      exact (parabolicAffineHomeomorph t0 v0 s hs).isCompact_preimage.mpr hK
    have exists_source_local_parabolic_harnack_nonnegative :
        ∃ hBox C : Real, 0 < hBox ∧ hBox ≤ 1 ∧ 0 < C ∧
        ∀ (K U : Set (TimeVelocity N)) (B : CoefficientField N)
          (q F : TimeVelocity N → Real),
          IsCompact K → K ⊆ U → IsOpen U →
          parabolicClosedBox 2 2 0 0 ⊆ K →
          IsContinuousCoefficientOn B U → ContDiffOn Real 2 q U →
          ContinuousOn F U → IsNonnegativeOn q K →
          HasLowerEllipticityOn lam B K → HasUpperEllipticityOn Lam B K →
          (∀ x ∈ K, parabolicOperator B q x = F x) →
          ∀ v : PDE.Vec N, v ∈ velocityCube 0 1 →
            hBox * q (4, 0) ≤
              q (8, v) + C * parabolicLpNormOn N F K := open Filter in by
      obtain ⟨hBox, C, hhBox0, hhBox1, hC, hpositive⟩ :=
        exists_source_local_parabolic_harnack_positive N hN lam hlam Lam hlamLam
      refine ⟨hBox, C, hhBox0, hhBox1, hC, ?_⟩
      intro K U B q F hK hKU hU hbox hB hq hF hnonneg hlower hupper heq v hv
      have hsource : (4, (0 : PDE.Vec N)) ∈ parabolicClosedBox 2 2 0 0 := by
        rw [mem_parabolicClosedBox_iff]
        refine ⟨by norm_num, by norm_num, ?_⟩
        intro i
        norm_num
      apply le_of_forall_pos_le_add
      intro eps heps
      have hlimitEps : hBox * (q (4, 0) + eps) ≤
          q (8, v) + eps + C * parabolicLpNormOn N F K := by
        exact le_of_tendsto_of_tendsto'
          (tendsto_const_nhds : Tendsto
            (fun _ => hBox * (q (4, 0) + eps)) atTop
            (_root_.nhds (hBox * (q (4, 0) + eps))))
          (((ContinuousOn.tendsto_localHarnackTerminalApprox (hq.continuousOn.mono (hbox.trans hKU)) hv).add
            (tendsto_const_nhds : Tendsto (fun _ => eps) atTop (_root_.nhds eps))).add
            (tendsto_const_nhds : Tendsto
              (fun _ => C * parabolicLpNormOn N F K) atTop
              (_root_.nhds (C * parabolicLpNormOn N F K))))
          (fun j => hpositive K U B (fun z => q z + eps) F hK hKU hU hbox hB
            (hq.add contDiffOn_const) hF
            (fun z hz => add_nonneg (hnonneg z hz) heps.le) hlower hupper
            (fun z hz => by rw [parabolicOperator_add_const, heq z hz]) (add_pos_of_nonneg_of_pos (hnonneg _ (hbox hsource)) heps) j v hv)
      calc
        hBox * q (4, 0) ≤ hBox * (q (4, 0) + eps) := by
          gcongr
          linarith
        _ ≤ q (8, v) + C * parabolicLpNormOn N F K + eps := by
          linarith
    obtain ⟨hBox, C, hhBox0, hhBox1, hC, hnormalized⟩ :=
      exists_source_local_parabolic_harnack_nonnegative
    refine ⟨hBox, C, hhBox0, hhBox1, hC, ?_⟩
    intro K U B q F t0 v0 r hr hK hKU hU hbox hB hq hF hnonneg hlower hupper heq v hv
    let s : ℝ := r / 2
    let a := parabolicAffine (t0 - r ^ 2) v0 s
    let KHat := a ⁻¹' K
    let UHat := a ⁻¹' U
    let BHat := pullbackCoefficient B (t0 - r ^ 2) v0 s
    let qHat := pullbackScalar q (t0 - r ^ 2) v0 s
    let FHat : TimeVelocity N → ℝ := fun z ↦ s ^ 2 * F (a z)
    have hs : 0 < s := by
      dsimp [s]
      linarith
    have hmapK : MapsTo a KHat K := mapsTo_preimage _ _
    have hmapU : MapsTo a UHat U := mapsTo_preimage _ _
    have hKHat : IsCompact KHat := by
      dsimp [KHat, a]
      exact isCompact_parabolicAffine_preimage hs hK
    have hUHat : IsOpen UHat := by
      dsimp [UHat, a]
      exact hU.preimage (contDiff_infty_parabolicAffine (t0 - r ^ 2) v0 s).continuous
    have hboxHat : parabolicClosedBox 2 2 0 0 ⊆ KHat := by
      intro z hz
      change a z ∈ K
      apply hbox
      have hz' : z ∈ parabolicAffine (t0 - r ^ 2) v0 (r / 2) ⁻¹'
          parabolicClosedBox 2 r (t0 - r ^ 2) v0 := by
        rw [parabolicAffine_preimage_localHarnackClosedBox hr]
        exact hz
      simpa [s] using hz'
    have hBHat : IsContinuousCoefficientOn BHat UHat := by
      exact hB.pullback hmapU
    have hqHat : ContDiffOn ℝ 2 qHat UHat := by
      exact ContDiffOn.pullbackScalar hq hmapU
    have hFHat : ContinuousOn FHat UHat := by
      exact continuousOn_const.mul
        (hF.comp (contDiff_infty_parabolicAffine (t0 - r ^ 2) v0 s).continuous.continuousOn hmapU)
    have hnonnegHat : IsNonnegativeOn qHat KHat := by
      exact hnonneg.pullbackScalar hmapK
    have hlowerHat : HasLowerEllipticityOn lam BHat KHat := by
      exact hlower.pullback hmapK
    have hupperHat : HasUpperEllipticityOn Lam BHat KHat := by
      exact hupper.pullback hmapK
    have heqHat : ∀ z ∈ KHat, parabolicOperator BHat qHat z = FHat z := by
      intro z hz
      have hzU : z ∈ UHat := by
        change a z ∈ U
        exact hKU (hmapK hz)
      rw [parabolicOperator_pullbackScalar
        (contDiffAt_of_contDiffOn_of_isOpen hU hq (hmapU hzU))]
      change s ^ 2 * parabolicOperator B q (a z) = s ^ 2 * F (a z)
      rw [heq (a z) (hmapK hz)]
    let w : PDE.Vec N := (2 / r) • (v - v0)
    have hw : w ∈ velocityCube 0 1 := by
      exact normalized_target_velocity hr hv
    have hphysical : v0 + (r / 2) • w = v := by
      exact physical_target_from_normalized_velocity hr
    have hKHatUHat : KHat ⊆ UHat := by
      exact Set.preimage_mono hKU
    have hsource : qHat (4, 0) = q (t0, v0) := by
      dsimp [qHat, s]
      rw [parabolicAffine_localHarnack_source]
    have hterminal : qHat (8, w) = q (t0 + r ^ 2, v) := by
      dsimp [qHat, s]
      rw [parabolicAffine_localHarnack_terminal, hphysical]
    have hnorm : parabolicLpNormOn N FHat KHat =
        s ^ ((N : Real) / ((N : Real) + 1)) * parabolicLpNormOn N F K := by
      rw [parabolicLpNormOn_pullback (t0 - r ^ 2) v0 hs F KHat]
      rw [show parabolicAffine (t0 - r ^ 2) v0 s '' KHat = K by
        dsimp [KHat, a]
        exact parabolicAffine_image_preimage_eq hs K]
    let p : ℝ := (N : Real) / ((N : Real) + 1)
    have hp : 0 ≤ p := by
      dsimp [p]
      positivity
    have hscale : s ^ p ≤ r ^ p := by
      exact Real.rpow_le_rpow hs.le (by dsimp [s]; linarith) hp
    have hnormnonneg : 0 ≤ parabolicLpNormOn N F K := ENNReal.toReal_nonneg
    have herror : C * (s ^ p * parabolicLpNormOn N F K) ≤
        C * r ^ p * parabolicLpNormOn N F K := by
      calc
        C * (s ^ p * parabolicLpNormOn N F K) =
            C * s ^ p * parabolicLpNormOn N F K := by ring
        _ ≤ C * r ^ p * parabolicLpNormOn N F K := by
          gcongr
    calc
      hBox * q (t0, v0) = hBox * qHat (4, 0) := by rw [hsource]
      _ ≤ qHat (8, w) + C * parabolicLpNormOn N FHat KHat := (hnormalized KHat UHat BHat qHat FHat hKHat hKHatUHat hUHat hboxHat hBHat hqHat hFHat hnonnegHat hlowerHat hupperHat heqHat w hw)
      _ = q (t0 + r ^ 2, v) + C * (s ^ p * parabolicLpNormOn N F K) := by
        rw [hterminal, hnorm]
      _ ≤ q (t0 + r ^ 2, v) + C * r ^ p * parabolicLpNormOn N F K := by
        linarith
  have exists_bound_parabolicConvolution {d : ℕ} {f : TimeVelocity d → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) :
      ∃ M : ℝ, 0 ≤ M ∧ ∀ n z, |parabolicConvolution f (parabolicMollifier d n) z| ≤ M := by
    obtain ⟨M₀, hM₀⟩ := hfc.exists_bound_of_continuous hf
    let M := max M₀ 0
    refine ⟨M, le_max_right _ _, fun n z => ?_⟩
    have hint_rho : Integrable (fun y => parabolicMollifier d n (z - y)) volume :=
      ((contDiff_parabolicMollifier d n).continuous.integrable_of_hasCompactSupport
        (hasCompactSupport_parabolicMollifier d n)).comp_sub_left z
    calc |∫ y, f y * parabolicMollifier d n (z - y)|
      _ ≤ ∫ y, |f y * parabolicMollifier d n (z - y)| := abs_integral_le_integral_abs
      _ ≤ ∫ y, M * parabolicMollifier d n (z - y) := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
            (hint_rho.const_mul M) (Eventually.of_forall fun y => ?_)
          dsimp only
          rw [abs_mul, abs_of_nonneg (parabolicMollifier_nonneg d n _)]
          exact mul_le_mul_of_nonneg_right
            ((Real.norm_eq_abs _ ▸ hM₀ y).trans (le_max_left _ _))
            (parabolicMollifier_nonneg d n _)
      _ = M * ∫ y, parabolicMollifier d n (z - y) := integral_const_mul _ _
      _ = M := by
          rw [integral_sub_left_eq_self (parabolicMollifier d n) volume z,
            integral_parabolicMollifier, mul_one]
  have tendsto_parabolicConvolution_of_continuous {d : ℕ} {f : TimeVelocity d → ℝ} (hf : Continuous f) (z : TimeVelocity d) :
      Tendsto (fun n => parabolicConvolution f (parabolicMollifier d n) z) atTop (nhds (f z)) := by
    have : Measure.IsAddHaarMeasure (volume : Measure (TimeVelocity d)) :=
      Measure.prod.instIsAddHaarMeasure _ _
    have heq : ∀ n, parabolicConvolution f (parabolicMollifier d n) z =
        ((parabolicMollifierBump d n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) z := by
      intro n
      rw [← convolution_flip]
      simp only [parabolicConvolution, parabolicMollifier, convolution_def]
      exact integral_congr_ae (Eventually.of_forall fun _ => mul_comm _ _)
    simpa only [heq] using
      ContDiffBump.convolution_tendsto_right_of_continuous tendsto_parabolicMollifierScale_zero hf z
  have continuous_parabolicOperator_on {d : ℕ} {U : Set (TimeVelocity d)} {B : CoefficientField d} {q : TimeVelocity d → ℝ} (hB : IsContinuousCoefficientOn B U) (hq : ContDiff ℝ (⊤ : ℕ∞) q) :
      ContinuousOn (fun z => parabolicOperator B q z) U := by
    change ContinuousOn (fun x =>
      timeDerivative q x - matrixContraction (coefficientAt B x) (velocityHessian q x)) U
    refine ContinuousOn.sub ?_ ?_
    · unfold timeDerivative
      exact (((hq.contDiff_fderiv_apply (m := 0) (by norm_num)).comp
        (contDiff_id.prodMk contDiff_const)).continuous).continuousOn
    · unfold matrixContraction
      refine continuousOn_finsetSum Finset.univ fun i _ =>
        continuousOn_finsetSum Finset.univ fun j _ => ContinuousOn.mul ?_ ?_
      · exact ((continuous_apply j).comp ((continuous_apply i))).comp_continuousOn hB
      · unfold velocityHessian
        have hfirst : ContDiff ℝ 1 (fderiv ℝ q) :=
          hq.fderiv_right (m := 1) (WithTop.coe_le_coe.mpr le_top)
        exact (((hfirst.continuous_fderiv (by norm_num)).clm_apply
          continuous_const |>.clm_apply continuous_const)).continuousOn
  obtain ⟨hBox, C, hh0, _hh1, _hC, hsource⟩ :=
    exists_source_local_parabolic_harnack
  refine ⟨hBox ^ (256 * N), pow_pos hh0 _, ?_⟩
  intro B u hB _hSymm hLower hUpper hu huNonneg heq P hP P' hP'
  let U := Ioo (0 : ℝ) 1 ×ˢ PDE.euclideanBall (0 : PDE.Vec N) 1
  have hU : IsOpen U := isOpen_Ioo.prod (PDE.isOpen_euclideanBall _ _)
  have hlocal : ∀ (t0 : ℝ) (v0 : PDE.Vec N) (r : ℝ), 0 < r →
      parabolicClosedBox 2 r (t0 - r ^ 2) v0 ⊆ U →
      ∀ v ∈ velocityCube v0 (r / 2), hBox * u (t0, v0) ≤ u (t0 + r ^ 2, v) := by
    intro t0 v0 r hr hKU v hv
    let K := parabolicClosedBox 2 r (t0 - r ^ 2) v0
    have hK : IsCompact K := isCompact_parabolicClosedBox _ _ _ _
    let : IsFiniteMeasure (volume.restrict K) := ⟨by
      rw [Measure.restrict_apply_univ]
      exact hK.measure_lt_top⟩
    obtain ⟨V, hV, hKV, hVU, hVCompact⟩ := exists_open_between_and_isCompact_closure hK hU hKU
    have hsub : V ⊆ U := subset_closure.trans hVU
    have hlocalC12 : IsScalarC12On u V :=
      ⟨hu.1.mono hsub, fun z hz => hu.2.1 z (hsub hz), fun z hz => hu.2.2.1 z (hsub hz),
        hu.2.2.2.1.mono hsub, hu.2.2.2.2.1.mono hsub, hu.2.2.2.2.2.mono hsub⟩
    let w : ParabolicW12Function N V (parabolicExponent N) :=
      { toFun := u
        timeDeriv := scalarTimeDerivative u
        velocityGrad := scalarSpatialGradient u
        velocityHessian := scalarSpatialHessian u
        memLp := memLp_on_of_continuousOn_compact_closure hu.continuousOn hV hVCompact hVU _
        timeDeriv_memLp := memLp_on_of_continuousOn_compact_closure
          hu.continuousOn_scalarTimeDerivative hV hVCompact hVU _
        velocityGrad_memLp := fun i => memLp_on_of_continuousOn_compact_closure
          ((continuous_apply i).comp_continuousOn hu.continuousOn_scalarSpatialGradient)
          hV hVCompact hVU _
        velocityHessian_memLp := fun i j => memLp_on_of_continuousOn_compact_closure
          ((continuous_apply j).comp_continuousOn
            ((continuous_apply i).comp_continuousOn hu.continuousOn_scalarSpatialHessian))
          hV hVCompact hVU _
        hasWeakTimeDeriv := IsScalarC12On.hasWeakTimeDerivOn hV hlocalC12
        hasWeakVelocityPartialDeriv := IsScalarC12On.hasWeakVelocityPartialDerivOn hV hlocalC12
        hasWeakVelocitySecondPartialDeriv :=
          IsScalarC12On.hasWeakVelocitySecondPartialDerivOn hV hlocalC12 }
    have hp : 1 ≤ parabolicExponent N := by simp [parabolicExponent]
    obtain ⟨b, hb, hbCompact, _hbOne, hbV, hvalEq, hdtEq, _, hhessEq⟩ :=
      exists_smooth_compact_cutoff_mul_eventuallyEq_jet hK hV hVCompact hKV w hp
    let G := w.mulContDiffHasCompactSupport_univ hp hb hbCompact hV hbV
    have hbU : tsupport b ⊆ U := hbV.trans hsub
    have hcont_supp {f : TimeVelocity N → ℝ} (hf : ContinuousOn f U)
        (hsupp : tsupport f ⊆ tsupport b) : Continuous f ∧ HasCompactSupport f := by
      refine ⟨continuous_iff_continuousAt.mpr fun z => ?_,
        HasCompactSupport.of_support_subset_isCompact hbCompact
          ((subset_tsupport f).trans hsupp)⟩
      by_cases hz : z ∈ U
      · exact hf.continuousAt (hU.mem_nhds hz)
      · exact continuousAt_const.congr ((notMem_tsupport_iff_eventuallyEq.mp
          fun hzf => hz (hbU (hsupp hzf))).symm)
    obtain ⟨hGval_cont, _⟩ := hcont_supp (f := G.toFun)
      (hb.continuous.continuousOn.mul hu.continuousOn) tsupport_mul_subset_left
    obtain ⟨hGdt_cont, hGdt_comp⟩ := hcont_supp (f := G.timeDeriv)
      ((hb.continuous.continuousOn.mul hu.continuousOn_scalarTimeDerivative).add
        (hu.continuousOn.mul
          (((hb.continuous_fderiv (by simp)).clm_apply continuous_const).continuousOn)))
      (tsupport_mul_timeDeriv_subset b u (scalarTimeDerivative u))
    have hGhess_cb (i j : Fin N) :
        Continuous (fun z => G.velocityHessian z i j) ∧
          HasCompactSupport (fun z => G.velocityHessian z i j) := by
      refine hcont_supp ?_
        (tsupport_mul_velocityHessian_subset (i := i) (j := j) b u
          (fun z => scalarSpatialGradient u z i) (fun z => scalarSpatialGradient u z j)
          (fun z => scalarSpatialHessian u z i j))
      have hb_grad (k : Fin N) : Continuous (fun z => velocityGradient b z k) :=
        (hb.continuous_fderiv (by simp)).clm_apply continuous_const
      have hb_hess : Continuous (fun z => velocityHessian b z i j) := by
        have h1 : ContDiff ℝ 1 (fderiv ℝ b) :=
          hb.fderiv_right (m := 1) (WithTop.coe_le_coe.mpr le_top)
        exact (h1.continuous_fderiv (by norm_num)).clm_apply
          continuous_const |>.clm_apply continuous_const
      exact (((hb.continuous.continuousOn.mul
        ((continuous_apply j).comp_continuousOn
          ((continuous_apply i).comp_continuousOn hu.continuousOn_scalarSpatialHessian))).add
        ((hb_grad j).continuousOn.mul
          ((continuous_apply i).comp_continuousOn hu.continuousOn_scalarSpatialGradient))).add
        (((continuous_apply j).comp_continuousOn hu.continuousOn_scalarSpatialGradient).mul
          (hb_grad i).continuousOn)).add
        (hu.continuousOn.mul hb_hess.continuousOn)
    let q : ℕ → TimeVelocity N → ℝ := fun n =>
      parabolicConvolution G.toFun (parabolicMollifier N n)
    let F : ℕ → TimeVelocity N → ℝ := fun n z => parabolicOperator B (q n) z
    have hq_smooth (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (q n) :=
      G.contDiff_convolution hp _ (contDiff_parabolicMollifier N n)
        (hasCompactSupport_parabolicMollifier N n)
    have hdt_q (n : ℕ) : timeDerivative (q n) =
        parabolicConvolution G.timeDeriv (parabolicMollifier N n) :=
      G.timeDerivative_convolution hp _ (contDiff_parabolicMollifier N n)
        (hasCompactSupport_parabolicMollifier N n)
    have hhess_q (n : ℕ) (i j : Fin N) :
        (fun z => velocityHessian (q n) z i j) =
          parabolicConvolution (fun y => G.velocityHessian y i j) (parabolicMollifier N n) :=
      G.velocityHessian_convolution hp _ (contDiff_parabolicMollifier N n)
        (hasCompactSupport_parabolicMollifier N n) i j
    obtain ⟨O, hOOpen, hKO, hvalO⟩ := eventually_nhdsSet_iff_exists.mp hvalEq
    have hq_nonneg : ∀ᶠ n in atTop, IsNonnegativeOn (q n) K := by
      filter_upwards [eventually_translated_parabolicMollifier_support_subset
        N K (O ∩ U) hK (hOOpen.inter hU) (subset_inter hKO hKU)] with n hn z hz
      refine integral_nonneg fun y => ?_
      by_cases hy : parabolicMollifier N n (z - y) = 0
      · simp [hy]
      · have hyOU := hn z hz hy
        have hgy : G.toFun y = u y := hvalO y hyOU.1
        exact mul_nonneg (hgy ▸ huNonneg y hyOU.2) (parabolicMollifier_nonneg N n _)
    have hF_pt : ∀ z ∈ K, Tendsto (fun n => F n z) atTop (nhds 0) := by
      intro z hz
      have htz : G.timeDeriv z = scalarTimeDerivative u z :=
        (subset_of_mem_nhdsSet hdtEq) hz
      have hhz (i j : Fin N) : G.velocityHessian z i j = scalarSpatialHessian u z i j :=
        congrFun (congrFun ((subset_of_mem_nhdsSet hhessEq) hz) i) j
      have hlim_t : Tendsto (fun n => timeDerivative (q n) z) atTop
          (nhds (scalarTimeDerivative u z)) := by
        rw [← htz]
        exact (tendsto_parabolicConvolution_of_continuous hGdt_cont z).congr fun n =>
          (congrFun (hdt_q n) z).symm
      have hlim_h : Tendsto (fun n => matrixContraction (coefficientAt B z)
          (velocityHessian (q n) z)) atTop
          (nhds (matrixContraction (coefficientAt B z) (scalarSpatialHessian u z))) := by
        unfold matrixContraction
        refine tendsto_finsetSum Finset.univ fun i _ =>
          tendsto_finsetSum Finset.univ fun j _ => tendsto_const_nhds.mul ?_
        rw [← hhz i j]
        exact (tendsto_parabolicConvolution_of_continuous (hGhess_cb i j).1 z).congr fun n =>
          (congrFun (hhess_q n i j) z).symm
      simpa [F, parabolicOperator, heq z (hKU hz)] using hlim_t.sub hlim_h
    obtain ⟨Mt, hMt0, hMt⟩ := exists_bound_parabolicConvolution hGdt_cont hGdt_comp
    choose Mh hMh0 hMh using fun i j =>
      exists_bound_parabolicConvolution (hGhess_cb i j).1 (hGhess_cb i j).2
    let BF : ℝ := Mt + ∑ i : Fin N, ∑ j : Fin N, Lam * Mh i j
    have hLam0 : 0 ≤ Lam := hlam.le.trans hlamLam
    have hBF0 : 0 ≤ BF := add_nonneg hMt0
      (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_nonneg hLam0 (hMh0 i j))
    have hF_norm : Tendsto (fun n => parabolicLpNormOn N (F n) K) atTop (nhds 0) := by
      have hp_eq : ENNReal.ofReal ((N : ℝ) + 1) = parabolicExponent N := by
        rw [ENNReal.ofReal_add (Nat.cast_nonneg N) zero_le_one,
          ENNReal.ofReal_natCast, ENNReal.ofReal_one]
        rfl
      have hconv := HypoellipticAleksandrov.KineticAleksandrov.borel_bounded_error_norm_tendsto
        (volume.restrict K) (p := (N : ℝ) + 1) (B := BF) (by positivity) hBF0
        (fun n z => |F n z|)
        (fun n => (((continuous_parabolicOperator_on hB (hq_smooth n)).mono
          hKU).abs).aestronglyMeasurable hK.measurableSet)
        (fun _ => Eventually.of_forall fun _ => abs_nonneg _)
        (fun n => by
          filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
          refine ((abs_sub _ _).trans (add_le_add ?_ ?_)).trans_eq rfl
          · rw [hdt_q n]
            exact hMt n z
          · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ =>
              (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_))
            rw [abs_mul, congrFun (hhess_q n i j) z]
            exact mul_le_mul
              (HypoellipticAleksandrov.abs_apply_le_of_loewner hlam
                (hLower z (hKU hz)) (hUpper z (hKU hz)) i j)
              (hMh i j n z) (abs_nonneg _) hLam0)
        (by
          filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
          simpa using (hF_pt z hz).abs)
      refine hconv.congr fun n => ?_
      unfold parabolicLpNormOn parabolicELpNormOn
      congr 1
      rw [← hp_eq]
      simpa using eLpNorm_norm (F n)
        (((continuous_parabolicOperator_on hB (hq_smooth n)).mono hKU).aestronglyMeasurable
          hK.measurableSet)
    let ε : ℕ → ℝ := fun n =>
      C * r ^ ((N : ℝ) / ((N : ℝ) + 1)) * parabolicLpNormOn N (F n) K
    have hε : Tendsto ε atTop (nhds 0) := by
      simpa [ε] using tendsto_const_nhds.mul hF_norm
    have hsourceMem : (t0, v0) ∈ K := by
      rw [mem_parabolicClosedBox_iff]
      exact ⟨by nlinarith [sq_nonneg r], by nlinarith [sq_nonneg r], fun _ => by simpa using hr.le⟩
    have htargetMem : (t0 + r ^ 2, v) ∈ K := by
      rw [mem_parabolicClosedBox_iff]
      exact ⟨by nlinarith [sq_nonneg r], by nlinarith, fun i => (hv i).le.trans (by linarith)⟩
    have hEventually : ∀ᶠ n in atTop,
        hBox * q n (t0, v0) ≤ q n (t0 + r ^ 2, v) + ε n := by
      filter_upwards [hq_nonneg] with n hn
      exact hsource K U B (q n) (F n) t0 v0 r hr hK hKU hU (Subset.refl _) hB
        ((hq_smooth n).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffOn
        (continuous_parabolicOperator_on hB (hq_smooth n)) hn
        (hLower.mono hKU) (hUpper.mono hKU) (fun _ _ => rfl) v hv
    have hq_pt {z : TimeVelocity N} (hz : z ∈ K) :
        Tendsto (fun n => q n z) atTop (nhds (u z)) := by
      have hgz : G.toFun z = u z := (subset_of_mem_nhdsSet hvalEq) hz
      rw [← hgz]
      exact tendsto_parabolicConvolution_of_continuous hGval_cont z
    exact le_of_tendsto_of_tendsto (tendsto_const_nhds.mul (hq_pt hsourceMem))
      (by simpa using (hq_pt htargetMem).add hε) hEventually
  let m : ℕ := 256 * N
  let dt : ℝ := (P'.1 - P.1) / (m : ℝ)
  let r : ℝ := Real.sqrt dt
  let t : ℕ → ℝ := fun k => P.1 + (k : ℝ) * dt
  let v : ℕ → PDE.Vec N := fun k =>
    P.2 + ((k : ℝ) / (m : ℝ)) • (P'.2 - P.2)
  have hgeom := unitCylinder_harnack_link_geometry N hN P P' hP hP'
  change 0 < m ∧ 0 < r ∧ (t 0, v 0) = P ∧ (t m, v m) = P' ∧
    (∀ k < m, t (k + 1) = t k + r ^ 2) ∧
    (∀ k < m, parabolicClosedBox 2 r (t k - r ^ 2) (v k) ⊆ U) ∧
    (∀ k < m, v (k + 1) ∈ velocityCube (v k) (r / 2)) at hgeom
  obtain ⟨_hm, hr, hstart, hend, htstep, hboxes, hvstep⟩ := hgeom
  have hchain : ∀ k ≤ m, hBox ^ k * u P ≤ u (t k, v k) := by
    intro k
    induction k with
    | zero =>
      intro _
      simp [hstart, le_refl]
    | succ k ih =>
      intro hk
      have hkm : k < m := Nat.lt_of_succ_le hk
      have hlink := hlocal (t k) (v k) r hr (hboxes k hkm) (v (k + 1)) (hvstep k hkm)
      rw [← htstep k hkm] at hlink
      calc
        hBox ^ (k + 1) * u P = hBox * (hBox ^ k * u P) := by rw [pow_succ]; ring
        _ ≤ hBox * u (t k, v k) :=
          mul_le_mul_of_nonneg_left (ih (Nat.le_of_lt hkm)) hh0.le
        _ ≤ u (t (k + 1), v (k + 1)) := hlink
  simpa only [hend] using hchain m le_rfl

end HypoellipticAleksandrov.Parabolic

