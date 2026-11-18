module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ReturnGeometryDistance
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Assembly
import HypoellipticAleksandrov.KineticAleksandrov.Holder.OscillationContractionGeometry
import Mathlib.Tactic
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ReturnGeometryKernel
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PatchPowerDoubling
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.GreenPotentialsRegularity
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.IsLUB
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Algebra.Order.Field.GeomSum
public import HypoellipticAleksandrov.KineticAleksandrov.Scaling.Calculus

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Parabolic Set MeasureTheory Holder SectionTwo Evolution TheoremA Filter Finset
open scoped Topology

/-- The concrete return boxes increase with their radius parameter. -/
theorem returnBox_mono (v : ℝ) {a b : ℝ} (hab : a ≤ b) :
    returnBox v a ⊆ returnBox v b := by
  intro p hp
  exact ⟨hp.1.trans_le (by linarith), hp.2.1.trans_le (by linarith),
    hp.2.2.trans_le (by linarith)⟩



/-- Reflection preserves the smooth autonomous coefficient class. -/
def returnReflectedCoefficient {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) :
    SmoothAutonomous lam Lam :=
  ⟨reflectedAutonomous A.a, reflectedAutonomous_smooth A, reflectedAutonomous_bounds A⟩


/-- A numerical radius factor making the Holder error at most half the positive height. -/
def returnHolderRadiusFactor (alpha D : ℝ) : ℝ := (1 / (2 * (D + 1))) ^ (1 / alpha)

/-- The fixed radius factor is positive and at most one. -/
theorem returnHolderRadiusFactor_bounds (alpha D : ℝ) (ha : 0 < alpha) (hD : 0 < D) :
    0 < returnHolderRadiusFactor alpha D ∧ returnHolderRadiusFactor alpha D ≤ 1 := by
  have hb : 0 < 1 / (2 * (D + 1)) := by positivity
  have hb1 : 1 / (2 * (D + 1)) ≤ 1 := by
    apply (div_le_one (by positivity : 0 < 2 * (D + 1))).mpr
    linarith
  exact ⟨Real.rpow_pos_of_pos hb _, Real.rpow_le_one hb.le hb1 (by positivity)⟩

/-- A value-relative radius makes the absolute modulus smaller than half that value. -/
theorem return_holder_radius (alpha D h value M : ℝ)
    (ha : 0 < alpha) (hD : 0 < D) (hh : 0 < h)
    (hvalue : 0 < value) (hM : 0 < M) (hvalueM : value ≤ M) :
    let ell := returnHolderRadiusFactor alpha D * h * (value / M) ^ (1 / alpha)
    0 < ell ∧ ell ≤ h ∧ D * M * (ell / h) ^ alpha ≤ value / 2 := by
  let δ := returnHolderRadiusFactor alpha D
  have hδ := returnHolderRadiusFactor_bounds alpha D ha hD
  have hratio := div_pos hvalue hM
  have hroot : 0 < (value / M) ^ (1 / alpha) := Real.rpow_pos_of_pos hratio _
  have hroot1 : (value / M) ^ (1 / alpha) ≤ 1 :=
    Real.rpow_le_one hratio.le ((div_le_one hM).mpr hvalueM) (by positivity)
  have hδpower : δ ^ alpha = 1 / (2 * (D + 1)) := by
    dsimp [δ, returnHolderRadiusFactor]
    rw [← Real.rpow_mul (by positivity : 0 ≤ 1 / (2 * (D + 1)))]
    rw [one_div_mul_cancel ha.ne', Real.rpow_one]
  have hpower : (δ * h * (value / M) ^ (1 / alpha) / h) ^ alpha =
      (1 / (2 * (D + 1))) * (value / M) := by
    have he : δ * h * (value / M) ^ (1 / alpha) / h =
        δ * (value / M) ^ (1 / alpha) := by field_simp
    rw [he, Real.mul_rpow hδ.1.le hroot.le, hδpower,
      ← Real.rpow_mul hratio.le, one_div_mul_cancel ha.ne', Real.rpow_one]
  refine ⟨mul_pos (mul_pos hδ.1 hh) hroot, ?_, ?_⟩
  · have hprod := mul_le_mul hδ.2 hroot1 hroot.le zero_le_one
    have he := mul_le_mul_of_nonneg_right hprod hh.le
    dsimp only [δ] at *
    nlinarith
  · change D * M * (δ * h * (value / M) ^ (1 / alpha) / h) ^ alpha ≤ value / 2
    rw [hpower]
    have he : D * M * (1 / (2 * (D + 1)) * (value / M)) =
        (D / (2 * (D + 1))) * value := by field_simp
    rw [he]
    have hcoef : D / (2 * (D + 1)) ≤ 1 / 2 := by
      apply (div_le_iff₀ (by positivity : 0 < 2 * (D + 1))).mpr
      linarith
    exact (mul_le_mul_of_nonneg_right hcoef hvalue.le).trans_eq (by ring)

/-- The height-relative radius produces the source nonlinear height expression. -/
theorem return_holder_height_factor (alpha beta c δ h value M : ℝ)
    (hδ : 0 ≤ δ) (hh : 0 ≤ h) (hvalue : 0 < value) (hM : 0 < M) :
    c * (δ * h * (value / M) ^ (1 / alpha)) ^ beta * (value / 2) =
      (c * δ ^ beta / 2) * h ^ beta * value ^ (1 + beta / alpha) * M ^ (-beta / alpha) := by
  rw [Real.mul_rpow (mul_nonneg hδ hh) (Real.rpow_nonneg (div_nonneg hvalue.le hM.le) _),
    Real.mul_rpow hδ hh, ← Real.rpow_mul (div_nonneg hvalue.le hM.le)]
  have he : 1 / alpha * beta = beta / alpha := by ring
  rw [he, Real.div_rpow hvalue.le hM.le, Real.rpow_add hvalue,
    Real.rpow_one, neg_div, Real.rpow_neg hM.le]
  ring


/-- A nonlinear height comparison implies a linear absorption bound. -/
theorem return_height_absorption (beta gamma c eps d Ma Mb U : ℝ)
    (hgamma : 0 < gamma) (hc : 0 < c) (heps : 0 < eps) (hd : 0 < d)
    (hMa : 0 ≤ Ma) (hMb : Ma ≤ Mb) (hU : 0 ≤ U)
    (hheight : 0 < Mb → c * d ^ beta * Ma ^ (1 + gamma) * Mb ^ (-gamma) ≤ U) :
    Ma ≤ eps * Mb + (c * eps ^ gamma)⁻¹ * d ^ (-beta) * U := by
  have hMb0 := hMa.trans hMb
  have herr0 : 0 ≤ (c * eps ^ gamma)⁻¹ * d ^ (-beta) * U := by positivity
  by_cases hsmall : Ma ≤ eps * Mb
  · exact hsmall.trans (le_add_of_nonneg_right herr0)
  have hMapos := (mul_nonneg heps.le hMb0).trans_lt (lt_of_not_ge hsmall)
  have hMbpos := hMapos.trans_le hMb
  have hpow := Real.rpow_le_rpow (mul_nonneg hMb0 heps.le)
    (by nlinarith : Mb * eps ≤ Ma) hgamma.le
  rw [Real.mul_rpow hMb0 heps.le] at hpow
  have hinv : Mb ^ gamma * Mb ^ (-gamma) = 1 := by
    rw [← Real.rpow_add hMbpos, add_neg_cancel, Real.rpow_zero]
  have hlower : eps ^ gamma * Ma ≤ Ma ^ (1 + gamma) * Mb ^ (-gamma) := by
    rw [Real.rpow_add hMapos, Real.rpow_one]
    calc
      _ = (eps ^ gamma * Ma) * (Mb ^ gamma * Mb ^ (-gamma)) := by rw [hinv, mul_one]
      _ = (Mb ^ gamma * eps ^ gamma) * (Ma * Mb ^ (-gamma)) := by ring
      _ ≤ _ := (mul_le_mul_of_nonneg_right hpow (mul_nonneg hMa (Real.rpow_nonneg hMb0 (-gamma))))
      _ = _ := by ring
  have hden : 0 < c * d ^ beta * eps ^ gamma := by positivity
  have hbound : Ma ≤ U / (c * d ^ beta * eps ^ gamma) := by
    apply (le_div_iff₀ hden).mpr
    nlinarith [(mul_le_mul_of_nonneg_left hlower (mul_nonneg hc.le (Real.rpow_nonneg hd.le beta))).trans (by simpa only [mul_assoc] using hheight hMbpos)]
  have he : U / (c * d ^ beta * eps ^ gamma) =
      (c * eps ^ gamma)⁻¹ * d ^ (-beta) * U := by
    rw [Real.rpow_neg hd.le]
    field_simp
  rw [he] at hbound
  exact hbound.trans (le_add_of_nonneg_left (mul_nonneg heps.le hMb0))



/-- A bounded sequence loses the terminal supremum when the absorption ratio is small. -/
theorem return_recurrence_bound (f : ℕ → ℝ) (q r B M : ℝ)
    (hq : 0 ≤ q) (hq1 : q < 1) (hr : 0 ≤ r) (hqr : q * r < 1)
    (hB : 0 ≤ B) (hbounded : ∀ n, f n ≤ M)
    (hstep : ∀ n, f n ≤ q * f (n + 1) + B * r ^ n) :
    f 0 ≤ B / (1 - q * r)  := by
  have return_recurrence_substitution (n : ℕ) (N : ℕ) :
      f n ≤ q ^ N * f (n + N) + B * r ^ n * ∑ j ∈ range N, (q * r) ^ j := by
    induction N generalizing n with
    | zero => simp
    | succ N ih =>
      apply (hstep n).trans
      apply (add_le_add (mul_le_mul_of_nonneg_left (ih (n + 1)) hq) (le_refl (B * r ^ n))).trans_eq
      rw [geom_sum_succ, pow_succ]
      simp only [pow_succ]
      have hindex : n + 1 + N = n + (N + 1) := by omega
      rw [hindex]
      ring
  have hsum (N : ℕ) : (∑ j ∈ range N, (q * r) ^ j) ≤ 1 / (1 - q * r) := by
    simpa using
      (geom_sum_Ico_le_of_lt_one (m := 0) (n := N) (mul_nonneg hq hr) hqr)
  have hN (N : ℕ) : f 0 ≤ q ^ N * M + B / (1 - q * r) := by
    have h := return_recurrence_substitution 0 N
    simp at h
    apply h.trans
    exact (add_le_add
      (mul_le_mul_of_nonneg_left (hbounded N) (pow_nonneg hq N))
      (mul_le_mul_of_nonneg_left (hsum N) hB)).trans_eq (by ring)
  have ht : Tendsto (fun N : ℕ => q ^ N * M + B / (1 - q * r)) atTop
      (𝓝 (B / (1 - q * r))) := by
    simpa using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hq hq1).mul_const M).add_const
        (B / (1 - q * r))
  exact ge_of_tendsto ht (Eventually.of_forall hN)


/-- The nested radii in the source iteration. -/
def returnIterationRadius (n : ℕ) : ℝ := 1 - (1 / 2 : ℝ) ^ (n + 1)

/-- Every radius belongs to the permitted half-to-one interval. -/
theorem returnIterationRadius_bounds (n : ℕ) :
    1 / 2 ≤ returnIterationRadius n ∧ returnIterationRadius n < 1 := by
  have hp := pow_pos (by norm_num : (0 : ℝ) < 1 / 2) (n + 1)
  have hb : (1 / 2 : ℝ) ^ (n + 1) ≤ 1 / 2 := by
    rw [pow_succ]
    have h := pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) ≤ 1) (n := n)
    nlinarith
  dsimp [returnIterationRadius]
  constructor <;> linarith

/-- The consecutive radius gap is the exact dyadic gap in the source. -/
theorem returnIterationRadius_gap (n : ℕ) :
    returnIterationRadius (n + 1) - returnIterationRadius n =
      (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ n := by
  simp only [returnIterationRadius, pow_succ]
  ring

/-- The error term grows by the fixed factor `2^beta` at each iteration. -/
theorem returnIterationRadius_gap_power (n : ℕ) (beta : ℝ) :
    (returnIterationRadius (n + 1) - returnIterationRadius n) ^ (-beta) =
      (4 : ℝ) ^ beta * ((2 : ℝ) ^ beta) ^ n := by
  rw [returnIterationRadius_gap,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1 / 4) (pow_nonneg (by norm_num) n),
    ← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  rw [Real.rpow_neg_eq_inv_rpow, Real.rpow_neg_eq_inv_rpow]
  norm_num



/-- The kinetic scaling keeps physical position translations and does not shift velocity. -/
def returnScaling (r : ℝ) (hr : 0 < r) (X : ℝ) : Scaling.KineticAffineScaling 1 :=
  ⟨r ^ 2, r, r ^ 3, 0, 0, fun _ => X, 0, by positivity, hr, by positivity⟩

/-- The scaled autonomous coefficient retains exactly the original ellipticity constants. -/
def returnScaledCoefficient {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) (r X : ℝ) :
    SmoothAutonomous lam Lam where
  a x v := A.a (X + r ^ 3 * x) (r * v)
  smooth := by
    change ContDiff ℝ (⊤ : ℕ∞)
      ((Function.uncurry A.a) ∘ fun z : ℝ × ℝ => (X + r ^ 3 * z.1, r * z.2))
    exact A.smooth.comp (by fun_prop)
  bounds x v := A.bounds _ _



/-- A normalized classical homogeneous solution represents the original canonical action.
The existence assertion is proved from the full-space producer; it is not a premise. -/
theorem exists_return_scaled_solution
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (F : BoundedBorel Z)
    (hF0 : ∀ z, 0 ≤ F z) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (r : ℝ) (hr : 0 < r) (X : ℝ) :
    ∃ U : Point → ℝ, IsNonnegativeHomogeneousSolution
      (returnReflectedCoefficient (returnScaledCoefficient A r X)) U ∧
      ∀ p : Point, 0 < p.time →
        U p = S hH hLE hlam hLam A (r ^ 2 * p.time) F
          (X - r ^ 3 * p.position 0, r * p.velocity 0)   := by
  have returnScaling_drift :
      (returnScaling r hr X).drift (identityDrift 1) = identityDrift 1 := by
    funext y
    ext i
    simp [Scaling.KineticAffineScaling.drift, Scaling.KineticAffineScaling.position,
      returnScaling, identityDrift]
    field_simp
  have returnScaling_coefficient :
      (returnScaling r hr X).coefficient (evolutionCoefficient A.a) =
      evolutionCoefficient (returnScaledCoefficient A r X).a := by
    ext s y z i j
    simp [Scaling.KineticAffineScaling.coefficient, Scaling.KineticAffineScaling.time,
      Scaling.KineticAffineScaling.position, Scaling.KineticAffineScaling.transport,
      returnScaling, evolutionCoefficient, returnScaledCoefficient, hr.ne']
  have hG :=
    (scalarTerminalDatum_smooth F hF).comp (contDiff_snd.prodMk contDiff_fst)
  obtain ⟨w, hw, hrep⟩ := fullspace_bounded_smooth_solution hH hlam hLam A (fullSpaceEvolution hH hLE hlam hLam A)
    (fullSpaceEvolution_spec hH hLE hlam hLam A) 0 (physicalTerminalDatum (scalarTerminalDatum F)) hG
  let Φ := returnScaling r hr X
  let W := w ∘ Φ.point
  let U := W ∘ autonomousReversal ∘ autonomousPositionReflection
  have heq (p : Point) (hp : 0 < p.time) :
      U p = S hH hLE hlam hLam A (r ^ 2 * p.time) F
        (X - r ^ 3 * p.position 0, r * p.velocity 0) := by
    have ht : 0 ≤ r ^ 2 * p.time := by positivity
    have hpoint : Φ.point (autonomousReversal (autonomousPositionReflection p)) =
        ⟨-(r ^ 2 * p.time), fun _ => r * p.velocity 0,
          fun _ => X - r ^ 3 * p.position 0⟩ := by
      apply KineticPoint.ext
      · simp [Φ, returnScaling, Scaling.KineticAffineScaling.point,
          Scaling.KineticAffineScaling.time, autonomousReversal, autonomousPositionReflection]
      · funext i
        rw [Fin.eq_zero i]
        simp [Φ, returnScaling, Scaling.KineticAffineScaling.point,
          Scaling.KineticAffineScaling.position, autonomousReversal, autonomousPositionReflection]
      · funext i
        rw [Fin.eq_zero i]
        simp [Φ, returnScaling, Scaling.KineticAffineScaling.point,
          Scaling.KineticAffineScaling.transport, autonomousReversal,
          autonomousPositionReflection, sub_eq_add_neg]
    dsimp only [U, W, Function.comp_apply]
    rw [hpoint]
    unfold S fullSpaceAction
    split
    · exact hrep (wholeSpaceQuery (-(r ^ 2 * p.time)) 0 (neg_nonpos.mpr ht)
      (fun _ => r * p.velocity 0) (fun _ => X - r ^ 3 * p.position 0)) rfl
    · rename_i h
      exact False.elim (h ht)
  let O : Set Point := {p | 0 < p.time}
  let T : EvolutionVec 1 → ℝ × (PDE.Vec 1 × PDE.Vec 1) := fun q =>
    (-(r ^ 2 * timeCoord 1 q), r • transportedCoord 1 q,
      (fun _ => X) - r ^ 3 • diffusedCoord 1 q)
  have hT : ContDiff ℝ (⊤ : ℕ∞) T := by unfold T; fun_prop
  have hmaps : MapsTo T (evolutionHomeomorph 1 ⁻¹' O)
      (evolutionPastInteriorRaw autonomousWholeDomain (fun _ => 0) 0) := by
    intro q hq
    refine ⟨?_, ?_⟩
    · change -(r ^ 2 * timeCoord 1 q) < 0
      change 0 < timeCoord 1 q at hq
      nlinarith [sq_pos_of_pos hr]
    · change r • transportedCoord 1 q ∈ movingDomain (wholeSpace 1) (fun _ => 0) _
      rw [movingDomain_wholeSpace]
      trivial
  have hreg : IsKineticC112On U O := by
    apply isKineticC112On_of_contDiffOn (isOpen_lt continuous_const continuous_time)
    convert (hw.2.2.1.comp hT.contDiffOn hmaps) using 1
    funext q
    dsimp [U, W, Φ, returnScaling, Scaling.KineticAffineScaling.point,
      Scaling.KineticAffineScaling.time, Scaling.KineticAffineScaling.position,
      Scaling.KineticAffineScaling.transport, autonomousReversal,
      autonomousPositionReflection, T]
    congr 1
    apply KineticPoint.ext
    · change 0 + r ^ 2 * (-q 0) = -(r ^ 2 * q 0)
      ring
    · funext i
      change 0 + r * transportedCoord 1 q i = r * transportedCoord 1 q i
      ring
    · funext i
      change X + (r ^ 2 * -q 0) * 0 + r ^ 3 * -(diffusedCoord 1 q i) =
        X - r ^ 3 * diffusedCoord 1 q i
      ring
  obtain ⟨M, hM, hbound⟩ := F.exists_bound
  refine ⟨U, ⟨⟨M, ?_⟩, ?_, hreg, ?_⟩, heq⟩
  · intro p hp
    rw [heq p hp, S_eq_integral hH hLE hlam hLam A _ (by positivity)]
    exact abs_integral_boundedBorel_le F _
      (Kphysical_mass_one hH hLE hlam hLam A _ (by positivity) _).le hM hbound
  · intro p hp
    rw [heq p hp, S_eq_integral hH hLE hlam hLam A _ (by positivity)]
    exact integral_nonneg hF0
  · intro p hp
    change autonomousScalarOperator (reflectedAutonomous (returnScaledCoefficient A r X).a)
      ((W ∘ autonomousReversal) ∘ autonomousPositionReflection) p = 0
    rw [autonomous_generator_positionReflection, autonomous_generator_reversal]
    let q := autonomousReversal (autonomousPositionReflection p)
    have hq : Φ.point q ∈ evolutionPastOpenCylinder autonomousWholeDomain (fun _ => 0) 0 := by
      refine ⟨?_, ?_⟩
      · change 0 + r ^ 2 * (-p.time) < 0
        nlinarith [sq_pos_of_pos hr]
      · change (Φ.point q).position ∈ movingDomain (wholeSpace 1) (fun _ => 0) _
        rw [movingDomain_wholeSpace]
        trivial
    have hrawmem : Scaling.rawPoint (Φ.point q) ∈
        evolutionPastInteriorRaw autonomousWholeDomain (fun _ => 0) 0 := hq
    have hopen : IsOpen (evolutionPastInteriorRaw autonomousWholeDomain (fun _ => 0) 0) := by
      have he : evolutionPastInteriorRaw autonomousWholeDomain (fun _ => 0) 0 =
          {x : ℝ × (PDE.Vec 1 × PDE.Vec 1) | x.1 < 0} := by
        ext x
        simp [evolutionPastInteriorRaw, autonomousWholeDomain, movingDomain]
      rw [he]
      exact isOpen_lt continuous_fst continuous_const
    have hw2 := (hw.2.2.1.contDiffAt (hopen.mem_nhds hrawmem)).of_le
      (by norm_num : (2 : WithTop ℕ∞) ≤ (⊤ : ℕ∞))
    have hscaled := Scaling.KineticAffineScaling.transportedForwardOperator_comp_point (Φ := Φ)
      (u := w) (p := q) (evolutionCoefficient A.a) (identityDrift 1) hw2
    rw [returnScaling_coefficient, returnScaling_drift] at hscaled
    rw [show transportedForwardOperator (evolutionCoefficient (returnScaledCoefficient A r X).a)
        (identityDrift 1) W q = r ^ 2 *
          transportedForwardOperator (evolutionCoefficient A.a) (identityDrift 1) w
            (Φ.point q) from hscaled,
      hw.2.2.2.1 _ hq, mul_zero, neg_zero]



/-- Bounded nonnegative Borel data satisfy the same full-space return comparison. -/
theorem return_time
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hp6 : SmoothAutonomousP6Statement lam Lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (F : BoundedBorel Z),
      (∀ z, 0 ≤ F z) → ∀ t s X v : ℝ,
      0 < t → 2 * t ≤ s → s ≤ 3 * t → |v| ≤ Real.sqrt t →
      S hH hLE hlam hLam A t F (X, v) ≤ C * S hH hLE hlam hLam A s F (X, v)   := by
  have return_holder_modulus :
      ∃ alpha D : ℝ, 0 < alpha ∧ alpha ≤ 1 ∧ 0 < D ∧
      ∀ (A : SmoothAutonomous lam Lam) (u : Point → ℝ),
      IsNonnegativeHomogeneousSolution A u → ∀ a b v : ℝ,
      1 / 2 ≤ a → a < b → b ≤ 1 → |v| ≤ 1 →
      ∀ (z p : Point) (ell : ℝ), z ∈ returnBox v a →
      0 < ell → ell ≤ (b - a) / 8192 →
      p ∈ closure (backwardCylinder z ell) →
      |u z - u p| ≤ D * sSup (u '' returnBox v b) *
        (ell / ((b - a) / 8192)) ^ alpha := by
    obtain ⟨C_A, _hCA, hadm⟩ := hp6
    obtain ⟨alpha, C, halpha, halpha1, hholder⟩ :=
      kinetic_holder_of_aleksandrov_aux 1 (by omega) lam Lam 6 C_A
        hlam hLam (by norm_num)
    let D := max C 1 * 4 ^ alpha
    have hCpos : 0 < max C 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    refine ⟨alpha, D, halpha, halpha1, mul_pos hCpos (by positivity), ?_⟩
    intro A u hu a b v ha hab hb hv z p ell hz hell hellh hp
    let h := (b - a) / 8192
    let mid := (a + b) / 2
    let O := returnBox v b
    let K : Set Point := {z, p}
    let E := holderNeighbourhood h K
    have hh : 0 < h := by dsimp [h]; positivity
    have hamid : a < mid := by dsimp [mid]; linarith
    have hmidb : mid < b := by dsimp [mid]; linarith
    have hpcl : p ∈ closure (backwardCylinder z (2 * h)) :=
      closure_mono (backwardCylinder_radius_mono z hell (by dsimp [h]; linarith)) hp
    have hinner : closure (backwardCylinder z (2 * h)) ⊆ returnBox v mid := by
      have he : 2 * h = 2 * ((mid - a) / 4096) := by dsimp [h, mid]; ring
      rw [he]
      exact returnBox_cylinder_subset v a mid hv ha hamid (by dsimp [mid]; linarith) z hz
    have hKmid : K ⊆ returnBox v mid := by
      intro q hq
      rcases hq with hq | hq <;> subst q
      · exact (returnBox_mono v hamid.le hz)
      · exact (hinner hpcl)
    have hQ : ∀ q ∈ K, closure (backwardCylinder q (2 * h)) ⊆ O := by
      intro q hq
      have he : 2 * h = 2 * ((b - mid) / 4096) := by dsimp [h, mid]; ring
      rw [he]
      exact returnBox_cylinder_subset v mid b hv (by dsimp [mid]; linarith)
        hmidb hb q (hKmid hq)
    have hOpos : O ⊆ {q | 0 < q.time} := by
      intro q hq
      have hr := returnBox_subset_reference v b hv hb hq
      change 0 < q.time
      linarith [hr.1.1]
    have hO := returnBox_isOpen v b
    have hreg : IsKineticC112On u O := by
      rcases hu.2.2.1 with ⟨hc, ht, hx, hv, hct, hcx, hcv, hcvv⟩
      exact ⟨hc.mono hOpos, fun q hq => ht q (hOpos hq), fun q hq => hx q (hOpos hq),
        fun q hq => hv q (hOpos hq), hct.mono hOpos, hcx.mono hOpos,
        hcv.mono hOpos, hcvv.mono hOpos⟩
    obtain ⟨M, hM⟩ := hu.1
    have hbounded : ∀ q ∈ O, |u q| ≤ M := fun q hq => hM q (hOpos hq)
    have hEll := autonomous_fullElliptic A
    have hmod := hholder _ hEll.1 hEll.2.1 hEll.2.2.1 hEll.2.2.2 O hO u
      ⟨M, hbounded⟩ (hadm A O hO u hreg (ae_restrict_of_forall_mem hO.measurableSet (fun q hq => hu.2.2.2 q (hOpos hq)))) K (hKmid.trans (returnBox_mono v hmidb.le)) (isCompact_singleton.insert z) h hh hQ
      z (by simp [K]) p (by simp [K])
    have hEO : E ⊆ O := by
      intro q hq
      simp only [E, holderNeighbourhood, mem_iUnion] at hq
      obtain ⟨w, hw, hq⟩ := hq
      exact hQ w hw (subset_closure hq)
    have hEne : E.Nonempty := by
      obtain ⟨q, hq⟩ := backwardCylinder_nonempty z (by positivity : 0 < 2 * h)
      exact ⟨q, mem_iUnion.mpr ⟨z, mem_iUnion.mpr ⟨by simp [K], hq⟩⟩⟩
    have habO : BddAbove (u '' O) := ⟨M, by
      rintro _ ⟨q, hq, rfl⟩
      exact (le_abs_self _).trans (hbounded q hq)⟩
    have hbbE : BddBelow (u '' E) := ⟨0, by
      rintro _ ⟨q, hq, rfl⟩
      exact hu.2.1 q (hOpos (hEO hq))⟩
    have hosc0 := oscillationOn_nonneg hEne (habO.mono (image_mono hEO)) hbbE
    have hosc : oscillationOn u E ≤ sSup (u '' O) := by
      have hs :=
        csSup_le (hEne.image u) (fun _ hx => le_csSup habO (image_mono hEO hx))
      have hi : 0 ≤ sInf (u '' E) := le_csInf (hEne.image u) (by
        rintro _ ⟨q, hq, rfl⟩
        exact hu.2.1 q (hOpos (hEO hq)))
      unfold oscillationOn
      linarith
    have hd0 := quasiDistance_nonneg z p
    have hratio : quasiDistance z p / h ≤ 4 * (ell / h) := by
      exact (div_le_div_of_nonneg_right (returnCylinder_distance z p ell hell hp) hh.le).trans_eq (by ring)
    have hrpow := Real.rpow_le_rpow (div_nonneg hd0 hh.le) hratio halpha.le
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (div_nonneg hell.le hh.le)] at hrpow
    have h₁ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left C 1) hosc0)
      (Real.rpow_nonneg (div_nonneg hd0 hh.le) alpha)
    have h₂ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hosc hCpos.le)
      (Real.rpow_nonneg (div_nonneg hd0 hh.le) alpha)
    have hMb0 : 0 ≤ sSup (u '' O) := hosc0.trans hosc
    have h₃ := mul_le_mul_of_nonneg_left hrpow (mul_nonneg hCpos.le hMb0)
    exact (hmod.trans (h₁.trans (h₂.trans h₃))).trans_eq (by dsimp [D, h, O]; ring)
  have return_time_smooth :
      ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (F : BoundedBorel Z),
      (∀ z, 0 ≤ F z) → ContDiff ℝ (⊤ : ℕ∞) F →
      ∀ t s X v : ℝ, 0 < t → 2 * t ≤ s → s ≤ 3 * t → |v| ≤ Real.sqrt t →
      S hH hLE hlam hLam A t F (X, v) ≤ C * S hH hLE hlam hLam A s F (X, v) := by
    have return_time_unit_solution :
        ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (u : Point → ℝ),
        IsNonnegativeHomogeneousSolution A u → ∀ v : ℝ, |v| ≤ 1 →
        ∀ zStar ∈ returnFutureRegion, u (point 1 0 v) ≤ C * u zStar := by
      have return_holder_patch_solution :
          ∃ alpha beta c₀ : ℝ, 0 < alpha ∧ alpha ≤ 1 ∧ 0 < beta ∧ 0 < c₀ ∧
          ∀ (A : SmoothAutonomous lam Lam) (u : Point → ℝ),
          IsNonnegativeHomogeneousSolution A u → ∀ a b v : ℝ,
          1 / 2 ≤ a → a < b → b ≤ 1 → |v| ≤ 1 →
          ∀ zStar ∈ returnFutureRegion,
          0 < sSup (u '' returnBox v b) →
          c₀ * (b - a) ^ beta * sSup (u '' returnBox v a) ^ (1 + beta / alpha) *
            sSup (u '' returnBox v b) ^ (-beta / alpha) ≤ u zStar := open MeasureTheory Filter in by
        have return_holder_patch_point :
            ∃ alpha beta c₀ : ℝ, 0 < alpha ∧ alpha ≤ 1 ∧ 0 < beta ∧ 0 < c₀ ∧
            ∀ (A : SmoothAutonomous lam Lam) (u : Point → ℝ),
            IsNonnegativeHomogeneousSolution A u → ∀ a b v : ℝ,
            1 / 2 ≤ a → a < b → b ≤ 1 → |v| ≤ 1 →
            ∀ z zStar : Point, z ∈ returnBox v a → zStar ∈ returnFutureRegion →
            0 < sSup (u '' returnBox v b) →
            c₀ * (b - a) ^ beta * (u z) ^ (1 + beta / alpha) *
              sSup (u '' returnBox v b) ^ (-beta / alpha) ≤ u zStar := by
          obtain ⟨alpha, D, ha, ha1, hD, hmod⟩ := return_holder_modulus
          obtain ⟨beta, cp, hb, hcp, hpatch⟩ := return_patch_power lam Lam hlam hLam hp6
          let δ := returnHolderRadiusFactor alpha D
          let c₀ := (cp * δ ^ beta / 2) / 8192 ^ beta
          have hδ := returnHolderRadiusFactor_bounds alpha D ha hD
          have hδpos : 0 < δ := hδ.1
          have hc₀ : 0 < c₀ := by dsimp [c₀]; positivity
          refine ⟨alpha, beta, c₀, ha, ha1, hb, hc₀, ?_⟩
          intro A u hu a b v habase hab hb1 hv z zStar hz hstar hMb
          have hzref := returnBox_subset_reference v a hv (by linarith) hz
          by_cases huz : u z = 0
          · rw [huz, Real.zero_rpow (by positivity : (1 + beta / alpha) ≠ 0), mul_zero, zero_mul]
            exact hu.2.1 zStar (by linarith [hstar.1.1])
          have huzpos : 0 < u z := lt_of_le_of_ne (hu.2.1 z (by linarith [hzref.1.1])) (Ne.symm huz)
          let M := sSup (u '' returnBox v b)
          let h := (b - a) / 8192
          let ell := δ * h * (u z / M) ^ (1 / alpha)
          have hh : 0 < h := by dsimp [h]; positivity
          have hh1 : h ≤ 1 := by dsimp [h]; linarith
          have hOpos : returnBox v b ⊆ {q | 0 < q.time} := by
            intro q hq
            have hqref := returnBox_subset_reference v b hv hb1 hq
            change 0 < q.time
            linarith [hqref.1.1]
          obtain ⟨B, hB⟩ := hu.1
          have hbounded : BddAbove (u '' returnBox v b) := ⟨B, by
            rintro _ ⟨q, hq, rfl⟩
            exact (le_abs_self _).trans (hB q (hOpos hq))⟩
          have huzM : u z ≤ M := le_csSup hbounded
            (mem_image_of_mem u (returnBox_mono v hab.le hz))
          have hradius := return_holder_radius alpha D h (u z) M ha hD hh huzpos hMb huzM
          change 0 < ell ∧ ell ≤ h ∧ D * M * (ell / h) ^ alpha ≤ u z / 2 at hradius
          have hlower : ∀ q ∈ backwardCylinder z ell, u z / 2 ≤ u q := by
            intro q hq
            have hc := hmod A u hu a b v habase hab hb1 hv z q ell hz
              hradius.1 hradius.2.1 (subset_closure hq)
            linarith [(abs_le.mp (hc.trans hradius.2.2)).2]
          have hheight := hpatch A u hu ell (u z / 2) z zStar hradius.1
            (hradius.2.1.trans hh1) (by positivity) hzref hstar hlower
          have hhpower : h ^ beta = (b - a) ^ beta / 8192 ^ beta :=
            Real.div_rpow (by linarith) (by norm_num) beta
          change cp * (δ * h * (u z / M) ^ (1 / alpha)) ^ beta * (u z / 2) ≤ u zStar at hheight
          rw [(return_holder_height_factor alpha beta cp δ h (u z) M hδ.1.le hh.le huzpos hMb), hhpower] at hheight
          convert hheight using 1; dsimp [c₀, M]; ring
        obtain ⟨alpha, beta, c₀, ha, ha1, hb, hc, hpoint⟩ :=
          return_holder_patch_point
        refine ⟨alpha, beta, c₀, ha, ha1, hb, hc, ?_⟩
        intro A u hu a b v habase hab hb1 hv zStar hstar hMb
        have hne : (u '' returnBox v a).Nonempty :=
          ⟨u (point 1 0 v), mem_image_of_mem u (returnBox_center v a (by linarith))⟩
        obtain ⟨M, hM⟩ := hu.1
        have hbounded : BddAbove (u '' returnBox v a) := ⟨M, by
          rintro _ ⟨q, hq, rfl⟩
          exact (le_abs_self _).trans (hM q (by linarith [(returnBox_subset_reference v a hv (by linarith) hq).1.1]))⟩
        obtain ⟨f, _hmono, hlim, hf⟩ := exists_seq_tendsto_sSup hne hbounded
        let g : ℝ → ℝ := fun x => c₀ * (b - a) ^ beta * x ^ (1 + beta / alpha) *
          sSup (u '' returnBox v b) ^ (-beta / alpha)
        have hg : Continuous g :=
          ((Real.continuous_rpow_const (by positivity : 0 ≤ 1 + beta / alpha)).const_mul
            (c₀ * (b - a) ^ beta)).mul_const _
        have hseq : ∀ n, g (f n) ≤ u zStar := by
          intro n
          obtain ⟨z, hz, hzf⟩ := hf n
          rw [← hzf]
          exact hpoint A u hu a b v habase hab hb1 hv z zStar hz hstar hMb
        exact le_of_tendsto (hg.continuousAt.tendsto.comp hlim) (Eventually.of_forall hseq)
      obtain ⟨alpha, beta, c₀, ha, _ha1, hb, hc, hheight⟩ :=
        return_holder_patch_solution
      let r := (2 : ℝ) ^ beta
      let eps := 1 / (2 * r)
      let K := (c₀ * eps ^ (beta / alpha))⁻¹
      let C := 2 * K * 4 ^ beta
      have hr : 0 < r := by dsimp [r]; positivity
      have hr1 : 1 ≤ r := Real.one_le_rpow (by norm_num) hb.le
      have heps : 0 < eps := by dsimp [eps]; positivity
      have heps1 : eps < 1 := by
        apply (div_lt_one (by positivity : 0 < 2 * r)).mpr
        linarith
      have her : eps * r = 1 / 2 := by dsimp [eps]; field_simp
      have hK : 0 < K := by dsimp [K]; positivity
      have hC : 0 < C := by dsimp [C]; positivity
      refine ⟨C, hC, ?_⟩
      intro A u hu v hv zStar hstar
      obtain ⟨M, hM⟩ := hu.1
      have hprops (R : ℝ) (hRlo : 1 / 2 ≤ R) (hRhi : R ≤ 1) :
          BddAbove (u '' returnBox v R) ∧ 0 ≤ sSup (u '' returnBox v R) ∧
            sSup (u '' returnBox v R) ≤ M := by
        have hpos : returnBox v R ⊆ {q | 0 < q.time} := by
          intro q hq
          change 0 < q.time
          linarith [(returnBox_subset_reference v R hv hRhi hq).1.1]
        have hbd : BddAbove (u '' returnBox v R) := ⟨M, by
          rintro _ ⟨q, hq, rfl⟩
          exact (le_abs_self _).trans (hM q (hpos hq))⟩
        have hcenter := returnBox_center v R (by linarith)
        exact ⟨hbd, (hu.2.1 _ (by norm_num [point])).trans
          (le_csSup hbd (mem_image_of_mem u hcenter)), csSup_le ((show (returnBox v R).Nonempty from ⟨point 1 0 v, hcenter⟩).image u) (by
            rintro _ ⟨q, hq, rfl⟩
            exact (le_abs_self _).trans (hM q (hpos hq)))⟩
      let f : ℕ → ℝ := fun n => sSup (u '' returnBox v (returnIterationRadius n))
      have hf0 (n : ℕ) : 0 ≤ f n :=
        (hprops _ (returnIterationRadius_bounds n).1 (returnIterationRadius_bounds n).2.le).2.1
      have hfM (n : ℕ) : f n ≤ M :=
        (hprops _ (returnIterationRadius_bounds n).1 (returnIterationRadius_bounds n).2.le).2.2
      have hU : 0 ≤ u zStar := hu.2.1 zStar (by linarith [hstar.1.1])
      have hstep (n : ℕ) : f n ≤ eps * f (n + 1) +
          (K * (4 : ℝ) ^ beta * u zStar) * r ^ n := by
        have hgap : 0 < returnIterationRadius (n + 1) - returnIterationRadius n := by
          rw [returnIterationRadius_gap]
          positivity
        have hfmono : f n ≤ f (n + 1) := by
          apply csSup_le
          · exact ⟨u (point 1 0 v), mem_image_of_mem u (returnBox_center v _
              (by linarith [(returnIterationRadius_bounds n).1]))⟩
          · intro x hx
            exact le_csSup (hprops _ (returnIterationRadius_bounds (n + 1)).1
              (returnIterationRadius_bounds (n + 1)).2.le).1
              (image_mono (returnBox_mono v (by linarith)) hx)
        have hh := return_height_absorption beta (beta / alpha) c₀ eps
          (returnIterationRadius (n + 1) - returnIterationRadius n) (f n) (f (n + 1))
          (u zStar) (by positivity) hc heps hgap (hf0 n) hfmono hU
          (fun hMb => by
            simpa only [f, neg_div] using hheight A u hu _ _ v (returnIterationRadius_bounds n).1
              (by linarith) (returnIterationRadius_bounds (n + 1)).2.le hv zStar hstar hMb)
        rw [returnIterationRadius_gap_power] at hh
        convert hh using 1; dsimp [K, r]; ring
      have hbound := return_recurrence_bound f eps r (K * (4 : ℝ) ^ beta * u zStar) M
        heps.le heps1 hr.le (by rw [her]; norm_num) (by positivity) hfM hstep
      rw [her] at hbound
      have hcenter : u (point 1 0 v) ≤ f 0 :=
        le_csSup (hprops _ (returnIterationRadius_bounds 0).1
          (returnIterationRadius_bounds 0).2.le).1
          (mem_image_of_mem u (returnBox_center v _ (by norm_num [returnIterationRadius])))
      exact (hcenter.trans hbound).trans_eq (by dsimp [C]; ring)
    obtain ⟨C, hC, hunit⟩ := return_time_unit_solution
    refine ⟨C, hC, ?_⟩
    intro A F hF0 hF t s X v ht hs hs1 hv
    let r := Real.sqrt t
    have hr : 0 < r := Real.sqrt_pos.mpr ht
    have hr2 : r ^ 2 = t := Real.sq_sqrt ht.le
    have hvn : |v / r| ≤ 1 := by
      rw [abs_div, abs_of_pos hr]
      exact (div_le_one hr).mpr hv
    have hslo : 2 ≤ s / t := (le_div_iff₀ ht).mpr (by linarith)
    have hshi : s / t ≤ 3 := (div_le_iff₀ ht).mpr hs1
    have hspos : 0 < s / t := by linarith
    obtain ⟨U, hu, hrep⟩ := exists_return_scaled_solution hH hLE hlam hLam A F hF0 hF r hr X
    have hstar : point (s / t) 0 (v / r) ∈ returnFutureRegion :=
      ⟨⟨hslo, hshi⟩, by simp [point, return_norm_one],
        by simpa only [point, return_norm_one] using hvn.trans (by norm_num : (1 : ℝ) ≤ 2)⟩
    have h := hunit _ U hu (v / r) hvn _ hstar
    rw [hrep _ (by norm_num [point]), hrep _ hspos] at h
    have hrv : r * (v / r) = v := by field_simp
    have hst : t * (s / t) = s := by field_simp
    simpa [point, hr2, hrv, hst] using h
  obtain ⟨C, hC, hsmooth⟩ := return_time_smooth
  refine ⟨C, hC, ?_⟩
  intro A F hF0 t s X v ht hs hs1 hv
  apply return_time_borel_of_smooth_tests hH hLE hlam hLam C hC.le A t s ht.le
    (by linarith) (X, v) ?_ F hF0
  intro G hG0 hG
  exact hsmooth A G hG0 hG t s X v ht hs hs1 hv

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

