module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.PropagationParametersBounds
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.AffineGeometryTopology
import PDEFoundation.Geometry.EuclideanBall.Topology
import Mathlib.Tactic
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.SkeletonApproximation
import PDEFoundation.Ambient.HilbertVec
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Group.Real
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.PropagationBlockQuadraticBounds
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelSource
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.BarrierSign
import Mathlib.Algebra.Order.Floor.Ring

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder
open Set MeasureTheory Filter
open scoped Topology


/-- The closure has precisely the weak time and Euclidean radius bounds needed for blocks. -/
theorem closure_backwardCylinder_bounds {d : ℕ} (P₀ : KineticPoint d) {R : ℝ}
    (hR : 0 < R) :
    closure (backwardCylinder P₀ R) ⊆
      {P | P₀.time - R ^ 2 ≤ P.time ∧ P.time ≤ P₀.time ∧
        PDE.vecEuclideanNorm (P.velocity - P₀.velocity) ≤ R ∧
        PDE.vecEuclideanNorm (relativePosition P₀ P) ≤ R ^ 3} := by
  have hx : Continuous (relativePosition P₀) := by
    unfold relativePosition
    exact (continuous_position.sub continuous_const).sub
      ((continuous_time.sub continuous_const).smul continuous_const)
  have hv : Continuous (fun P : KineticPoint d => P.velocity - P₀.velocity) :=
    continuous_velocity.sub continuous_const
  apply closure_minimal
  · intro P hP
    refine ⟨hP.1.le, hP.2.1.le, ?_, ?_⟩
    · exact ((PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hR).mp hP.2.2.1).le
    · have he := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (pow_pos hR 3)).mp hP.2.2.2
      simpa only [sub_zero] using he.le
  · exact (isClosed_le continuous_const continuous_time).inter
      ((isClosed_le continuous_time continuous_const).inter
        ((isClosed_le (PDE.continuous_vecEuclideanNorm.comp hv) continuous_const).inter
          (isClosed_le (PDE.continuous_vecEuclideanNorm.comp hx) continuous_const)))

/-- The block radius has its literal source time scale. -/
theorem propagation_block_radius_sq {h W : ℝ} (hh : 0 ≤ h) :
    (W * Real.sqrt h) ^ 2 = W ^ 2 * h := by rw [mul_pow, Real.sq_sqrt hh]

/-- The block radius has its literal source position scale. -/
theorem propagation_block_radius_cube {h W : ℝ} (hh : 0 ≤ h) :
    (W * Real.sqrt h) ^ 3 = W ^ 3 * h ^ (3 / 2 : ℝ) := by
  rw [mul_pow, Real.sqrt_eq_rpow, ← Real.rpow_natCast (h ^ (1 / 2 : ℝ)) 3,
    ← Real.rpow_mul hh]
  norm_num



/-- The tangent-line position error has exactly the source coefficient one half. -/
theorem skeleton_position_remainder_le {d : ℕ} {x v : ℝ → PDE.Vec d} {H : ℝ}
    (hv : Continuous v) (hkin : ∀ t, HasDerivAt x (v t) t)
    (hLip : ∀ s t, PDE.vecEuclideanNorm (v s - v t) ≤ H * |s - t|)
    (s b : ℝ) (hsb : s ≤ b) :
    PDE.vecEuclideanNorm (x s - x b - (s - b) • v b) ≤ H * (b - s) ^ 2 / 2 := by
  have hsk : IsSkeleton x v H s b :=
    ⟨hv.continuousOn, fun t _ => (hkin t).hasDerivWithinAt, fun t _ r _ => hLip t r⟩
  have hint : IntervalIntegrable (fun t => v t - v b) volume s b :=
    (hv.intervalIntegrable s b).sub intervalIntegrable_const
  have hI : (∫ t in s..b, v t - v b) = x b - x s - (b - s) • v b := by
    rw [intervalIntegral.integral_sub (hv.intervalIntegrable s b) intervalIntegrable_const,
      intervalIntegral.integral_const]
    rw [(hsk.position_eq_integral (show b ∈ Icc s b from ⟨hsb, le_rfl⟩))]
    abel_nf
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
  have he := e.toContinuousLinearMap.intervalIntegral_comp_comm hint
  change (∫ t in s..b, e (v t - v b)) = e (∫ t in s..b, v t - v b) at he
  have hc1 : Continuous (fun t => ‖e (v t - v b)‖) :=
    (e.continuous.comp (hv.sub continuous_const)).norm
  have hc2 : Continuous (fun t => H * (b - t)) := by fun_prop
  have hm := intervalIntegral.integral_mono_on (μ := volume) hsb (hc1.intervalIntegrable s b)
    (hc2.intervalIntegrable s b) (fun t ht => show ‖e (v t - v b)‖ ≤ H * (b - t) from by
      change ‖(v t - v b).toHilbertVec‖ ≤ H * (b - t)
      rw [← PDE.Vec.vecEuclideanNorm_eq_norm_toHilbertVec]
      have h := hLip t b
      rw [abs_of_nonpos (sub_nonpos.mpr ht.2)] at h
      simpa only [neg_sub] using h)
  have hid : IntervalIntegrable (fun t => t) volume s b :=
    continuous_id.intervalIntegrable s b
  have hi : (∫ t in s..b, H * (b - t)) = H * (b - s) ^ 2 / 2 := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub intervalIntegrable_const hid,
      intervalIntegral.integral_const, integral_id]
    simp only [smul_eq_mul]
    ring
  have hb := (intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := fun t => e (v t - v b)) hsb).trans (hm.trans_eq hi)
  rw [he] at hb
  have hneg : x s - x b - (s - b) • v b = -(x b - x s - (b - s) • v b) := by
    ext i
    simp only [Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hneg, PDE.vecEuclideanNorm_neg, ← hI, PDE.Vec.vecEuclideanNorm_eq_norm_toHilbertVec]
  exact hb



/-- The source block closure lies in the path tube with halved position and velocity radii. -/
theorem propagation_block_containment {d : ℕ} {lam Lam H T0 T1 kx kv h : ℝ}
    (hH : 0 ≤ H) (_hT0 : 0 < T0) (hT1 : T0 ≤ T1) (hkx : 0 < kx) (hkv : 0 < kv)
    (hh : 0 < h) (hhstar : h ≤ stepSize d lam Lam H T0 T1 kx kv)
    (tminus sblock TP : ℝ) (hsblock : 0 ≤ sblock) (hblock : sblock + h ≤ TP)
    {x v : ℝ → PDE.Vec d} (hv : Continuous v) (hkin : ∀ t, HasDerivAt x (v t) t)
    (hLip : ∀ s t, PDE.vecEuclideanNorm (v s - v t) ≤ H * |s - t|) :
    closure (backwardCylinder
      ⟨tminus + sblock + h, x (sblock + h), v (sblock + h)⟩
      (barrierW d lam Lam H T1 * Real.sqrt h)) ⊆
      corridor tminus (-T0) TP (kx / 2) (kv / 2) x v := by
  let W := barrierW d lam Lam H T1
  let b := sblock + h
  let R := W * Real.sqrt h
  let P₀ : KineticPoint d := ⟨tminus + sblock + h, x b, v b⟩
  have hW : 0 < W := lt_of_lt_of_le (by norm_num) (two_le_barrierW hH)
  have hR : 0 < R := mul_pos hW (Real.sqrt_pos.mpr hh)
  have htime := propagation_step_time hH hh hhstar
  have hhT1 : h ≤ T1 := by linarith only [htime.2, hT1, hh]
  have hsqrt := Real.sqrt_le_sqrt hhT1
  have hhalf : h ≤ Real.sqrt T1 * Real.sqrt h := by
    calc
      h = Real.sqrt h * Real.sqrt h := by nlinarith only [Real.sq_sqrt hh.le]
      _ ≤ Real.sqrt T1 * Real.sqrt h :=
        mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg h)
  have hpower : h ^ 2 = h ^ (3 / 2 : ℝ) * Real.sqrt h := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hh]
    norm_num
  have hthree : h ^ 2 ≤ Real.sqrt T1 * h ^ (3 / 2 : ℝ) := by
    rw [hpower]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hsqrt (Real.rpow_nonneg hh.le _)
  intro P hP
  let s := P.time - tminus
  obtain ⟨htlo, htup, hvel, hpos⟩ := closure_backwardCylinder_bounds P₀ hR hP
  have hdelta : 0 ≤ b - s ∧ b - s ≤ W ^ 2 * h := by
    rw [propagation_block_radius_sq hh.le] at htlo
    change tminus + sblock + h - W ^ 2 * h ≤ P.time at htlo
    change P.time ≤ tminus + sblock + h at htup
    dsimp only [b, s]
    constructor <;> linarith only [htlo, htup]
  have hs : s ∈ Icc (-T0) TP := by
    have hb : b ≤ TP := hblock
    have ht : W ^ 2 * h ≤ T0 := htime.1
    constructor <;> dsimp only [b] at * <;> linarith only [hdelta.1, hdelta.2, hb, ht, hsblock, hh]
  have hvelEq : P.velocity - v s = (P.velocity - v b) + (v b - v s) := by abel
  have hvelPath := hLip b s
  rw [abs_of_nonneg hdelta.1] at hvelPath
  have hvelTotal : PDE.vecEuclideanNorm (P.velocity - v s) ≤ R + H * (b - s) := by
    rw [hvelEq]
    exact (PDE.vecEuclideanNorm_add_le _ _).trans (add_le_add hvel hvelPath)
  have hvelTube : PDE.vecEuclideanNorm (P.velocity - v s) ≤
      velocityTubeConstant d lam Lam H T1 * Real.sqrt h := by
    calc
      _ ≤ R + H * (W ^ 2 * h) := hvelTotal.trans
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left hdelta.2 hH))
      _ ≤ R + (H * W ^ 2) * (Real.sqrt T1 * Real.sqrt h) := by
        apply add_le_add le_rfl
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hhalf
          (mul_nonneg hH (sq_nonneg W))
      _ = _ := by dsimp only [R, W, velocityTubeConstant]; ring
  have hposEq : P.position - x s = relativePosition P₀ P +
      (-(x s - x b - (s - b) • v b)) := by
    ext i
    simp only [relativePosition, P₀, Pi.sub_apply, Pi.add_apply, Pi.neg_apply,
      Pi.smul_apply, smul_eq_mul]
    dsimp only [s, b]
    ring
  have hposTotal : PDE.vecEuclideanNorm (P.position - x s) ≤ R ^ 3 + H * (b - s) ^ 2 / 2 := by
    rw [hposEq]
    exact (PDE.vecEuclideanNorm_add_le _ _).trans
      (add_le_add hpos (by simpa only [PDE.vecEuclideanNorm_neg] using (skeleton_position_remainder_le hv hkin hLip s b (sub_nonneg.mp hdelta.1))))
  have hdeltaSq : (b - s) ^ 2 ≤ (W ^ 2 * h) ^ 2 :=
    (sq_le_sq₀ hdelta.1 (mul_nonneg (sq_nonneg W) hh.le)).mpr hdelta.2
  have hposTube : PDE.vecEuclideanNorm (P.position - x s) ≤
      positionTubeConstant d lam Lam H T1 * h ^ (3 / 2 : ℝ) := by
    calc
      _ ≤ R ^ 3 + H * (W ^ 2 * h) ^ 2 / 2 := hposTotal.trans
        (add_le_add le_rfl (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hdeltaSq hH) (by norm_num)))
      _ = W ^ 3 * h ^ (3 / 2 : ℝ) + (H * W ^ 4 / 2) * h ^ 2 := by
        rw [propagation_block_radius_cube hh.le]
        ring
      _ ≤ W ^ 3 * h ^ (3 / 2 : ℝ) +
          (H * W ^ 4 / 2) * (Real.sqrt T1 * h ^ (3 / 2 : ℝ)) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hthree (by positivity))
      _ = _ := by dsimp only [W, positionTubeConstant]; ring
  exact ⟨hs, hposTube.trans (propagation_step_position hH hkx hh hhstar),
    hvelTube.trans (propagation_step_velocity hH hkv hh hhstar)⟩


/-- The source damping coefficient is nonnegative under positive ellipticity. -/
theorem Xi_nonneg (d : ℕ) {lam Lam H h : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hh : 0 < h) : 0 ≤ Xi d lam Lam H h := by
  have hLam0 : 0 ≤ Lam := (hlam.trans_le hLam).le
  unfold Xi
  positivity

/-- Positivity of the whole-carrier barrier forces the definite strip and the source q bound. -/
theorem gaussianBarrier_pos_quadratic {d : ℕ} {lam h : ℝ} (hlam : 0 < lam) (hh : 0 < h)
    (Lam H L ell tminus sblock : ℝ) (hLam : lam ≤ Lam) (hell : 0 ≤ ell)
    (hbudget : Xi d lam Lam H h * h ≤ L ^ 2 / 4)
    (x v : ℝ → PDE.Vec d) (P : KineticPoint d)
    (hpos : 0 < gaussianBarrier lam Lam H h L ell tminus sblock x v P) :
    -(h / 128) < P.time - tminus - sblock ∧
      qform lam h (P.time - tminus - sblock)
        (P.position - x (P.time - tminus)) (P.velocity - v (P.time - tminus)) <
        (513 / 512 : ℝ) * L ^ 2 := by
  let sigma := P.time - tminus - sblock
  have hs : -(1 / 128 : ℝ) < sigma / h := by
    by_contra hn
    unfold gaussianBarrier at hpos
    rw [ite_eq_right hn] at hpos
    exact lt_irrefl 0 hpos
  have hs' : -(h / 128) < sigma := by
    linarith only [((lt_div_iff₀ hh).mp hs)]
  have hXi : 0 ≤ Xi d lam Lam H h := Xi_nonneg d hlam hLam hh
  rw [gaussianBarrier_eq_formula] at hpos
  dsimp only [gaussianFormula] at hpos
  have hG := pos_of_mul_pos_right hpos (mul_nonneg hell (barrierCutoff_bounds (sigma / h)).1)
  constructor
  · exact hs'
  · change qform lam h sigma (P.position - x (P.time - tminus))
      (P.velocity - v (P.time - tminus)) < (513 / 512 : ℝ) * L ^ 2
    linarith only [(Real.exp_lt_exp.mp (sub_pos.mp hG)), (mul_le_mul_of_nonneg_left hs'.le hXi), hbudget]

/-- The covariance upper bound turns the source q bound into both scaled Euclidean bounds. -/
theorem qform_scaled_norm_bounds {d : ℕ} {lam h sigma L : ℝ}
    (hlam : 0 < lam) (hh : 0 < h) (hL : 0 ≤ L) (hs : -(h / 128) ≤ sigma)
    (ht : |sigma / h| ≤ 1) (y V : PDE.Vec d)
    (hq : qform lam h sigma y V ≤ (513 / 512 : ℝ) * L ^ 2) :
    PDE.vecEuclideanNorm ((h ^ (3 / 2 : ℝ))⁻¹ • y) ≤ (3 / 2 : ℝ) * L * Real.sqrt lam ∧
      PDE.vecEuclideanNorm ((h ^ (1 / 2 : ℝ))⁻¹ • V) ≤ (3 / 2 : ℝ) * L * Real.sqrt lam := by
  let Y := (h ^ (3 / 2 : ℝ))⁻¹ • y
  let U := (h ^ (1 / 2 : ℝ))⁻¹ • V
  let C := (3 / 2 : ℝ) * L * Real.sqrt lam
  have hC : 0 ≤ C := by positivity
  have hq' := mul_le_mul_of_nonneg_left hq (show 0 ≤ 2 * lam by positivity)
  have hupper : PDE.vecNormSq Y + PDE.vecNormSq U ≤ C ^ 2 := by
    apply (qform_scaled_normSq_le hlam hh hs ht y V).trans (hq'.trans ?_)
    dsimp only [C]
    rw [mul_pow, mul_pow, Real.sq_sqrt hlam.le]
    nlinarith only [mul_nonneg hlam.le (sq_nonneg L)]
  constructor
  · apply (sq_le_sq₀ (PDE.vecEuclideanNorm_nonneg Y) hC).mp
    rw [PDE.vecEuclideanNorm_sq]
    linarith only [hupper, PDE.vecNormSq_nonneg U]
  · apply (sq_le_sq₀ (PDE.vecEuclideanNorm_nonneg U) hC).mp
    rw [PDE.vecEuclideanNorm_sq]
    linarith only [hupper, PDE.vecNormSq_nonneg Y]

/-- Undoing a positive scalar scaling preserves the native Euclidean radius bound exactly. -/
theorem vecEuclideanNorm_le_of_scaled {d : ℕ} {a C : ℝ} (ha : 0 < a)
    (y : PDE.Vec d) (h : PDE.vecEuclideanNorm (a⁻¹ • y) ≤ C) :
    PDE.vecEuclideanNorm y ≤ C * a := by
  rw [PDE.vecEuclideanNorm_smul, abs_of_pos (inv_pos.mpr ha)] at h
  simpa only [← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul, mul_comm a C] using (mul_le_mul_of_nonneg_left h ha.le)

/-- Both native Euclidean coordinates obey the exact source positivity-set radii. -/
theorem gaussianBarrier_positive_set {d : ℕ} {lam h : ℝ} (hlam : 0 < lam) (hh : 0 < h)
    (Lam H L ell tminus sblock : ℝ) (hLam : lam ≤ Lam) (hell : 0 ≤ ell) (hL : 0 ≤ L)
    (hbudget : Xi d lam Lam H h * h ≤ L ^ 2 / 4)
    (x v : ℝ → PDE.Vec d) (P : KineticPoint d)
    (hs1 : P.time - tminus - sblock ≤ h)
    (hpos : 0 < gaussianBarrier lam Lam H h L ell tminus sblock x v P) :
    PDE.vecEuclideanNorm (P.position - x (P.time - tminus)) ≤
      (3 / 2 : ℝ) * L * Real.sqrt lam * h ^ (3 / 2 : ℝ) ∧
    PDE.vecEuclideanNorm (P.velocity - v (P.time - tminus)) ≤
      (3 / 2 : ℝ) * L * Real.sqrt lam * Real.sqrt h := by
  obtain ⟨hs0, hq⟩ := gaussianBarrier_pos_quadratic hlam hh Lam H L ell tminus sblock
    hLam hell hbudget x v P hpos
  have ht0 : -(1 / 128 : ℝ) < (P.time - tminus - sblock) / h := by
    apply (lt_div_iff₀ hh).mpr
    linarith only [hs0]
  have ht1 : (P.time - tminus - sblock) / h ≤ 1 := (div_le_one hh).mpr hs1
  have ht : |(P.time - tminus - sblock) / h| ≤ 1 :=
    abs_le.mpr ⟨by linarith only [ht0], ht1⟩
  obtain ⟨hy, hV⟩ := qform_scaled_norm_bounds hlam hh hL hs0.le ht _ _ hq.le
  constructor
  · exact vecEuclideanNorm_le_of_scaled (Real.rpow_pos_of_pos hh _)
      (P.position - x (P.time - tminus)) hy
  · have he := vecEuclideanNorm_le_of_scaled (Real.rpow_pos_of_pos hh _)
      (P.velocity - v (P.time - tminus)) hV
    rwa [← Real.sqrt_eq_rpow] at he



/-- Positivity puts the Gaussian strictly inside the velocity and position block faces. -/
theorem gaussianBarrier_positive_lateral {d : ℕ} (hd : 1 ≤ d)
    {lam Lam H T0 T1 kx kv h ell : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hH : 0 ≤ H) (hT0 : 0 < T0) (hT1 : T0 ≤ T1) (hh : 0 < h)
    (hhstar : h ≤ stepSize d lam Lam H T0 T1 kx kv) (hell : 0 ≤ ell)
    (tminus sblock : ℝ) {x v : ℝ → PDE.Vec d} (hv : Continuous v)
    (hkin : ∀ t, HasDerivAt x (v t) t)
    (hLip : ∀ s t, PDE.vecEuclideanNorm (v s - v t) ≤ H * |s - t|)
    (P : KineticPoint d)
    (hP : P ∈ closure (backwardCylinder
      ⟨tminus + sblock + h, x (sblock + h), v (sblock + h)⟩
      (barrierW d lam Lam H T1 * Real.sqrt h)))
    (hpos : 0 < gaussianBarrier lam Lam H h (barrierL d lam Lam H T1)
      ell tminus sblock x v P) :
    P.velocity ∈ PDE.euclideanBall (v (sblock + h))
        (barrierW d lam Lam H T1 * Real.sqrt h) ∧
      relativePosition ⟨tminus + sblock + h, x (sblock + h), v (sblock + h)⟩ P ∈
        PDE.euclideanBall (0 : PDE.Vec d) ((barrierW d lam Lam H T1 * Real.sqrt h) ^ 3) := by
  let L := barrierL d lam Lam H T1
  let W := barrierW d lam Lam H T1
  let C := (3 / 2 : ℝ) * L * Real.sqrt lam
  let b := sblock + h
  let s := P.time - tminus
  let R := W * Real.sqrt h
  let P₀ : KineticPoint d := ⟨tminus + sblock + h, x b, v b⟩
  have hW2 : 2 ≤ W := two_le_barrierW hH
  have hW : 0 < W := by linarith only [hW2]
  have hR : 0 < R := mul_pos hW (Real.sqrt_pos.mpr hh)
  have hbudget := propagation_step_damping hd hlam hLam hH hT0 hT1 hh hhstar
  have ht := (closure_backwardCylinder_bounds P₀ hR hP).2.1
  have hs1 : P.time - tminus - sblock ≤ h := by
    change P.time ≤ tminus + sblock + h at ht
    linarith only [ht]
  obtain ⟨hs0, _⟩ := gaussianBarrier_pos_quadratic hlam hh Lam H L ell tminus sblock
    hLam hell hbudget x v P hpos
  obtain ⟨hy, hV⟩ := gaussianBarrier_positive_set hlam hh Lam H L ell tminus sblock
    hLam hell (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hbudget x v P hs1 hpos
  have hdelta : 0 ≤ b - s ∧ b - s ≤ 2 * h := by
    dsimp only [b, s]
    constructor <;> linarith only [hs0, hs1, hh]
  have hhT1 : h ≤ T1 := by
    have he := (propagation_step_time hH hh hhstar).2
    linarith only [he, hT1, hh]
  have hhalf : h ≤ Real.sqrt T1 * Real.sqrt h := by
    have he := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hhT1) (Real.sqrt_nonneg h)
    nlinarith only [he, Real.sq_sqrt hh.le]
  have hthree : h ^ 2 ≤ Real.sqrt T1 * h ^ (3 / 2 : ℝ) := by
    have he : h ^ 2 = h ^ (3 / 2 : ℝ) * Real.sqrt h := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hh]
      norm_num
    rw [he]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt hhT1) (Real.rpow_nonneg hh.le _)
  have hpathv := hLip s b
  rw [abs_sub_comm, abs_of_nonneg hdelta.1] at hpathv
  have hveq : P.velocity - v b = (P.velocity - v s) + (v s - v b) := by abel
  have hvbound : PDE.vecEuclideanNorm (P.velocity - v b) ≤
      (C + 2 * H * Real.sqrt T1) * Real.sqrt h := by
    rw [hveq]
    apply (PDE.vecEuclideanNorm_add_le _ _).trans
    calc
      _ ≤ C * Real.sqrt h + H * (b - s) := add_le_add hV hpathv
      _ ≤ C * Real.sqrt h + H * (2 * h) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hdelta.2 hH)
      _ ≤ C * Real.sqrt h + (2 * H) * (Real.sqrt T1 * Real.sqrt h) := by
        nlinarith only [(mul_le_mul_of_nonneg_left hhalf (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hH))]
      _ = _ := by ring
  have hrel : relativePosition P₀ P = (P.position - x s) +
      (x s - x b - (s - b) • v b) := by
    ext i
    simp only [relativePosition, P₀, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    dsimp only [b, s]
    ring
  have hdeltaSq : (b - s) ^ 2 ≤ (2 * h) ^ 2 :=
    (sq_le_sq₀ hdelta.1 (by positivity)).mpr hdelta.2
  have hxb : PDE.vecEuclideanNorm (relativePosition P₀ P) ≤
      (C + 2 * H * Real.sqrt T1) * h ^ (3 / 2 : ℝ) := by
    rw [hrel]
    apply (PDE.vecEuclideanNorm_add_le _ _).trans
    calc
      _ ≤ C * h ^ (3 / 2 : ℝ) + H * (b - s) ^ 2 / 2 := add_le_add hy (skeleton_position_remainder_le hv hkin hLip s b (sub_nonneg.mp hdelta.1))
      _ ≤ C * h ^ (3 / 2 : ℝ) + H * (2 * h) ^ 2 / 2 :=
        add_le_add le_rfl (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hdeltaSq hH) (by norm_num))
      _ = C * h ^ (3 / 2 : ℝ) + (2 * H) * h ^ 2 := by ring
      _ ≤ C * h ^ (3 / 2 : ℝ) + (2 * H) * (Real.sqrt T1 * h ^ (3 / 2 : ℝ)) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hthree (by positivity))
      _ = _ := by ring
  have hCW : C + 2 * H * Real.sqrt T1 < W := by dsimp only [C, L, W, barrierW]; linarith
  have hcube : W ≤ W ^ 3 := by
    have hsq : 1 ≤ W ^ 2 := by nlinarith only [hW2]
    nlinarith only [mul_nonneg hW.le (sub_nonneg.mpr hsq)]
  constructor
  · apply (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hR).mpr
    exact hvbound.trans_lt (mul_lt_mul_of_pos_right hCW (Real.sqrt_pos.mpr hh))
  · apply (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (pow_pos hR 3)).mpr
    rw [sub_zero, propagation_block_radius_cube hh.le]
    exact hxb.trans_lt (mul_lt_mul_of_pos_right (hCW.trans_le hcube)
      (Real.rpow_pos_of_pos hh _))

/-- The Gaussian is nonpositive on the entire kinetic boundary of a source block. -/
theorem gaussianBarrier_nonpos_boundary {d : ℕ} (hd : 1 ≤ d)
    {lam Lam H T0 T1 kx kv h ell : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hH : 0 ≤ H) (hT0 : 0 < T0) (hT1 : T0 ≤ T1) (hh : 0 < h)
    (hhstar : h ≤ stepSize d lam Lam H T0 T1 kx kv) (hell : 0 ≤ ell)
    (tminus sblock : ℝ) {x v : ℝ → PDE.Vec d} (hv : Continuous v)
    (hkin : ∀ t, HasDerivAt x (v t) t)
    (hLip : ∀ s t, PDE.vecEuclideanNorm (v s - v t) ≤ H * |s - t|)
    (P : KineticPoint d)
    (hP : P ∈ kineticBoundary
      ⟨tminus + sblock + h, x (sblock + h), v (sblock + h)⟩
      (barrierW d lam Lam H T1 * Real.sqrt h)) :
    gaussianBarrier lam Lam H h (barrierL d lam Lam H T1)
      ell tminus sblock x v P ≤ 0 := by
  by_contra hn
  have hp := lt_of_not_ge hn
  obtain ⟨hc, hb⟩ := mem_kineticBoundary_iff.mp hP
  obtain ⟨hvball, hxball⟩ := gaussianBarrier_positive_lateral hd hlam hLam hH hT0 hT1
    hh hhstar hell tminus sblock hv hkin hLip P hc hp
  rcases hb with ht | hvface | ⟨hxface, _⟩
  · have hbudget := propagation_step_damping hd hlam hLam hH hT0 hT1 hh hhstar
    rw [propagation_block_radius_sq hh.le] at ht
    change P.time = tminus + sblock + h - barrierW d lam Lam H T1 ^ 2 * h at ht
    have he : 4 * h ≤ barrierW d lam Lam H T1 ^ 2 * h := by
      have hw : 4 ≤ barrierW d lam Lam H T1 ^ 2 := by nlinarith only [(two_le_barrierW (d := d) (lam := lam) (Lam := Lam) (T1 := T1) hH)]
      exact mul_le_mul_of_nonneg_right hw hh.le
    linarith only [ht, ((gaussianBarrier_pos_quadratic hlam hh Lam H (barrierL d lam Lam H T1) ell tminus sblock hLam hell hbudget x v P hp).1), he, hh]
  · exact (ne_of_lt hvball) hvface
  · exact (ne_of_lt hxball) hxface



/-- A smooth test with zero localized source and controlled kinetic boundary lies below u. -/
theorem admissible_test_le_of_zero_source {d : ℕ} {A : FullKineticCoefficient d}
    {O : Set (KineticPoint d)} {p C_A : ℝ} {u psi : KineticPoint d → ℝ}
    (hu : IsAdmissibleSupersolution A O p C_A u) (P₀ : KineticPoint d) {R : ℝ} (hR : 0 < R)
    (hQO : closure (backwardCylinder P₀ R) ⊆ O)
    (hpsi : IsSmoothNear psi (closure (backwardCylinder P₀ R)))
    (hboundary : ∀ P ∈ kineticBoundary P₀ R, psi P ≤ u P)
    (hsource : localizedSource A psi u =ᵐ[volume.restrict (backwardCylinder P₀ R)] 0) :
    ∀ P ∈ closure (backwardCylinder P₀ R), psi P ≤ u P := by
  have hnorm : eLpNorm (localizedSource A psi u) (ENNReal.ofReal p)
      (volume.restrict (backwardCylinder P₀ R)) = 0 := by
    rw [eLpNorm_congr_ae hsource, eLpNorm_zero]
  have hsup : sSup ((fun P => max (psi P - u P) 0) '' kineticBoundary P₀ R) ≤ 0 := by
    apply csSup_le ((kineticBoundary_nonempty P₀ hR).image _)
    rintro _ ⟨P, hP, rfl⟩
    exact max_le (sub_nonpos.mpr (hboundary P hP)) le_rfl
  have hbounded := (isCompact_closure_backwardCylinder P₀ R hR).bddAbove_image
    (hpsi.continuousOn.sub (hu.1.mono hQO))
  intro P hP
  have hpoint := (le_csSup hbounded (mem_image_of_mem (fun T => psi T - u T) hP)).trans
    (hu.2 P₀ R hR hQO psi hpsi)
  rw [hnorm, ENNReal.toReal_zero, mul_zero, add_zero] at hpoint
  exact sub_nonpos.mp (hpoint.trans hsup)




/-- Initial-strip comparison and the multiplied sign annihilate the localized source. -/
theorem gaussianBarrier_localizedSource_zero {d : ℕ} {lam h R : ℝ}
    (hlam : 0 < lam) (hh : 0 < h) (hR : 0 < R) (Lam H L ell tminus sblock : ℝ)
    (hLam : lam ≤ Lam) (hH : 0 ≤ H) (hell : 0 ≤ ell)
    (A : FullKineticCoefficient d) (hA : FullElliptic lam Lam A)
    {x v : ℝ → PDE.Vec d} (hx : ContDiff ℝ (⊤ : ℕ∞) x)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hkin : ∀ s, HasDerivAt x (v s) s)
    (hLip : ∀ s t, PDE.vecEuclideanNorm (v s - v t) ≤ H * |s - t|)
    (u : KineticPoint d → ℝ)
    (hinit : ∀ P ∈ closure (backwardCylinder
      ⟨tminus + sblock + h, x (sblock + h), v (sblock + h)⟩ R),
      P.time - tminus - sblock ≤ 0 →
      gaussianBarrier lam Lam H h L ell tminus sblock x v P ≤ u P) :
    localizedSource A (gaussianBarrier lam Lam H h L ell tminus sblock x v) u
      =ᵐ[volume.restrict (backwardCylinder
        ⟨tminus + sblock + h, x (sblock + h), v (sblock + h)⟩ R)] 0 := by
  let S := {P : KineticPoint d | 0 < P.time - tminus - sblock ∧
    P.time - tminus - sblock ≤ h}
  have ht : Continuous (fun P : KineticPoint d => P.time - tminus - sblock) :=
    (continuous_time.sub continuous_const).sub continuous_const
  have hS : MeasurableSet S :=
    (isOpen_lt continuous_const ht).measurableSet.inter
      (isClosed_le ht continuous_const).measurableSet
  have hs := (ae_restrict_iff' hS).mp
    (gaussianBarrier_sign hlam hh Lam H L ell tminus sblock hLam hH hell A hA
      hx hv hkin hLip)
  let Q := backwardCylinder
    (⟨tminus + sblock + h, x (sblock + h), v (sblock + h)⟩ : KineticPoint d) R
  have hQ : MeasurableSet Q := (isOpen_backwardCylinder _ R hR).measurableSet
  filter_upwards [hs.filter_mono (ae_restrict_le (μ := volume) (s := Q)),
    ae_restrict_mem hQ] with P hsign hP
  by_cases hp : u P < gaussianBarrier lam Lam H h L ell tminus sblock x v P
  · have hc := subset_closure hP
    have hpositive : 0 < P.time - tminus - sblock := by
      by_contra hn
      exact (not_lt_of_ge (hinit P hc (le_of_not_gt hn))) hp
    have hupper := (closure_backwardCylinder_bounds
      (⟨tminus + sblock + h, x (sblock + h), v (sblock + h)⟩ : KineticPoint d)
      hR hc).2.1
    have hmem : P ∈ S := ⟨hpositive, by change P.time ≤ tminus + sblock + h at hupper
                                        linarith only [hupper]⟩
    have hnonpos := (hsign hmem).1.trans (hsign hmem).2
    rw [localizedSource, Set.indicator_of_mem (show P ∈ {Q | u Q <
      gaussianBarrier lam Lam H h L ell tminus sblock x v Q} from hp)]
    exact max_eq_right hnonpos
  · rw [localizedSource, Set.indicator_of_notMem (show P ∉ {Q | u Q <
      gaussianBarrier lam Lam H h L ell tminus sblock x v Q} from hp)]
    rfl



/-- Initial-strip comparison propagates throughout the source block in the halved tube. -/
theorem propagation_one_block {d : ℕ} (hd : 1 ≤ d)
    {lam Lam H T0 T1 kx kv h ell : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hH : 0 ≤ H) (hT0 : 0 < T0) (hT1 : T0 ≤ T1) (hkx : 0 < kx) (hkv : 0 < kv)
    (hh : 0 < h) (hhstar : h ≤ stepSize d lam Lam H T0 T1 kx kv) (hell : 0 ≤ ell)
    (A : FullKineticCoefficient d) (hA : FullElliptic lam Lam A)
    (O : Set (KineticPoint d)) (tminus sblock TP : ℝ)
    (hsblock : 0 ≤ sblock) (hblock : sblock + h ≤ TP)
    {x v : ℝ → PDE.Vec d} (hx : ContDiff ℝ (⊤ : ℕ∞) x)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hkin : ∀ s, HasDerivAt x (v s) s)
    (hLip : ∀ s t, PDE.vecEuclideanNorm (v s - v t) ≤ H * |s - t|)
    (htube : corridor tminus (-T0) TP (kx / 2) (kv / 2) x v ⊆ O)
    {p C_A : ℝ} (u : KineticPoint d → ℝ) (hnonneg : ∀ P ∈ O, 0 ≤ u P)
    (hu : IsAdmissibleSupersolution A O p C_A u)
    (hinit : ∀ P ∈ closure (backwardCylinder
      ⟨tminus + sblock + h, x (sblock + h), v (sblock + h)⟩
      (barrierW d lam Lam H T1 * Real.sqrt h)),
      P.time - tminus - sblock ≤ 0 →
      gaussianBarrier lam Lam H h (barrierL d lam Lam H T1)
        ell tminus sblock x v P ≤ u P) :
    ∀ P ∈ closure (backwardCylinder
      ⟨tminus + sblock + h, x (sblock + h), v (sblock + h)⟩
      (barrierW d lam Lam H T1 * Real.sqrt h)),
      gaussianBarrier lam Lam H h (barrierL d lam Lam H T1)
        ell tminus sblock x v P ≤ u P  := by
  have gaussianBarrier_isSmoothNear {d : ℕ} (L : ℝ) (ell : ℝ) (tminus : ℝ) (sblock : ℝ) {x : ℝ → PDE.Vec d} {v : ℝ → PDE.Vec d} (hx : ContDiff ℝ (⊤ : ℕ∞) x) (hv : ContDiff ℝ (⊤ : ℕ∞) v) (E : Set (KineticPoint d)) :
      IsSmoothNear (gaussianBarrier lam Lam H h L ell tminus sblock x v) E := by
    refine ⟨univ, isOpen_univ, subset_univ E, ?_⟩
    exact (contDiff_raw_gaussianBarrier hlam hh Lam H L ell tminus sblock hx hv).contDiffOn
  let R := barrierW d lam Lam H T1 * Real.sqrt h
  let P₀ : KineticPoint d :=
    ⟨tminus + sblock + h, x (sblock + h), v (sblock + h)⟩
  have hR : 0 < R := mul_pos
    (lt_of_lt_of_le (by norm_num) (two_le_barrierW hH)) (Real.sqrt_pos.mpr hh)
  have hQO := (propagation_block_containment hH hT0 hT1 hkx hkv hh hhstar
    tminus sblock TP hsblock hblock hv.continuous hkin hLip).trans htube
  apply admissible_test_le_of_zero_source hu P₀ hR hQO
    (gaussianBarrier_isSmoothNear (barrierL d lam Lam H T1)
      ell tminus sblock hx hv _)
  · intro P hP
    exact (gaussianBarrier_nonpos_boundary hd hlam hLam hH hT0 hT1 hh hhstar
      hell tminus sblock hv.continuous hkin hLip P hP).trans
      (hnonneg P (hQO (mem_kineticBoundary_iff.mp hP).1))
  · exact gaussianBarrier_localizedSource_zero hlam hh hR Lam H
      (barrierL d lam Lam H T1) ell tminus sblock hLam hH hell A hA
      hx hv hkin hLip u hinit


/-- Before the block starts its positive Gaussian height is at most the source loss factor. -/
theorem gaussianBarrier_initial_upper {d : ℕ} {lam h : ℝ}
    (hlam : 0 < lam) (hh : 0 < h) (Lam H L ell tminus sblock : ℝ)
    (hLam : lam ≤ Lam) (hell : 0 ≤ ell)
    (hbudget : Xi d lam Lam H h * h ≤ L ^ 2 / 4)
    (x v : ℝ → PDE.Vec d) (P : KineticPoint d)
    (_ht : P.time - tminus - sblock ≤ 0) :
    gaussianBarrier lam Lam H h L ell tminus sblock x v P ≤
      ell * Real.exp (L ^ 2 / 512) := by
  by_cases hp : 0 < gaussianBarrier lam Lam H h L ell tminus sblock x v P
  · have hs := (gaussianBarrier_pos_quadratic hlam hh Lam H L ell tminus sblock
      hLam hell hbudget x v P hp).1
    have hq := qform_nonneg hlam hh hs.le
      (P.position - x (P.time - tminus)) (P.velocity - v (P.time - tminus))
    have hXi := Xi_nonneg d (H := H) hlam hLam hh
    have htime := mul_le_mul_of_nonneg_left hs.le hXi
    have hexp : Real.exp (-Xi d lam Lam H h * (P.time - tminus - sblock) -
        qform lam h (P.time - tminus - sblock)
          (P.position - x (P.time - tminus)) (P.velocity - v (P.time - tminus))) ≤
        Real.exp (L ^ 2 / 512) := by
      apply Real.exp_le_exp.mpr
      linarith only [htime, hbudget, hq]
    rw [gaussianBarrier_eq_formula]
    dsimp only [gaussianFormula]
    have hc := barrierCutoff_bounds ((P.time - tminus - sblock) / h)
    have hg : 0 ≤ Real.exp (-Xi d lam Lam H h * (P.time - tminus - sblock) -
        qform lam h (P.time - tminus - sblock)
          (P.position - x (P.time - tminus)) (P.velocity - v (P.time - tminus))) -
        Real.exp (-L ^ 2) := by
      rw [gaussianBarrier_eq_formula] at hp
      dsimp only [gaussianFormula] at hp
      exact (pos_of_mul_pos_right hp (mul_nonneg hell hc.1)).le
    calc
      _ ≤ ell * (Real.exp (-Xi d lam Lam H h * (P.time - tminus - sblock) -
          qform lam h (P.time - tminus - sblock)
            (P.position - x (P.time - tminus)) (P.velocity - v (P.time - tminus))) -
          Real.exp (-L ^ 2)) := by
        have he := mul_le_mul_of_nonneg_right hc.2 hell
        nlinarith only [mul_le_mul_of_nonneg_right he hg]
      _ ≤ ell * Real.exp (L ^ 2 / 512) :=
        mul_le_mul_of_nonneg_left
          ((sub_le_self _ (Real.exp_pos _).le).trans hexp) hell
  · exact (le_of_not_gt hp).trans (mul_nonneg hell (Real.exp_pos _).le)

/-- In the terminal half-height ellipsoid the Gaussian dominates the source block height. -/
theorem gaussianBarrier_terminal_lower {d : ℕ} {lam h : ℝ}
    (hh : 0 < h) (Lam H L ell tminus sblock : ℝ) (hell : 0 ≤ ell)
    (hXi : 0 ≤ Xi d lam Lam H h) (hbudget : Xi d lam Lam H h * h ≤ L ^ 2 / 4)
    (x v : ℝ → PDE.Vec d) (P : KineticPoint d)
    (hs : 0 ≤ P.time - tminus - sblock) (ht : P.time - tminus - sblock ≤ h)
    (hq : qform lam h (P.time - tminus - sblock)
      (P.position - x (P.time - tminus)) (P.velocity - v (P.time - tminus)) ≤ L ^ 2 / 2) :
    ell * barrierCb L ≤ gaussianBarrier lam Lam H h L ell tminus sblock x v P := by
  rw [gaussianBarrier_eq_formula]
  dsimp only [gaussianFormula]
  rw [barrierCutoff_one (div_nonneg hs hh.le), mul_one]
  apply mul_le_mul_of_nonneg_left _ hell
  unfold barrierCb
  apply sub_le_sub_right
  apply Real.exp_le_exp.mpr
  have he := (mul_le_mul_of_nonneg_left ht hXi).trans hbudget
  linarith only [he, hq]



/-- Interior spatial coordinates and the closed terminal time belong to the cylinder closure. -/
theorem mem_closure_backwardCylinder_of_strict_spatial {d : ℕ}
    (P₀ P : KineticPoint d) {R : ℝ} (_hR : 0 < R)
    (htlo : P₀.time - R ^ 2 < P.time) (htup : P.time ≤ P₀.time)
    (hv : P.velocity ∈ PDE.euclideanBall P₀.velocity R)
    (hx : relativePosition P₀ P ∈ PDE.euclideanBall (0 : PDE.Vec d) (R ^ 3)) :
    P ∈ closure (backwardCylinder P₀ R) := by
  by_cases ht : P.time < P₀.time
  · exact subset_closure ⟨htlo, ht, hv, hx⟩
  have heq : P.time = P₀.time := le_antisymm htup (le_of_not_gt ht)
  let f : ℝ → KineticPoint d := fun r =>
    ⟨P.time + r, P.position + r • P₀.velocity, P.velocity⟩
  have hf : Continuous f := KineticPoint.continuous_mk
    (continuous_const.add continuous_id)
    (continuous_const.add (continuous_id.smul continuous_const)) continuous_const
  have hf0 : f 0 = P := by simp [f]
  have hlimit : Tendsto f (𝓝[<] (0 : ℝ)) (𝓝 P) :=
    hf0 ▸ hf.continuousAt.tendsto.mono_left inf_le_left
  apply mem_closure_of_tendsto hlimit
  have hcont : ContinuousAt (fun r => P.time + r) 0 :=
    continuousAt_const.add continuousAt_id
  have hlow : ∀ᶠ r in 𝓝[<] (0 : ℝ), P₀.time - R ^ 2 < P.time + r :=
    hcont.eventually
      (lt_mem_nhds (by simpa only [add_zero] using htlo)) |>.filter_mono inf_le_left
  filter_upwards [hlow, self_mem_nhdsWithin] with r hr hneg
  refine ⟨hr, ?_, hv, ?_⟩
  · change P.time + r < P₀.time
    rw [heq]
    change r < 0 at hneg
    linarith only [hneg]
  · have hrel : relativePosition P₀ (f r) = relativePosition P₀ P := by
      ext i
      simp only [relativePosition, f, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    simpa only [hrel] using hx



/-- An initial-strip positive point lies strictly inside the preceding block spatial faces. -/
theorem gaussianBarrier_initial_previous_spatial {d : ℕ} (hd : 1 ≤ d)
    {lam Lam H T0 T1 kx kv h ell : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hH : 0 ≤ H) (hT0 : 0 < T0) (hT1 : T0 ≤ T1) (hh : 0 < h)
    (hhstar : h ≤ stepSize d lam Lam H T0 T1 kx kv) (hell : 0 ≤ ell)
    (tminus sblock : ℝ) {x v : ℝ → PDE.Vec d} (hv : Continuous v)
    (hkin : ∀ t, HasDerivAt x (v t) t)
    (hLip : ∀ s t, PDE.vecEuclideanNorm (v s - v t) ≤ H * |s - t|)
    (P : KineticPoint d)
    (ht : P.time - tminus - sblock ≤ 0)
    (hpos : 0 < gaussianBarrier lam Lam H h (barrierL d lam Lam H T1)
      ell tminus sblock x v P) :
    P.velocity ∈ PDE.euclideanBall (v sblock)
        (barrierW d lam Lam H T1 * Real.sqrt h) ∧
      relativePosition ⟨tminus + sblock, x sblock, v sblock⟩ P ∈
        PDE.euclideanBall (0 : PDE.Vec d) ((barrierW d lam Lam H T1 * Real.sqrt h) ^ 3) := by
  let L := barrierL d lam Lam H T1
  let W := barrierW d lam Lam H T1
  let C := (3 / 2 : ℝ) * L * Real.sqrt lam
  let b := sblock
  let s := P.time - tminus
  let R := W * Real.sqrt h
  let P₀ : KineticPoint d := ⟨tminus + sblock, x b, v b⟩
  have hW2 : 2 ≤ W := two_le_barrierW hH
  have hW : 0 < W := by linarith only [hW2]
  have hR : 0 < R := mul_pos hW (Real.sqrt_pos.mpr hh)
  have hbudget := propagation_step_damping hd hlam hLam hH hT0 hT1 hh hhstar
  obtain ⟨hs0, _⟩ := gaussianBarrier_pos_quadratic hlam hh Lam H L ell tminus sblock
    hLam hell hbudget x v P hpos
  obtain ⟨hy, hV⟩ := gaussianBarrier_positive_set hlam hh Lam H L ell tminus sblock
    hLam hell (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hbudget x v P (ht.trans hh.le) hpos
  have hdelta : 0 ≤ b - s ∧ b - s ≤ 2 * h := by
    dsimp only [b, s]
    constructor <;> linarith only [hs0, ht, hh]
  have hhT1 : h ≤ T1 := by
    have he := (propagation_step_time hH hh hhstar).2
    linarith only [he, hT1, hh]
  have hhalf : h ≤ Real.sqrt T1 * Real.sqrt h := by
    have he := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hhT1) (Real.sqrt_nonneg h)
    nlinarith only [he, Real.sq_sqrt hh.le]
  have hthree : h ^ 2 ≤ Real.sqrt T1 * h ^ (3 / 2 : ℝ) := by
    have he : h ^ 2 = h ^ (3 / 2 : ℝ) * Real.sqrt h := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hh]
      norm_num
    rw [he]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt hhT1) (Real.rpow_nonneg hh.le _)
  have hpathv := hLip s b
  rw [abs_sub_comm, abs_of_nonneg hdelta.1] at hpathv
  have hveq : P.velocity - v b = (P.velocity - v s) + (v s - v b) := by abel
  have hvbound : PDE.vecEuclideanNorm (P.velocity - v b) ≤
      (C + 2 * H * Real.sqrt T1) * Real.sqrt h := by
    rw [hveq]
    apply (PDE.vecEuclideanNorm_add_le _ _).trans
    calc
      _ ≤ C * Real.sqrt h + H * (b - s) := add_le_add hV hpathv
      _ ≤ C * Real.sqrt h + H * (2 * h) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hdelta.2 hH)
      _ ≤ C * Real.sqrt h + (2 * H) * (Real.sqrt T1 * Real.sqrt h) := by
        have he := mul_le_mul_of_nonneg_left hhalf (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hH)
        nlinarith only [he]
      _ = _ := by ring
  have hrel : relativePosition P₀ P = (P.position - x s) +
      (x s - x b - (s - b) • v b) := by
    ext i
    simp only [relativePosition, P₀, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    dsimp only [b, s]
    ring
  have hrem := skeleton_position_remainder_le hv hkin hLip s b (sub_nonneg.mp hdelta.1)
  have hdeltaSq : (b - s) ^ 2 ≤ (2 * h) ^ 2 :=
    (sq_le_sq₀ hdelta.1 (by positivity)).mpr hdelta.2
  have hxb : PDE.vecEuclideanNorm (relativePosition P₀ P) ≤
      (C + 2 * H * Real.sqrt T1) * h ^ (3 / 2 : ℝ) := by
    rw [hrel]
    apply (PDE.vecEuclideanNorm_add_le _ _).trans
    calc
      _ ≤ C * h ^ (3 / 2 : ℝ) + H * (b - s) ^ 2 / 2 := add_le_add hy hrem
      _ ≤ C * h ^ (3 / 2 : ℝ) + H * (2 * h) ^ 2 / 2 :=
        add_le_add le_rfl (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hdeltaSq hH) (by norm_num))
      _ = C * h ^ (3 / 2 : ℝ) + (2 * H) * h ^ 2 := by ring
      _ ≤ C * h ^ (3 / 2 : ℝ) + (2 * H) * (Real.sqrt T1 * h ^ (3 / 2 : ℝ)) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hthree (by positivity))
      _ = _ := by ring
  have hCW : C + 2 * H * Real.sqrt T1 < W := by dsimp only [C, L, W, barrierW]; linarith
  have hcube : W ≤ W ^ 3 := by
    have hsq : 1 ≤ W ^ 2 := by nlinarith only [hW2]
    nlinarith only [mul_nonneg hW.le (sub_nonneg.mpr hsq)]
  constructor
  · apply (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hR).mpr
    exact hvbound.trans_lt (mul_lt_mul_of_pos_right hCW (Real.sqrt_pos.mpr hh))
  · apply (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (pow_pos hR 3)).mpr
    rw [sub_zero, propagation_block_radius_cube hh.le]
    exact hxb.trans_lt (mul_lt_mul_of_pos_right (hCW.trans_le hcube)
      (Real.rpow_pos_of_pos hh _))



/-- The source overlap contraction gives both preceding-block membership and height control. -/
theorem gaussianBarrier_overlap_compare {d : ℕ} (hd : 1 ≤ d)
    {lam Lam H T0 T1 kx kv h ell : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hH : 0 ≤ H) (hT0 : 0 < T0) (hT1 : T0 ≤ T1) (hh : 0 < h)
    (hhstar : h ≤ stepSize d lam Lam H T0 T1 kx kv) (hell : 0 ≤ ell)
    (tminus sblock : ℝ) {x v : ℝ → PDE.Vec d} (hv : Continuous v)
    (hkin : ∀ t, HasDerivAt x (v t) t)
    (hLip : ∀ s t, PDE.vecEuclideanNorm (v s - v t) ≤ H * |s - t|)
    (P : KineticPoint d) (ht : P.time - tminus - sblock ≤ 0)
    (hp : 0 < gaussianBarrier lam Lam H h (barrierL d lam Lam H T1)
      (barrierGamma (barrierL d lam Lam H T1) * ell) tminus sblock x v P) :
    P ∈ closure (backwardCylinder ⟨tminus + sblock, x sblock, v sblock⟩
      (barrierW d lam Lam H T1 * Real.sqrt h)) ∧
      gaussianBarrier lam Lam H h (barrierL d lam Lam H T1)
        (barrierGamma (barrierL d lam Lam H T1) * ell) tminus sblock x v P ≤
      gaussianBarrier lam Lam H h (barrierL d lam Lam H T1)
        ell tminus (sblock - h) x v P := by
  let L := barrierL d lam Lam H T1
  let W := barrierW d lam Lam H T1
  let sigma := P.time - tminus - sblock
  have hL : 0 < L := barrierL_pos hd hlam hLam (hT0.le.trans hT1)
  have hgamma := (barrierGamma_bounds hL).1
  have hell' : 0 ≤ barrierGamma L * ell := mul_nonneg hgamma.le hell
  have hbudget := propagation_step_damping hd hlam hLam hH hT0 hT1 hh hhstar
  obtain ⟨hs, hq⟩ := gaussianBarrier_pos_quadratic hlam hh Lam H L
    (barrierGamma L * ell) tminus sblock hLam hell' hbudget x v P hp
  obtain ⟨hvball, hxball⟩ := gaussianBarrier_initial_previous_spatial hd hlam hLam
    hH hT0 hT1 hh hhstar hell' tminus sblock hv hkin hLip P ht hp
  have hW := two_le_barrierW (d := d) (lam := lam) (Lam := Lam) (T1 := T1) hH
  have hR : 0 < W * Real.sqrt h := mul_pos (by linarith only [hW])
    (Real.sqrt_pos.mpr hh)
  constructor
  · apply mem_closure_backwardCylinder_of_strict_spatial _ P hR _ _ hvball hxball
    · rw [propagation_block_radius_sq hh.le]
      change tminus + sblock - W ^ 2 * h < P.time
      have he : 4 * h ≤ W ^ 2 * h :=
        mul_le_mul_of_nonneg_right (by nlinarith only [hW]) hh.le
      linarith only [hs, he, hh]
    · change P.time ≤ tminus + sblock
      linarith only [ht]
  · have hqover := qform_overlap hlam hh hs.le ht
      (P.position - x (P.time - tminus)) (P.velocity - v (P.time - tminus))
    have hqhalf : qform lam h (sigma + h)
        (P.position - x (P.time - tminus)) (P.velocity - v (P.time - tminus)) ≤ L ^ 2 / 2 := by
      have he := mul_le_mul_of_nonneg_left hq.le (by norm_num : (0 : ℝ) ≤ 13 / 50)
      nlinarith only [hqover, he, sq_nonneg L]
    have hs' : 0 ≤ P.time - tminus - (sblock - h) := by linarith only [hs, hh]
    have ht' : P.time - tminus - (sblock - h) ≤ h := by linarith only [ht]
    have hq' : qform lam h (P.time - tminus - (sblock - h))
        (P.position - x (P.time - tminus)) (P.velocity - v (P.time - tminus)) ≤ L ^ 2 / 2 := by
      have he : P.time - tminus - (sblock - h) = sigma + h := by
        dsimp only [sigma]
        ring
      rw [he]
      exact hqhalf
    have hlower := gaussianBarrier_terminal_lower hh Lam H L ell tminus (sblock - h)
      hell (Xi_nonneg d (H := H) hlam hLam hh) hbudget x v P hs' ht' hq'
    have hupper := gaussianBarrier_initial_upper hlam hh Lam H L (barrierGamma L * ell)
      tminus sblock hLam hell' hbudget x v P ht
    have heq : barrierGamma L * ell * Real.exp (L ^ 2 / 512) = ell * barrierCb L := by
      unfold barrierGamma
      have hexp : Real.exp (-L ^ 2 / 512) * Real.exp (L ^ 2 / 512) = 1 := by
        rw [← Real.exp_add]
        have he : -L ^ 2 / 512 + L ^ 2 / 512 = 0 := by ring
        rw [he, Real.exp_zero]
      calc
        _ = ell * barrierCb L *
          (Real.exp (-L ^ 2 / 512) * Real.exp (L ^ 2 / 512)) := by ring
        _ = _ := by rw [hexp, mul_one]
    exact (hupper.trans_eq heq).trans hlower



/-- A uniformly close path's halved corridor lies in the original full corridor. -/
theorem corridor_half_subset_of_approximation {d : ℕ}
    (tminus a b kx kv eps : ℝ) (x v y w : ℝ → PDE.Vec d)
    (hex : eps ≤ kx / 2) (hev : eps ≤ kv / 2)
    (hclose : ∀ s ∈ Icc a b, PDE.vecEuclideanNorm (y s - x s) < eps ∧
      PDE.vecEuclideanNorm (w s - v s) < eps) :
    corridor tminus a b (kx / 2) (kv / 2) y w ⊆ corridor tminus a b kx kv x v := by
  intro P hP
  obtain ⟨ht, hx, hv⟩ := hP
  have hc := hclose (P.time - tminus) ht
  refine ⟨ht, ?_, ?_⟩
  · have heq : P.position - x (P.time - tminus) =
        (P.position - y (P.time - tminus)) + (y (P.time - tminus) - x (P.time - tminus)) :=
      by abel
    rw [heq]
    apply (PDE.vecEuclideanNorm_add_le _ _).trans
    linarith only [hx, hc.1, hex]
  · have heq : P.velocity - v (P.time - tminus) =
        (P.velocity - w (P.time - tminus)) + (w (P.time - tminus) - v (P.time - tminus)) :=
      by abel
    rw [heq]
    apply (PDE.vecEuclideanNorm_add_le _ _).trans
    linarith only [hv, hc.2, hev]


/-- Cancelling a positive spatial scale preserves the Euclidean endpoint allowance. -/
theorem endpoint_scaled_norm_le {d : ℕ} {a C : ℝ} (ha : 0 < a)
    (y : PDE.Vec d) (hy : PDE.vecEuclideanNorm y ≤ C * a) :
    PDE.vecEuclideanNorm (a⁻¹ • y) ≤ C := by
  rw [PDE.vecEuclideanNorm_smul, abs_of_pos (inv_pos.mpr ha)]
  have he := mul_le_mul_of_nonneg_left hy (inv_nonneg.mpr ha.le)
  have heq : a⁻¹ * (C * a) = C := by field_simp
  exact he.trans_eq heq

/-- The source one-eighth endpoint allowance gives q_h at most L squared over two. -/
theorem qform_endpoint_half {d : ℕ} {lam h L : ℝ}
    (hlam : 0 < lam) (hh : 0 < h) (hL : 0 ≤ L) (y V : PDE.Vec d)
    (hy : PDE.vecEuclideanNorm y ≤ (L * Real.sqrt lam / 8) * h ^ (3 / 2 : ℝ))
    (hV : PDE.vecEuclideanNorm V ≤ (L * Real.sqrt lam / 8) * Real.sqrt h) :
    qform lam h h y V ≤ L ^ 2 / 2 := by
  let C := L * Real.sqrt lam / 8
  have hC : 0 ≤ C := by positivity
  have hy' := endpoint_scaled_norm_le (Real.rpow_pos_of_pos hh (3 / 2 : ℝ)) y hy
  have hV' := endpoint_scaled_norm_le (Real.sqrt_pos.mpr hh) V hV
  rw [Real.sqrt_eq_rpow] at hV'
  have hysq := (sq_le_sq₀ (PDE.vecEuclideanNorm_nonneg _) hC).mpr hy'
  have hVsq := (sq_le_sq₀ (PDE.vecEuclideanNorm_nonneg _) hC).mpr hV'
  rw [PDE.vecEuclideanNorm_sq] at hysq hVsq
  have he := qform_endpoint_upper hlam hh y V
  have hn : PDE.vecNormSq ((h ^ (3 / 2 : ℝ))⁻¹ • y) +
      PDE.vecNormSq ((h ^ (1 / 2 : ℝ))⁻¹ • V) ≤ 2 * C ^ 2 := by
    linarith only [hysq, hVsq]
  apply he.trans ((mul_le_mul_of_nonneg_left hn (by positivity)).trans ?_)
  dsimp only [C]
  rw [div_pow, mul_pow, Real.sq_sqrt hlam.le]
  have hl : lam ≠ 0 := hlam.ne'
  field_simp
  nlinarith only [sq_nonneg L]



/-- Successive source Gaussian blocks propagate their comparison through the halved tube. -/
theorem propagation_overlap_induction {d : ℕ} (hd : 1 ≤ d)
    {lam Lam H T0 T1 kx kv h ell TP : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hH : 0 ≤ H) (hT0 : 0 < T0) (hT1 : T0 ≤ T1) (hkx : 0 < kx) (hkv : 0 < kv)
    (hh : 0 < h) (hhstar : h ≤ stepSize d lam Lam H T0 T1 kx kv) (hell : 0 ≤ ell)
    (n : ℕ) (hnTP : (n : ℝ) * h ≤ TP)
    (A : FullKineticCoefficient d) (hA : FullElliptic lam Lam A)
    (O : Set (KineticPoint d)) (tminus : ℝ)
    {x v : ℝ → PDE.Vec d} (hx : ContDiff ℝ (⊤ : ℕ∞) x)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hkin : ∀ s, HasDerivAt x (v s) s)
    (hLip : ∀ s t, PDE.vecEuclideanNorm (v s - v t) ≤ H * |s - t|)
    (htube : corridor tminus (-T0) TP (kx / 2) (kv / 2) x v ⊆ O)
    {p C_A : ℝ} (u : KineticPoint d → ℝ) (hnonneg : ∀ P ∈ O, 0 ≤ u P)
    (hu : IsAdmissibleSupersolution A O p C_A u)
    (hinitial : ∀ P ∈ corridor tminus (-T0) TP (kx / 2) (kv / 2) x v,
      P.time ≤ tminus → ell ≤ u P) :
    ∀ k : ℕ, k < n → ∀ P ∈ closure (backwardCylinder
      ⟨tminus + (k : ℝ) * h + h, x ((k : ℝ) * h + h), v ((k : ℝ) * h + h)⟩
      (barrierW d lam Lam H T1 * Real.sqrt h)),
      gaussianBarrier lam Lam H h (barrierL d lam Lam H T1)
        ((barrierGamma (barrierL d lam Lam H T1)) ^ k *
          Real.exp (-(barrierL d lam Lam H T1) ^ 2 / 512) * ell)
        tminus ((k : ℝ) * h) x v P ≤ u P := by
  let L := barrierL d lam Lam H T1
  let gamma := barrierGamma L
  let a := fun k => gamma ^ k * Real.exp (-L ^ 2 / 512) * ell
  have hL : 0 < L := barrierL_pos (H := H) hd hlam hLam (hT0.le.trans hT1)
  have hgamma := (barrierGamma_bounds hL).1
  have ha : ∀ k, 0 ≤ a k := fun k =>
    mul_nonneg (mul_nonneg (pow_nonneg hgamma.le k) (Real.exp_pos _).le) hell
  have hstep : ∀ k, a (k + 1) = gamma * a k := by
    intro k
    dsimp only [a]
    rw [pow_succ]
    ring
  have hbudget := propagation_step_damping hd hlam hLam hH hT0 hT1 hh hhstar
  intro k
  induction k with
  | zero =>
    intro hkn
    simp only [Nat.cast_zero, zero_mul]
    have hb : h ≤ TP := by
      have he := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hkn) hh.le
      norm_num at he
      exact he.trans hnTP
    apply propagation_one_block hd hlam hLam hH hT0 hT1 hkx hkv hh hhstar (ha 0)
      A hA O tminus 0 TP (by norm_num) (by simpa only [zero_add] using hb)
      hx hv hkin hLip htube u hnonneg hu
    intro P hP ht
    have hcont := propagation_block_containment hH hT0 hT1 hkx hkv hh hhstar
      tminus 0 TP (by norm_num) (by
        have he := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hkn) hh.le
        norm_num at he ⊢
        exact he.trans hnTP) hv.continuous hkin hLip hP
    have hupper := gaussianBarrier_initial_upper hlam hh Lam H L (a 0) tminus 0
      hLam (ha 0) hbudget x v P ht
    have heq : a 0 * Real.exp (L ^ 2 / 512) = ell := by
      dsimp only [a]
      rw [pow_zero, one_mul, mul_comm _ ell, mul_assoc, ← Real.exp_add]
      simp only [neg_div, neg_add_cancel, Real.exp_zero, mul_one]
    exact (hupper.trans_eq heq).trans (hinitial P hcont (by linarith only [ht]))
  | succ k ih =>
    intro hkn
    have hk : k < n := Nat.lt_trans (Nat.lt_succ_self k) hkn
    have hb : ((k + 1 : ℕ) : ℝ) * h + h ≤ TP := by
      have he := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hkn) hh.le
      push_cast at he ⊢
      linarith only [he, hnTP]
    apply propagation_one_block hd hlam hLam hH hT0 hT1 hkx hkv hh hhstar (ha (k + 1))
      A hA O tminus (((k + 1 : ℕ) : ℝ) * h) TP (by positivity) hb
      hx hv hkin hLip htube u hnonneg hu
    intro P hP ht
    by_cases hp : 0 < gaussianBarrier lam Lam H h L (a (k + 1))
        tminus (((k + 1 : ℕ) : ℝ) * h) x v P
    · rw [hstep] at hp
      obtain ⟨hprev, hcompare⟩ := gaussianBarrier_overlap_compare hd hlam hLam hH hT0 hT1
        hh hhstar (ha k) tminus (((k + 1 : ℕ) : ℝ) * h)
        hv.continuous hkin hLip P ht hp
      have heq : ((k + 1 : ℕ) : ℝ) * h = (k : ℝ) * h + h := by push_cast; ring
      rw [heq, ← add_assoc] at hprev
      have hprevtime : ((k + 1 : ℕ) : ℝ) * h - h = (k : ℝ) * h := by
        rw [heq]
        ring
      rw [hprevtime] at hcompare
      rw [hstep]
      exact hcompare.trans (ih hk P hprev)
    · have hcont := propagation_block_containment hH hT0 hT1 hkx hkv hh hhstar
        tminus (((k + 1 : ℕ) : ℝ) * h) TP (by positivity) hb hv.continuous hkin hLip hP
      exact (le_of_not_gt hp).trans (hnonneg P (htube hcont))



/-- The source endpoint allowance closes propagation along a smooth approximating path. -/
theorem propagation_smooth_endpoint {d : ℕ} (hd : 1 ≤ d)
    {lam Lam H T0 T1 kx kv h ell TP : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hH : 0 ≤ H) (hT0 : 0 < T0) (hT1 : T0 ≤ T1) (hkx : 0 < kx) (hkv : 0 < kv)
    (hh : 0 < h) (hhstar : h ≤ stepSize d lam Lam H T0 T1 kx kv) (hell : 0 ≤ ell)
    (n : ℕ) (hn : 0 < n) (hnTP : (n : ℝ) * h = TP)
    (A : FullKineticCoefficient d) (hA : FullElliptic lam Lam A)
    (O : Set (KineticPoint d)) (tminus : ℝ)
    {x v : ℝ → PDE.Vec d} (hx : ContDiff ℝ (⊤ : ℕ∞) x)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hkin : ∀ s, HasDerivAt x (v s) s)
    (hLip : ∀ s t, PDE.vecEuclideanNorm (v s - v t) ≤ H * |s - t|)
    (htube : corridor tminus (-T0) TP (kx / 2) (kv / 2) x v ⊆ O)
    {p C_A : ℝ} (u : KineticPoint d → ℝ) (hnonneg : ∀ P ∈ O, 0 ≤ u P)
    (hu : IsAdmissibleSupersolution A O p C_A u)
    (hinitial : ∀ Q ∈ corridor tminus (-T0) TP (kx / 2) (kv / 2) x v,
      Q.time ≤ tminus → ell ≤ u Q)
    (P : KineticPoint d) (htime : P.time = tminus + TP)
    (hposition : PDE.vecEuclideanNorm (P.position - x TP) ≤
      (barrierL d lam Lam H T1 * Real.sqrt lam / 8) * h ^ (3 / 2 : ℝ))
    (hvelocity : PDE.vecEuclideanNorm (P.velocity - v TP) ≤
      (barrierL d lam Lam H T1 * Real.sqrt lam / 8) * Real.sqrt h) :
    (barrierGamma (barrierL d lam Lam H T1)) ^ n * ell ≤ u P := by
  let L := barrierL d lam Lam H T1
  let W := barrierW d lam Lam H T1
  let C := L * Real.sqrt lam / 8
  let a := (barrierGamma L) ^ (n - 1) * Real.exp (-L ^ 2 / 512) * ell
  have hL : 0 < L := barrierL_pos hd hlam hLam (hT0.le.trans hT1)
  have hg := (barrierGamma_bounds hL).1
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hW : 2 ≤ W := two_le_barrierW hH
  have hCW : C < W := by
    have he : 0 ≤ L * Real.sqrt lam := mul_nonneg hL.le (Real.sqrt_nonneg _)
    dsimp only [C, W, barrierW]
    linarith only [he, mul_nonneg hH (Real.sqrt_nonneg T1)]
  have hcube : W ≤ W ^ 3 := by
    have hw : 0 ≤ W := by linarith only [hW]
    have hw2 : 1 ≤ W ^ 2 := by nlinarith only [hW]
    nlinarith only [mul_nonneg hw (sub_nonneg.mpr hw2)]
  have hR : 0 < W * Real.sqrt h := mul_pos (by linarith only [hW])
    (Real.sqrt_pos.mpr hh)
  have hnstep : ((n - 1 : ℕ) : ℝ) * h + h = TP := by
    have he : n - 1 + 1 = n := Nat.sub_add_cancel hn
    have he' := congrArg (fun k : ℕ => (k : ℝ) * h) he
    push_cast at he'
    linarith only [he', hnTP]
  have hclosure : P ∈ closure (backwardCylinder
      ⟨tminus + ((n - 1 : ℕ) : ℝ) * h + h,
        x (((n - 1 : ℕ) : ℝ) * h + h), v (((n - 1 : ℕ) : ℝ) * h + h)⟩
      (W * Real.sqrt h)) := by
    rw [add_assoc tminus, hnstep]
    apply mem_closure_backwardCylinder_of_strict_spatial _ P hR
    · change tminus + TP - (W * Real.sqrt h) ^ 2 < P.time
      rw [htime]
      nlinarith only [sq_pos_of_pos hR]
    · change P.time ≤ tminus + TP
      exact htime.le
    · apply (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hR).mpr
      exact hvelocity.trans_lt (mul_lt_mul_of_pos_right hCW (Real.sqrt_pos.mpr hh))
    · apply (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (pow_pos hR 3)).mpr
      have hrel : relativePosition ⟨tminus + TP, x TP, v TP⟩ P = P.position - x TP := by
        simp only [relativePosition, htime, sub_self, zero_smul, sub_zero]
      rw [hrel, sub_zero, propagation_block_radius_cube hh.le]
      exact hposition.trans_lt
        (mul_lt_mul_of_pos_right (hCW.trans_le hcube) (Real.rpow_pos_of_pos hh _))
  have hcomparison := propagation_overlap_induction hd hlam hLam hH hT0 hT1 hkx hkv
    hh hhstar hell n hnTP.le A hA O tminus hx hv hkin hLip htube u hnonneg hu
    hinitial (n - 1) (Nat.sub_lt hn (by norm_num)) P hclosure
  have hbudget := propagation_step_damping hd hlam hLam hH hT0 hT1 hh hhstar
  have hs : P.time - tminus - ((n - 1 : ℕ) : ℝ) * h = h := by
    linarith only [htime, hnstep]
  have hPt : P.time - tminus = TP := by linarith only [htime]
  have hq := qform_endpoint_half hlam hh hL.le
    (P.position - x TP) (P.velocity - v TP) hposition hvelocity
  have hlower := gaussianBarrier_terminal_lower hh Lam H L a tminus
    (((n - 1 : ℕ) : ℝ) * h) ha (Xi_nonneg d (H := H) hlam hLam hh)
    hbudget x v P (by rw [hs]; exact hh.le) (by rw [hs]) (by rw [hs, hPt]; exact hq)
  have heq : a * barrierCb L = (barrierGamma L) ^ n * ell := by
    have hn' : n = (n - 1) + 1 := (Nat.sub_add_cancel hn).symm
    rw [hn', pow_succ]
    dsimp only [a, barrierGamma]
    ring
  exact (heq.symm ▸ hlower).trans hcomparison


/-- The source ceiling partition has steps between half the allowed size and the allowed size. -/
theorem propagation_ceiling_steps {hs TP T1 : ℝ} (hhs : 0 < hs) (hTP : hs ≤ TP)
    (hT1 : TP ≤ T1) :
    0 < Nat.ceil (TP / hs) ∧
      0 < TP / (Nat.ceil (TP / hs) : ℝ) ∧
      TP / (Nat.ceil (TP / hs) : ℝ) ≤ hs ∧
      hs / 2 ≤ TP / (Nat.ceil (TP / hs) : ℝ) ∧
      Nat.ceil (TP / hs) ≤ Nat.ceil (T1 / hs) ∧
      (Nat.ceil (TP / hs) : ℝ) * (TP / (Nat.ceil (TP / hs) : ℝ)) = TP := by
  have hTP0 := hhs.trans_le hTP
  have hn : 0 < Nat.ceil (TP / hs) := Nat.ceil_pos.mpr (div_pos hTP0 hhs)
  have hnr : 0 < (Nat.ceil (TP / hs) : ℝ) := Nat.cast_pos.mpr hn
  have hratio : 1 ≤ TP / hs := (le_div_iff₀ hhs).mpr (by simpa using hTP)
  have hlo := Nat.le_ceil (TP / hs)
  have hup := Nat.ceil_lt_add_one (div_pos hTP0 hhs).le
  have htwice : (Nat.ceil (TP / hs) : ℝ) ≤ 2 * (TP / hs) := by
    linarith only [hup, hratio]
  refine ⟨hn, div_pos hTP0 hnr, ?_, ?_, ?_, ?_⟩
  · apply (div_le_iff₀ hnr).mpr
    have he := (div_le_iff₀ hhs).mp hlo
    simpa only [mul_comm] using he
  · apply (le_div_iff₀ hnr).mpr
    have he := (le_div_iff₀ hhs).mp (by
      simpa only [mul_div_assoc] using htwice :
      (Nat.ceil (TP / hs) : ℝ) ≤ (2 * TP) / hs)
    nlinarith only [he]
  · exact Nat.ceil_mono (div_le_div_of_nonneg_right hT1 hhs.le)
  · field_simp



/-- The explicit source constant propagates along the original C-one-one skeleton. -/
theorem propagation_explicit (d : ℕ) (hd : 1 ≤ d) (lam Lam H T0 T1 kx kv : ℝ)
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (hH : 0 < H)
    (hkx : 0 < kx) (hkv : 0 < kv) (hT0 : 0 < T0) (hT1 : T0 ≤ T1)
    (p C_A : ℝ) (_hp : 1 ≤ p) (A : FullKineticCoefficient d)
    (hA : FullElliptic lam Lam A) (O : Set (KineticPoint d)) (_hO : IsOpen O)
    (tminus : ℝ) (P : KineticPoint d) (_hPO : P ∈ O)
    (hTP0 : T0 ≤ P.time - tminus) (hTP1 : P.time - tminus ≤ T1)
    (x v : ℝ → PDE.Vec d) (hsk : IsSkeleton x v H (-T0) (P.time - tminus))
    (hxP : x (P.time - tminus) = P.position) (hvP : v (P.time - tminus) = P.velocity)
    (htube : corridor tminus (-T0) (P.time - tminus) kx kv x v ⊆ O)
    (ell : ℝ) (hell : 0 ≤ ell) (u : KineticPoint d → ℝ)
    (hnonneg : ∀ Q ∈ O, 0 ≤ u Q) (hu : IsAdmissibleSupersolution A O p C_A u)
    (hinitial : ∀ Q ∈ corridor tminus (-T0) (P.time - tminus) kx kv x v,
      Q.time ≤ tminus → ell ≤ u Q) :
    (barrierGamma (barrierL d lam Lam H T1)) ^
      Nat.ceil (T1 / stepSize d lam Lam H T0 T1 kx kv) * ell ≤ u P := by
  let TP := P.time - tminus
  let hs := stepSize d lam Lam H T0 T1 kx kv
  let L := barrierL d lam Lam H T1
  let C := L * Real.sqrt lam / 8
  have hhs : 0 < hs := stepSize_pos hH.le hT0 hkx hkv
  have hhsTP : hs ≤ TP := by
    have he := (propagation_step_time hH.le hhs (le_refl hs)).2
    linarith only [he, hTP0, hhs]
  obtain ⟨hn, hh, hhstar, hhalf, hnstar, hnTP⟩ :=
    propagation_ceiling_steps hhs hhsTP hTP1
  let n := Nat.ceil (TP / hs)
  let h := TP / (n : ℝ)
  have hL : 0 < L := barrierL_pos hd hlam hLam (hT0.le.trans hT1)
  have hC : 0 < C := div_pos (mul_pos hL (Real.sqrt_pos.mpr hlam)) (by norm_num)
  let eps := min (kx / 2) (min (kv / 2)
    (min (C * (hs / 2) ^ (3 / 2 : ℝ)) (C * Real.sqrt (hs / 2))))
  have heps : 0 < eps := by dsimp only [eps]; positivity
  obtain ⟨y, w, hy, hw, hkin, hLip, hclose⟩ :=
    smooth_skeleton_approx x v H (-T0) TP (by linarith only [hT0, hTP0])
      hH.le hsk eps heps
  have hepsx : eps ≤ kx / 2 := min_le_left _ _
  have hepsv : eps ≤ kv / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hepspx : eps ≤ C * (hs / 2) ^ (3 / 2 : ℝ) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hepspv : eps ≤ C * Real.sqrt (hs / 2) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hcontain := corridor_half_subset_of_approximation tminus (-T0) TP kx kv eps
    x v y w hepsx hepsv hclose
  have hfinal := hclose TP ⟨by linarith only [hTP0, hT0], le_rfl⟩
  have hposition : PDE.vecEuclideanNorm (P.position - y TP) ≤ C * h ^ (3 / 2 : ℝ) := by
    rw [PDE.vecEuclideanNorm_sub_comm, ← hxP]
    apply hfinal.1.le.trans (hepspx.trans ?_)
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) hhalf (by norm_num)) hC.le
  have hvelocity : PDE.vecEuclideanNorm (P.velocity - w TP) ≤ C * Real.sqrt h := by
    rw [PDE.vecEuclideanNorm_sub_comm, ← hvP]
    exact hfinal.2.le.trans
      (hepspv.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hhalf) hC.le))
  have hendpoint := propagation_smooth_endpoint hd hlam hLam hH.le hT0 hT1 hkx hkv
    hh hhstar hell n hn hnTP A hA O tminus hy hw hkin hLip (hcontain.trans htube)
    u hnonneg hu (fun Q hQ ht => hinitial Q (hcontain hQ) ht) P
    (by dsimp only [TP]; ring) hposition hvelocity
  have hg := barrierGamma_bounds hL
  have hpow := pow_le_pow_of_le_one hg.1.le hg.2.le hnstar
  exact (mul_le_mul_of_nonneg_right hpow hell).trans hendpoint



/-- The source propagation constant is uniform over coefficients, domains and skeletons. -/
theorem propagation (d : ℕ) (hd : 1 ≤ d) (lam Lam : ℝ)
    (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (H kx kv T0 T1 : ℝ) (hH : 0 < H) (hkx : 0 < kx)
    (hkv : 0 < kv) (hT0 : 0 < T0) (hT1 : T0 ≤ T1) :
  ∃ cprop : ℝ, 0 < cprop ∧ cprop ≤ 1 ∧
    ∀ (p C_A : ℝ), 1 ≤ p →
    ∀ A : FullKineticCoefficient d, FullElliptic lam Lam A →
    ∀ O : Set (KineticPoint d), IsOpen O →
    ∀ (tminus : ℝ) (P : KineticPoint d), P ∈ O →
      T0 ≤ P.time-tminus → P.time-tminus ≤ T1 →
    ∀ x v : ℝ → PDE.Vec d,
      IsSkeleton x v H (-T0) (P.time-tminus) →
      x (P.time-tminus) = P.position → v (P.time-tminus) = P.velocity →
      corridor tminus (-T0) (P.time-tminus) kx kv x v ⊆ O →
    ∀ ell : ℝ, 0 ≤ ell →
    ∀ u : KineticPoint d → ℝ,
      (∀ Q ∈ O, 0 ≤ u Q) → IsAdmissibleSupersolution A O p C_A u →
      (∀ Q ∈ corridor tminus (-T0) (P.time-tminus) kx kv x v,
        Q.time ≤ tminus → ell ≤ u Q) → cprop*ell ≤ u P := by
  let L := barrierL d lam Lam H T1
  let hs := stepSize d lam Lam H T0 T1 kx kv
  have hL : 0 < L := barrierL_pos hd hlam hLam (hT0.le.trans hT1)
  have hg := barrierGamma_bounds hL
  refine ⟨(barrierGamma L) ^ Nat.ceil (T1 / hs), pow_pos hg.1 _,
    pow_le_one₀ hg.1.le hg.2.le, ?_⟩
  intro p C_A hp A hA O hO tminus P hPO hTP0 hTP1 x v hsk hxP hvP htube
    ell hell u hnonneg hu hinitial
  exact propagation_explicit d hd lam Lam H T0 T1 kx kv hlam hLam hH hkx hkv hT0 hT1
    p C_A hp A hA O hO tminus P hPO hTP0 hTP1 x v hsk hxP hvP htube
    ell hell u hnonneg hu hinitial







/-- The propagation constant depends only on the source dimensionless parameters. -/
theorem propagation_dimensionless
    (d : ℕ) (hd : 1 ≤ d) (lam Lam a0 b0 cx cv : ℝ)
    (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (ha0 : 0 < a0) (ha01 : a0 ≤ 1)
    (hb0 : 0 < b0) (hcx : 0 < cx) (hcv : 0 < cv) :
  ∃ cprop : ℝ, 0 < cprop ∧ cprop ≤ 1 ∧
    ∀ T1 : ℝ, 0 < T1 →
    ∀ (p C_A : ℝ), 1 ≤ p →
    ∀ A : FullKineticCoefficient d, FullElliptic lam Lam A →
    ∀ O : Set (KineticPoint d), IsOpen O →
    ∀ (tminus : ℝ) (P : KineticPoint d), P ∈ O →
      a0*T1 ≤ P.time-tminus → P.time-tminus ≤ T1 →
    ∀ x v : ℝ → PDE.Vec d,
      IsSkeleton x v (b0/Real.sqrt T1) (-a0*T1) (P.time-tminus) →
      x (P.time-tminus) = P.position → v (P.time-tminus) = P.velocity →
      corridor tminus (-a0*T1) (P.time-tminus)
        (cx*T1^(3/2 : ℝ)) (cv*Real.sqrt T1) x v ⊆ O →
    ∀ ell : ℝ, 0 ≤ ell →
    ∀ u : KineticPoint d → ℝ,
      (∀ Q ∈ O, 0 ≤ u Q) → IsAdmissibleSupersolution A O p C_A u →
      (∀ Q ∈ corridor tminus (-a0*T1) (P.time-tminus)
          (cx*T1^(3/2 : ℝ)) (cv*Real.sqrt T1) x v,
        Q.time ≤ tminus → ell ≤ u Q) → cprop*ell ≤ u P   := by
  have propagation_barrier_scaling (b : ℝ) {T : ℝ} (hT : 0 < T) :
      barrierL d lam Lam (b / Real.sqrt T) T = barrierL d lam Lam b 1 ∧
      barrierW d lam Lam (b / Real.sqrt T) T = barrierW d lam Lam b 1 := by
    have hs : Real.sqrt T ≠ 0 := (Real.sqrt_pos.mpr hT).ne'
    have he : (b / Real.sqrt T) ^ 2 * T = b ^ 2 := by
      rw [div_pow]
      calc
        _ = (b ^ 2 / (Real.sqrt T) ^ 2) * (Real.sqrt T) ^ 2 := by
          rw [Real.sq_sqrt hT.le]
        _ = b ^ 2 := div_mul_cancel₀ _ (pow_ne_zero 2 hs)
    have hmul : b / Real.sqrt T * Real.sqrt T = b := div_mul_cancel₀ b hs
    have hL : barrierL d lam Lam (b / Real.sqrt T) T = barrierL d lam Lam b 1 := by
      unfold barrierL XiStar
      rw [mul_assoc 2 ((b / Real.sqrt T) ^ 2) T, he]
      simp only [mul_one]
    refine ⟨hL, ?_⟩
    unfold barrierW
    rw [hL]
    have he' : 2 * (b / Real.sqrt T) * Real.sqrt T = 2 * b := by
      rw [mul_assoc, hmul]
    rw [he']
    simp only [Real.sqrt_one, mul_one]
  have propagation_step_scaling (a : ℝ) (b : ℝ) (hb : 0 ≤ b) (hcx : 0 ≤ cx) {T : ℝ} (hT : 0 < T) :
      stepSize d lam Lam (b / Real.sqrt T) (a * T) T
      (cx * T ^ (3 / 2 : ℝ)) (cv * Real.sqrt T) =
      T * stepSize d lam Lam b a 1 cx cv := by
    have propagation_tube_scaling :
        velocityTubeConstant d lam Lam (b / Real.sqrt T) T =
          velocityTubeConstant d lam Lam b 1 ∧
        positionTubeConstant d lam Lam (b / Real.sqrt T) T =
          positionTubeConstant d lam Lam b 1 := by
      have hW := (propagation_barrier_scaling b hT).2
      have hs : Real.sqrt T ≠ 0 := (Real.sqrt_pos.mpr hT).ne'
      have he : b / Real.sqrt T * Real.sqrt T = b := div_mul_cancel₀ b hs
      constructor
      · unfold velocityTubeConstant
        rw [hW]
        simp only [Real.sqrt_one, mul_one]
        have hm : b / Real.sqrt T * barrierW d lam Lam b 1 ^ 2 * Real.sqrt T =
            b * barrierW d lam Lam b 1 ^ 2 := by
          calc
            _ = (b / Real.sqrt T * Real.sqrt T) * barrierW d lam Lam b 1 ^ 2 := by ring
            _ = _ := by rw [he]
        rw [hm]
      · unfold positionTubeConstant
        rw [hW]
        simp only [Real.sqrt_one, mul_one]
        have hm : b / Real.sqrt T * barrierW d lam Lam b 1 ^ 4 * Real.sqrt T =
            b * barrierW d lam Lam b 1 ^ 4 := by
          calc
            _ = (b / Real.sqrt T * Real.sqrt T) * barrierW d lam Lam b 1 ^ 4 := by ring
            _ = _ := by rw [he]
        rw [hm]
    have hW := (propagation_barrier_scaling b hT).2
    obtain ⟨hc1, hc2⟩ := propagation_tube_scaling
    obtain ⟨_, hc2pos⟩ := tubeConstants_pos (d := d) (lam := lam) (Lam := Lam) (T1 := 1) hb
    have htime : a * T / barrierW d lam Lam b 1 ^ 2 =
        T * (a / barrierW d lam Lam b 1 ^ 2) := by ring
    have hvel : (cv * Real.sqrt T / (2 * velocityTubeConstant d lam Lam b 1)) ^ 2 =
        T * (cv / (2 * velocityTubeConstant d lam Lam b 1)) ^ 2 := by
      rw [div_pow, mul_pow, Real.sq_sqrt hT.le]
      ring
    have hpos : (cx * T ^ (3 / 2 : ℝ) / (2 * positionTubeConstant d lam Lam b 1)) ^
        (2 / 3 : ℝ) = T * (cx / (2 * positionTubeConstant d lam Lam b 1)) ^ (2 / 3 : ℝ) := by
      have he : cx * T ^ (3 / 2 : ℝ) / (2 * positionTubeConstant d lam Lam b 1) =
          (cx / (2 * positionTubeConstant d lam Lam b 1)) * T ^ (3 / 2 : ℝ) := by ring
      rw [he, Real.mul_rpow (div_nonneg hcx (by positivity))
        (Real.rpow_nonneg hT.le _), ← Real.rpow_mul hT.le]
      norm_num
      ring
    unfold stepSize
    rw [hW, hc1, hc2, htime, hvel, hpos]
    rw [mul_min_of_nonneg _ _ hT.le, mul_min_of_nonneg _ _ hT.le]
  let L := barrierL d lam Lam b0 1
  let hs := stepSize d lam Lam b0 a0 1 cx cv
  have hL : 0 < L := barrierL_pos hd hlam hLam (by norm_num)
  have hg := barrierGamma_bounds hL
  refine ⟨(barrierGamma L) ^ Nat.ceil (1 / hs), pow_pos hg.1 _,
    pow_le_one₀ hg.1.le hg.2.le, ?_⟩
  intro T1 hT1 p C_A hp A hA O hO tminus P hPO hTP0 hTP1 x v hsk hxP hvP htube
    ell hell u hnonneg hu hinitial
  have hsqrt : 0 < Real.sqrt T1 := Real.sqrt_pos.mpr hT1
  have hkx : 0 < cx * T1 ^ (3 / 2 : ℝ) :=
    mul_pos hcx (Real.rpow_pos_of_pos hT1 _)
  have hkv : 0 < cv * Real.sqrt T1 := mul_pos hcv hsqrt
  have hH : 0 < b0 / Real.sqrt T1 := div_pos hb0 hsqrt
  have hT0 : 0 < a0 * T1 := mul_pos ha0 hT1
  have hT01 : a0 * T1 ≤ T1 := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right ha01 hT1.le
  have hbarrier := (propagation_barrier_scaling b0 hT1).1
  have hstep := propagation_step_scaling a0 b0 hb0.le hcx.le hT1
  have hratio : T1 / (T1 * hs) = 1 / hs := by
    field_simp
  have hconstant :
      (barrierGamma (barrierL d lam Lam (b0 / Real.sqrt T1) T1)) ^
        Nat.ceil (T1 / stepSize d lam Lam (b0 / Real.sqrt T1) (a0 * T1) T1
          (cx * T1 ^ (3 / 2 : ℝ)) (cv * Real.sqrt T1)) =
      (barrierGamma L) ^ Nat.ceil (1 / hs) := by
    rw [hbarrier, hstep, hratio]
  have hresult := propagation_explicit d hd lam Lam (b0 / Real.sqrt T1) (a0 * T1) T1
    (cx * T1 ^ (3 / 2 : ℝ)) (cv * Real.sqrt T1) hlam hLam hH hkx hkv hT0 hT01
    p C_A hp A hA O hO tminus P hPO hTP0 hTP1 x v
    (by simpa only [neg_mul] using hsk) hxP hvP
    (by simpa only [neg_mul] using htube) ell hell u hnonneg hu
    (by simpa only [neg_mul] using hinitial)
  rw [hconstant] at hresult
  exact hresult

end HypoellipticAleksandrov.KineticAleksandrov.Holder

