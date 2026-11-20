module
public import HypoellipticAleksandrov.Parabolic.Transposition.MovingBarrier
public import HypoellipticAleksandrov.Parabolic.Transposition.Lift
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierIntervalGeometry
import HypoellipticAleksandrov.Parabolic.LocalGluing
import Mathlib

/-! # Lifts and barriers for the kinetic terminal problem

A single compactly supported lift of the terminal datum works on all the nested finite
slabs. Its source is compactly supported too, so is bounded by a multiple of `exp(t−T)`.
The time integral of this majorant stays bounded even as the lower time tends to `−∞`.
-/
@[expose] public noncomputable section
namespace HypoellipticAleksandrov.Parabolic.Transposition
open Hypoellipticity KineticAleksandrov KineticAleksandrov.Evolution Set Filter Metric
open scoped ContDiff Topology
variable {n : ℕ} {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n} {T : ℝ}

theorem terminal_lift (hΩ : IsOpen Ω) (hγ : Continuous γ) {F : BoundedBorel (EvolutionAmbientState n)}
    (hF : IsSmoothCompactTerminalDatum Ω γ T F) : ∃ H : Field (n+n), HasCompactSupport H.val ∧
      (∀ z : Plane n, (world n z).time = T → H.val z = F ((split n z).2)) ∧
      (∀ z : Plane n, (world n z).position ∉ movingDomain Ω γ (world n z).time → H.val z = 0) := by
  let slice y := (split n).symm (T,y)
  let K := slice '' tsupport F
  let W := (world n) ⁻¹' {p : KineticPoint n | p.position ∈ movingDomain Ω γ p.time}
  have hK : IsCompact K := hF.2.1.image ((split n).symm.continuous.comp (continuous_const.prodMk continuous_id))
  have hKW : K ⊆ W := by
    rintro z ⟨y,hy,rfl⟩
    change (split n (slice y)).2.1 ∈ movingDomain Ω γ (split n (slice y)).1
    simpa only [slice,ContinuousLinearEquiv.apply_symm_apply] using (hF.2.2 hy).1
  obtain ⟨r,hr⟩ := hK.isBounded.subset_ball 0
  obtain ⟨χ,hχ,hone,hsub⟩ := exists_smooth_cutoff_tsupport_subset hK (((isOpen_setOf_mem_movingDomain hΩ hγ).preimage (world n).continuous).inter (isOpen_ball (x := 0) (ε := r))) (subset_inter hKW hr)
  let H : Field (n+n) := ⟨fun z => χ z * F (split n z).2, hχ.mul (hF.1.comp (split n).contDiff.snd)⟩
  have hs : HasCompactSupport χ := isCompact_of_isClosed_isBounded (isClosed_tsupport χ) (isBounded_ball.subset (hsub.trans inter_subset_right))
  refine ⟨H, hs.mul_right, ?_,fun z hz => ?_⟩
  · intro z ht; change (split n z).1 = T at ht
    by_cases hy : (split n z).2 ∈ tsupport F
    · have eq : slice ((split n z).2) = z := by rw [show slice ((split n z).2) = (split n).symm (T,(split n z).2) from rfl, ← ht]; exact (split n).symm_apply_apply z
      have h1 := subset_of_mem_nhdsSet hone (show z ∈ K from ⟨_,hy,eq⟩)
      change χ z * _ = _; rw [h1,one_mul]
    · change χ z * F _ = F _; rw [image_eq_zero_of_notMem_tsupport hy,mul_zero]
  · have : z ∉ tsupport χ := fun h => hz (hsub h).1
    simp [H,image_eq_zero_of_notMem_tsupport this]

/-- The transported generator only differentiates a time profile once. -/
theorem time_op (B : FullKineticCoefficient n) (b : PDE.Vec n → PDE.Vec n) (q : ℝ → ℝ) (p : KineticPoint n) :
    transportedForwardOperator B b (fun p => q p.time) p = deriv q p.time := by
  have grad (y : PDE.Vec n) : PDE.classicalGradient (fun _ : PDE.Vec n => q p.time) y = 0 := by ext i; simp [PDE.classicalGradient]
  simp [transportedForwardOperator, kineticTimeDerivative, diffusedHessian, kineticPositionGradient, kineticVelocityGradient, grad, matrixContraction, PDE.vecDot]

abbrev Realizes (X : Fin (n+1) → Vector (n+n)) (B : FullKineticCoefficient n) (b : PDE.Vec n → PDE.Vec n) :=
  ∀ (u : KineticPoint n → ℝ) (z : Plane n), ContDiffAt ℝ 2 (u ∘ world n) z →
    generator X (u ∘ world n) z = transportedForwardOperator B b u (world n z)

variable {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}

private theorem time_generator {X} (op : Realizes X B b) (q : ℝ → ℝ) (hq : ContDiff ℝ ∞ q) (z : Plane n) :
    generator X (fun w => q (split n w).1) z = deriv q (split n z).1 :=
  (op (fun p => q p.time) z ((hq.comp (split n).contDiff.fst).contDiffAt.of_le (by simp))).trans (time_op B b q _)

theorem time_barrier {X} (op : Realizes X B b) (H : Field (n+n)) (hs : HasCompactSupport H.val) (T : ℝ) :
    ∃ (C : ℝ) (f : Field (n+n)) (M : Plane n → ℝ), 0 ≤ C ∧ Continuous M ∧
      (∀ z : Plane n, (world n z).time = T → f.val z = 0) ∧
      ∀ z : Plane n, (world n z).time ≤ T → 0 ≤ M z ∧ M z ≤ C ∧ |generator X H.val z| ≤ M z ∧
        0 ≤ f.val z ∧ f.val z ≤ C ∧ generator X f.val z ≤ -M z := by
  let w (z : Plane n) := Real.exp (T - (split n z).1)
  obtain ⟨C,hC⟩ := HasCompactSupport.exists_bound_of_continuous ((source_of_lift X H hs).mul_right (f' := w))
    ((generator_sm X H.prop).continuous.mul (Real.continuous_exp.comp (continuous_const.sub (split n).continuous.fst)))
  let q t := C * (1 - Real.exp (t-T))
  have hq : ContDiff ℝ ∞ q := contDiff_const.mul (contDiff_const.sub (Real.contDiff_exp.comp (contDiff_id.sub contDiff_const)))
  have C0 := (norm_nonneg _).trans (hC 0)
  refine ⟨C,⟨_,hq.comp (split n).contDiff.fst⟩,fun z => C * Real.exp ((split n z).1-T),C0,by fun_prop,?_,?_⟩
  · intro z ht; change (split n z).1 = T at ht; change q ((split n z).1) = 0; rw [ht]; simp [q]
  · intro z ht; change (split n z).1 ≤ T at ht
    let t := (split n z).1
    have he : Real.exp (t-T) ≤ 1 := Real.exp_le_one_iff.mpr (sub_nonpos.mpr ht)
    have hp := Real.exp_pos (t-T)
    have h : |generator X H.val z| * Real.exp (T-t) ≤ C := by simpa only [Pi.mul_apply,Real.norm_eq_abs,abs_mul,w,abs_of_pos (Real.exp_pos _)] using hC z
    have der := (((hasDerivAt_id t).sub_const T).exp.const_sub 1).const_mul C
    refine ⟨mul_nonneg C0 hp.le,mul_le_of_le_one_right C0 he,?_, mul_nonneg C0 (sub_nonneg.mpr he), mul_le_of_le_one_right C0 (by linarith), ?_⟩
    · simpa only [mul_assoc,← Real.exp_add,sub_add_sub_cancel,sub_self,Real.exp_zero,mul_one] using mul_le_mul_of_nonneg_right h hp.le
    · change generator X (fun w => q (split n w).1) z ≤ _; rw [time_generator op q hq]; change deriv q t ≤ _
      rw [show deriv q t = _ from der.deriv]; change C * -(Real.exp (t-T) * 1) ≤ -(C * Real.exp (t-T)); simp

theorem lateral_barrier (hn : 0 < n) (hΩ : IsAdmissibleEvolutionDomain Ω) (hγ : IsContinuousPiecewiseC1 γ) {lam Lam a M : ℝ}
    (hT : a < T) (hlam : 0 < lam) (hM : 0 ≤ M) (hell : HasEverywhereLoewnerBounds lam Lam B) : ∃ g, LateralBarrier Ω γ a T M B b g := by
  rcases eq_univ_or_exists_euclideanBall_of_isAdmissibleEvolutionDomain hΩ with rfl | ⟨c,r,hr,rfl⟩
  · let q t := M*(T-t)
    refine ⟨fun p => q p.time, continuous_const.mul (continuous_const.sub continuous_time),fun p hp => mul_nonneg hM (sub_nonneg.mpr hp.2.1.le),fun p hp => ?_,?_⟩
    · rw [show movingDomain univ γ p.time = univ from Set.eq_univ_of_forall fun y => mem_movingDomain_iff.mpr (mem_univ _),frontier_univ] at hp; exact hp.elim
    · intro ε hε; refine ⟨fun p => q p.time,show ContDiff ℝ ∞ (fun z => M*(T-(split n z).1)) from contDiff_const.mul (contDiff_const.sub (split n).contDiff.fst),fun p hp => ⟨mul_nonneg hM (sub_nonneg.mpr hp.2.1.le),?_,le_add_of_nonneg_right hε.le⟩⟩
      rw [time_op]; exact le_of_eq (by simpa [q] using (((hasDerivAt_id p.time).const_sub T).const_mul M).deriv)
  · exact ball_lateral_barrier hn c hr hT hlam hM hγ hell b

end HypoellipticAleksandrov.Parabolic.Transposition
