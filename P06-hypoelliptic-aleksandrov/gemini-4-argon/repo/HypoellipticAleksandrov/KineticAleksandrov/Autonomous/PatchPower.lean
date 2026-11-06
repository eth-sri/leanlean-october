module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PatchPowerFinalPath
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PatchPowerExponent
import HypoellipticAleksandrov.KineticAleksandrov.Holder.OscillationContractionGeometry
import Mathlib.Tactic
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PatchPowerIteration
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FullCoefficientAdapters
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PatchPowerDoubling
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SmoothAutonomousP6Statement
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.MacroscopicPropagationPhysical

/-! # Power-loss propagation of a positive return patch

The reference and future boxes are concrete and have a fixed positive time separation.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Parabolic Set Holder
open MeasureTheory Holder.Growth

/- The fixed compact reference box around time one. -/
def returnReferenceRegion : Set Point :=
  {z | z.time ∈ Icc (15 / 16) (17 / 16) ∧
    PDE.vecEuclideanNorm z.position ≤ 1 / 8 ∧ PDE.vecEuclideanNorm z.velocity ≤ 2}

/- The fixed compact future box, separated from the reference box in time. -/
def returnFutureRegion : Set Point :=
  {z | z.time ∈ Icc 2 3 ∧
    PDE.vecEuclideanNorm z.position ≤ 1 / 8 ∧ PDE.vecEuclideanNorm z.velocity ≤ 2}

private theorem norm_sub_le (x y : PDE.Vec 1) :
    PDE.vecEuclideanNorm (x - y) ≤ PDE.vecEuclideanNorm x + PDE.vecEuclideanNorm y := by
  simpa only [sub_eq_add_neg, PDE.vecEuclideanNorm_neg] using
    PDE.vecEuclideanNorm_add_le x (-y)

/- A positive neighbourhood reaches the later reference box with only a power loss. -/
theorem return_patch_power (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hp6 : SmoothAutonomousP6Statement lam Lam) :
    ∃ beta c₀ : ℝ, 0 < beta ∧ 0 < c₀ ∧
      ∀ (A : SmoothAutonomous lam Lam) (u : Point → ℝ),
      IsNonnegativeHomogeneousSolution A u → ∀ (ell k : ℝ) (z zStar : Point),
      0 < ell → ell ≤ 1 → 0 ≤ k → z ∈ returnReferenceRegion →
      zStar ∈ returnFutureRegion → (∀ p ∈ backwardCylinder z ell, k ≤ u p) →
      c₀ * ell ^ beta * k ≤ u zStar := by
  obtain ⟨c, hc, hc1, hd⟩ : ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ (A : SmoothAutonomous lam Lam) (u : Point → ℝ),
      IsNonnegativeHomogeneousSolution A u → ∀ (z : Point) (ell k : ℝ) (N : ℕ),
      0 < ell → 1 / 2 ≤ z.time → returnExpandedRadius ell N ≤ 1 / 64 → 0 ≤ k →
      (∀ p ∈ backwardCylinder z ell, k ≤ u p) →
      ∀ p ∈ backwardCylinder (returnExpandedCenter z ell N) (returnExpandedRadius ell N),
        c ^ N * k ≤ u p := by
    obtain ⟨c, hc, hc1, hd⟩ : ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ (A : SmoothAutonomous lam Lam) (u : Point → ℝ),
        IsNonnegativeHomogeneousSolution A u → ∀ (z : Point) (ell k : ℝ),
        0 < ell → 12 * ell ^ 2 < z.time → 0 ≤ k →
        (∀ p ∈ backwardCylinder z ell, k ≤ u p) →
        ∀ p ∈ backwardCylinder (returnDoubleCenter z ell) (2 * ell), c * k ≤ u p := by
      obtain ⟨c, hc, hc1, hmacro⟩ := exists_physical_macroscopic_cap_constant
        1 (by omega) lam Lam hlam hLam 0 (1 / 4) (by norm_num) (by norm_num)
      obtain ⟨C_A, _hC, hadm⟩ := return_solution_admissible hp6
      refine ⟨c, hc, hc1, ?_⟩
      intro A u hu z ell k hell htime hk hpatch p hp
      let z' := returnDoubleCenter z ell
      have hscale : 0 < 2 * ell := by positivity
      have hcenter : kineticAffine z' (2 * ell) (samplingCenter 1 0) = z := by
        ext i <;> simp [z', returnDoubleCenter, kineticAffine, samplingCenter] <;> ring
      have hregion : closure (kineticAffine z' (2 * ell) ''
          referenceRegion 1 0 (referenceBound 0)) ⊆ {p | 0 < p.time} := by
        have hclosed : IsClosed {p : Point | z.time - 12 * ell ^ 2 ≤ p.time} :=
          isClosed_le continuous_const continuous_time
        have hsub : kineticAffine z' (2 * ell) '' referenceRegion 1 0 (referenceBound 0) ⊆
            {p : Point | z.time - 12 * ell ^ 2 ≤ p.time} := by
          rintro _ ⟨q, hq, rfl⟩
          have ht : -5 < q.time := by simpa only [Nat.cast_zero, zero_add] using hq.1
          change z.time - 12 * ell ^ 2 ≤ z.time + 8 * ell ^ 2 + (2 * ell) ^ 2 * q.time
          nlinarith [sq_nonneg ell]
        intro q hq
        have hq' := closure_minimal hsub hclosed hq
        change z.time - 12 * ell ^ 2 ≤ q.time at hq'
        change 0 < q.time
        linarith
      apply hmacro 6 C_A (by norm_num) _ (autonomous_fullElliptic A) z' (2 * ell) hscale
        _ (isOpen_lt continuous_const continuous_time) hregion u
        (fun q hq => hu.2.1 q hq) (hadm A u hu).1 z ell k hell (by linarith)
        (by rw [hcenter]; exact backwardCylinder_radius_mono z hell (by linarith)) hk
        (fun q hq => hpatch q ?_) p hp
      rcases hq with ⟨q, hq, rfl⟩
      exact (kineticAffine_mem_cylinder z q hell).mpr
        ((cap_subset_closedCap 1).trans (closedCap_subset_unitCylinder 1) hq)
    refine ⟨c, hc, hc1, ?_⟩
    intro A u hu z ell k N hell hzt hrad hk hpatch
    have hrpos (n : ℕ) : 0 < returnExpandedRadius ell n := by
      dsimp only [returnExpandedRadius]
      positivity
    have hi : ∀ n, n ≤ N →
        ∀ p ∈ backwardCylinder (returnExpandedCenter z ell n) (returnExpandedRadius ell n),
          c ^ n * k ≤ u p := by
      intro n
      induction n with
      | zero =>
        intro _ p hp
        simpa only [returnExpandedCenter, returnExpandedRadius, pow_zero, one_mul,
          sub_self, mul_zero, add_zero, zero_smul] using hpatch p (by simpa only
            [returnExpandedCenter, returnExpandedRadius, pow_zero, one_mul, sub_self,
              mul_zero, add_zero, zero_smul] using hp)
      | succ n ih =>
        intro hn p hp
        have hnN : n ≤ N := by omega
        have hsmall :=
          (returnExpandedRadius_mono hell.le hnN).trans hrad
        have ht : z.time ≤ (returnExpandedCenter z ell n).time := by
          have hell := hell.le
          have h := returnExpandedRadius_mono hell (Nat.zero_le n)
          rw [show returnExpandedRadius ell 0 = ell by simp [returnExpandedRadius]] at h
          have hsq := pow_le_pow_left₀ hell h 2
          dsimp only [returnExpandedCenter]
          linarith
        have htime : 12 * (returnExpandedRadius ell n) ^ 2 <
            (returnExpandedCenter z ell n).time := by
          have hnn := (hrpos n).le
          nlinarith
        rw [returnExpandedCenter_succ, returnExpandedRadius_succ] at hp
        have h := hd A u hu (returnExpandedCenter z ell n) (returnExpandedRadius ell n)
          (c ^ n * k) (hrpos n) htime (mul_nonneg (pow_nonneg hc.le n) hk)
          (ih hnN) p hp
        simpa only [pow_succ', mul_assoc] using h
    exact hi N le_rfl
  obtain ⟨m, hm, hmloss⟩ : ∃ m : ℕ, 0 < m ∧ (1 / 2 : ℝ) ^ m ≤ c := by
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hc (by norm_num : (1 / 2 : ℝ) < 1)
      refine ⟨n + 1, by omega, ?_⟩
      rw [pow_succ]
      nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) n]

    /- Stop doubling at a radius between the fixed cutoff and twice that cutoff. -/
  obtain ⟨cf, hcf, hf⟩ := return_fixed_patch_path lam Lam hlam hLam hp6
    (1 / 128) (by norm_num) (by norm_num)
  refine ⟨(m : ℝ), cf * (1 / 128 : ℝ) ^ m, by exact_mod_cast hm, by positivity, ?_⟩
  intro A u hu ell k z zStar hell hell1 hk hz hstar hpatch
  let e := min ell (1 / 128 : ℝ)
  have he : 0 < e := lt_min hell (by norm_num)
  have heell : e ≤ ell := min_le_left _ _
  have hecut : e ≤ 1 / 128 := min_le_right _ _
  have hebase : (1 / 128 : ℝ) * ell ≤ e := by
    apply le_min
    · linarith
    · linarith
  obtain ⟨N, hRlo, hRhi⟩ := return_doubling_cutoff (1 / 128) e (by norm_num) he hecut
  have hsmall : returnExpandedRadius e N ≤ 1 / 64 := by linarith
  have hinit : ∀ p ∈ backwardCylinder z e, k ≤ u p :=
    fun p hp => hpatch p (backwardCylinder_radius_mono z he heell hp)
  have hexpand := hd A u hu z e k N he (by linarith [hz.1.1]) hsmall hk hinit
  let zN := returnExpandedCenter z e N
  let dt := (8 / 3 : ℝ) * ((returnExpandedRadius e N) ^ 2 - e ^ 2)
  have hdt0 : 0 ≤ dt := by
    have hR := returnExpandedRadius_mono he.le (Nat.zero_le N)
    rw [show returnExpandedRadius e 0 = e by simp [returnExpandedRadius]] at hR
    have hs := pow_le_pow_left₀ he.le hR 2
    dsimp [dt]
    linarith
  have hdt1 : dt ≤ 1 / 128 := by
    have hRp : 0 ≤ returnExpandedRadius e N := by dsimp [returnExpandedRadius]; positivity
    dsimp [dt]
    nlinarith [sq_nonneg e]
  have htN : zN.time = z.time + dt := rfl
  have hxN : zN.position = z.position + dt • z.velocity := rfl
  have hvN : zN.velocity = z.velocity := rfl
  have hNlo : 1 / 2 ≤ zN.time := by rw [htN]; linarith [hz.1.1]
  have hgaplo : 1 / 2 ≤ zStar.time - zN.time := by
    rw [htN]
    linarith [hstar.1.1, hz.1.2]
  have hgaphi : zStar.time - zN.time ≤ 3 := by
    rw [htN]
    linarith [hstar.1.2, hz.1.1]
  have hxNb : PDE.vecEuclideanNorm zN.position ≤ 1 := by
    rw [hxN]
    have h := PDE.vecEuclideanNorm_add_le z.position (dt • z.velocity)
    rw [PDE.vecEuclideanNorm_smul, abs_of_nonneg hdt0] at h
    have hmul := mul_le_mul_of_nonneg_left hz.2.2 hdt0
    linarith [hz.2.1]
  have hvNb : PDE.vecEuclideanNorm zN.velocity ≤ 2 := by rw [hvN]; exact hz.2.2
  have hdisp : PDE.vecEuclideanNorm
      (zStar.position - zN.position - (zStar.time - zN.time) • zN.velocity) ≤ 12 := by
    have h₁ := norm_sub_le zStar.position zN.position
    have h₂ := norm_sub_le (zStar.position - zN.position)
      ((zStar.time - zN.time) • zN.velocity)
    rw [PDE.vecEuclideanNorm_smul, abs_of_nonneg (by linarith :
      0 ≤ zStar.time - zN.time)] at h₂
    have hm := mul_le_mul_of_nonneg_left hvNb (by linarith :
      0 ≤ zStar.time - zN.time)
    linarith [hstar.2.1]
  have hvel : PDE.vecEuclideanNorm (zStar.velocity - zN.velocity) ≤ 4 :=
    (norm_sub_le _ _).trans (by linarith [hstar.2.2])
  have hlast := hf A u hu zN zStar (c ^ N * k) hNlo hgaplo hgaphi hdisp hvel
    (mul_nonneg (pow_nonneg hc.le N) hk) (fun p hp => hexpand p
      (backwardCylinder_radius_mono zN (by norm_num) hRlo hp))
  have hpower := return_loss_power hc.le he.le hmloss (by linarith)
  have hsmallpower : (1 / 128 : ℝ) ^ m * ell ^ m ≤ e ^ m := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hebase m
  have hcoeff := hsmallpower.trans hpower
  have hfinal := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcoeff hcf.le) hk
  rw [Real.rpow_natCast]
  simpa only [mul_assoc] using hfinal.trans (by simpa only [mul_assoc] using hlast)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
