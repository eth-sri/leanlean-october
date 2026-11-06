module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.PropagationEndpoint
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.PropagationApproximation
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.PropagationIterationSteps
import Mathlib.Tactic
import HypoellipticAleksandrov.KineticAleksandrov.Holder.SkeletonApproximation
import HypoellipticAleksandrov.KineticAleksandrov.Holder.PropagationParametersBounds
import Mathlib.Algebra.Order.Floor.Ring

/-! # Propagation with the explicit source constant for C-one-one skeletons -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Set

/- The explicit source constant propagates along the original C-one-one skeleton. -/
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
  obtain ⟨hn, hh, hhstar, hhalf, hnstar, hnTP⟩ : 0 < Nat.ceil (TP / hs) ∧
      0 < TP / (Nat.ceil (TP / hs) : ℝ) ∧
      TP / (Nat.ceil (TP / hs) : ℝ) ≤ hs ∧
      hs / 2 ≤ TP / (Nat.ceil (TP / hs) : ℝ) ∧
      Nat.ceil (TP / hs) ≤ Nat.ceil (T1 / hs) ∧
      (Nat.ceil (TP / hs) : ℝ) * (TP / (Nat.ceil (TP / hs) : ℝ)) = TP := by
    have hTP0 := hhs.trans_le hhsTP
    have hn : 0 < Nat.ceil (TP / hs) := Nat.ceil_pos.mpr (div_pos hTP0 hhs)
    have hnr : 0 < (Nat.ceil (TP / hs) : ℝ) := Nat.cast_pos.mpr hn
    have hratio : 1 ≤ TP / hs := (le_div_iff₀ hhs).mpr (by simpa using hhsTP)
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
    · exact Nat.ceil_mono (div_le_div_of_nonneg_right hTP1 hhs.le)
    · field_simp
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
  have hcontain : corridor tminus (-T0) TP (kx / 2) (kv / 2) y w ⊆ corridor tminus (-T0) TP kx kv x v := by
    let a := (-T0)
    intro P hP
    obtain ⟨ht, hx, hv⟩ := hP
    have hc := hclose (P.time - tminus) ht
    refine ⟨ht, ?_, ?_⟩
    · have heq : P.position - x (P.time - tminus) =
          (P.position - y (P.time - tminus)) + (y (P.time - tminus) - x (P.time - tminus)) :=
        by abel
      rw [heq]
      apply (PDE.vecEuclideanNorm_add_le _ _).trans
      linarith only [hx, hc.1, hepsx]
    · have heq : P.velocity - v (P.time - tminus) =
          (P.velocity - w (P.time - tminus)) + (w (P.time - tminus) - v (P.time - tminus)) :=
        by abel
      rw [heq]
      apply (PDE.vecEuclideanNorm_add_le _ _).trans
      linarith only [hv, hc.2, hepsv]
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

end HypoellipticAleksandrov.KineticAleksandrov.Holder
