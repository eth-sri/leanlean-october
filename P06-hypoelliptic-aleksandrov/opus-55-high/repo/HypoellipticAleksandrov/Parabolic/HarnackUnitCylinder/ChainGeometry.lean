module

public import HypoellipticAleksandrov.Parabolic.HarnackChainGeometry

/-! # Equal-time Harnack links inside the open unit cylinder -/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

open Set

variable {d : ℕ} {w : PDE.Vec d}

private theorem normSq_lt_quarter_of_mem_halfBall 
    (hw : w ∈ PDE.euclideanBall (0 : PDE.Vec d) (1 / 2 : ℝ)) :
    PDE.vecNormSq w < 1 / 4 := by
  norm_num [PDE.euclideanBall, PDE.euclideanSqDist] at hw ⊢
  exact hw

private theorem coordinate_lt_half_of_mem_halfBall 
    (hw : w ∈ PDE.euclideanBall (0 : PDE.Vec d) (1 / 2 : ℝ)) (i : Fin d) :
    |w i| < 1 / 2 := by
  have hs := (PDE.sq_apply_le_vecNormSq w i).trans_lt
    (normSq_lt_quarter_of_mem_halfBall hw)
  apply abs_lt_of_sq_lt_sq (by linarith) (by norm_num)

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
    (∀ k < m, v (k + 1) ∈ velocityCube (v k) (r / 2)) := by
  let m  := 256 * d
  let dt  := (P'.1 - P.1) / m
  let r  := Real.sqrt dt
  let t : ℕ → ℝ := fun k => P.1 + k * dt
  let v : ℕ → PDE.Vec d := fun k =>
    P.2 + (k / (m : ℝ)) • (P'.2 - P.2)
  change 0 < m ∧ 0 < r ∧ (t 0, v 0) = P ∧ (t m, v m) = P' ∧ _
  have hdreal : 1 ≤ (d : ℝ) := by simp_all
  have hm : 256 ≤ m := by omega
  have hmpos : 0 < (m : ℝ) := by positivity
  have hmd : m = 256 * (d : ℝ) := by simp [m]
  have hgap0 : 1 / 4 < P'.1 - P.1 := by grind
  have hgap1 : P'.1 - P.1 < 1 := by grind
  have hdt : 0 < dt := div_pos (by linarith) hmpos
  have hmul : m * dt = P'.1 - P.1 := by
    grind
  have hrsq : r ^ 2 = dt := Real.sq_sqrt hdt.le
  have hr : 0 < r := Real.sqrt_pos.mpr hdt
  have hdtSmall : dt < 1 / 256 := by nlinarith
  have htstep : ∀ k : ℕ, t (k + 1) = t k + r ^ 2 := by
    grind
  have hvstep : ∀ k : ℕ, v (k + 1) - v k = (1 / (m : ℝ)) • (P'.2 - P.2) := by
    intro k
    ext i
    simp only [v, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
      Nat.cast_add]
    ring
  have hcenter : ∀ k ≤ m,
      v k ∈ PDE.euclideanBall (0) (1 / 2) := by
    intro k hk
    have hkreal : k ≤ (m : ℝ) := by exact_mod_cast hk
    have ha : 0 ≤ k / (m : ℝ) := div_nonneg (Nat.cast_nonneg _) hmpos.le
    have hb : k / (m : ℝ) ≤ 1 := (div_le_one₀ hmpos).mpr hkreal
    have hconv := (PDE.convex_euclideanBall _ _)
      hP.2 hP'.2 (by linarith) ha
      (by ring : (1 - k / m) + k / (m : ℝ) = 1)
    convert hconv using 1
    ext i
    simp only [v, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
    ring
  have hrecip : 1 / m < r / 2 := by
    apply (div_lt_iff₀ hmpos).mpr
    nlinarith
  refine ⟨by omega, hr, ?_, ?_, fun k _ => htstep k, ?_, ?_⟩
  · aesop
  · apply Prod.ext
    · linarith
    · simp [v, div_self hmpos.ne']
  · intro k hk w hw
    rcases w with ⟨s, w⟩
    rw [mem_parabolicClosedBox_iff] at hw
    have hkreal : (k : ℝ) ≤ (m : ℝ) - 1 := by
      have hs : ((k + 1 : ℕ)) ≤ (m : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hk
      grind
    have htk0 : P.1 ≤ t k := by
      aesop
    have htk1 : t k + dt ≤ P'.1 := by
      nlinarith
    have hnorm := normSq_lt_quarter_of_mem_halfBall (hcenter k (Nat.le_of_lt hk))
    have hdisp := vecNormSq_sub_le_natCast_mul_sq_of_mem_velocityClosedCube hw.2.2
    have hsum := PDE.vecNormSq_add_le (v k) (w - v k)
    rw [add_sub_cancel] at hsum
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · grind
    · grind
    · change PDE.euclideanSqDist w 0 < 1 ^ 2
      simpa [PDE.euclideanSqDist] using (show PDE.vecNormSq w < 1 by nlinarith)
  · intro k _ i
    have hcoord0 := coordinate_lt_half_of_mem_halfBall hP.2 i
    have hcoord1 := coordinate_lt_half_of_mem_halfBall hP'.2 i
    have hcoord : |P'.2 i - P.2 i| < 1 := by
      grind
    have hstepi := congrFun (hvstep k) i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hstepi
    rw [hstepi, abs_mul, abs_of_pos (one_div_pos.mpr hmpos)]
    calc
      (1 / m) * |P'.2 i - P.2 i| < (1 / m) * 1 :=
        mul_lt_mul_of_pos_left hcoord (one_div_pos.mpr hmpos)
      _ = 1 / m := mul_one _
      _ < r / 2 := hrecip

end HypoellipticAleksandrov.Parabolic
