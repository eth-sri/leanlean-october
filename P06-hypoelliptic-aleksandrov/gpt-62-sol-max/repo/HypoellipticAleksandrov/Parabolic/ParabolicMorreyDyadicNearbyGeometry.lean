module

public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyDyadicPointSelector

/-!
# Two-centre parabolic dyadic geometry

This module gives the scale selection and literal two-box enclosure used by
the dyadic Morrey argument.  It makes no common-address, shifted-grid, or
analytic assertion: the enclosing box is an ordinary (non-dyadic) forward
parabolic box.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace HypoellipticAleksandrov.Parabolic

noncomputable section

section
variable (d : Nat) (z : TimeVelocity d) (hz : z ∈ parabolicDyadicReferenceCell d)
  (w : TimeVelocity d) (hw : w ∈ parabolicDyadicReferenceCell d)
include hw

/-- Two distinct points in the reference carrier have a least dyadic scale
whose source-box radius is no greater than their coordinate distance. -/
theorem exists_parabolicDyadicGeneration_radius_le_coordinateDist_lt_two_mul_radius
    (hzw : z ≠ w) :
    ∃ n : Nat,
      (parabolicDyadicSelectedBox z hz n).radius ≤
          parabolicCoordinateDist z w ∧
      parabolicCoordinateDist z w <
        2 * (parabolicDyadicSelectedBox z hz n).radius := by
  let rho : Real := parabolicCoordinateDist z w
  let radius : Nat → Real := fun n =>
    (parabolicDyadicSelectedBox z hz n).radius
  have hrhoPos : 0 < rho := by
    apply lt_of_le_of_ne (parabolicCoordinateDist_nonneg z w)
    intro hzero
    apply hzw
    exact (parabolicCoordinateDist_eq_zero_iff z w).mp hzero.symm
  have htime : Real.sqrt |z.1 - w.1| < 1 := by
    change z.1 ∈ Ioc (0 : Real) 1 ∧
      z.2 ∈ Set.univ.pi (fun _ : Fin d => Ioc (-1 : Real) 1) at hz
    change w.1 ∈ Ioc (0 : Real) 1 ∧
      w.2 ∈ Set.univ.pi (fun _ : Fin d => Ioc (-1 : Real) 1) at hw
    apply (Real.sqrt_lt' (by norm_num : (0 : Real) < 1)).mpr
    rw [abs_lt]
    constructor <;> linarith [hz.1.1, hz.1.2, hw.1.1, hw.1.2]
  have hvelocity : ‖z.2 - w.2‖ < 2 := by
    rw [pi_norm_lt_iff (by norm_num : (0 : Real) < 2)]
    intro coordinate
    simp only [Pi.sub_apply, Real.norm_eq_abs]
    obtain ⟨hzLower, hzUpper⟩ := hz.2 coordinate (Set.mem_univ coordinate)
    obtain ⟨hwLower, hwUpper⟩ := hw.2 coordinate (Set.mem_univ coordinate)
    rw [abs_lt]
    constructor <;> linarith
  have hrhoLtTwo : rho < 2 := by
    dsimp only [rho, parabolicCoordinateDist]
    apply max_lt
    · linarith
    · exact hvelocity
  let P : Nat → Prop := fun n => radius n ≤ rho
  have hP : ∃ n, P n := by
    have heventually : ∀ᶠ n in atTop, 2 * radius n < 2 * rho := by
      have hlimit := tendsto_two_mul_parabolicDyadicIndexContaining_radius_atTop d z hz
      exact hlimit.eventually_lt_const (by linarith)
    obtain ⟨n, hn⟩ := eventually_atTop.mp heventually
    refine ⟨n, ?_⟩
    exact le_of_lt (by linarith [hn n le_rfl])
  refine ⟨Nat.find hP, Nat.find_spec hP, ?_⟩
  have hfindZeroOrSucc : Nat.find hP = 0 ∨ ∃ m, Nat.find hP = m + 1 := by
    by_cases hzero : Nat.find hP = 0
    · exact Or.inl hzero
    · exact Or.inr (Nat.exists_eq_succ_of_ne_zero hzero)
  rcases hfindZeroOrSucc with hzero | ⟨m, hm⟩
  · rw [hzero]
    change rho < 2 * ((2 : Real) ^ 0)⁻¹
    norm_num
    exact hrhoLtTwo
  · have hnot : ¬ P m := by
      intro hmP
      have hmin := Nat.find_min' hP hmP
      rw [hm] at hmin
      omega
    have hltPrevious : rho < radius m := lt_of_not_ge hnot
    rw [hm]
    change rho < 2 * ((2 : Real) ^ (m + 1))⁻¹
    calc
      rho < ((2 : Real) ^ m)⁻¹ := hltPrevious
      _ = 2 * ((2 : Real) ^ (m + 1))⁻¹ := by
        rw [pow_succ]
        field_simp

/-- The two selected source boxes at a fixed generation lie in one literal
nearby forward box of radius three times the coordinate separation. -/
theorem parabolicDyadicSelectedForwardBoxes_subset_nearbyCommonBox
    (n : Nat)
    (hr : (parabolicDyadicSelectedBox z hz n).radius ≤ parabolicCoordinateDist z w) :
    let qz := parabolicDyadicSelectedBox z hz n
    let qw := parabolicDyadicSelectedBox w hw n
    let t := min qz.baseTime qw.baseTime
    let r := 3 * parabolicCoordinateDist z w
    let v := (z.2 + w.2) / 2
    inkSpotsSourceBox qz ⊆ parabolicBox 1 r t v ∧
    inkSpotsSourceBox qw ⊆ parabolicBox 1 r t v ∧
    parabolicClosedBox 1 qz.radius qz.baseTime qz.center ⊆ parabolicClosedBox 1 r t v ∧
    parabolicClosedBox 1 qw.radius qw.baseTime qw.center ⊆ parabolicClosedBox 1 r t v := by
  let rho := parabolicCoordinateDist z w
  let qz := parabolicDyadicSelectedBox z hz n
  let qw := parabolicDyadicSelectedBox w hw n
  let tMin := min qz.baseTime qw.baseTime
  have hqzRadiusPos : 0 < qz.radius := parabolicDyadicSourceBox_radius_pos _
  have hqwRadiusPos : 0 < qw.radius := hqzRadiusPos
  have hrhoPos : 0 < rho := hqzRadiusPos.trans_le hr
  have hRadiusSq : qz.radius ^ 2 = qw.radius ^ 2 := rfl
  have hzClosed : z ∈ parabolicClosedBox 1 qz.radius qz.baseTime qz.center :=
    parabolicDyadicAddressContaining_mem_closedForwardBox d z hz n
  have hwClosed : w ∈ parabolicClosedBox 1 qw.radius qw.baseTime qw.center :=
    parabolicDyadicAddressContaining_mem_closedForwardBox d w hw n
  have hzMem := mem_parabolicClosedBox_iff.mp hzClosed
  have hwMem := mem_parabolicClosedBox_iff.mp hwClosed
  have htimeRoot : Real.sqrt |z.1 - w.1| ≤ rho := by
    dsimp only [rho, parabolicCoordinateDist]
    exact le_max_left _ _
  have htime : |z.1 - w.1| ≤ rho ^ 2 := by
    have hsq := (sq_le_sq₀ (Real.sqrt_nonneg _) hrhoPos.le).mpr htimeRoot
    rwa [Real.sq_sqrt (abs_nonneg _)] at hsq
  have hvelocity (coordinate : Fin d) : |z.2 coordinate - w.2 coordinate| ≤ rho := by
    have hnorm : ‖z.2 - w.2‖ ≤ rho := by
      dsimp only [rho, parabolicCoordinateDist]
      exact le_max_right _ _
    have hcoordinate := (pi_norm_le_iff_of_nonneg hrhoPos.le).mp hnorm coordinate
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using hcoordinate
  have hzwTime : z.1 - w.1 ≤ rho ^ 2 := (le_abs_self _).trans htime
  have hwzTime : w.1 - z.1 ≤ rho ^ 2 := by
    nlinarith [neg_le_abs (z.1 - w.1), htime]
  have hqzBase : qz.baseTime ≤ tMin + qz.radius ^ 2 + rho ^ 2 := by
    simp only [tMin, min_def]
    split <;> nlinarith only [sq_nonneg qz.radius, sq_nonneg rho, hzMem.1,
      hwMem.2.1, hzwTime, hRadiusSq]
  have hqwBase : qw.baseTime ≤ tMin + qw.radius ^ 2 + rho ^ 2 := by
    simp only [tMin, min_def]
    split <;> nlinarith only [sq_nonneg qw.radius, sq_nonneg rho, hwMem.1,
      hzMem.2.1, hwzTime, hRadiusSq]
  have boxEnclosure : ∀ (q : InkSpotsBox d) (c other : TimeVelocity d),
      c ∈ parabolicClosedBox 1 q.radius q.baseTime q.center →
      tMin ≤ q.baseTime →
      q.baseTime ≤ tMin + q.radius ^ 2 + rho ^ 2 →
      0 < q.radius →
      q.radius ≤ rho →
      (∀ coordinate : Fin d, |c.2 coordinate - other.2 coordinate| ≤ rho) →
      c.2 + other.2 = z.2 + w.2 →
      parabolicBox 1 q.radius q.baseTime q.center ⊆
        parabolicBox 1 (3 * rho) tMin ((z.2 + w.2) / 2) ∧
      parabolicClosedBox 1 q.radius q.baseTime q.center ⊆
        parabolicClosedBox 1 (3 * rho) tMin ((z.2 + w.2) / 2) := by
    intro q c other hc hmin hbase hqRadiusNonneg hrad hcoordinate hmidpoint
    have hsq := (sq_le_sq₀ hqRadiusNonneg.le hrhoPos.le).mpr hrad
    have ho : parabolicBox 1 q.radius q.baseTime q.center ⊆
        parabolicBox 1 (3 * rho) tMin ((z.2 + w.2) / 2) := by
      intro x hx
      rw [mem_parabolicBox_iff] at hx ⊢
      refine ⟨hmin.trans_lt hx.1, ?_, mem_velocityCube_iff.mpr ?_⟩
      · nlinarith [hx.2.1, sq_pos_of_pos hrhoPos]
      intro i
      have hsplit : x.2 i - ((z.2 + w.2) / 2) i =
          (x.2 i - q.center i) + (q.center i - c.2 i) + (c.2 i - other.2 i) / 2 := by
        rw [← hmidpoint]
        simp only [Pi.add_apply, Pi.div_apply, Pi.ofNat_apply]
        ring
      have hx' := (mem_velocityCube_iff.mp hx.2.2) i
      have hc' := (mem_velocityClosedCube_iff.mp (mem_parabolicClosedBox_iff.mp hc).2.2) i
      rw [hsplit]
      have hb := (abs_add_le ((x.2 i - q.center i) + (q.center i - c.2 i))
        ((c.2 i - other.2 i) / 2)).trans (add_le_add
        (abs_add_le (x.2 i - q.center i) (q.center i - c.2 i))
        le_rfl)
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_sub_comm (q.center i)] at hb
      linarith only [hb, hx', hc', hcoordinate i, hrad, hrhoPos.le]
    refine ⟨ho, ?_⟩
    simpa only [closure_parabolicBox_of_pos one_pos hqRadiusNonneg,
      closure_parabolicBox_of_pos one_pos (show 0 < 3 * rho by positivity)]
      using closure_mono ho
  have hzEnclosure := boxEnclosure qz z w hzClosed (min_le_left _ _) hqzBase
    hqzRadiusPos hr hvelocity rfl
  have hwEnclosure := boxEnclosure qw w z hwClosed (min_le_right _ _) hqwBase
    hqwRadiusPos hr (fun i => by simpa only [abs_sub_comm] using hvelocity i) (add_comm _ _)
  exact ⟨hzEnclosure.1, hwEnclosure.1, hzEnclosure.2, hwEnclosure.2⟩

end

end

end HypoellipticAleksandrov.Parabolic
