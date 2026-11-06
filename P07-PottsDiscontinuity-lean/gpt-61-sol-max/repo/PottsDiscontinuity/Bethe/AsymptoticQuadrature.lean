module
public import Mathlib

public import PottsDiscontinuity.Bethe.AsymptoticPartition

/-! # Quadrature on the interior root cells

The boundary intervals are estimated separately. This avoids the incorrect
boundary correction in the printed proof of Theorem 2.6 and does not require
periodic boundary values of a continuous test function.
-/

@[expose] public section

open Set MeasureTheory intervalIntegral


namespace PottsDiscontinuity.Bethe

theorem sum_fin_adjacent_sub (k : ℕ) (f : Fin (k + 1) → ℝ) :
     ∑ j : Fin k, (f j.succ - f j.castSucc)  = f (Fin.last k) - f 0 := by
  have h0 := Fin.sum_univ_succ f
  have h1 := Fin.sum_univ_castSucc f
  rw [Finset.sum_sub_distrib]
  linarith

theorem sum_fin_integrals_adjacent (k : ℕ) (p : Fin (k + 1) → ℝ)
    {F : ℝ → ℝ} (hF : Continuous F) :
     ∑ j : Fin k, ∫ x in p j.castSucc..p j.succ, F x  =
      ∫ x in p 0..p (Fin.last k), F x := by
  let P  := fun y => ∫ x in p 0..y, F x
  have heq (j : Fin k) :  ∫ x in p j.castSucc..p j.succ, F x  =
      P (p j.succ) - P (p j.castSucc) := (intervalIntegral.integral_interval_sub_left
                                     (hF.intervalIntegrable _ _) (hF.intervalIntegrable _ _)).symm
  simp_rw [heq]
  rw [sum_fin_adjacent_sub k  fun j => P (p j) ]
  simp only [P, integral_same, sub_zero]

section

variable {N k : ℕ} {p : Fin (k + 1) → ℝ} (hp : p ∈ S_n (k + 1)) (hs : 2 * (k + 1) ≤ N)
include hp hs

theorem rootStepDensity_interior  (j : Fin k)
    {x : ℝ} (hx : p j.castSucc ≤ x ∧ x < p j.succ) :
    rootStepDensity N (k + 1) p hp (by omega) hs x =
      1 / ((N : ℝ) * (p j.succ - p j.castSucc)) := by
  let cell : Fin (k + 2) := ⟨j.val + 1, by omega⟩
  have ha : rootPartitionPoint (k + 1) p (by omega) cell.castSucc = p j.castSucc := by
    convert rootPartitionPoint_root p (by omega) j.castSucc using 1
    congr 1
  have hb : rootPartitionPoint (k + 1) p (by omega) cell.succ = p j.succ := by
    convert rootPartitionPoint_root p (by omega) j.succ using 1
    congr 1
  have hm : rootGapMultiplicity N (k + 1) hs cell = 1 := by
    grind [rootGapMultiplicity]
  
  rw [rootStepDensity_on_cell hp (by omega) hs cell (by rwa [ha, hb]), ha, hb, hm]

/-- A local quadrature estimate. `w` is any modulus bound for the test
function on this cell; `E` is the actual uniform error of its density. -/
theorem root_cell_quadrature_error 
    {Δ : ℝ} (hΔ : Δ < -1) {g : ℝ → ℝ} (hg : Continuous g)
    {G M E w : ℝ} (hG : 0 ≤ G)
    (hw : 0 ≤ w) (hgBound : ∀ x ∈ Icc (-Real.pi) Real.pi, |g x| ≤ G)
    (hρBound : ∀ x ∈ Icc (-Real.pi) Real.pi, |rho Δ x| ≤ M)
    (herror : ∀ x ∈ Icc (-Real.pi) Real.pi,
      |rootStepDensity N (k + 1) p hp (by omega) hs x - rho Δ x| ≤ E)
    (j : Fin k)
    (hmod : ∀ x ∈ Icc (p j.castSucc) (p j.succ), |g x - g (p j.castSucc)| ≤ w) :
    |(∫ x in p j.castSucc..p j.succ, g x * rho Δ x) - g (p j.castSucc) / (N : ℝ)| ≤
      (w * M + G * E) * (p j.succ - p j.castSucc) := by
  
   
  have hgap  := sub_pos.mpr
    (hp.2.1 (show j.castSucc < j.succ from by change j.val < j.val + 1; omega))
  let c  := 1 / ( N  * (p j.succ - p j.castSucc))
  have hF : Continuous  fun x => g x * rho Δ x  := hg.mul (continuous_rho hΔ)
  have hrewrite :  ∫ x in p j.castSucc..p j.succ,
       g x * rho Δ x - g (p j.castSucc) * c   =
      (∫ x in p j.castSucc..p j.succ, g x * rho Δ x) - g (p j.castSucc) /  N  := by
    rw [integral_sub (hF.intervalIntegrable _ _) intervalIntegrable_const, intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    grind
  rw [← hrewrite, ← Real.norm_eq_abs]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const_ae
    (a := p j.castSucc) (b := p j.succ) (C := w * M + G * E)
    (f := fun x => g x * rho Δ x - g (p j.castSucc) * c) ?_
  · simpa only [abs_of_pos hgap] using hb
  · filter_upwards [volume.ae_ne (p j.succ)] with x hne hx
    rw [uIoc_of_le (sub_pos.mp hgap).le] at hx
    have hxi : x ∈ Icc (p j.castSucc) (p j.succ) := ⟨hx.1.le, hx.2⟩
    have hxpi : x ∈ Icc (-Real.pi) Real.pi :=
      ⟨(hp.1 j.castSucc).1.le.trans hxi.1, hxi.2.trans (hp.1 j.succ).2.le⟩
    
    have he := herror x hxpi
    rw [ rootStepDensity_interior hp hs j ⟨hxi.1, lt_of_le_of_ne hxi.2 hne⟩ , abs_sub_comm] at he
    
    
    calc
      |g x * rho Δ x - g (p j.castSucc) * c| =
          |(g x - g (p j.castSucc)) * rho Δ x + g (p j.castSucc) * (rho Δ x - c)| := by
         ring
      _ ≤ |g x - g (p j.castSucc)| * |rho Δ x| + |g (p j.castSucc)| * |rho Δ x - c| := by
        simpa only [abs_mul] using abs_add_le
          ((g x - g (p j.castSucc)) * rho Δ x) (g (p j.castSucc) * (rho Δ x - c))
      _ ≤ w * M + G * E := add_le_add
        (mul_le_mul (hmod x hxi) (hρBound x hxpi) (abs_nonneg _) hw)
        (mul_le_mul (hgBound (p j.castSucc) ⟨(hp.1 j.castSucc).1.le, (hp.1 j.castSucc).2.le⟩) he (abs_nonneg _) hG)

end

theorem root_mesh_consequences {k : ℕ} {p : Fin (k + 1) → ℝ}
    (hp : p ∈ S_n (k + 1)) {d : ℝ}
    (hmesh : ∀ j : Fin (k + 2),
      rootPartitionPoint (k + 1) p (by omega) j.succ -
        rootPartitionPoint (k + 1) p (by omega) j.castSucc ≤ d) :
    p 0 + Real.pi ≤ d ∧ Real.pi - p (Fin.last k) ≤ d ∧
      ∀ j : Fin k, p j.succ - p j.castSucc ≤ d := by
  have hfirst := hmesh 0
  
  have h0 : rootPartitionPoint (k + 1) p (by omega) (0 : Fin (k + 2)).succ = p 0 := rfl
  
  have hzero : rootPartitionPoint (k + 1) p (by omega) (0 : Fin (k + 2)).castSucc =
      p (Fin.last k) - 2 * Real.pi := rfl
  
  
  
  refine ⟨by linarith [(hp.1 (Fin.last k)).2], by linarith [(hp.1 0).1], ?_⟩
  intro j
  let cell : Fin (k + 2) := ⟨j.val + 1, by omega⟩
  have ha : rootPartitionPoint (k + 1) p (by omega) cell.castSucc = p j.castSucc := by
    convert rootPartitionPoint_root p (by omega) j.castSucc using 1
    congr 1
  have hb : rootPartitionPoint (k + 1) p (by omega) cell.succ = p j.succ := by
    convert rootPartitionPoint_root p (by omega) j.succ using 1
    congr 1
  simpa only [ha, hb] using hmesh cell

/-- Finite quadrature with both endpoint tails explicitly controlled. -/
theorem root_quadrature_error {N k : ℕ} {p : Fin (k + 1) → ℝ}
    (hp : p ∈ S_n (k + 1)) (hs : 2 * (k + 1) ≤ N)
    {Δ : ℝ} (hΔ : Δ < -1) {g : ℝ → ℝ} (hg : Continuous g)
    {G M E w d : ℝ} (hG : 0 ≤ G) (hM : 0 ≤ M) (hE : 0 ≤ E)
    (hw : 0 ≤ w)
    (hgBound : ∀ x ∈ Icc (-Real.pi) Real.pi, |g x| ≤ G)
    (hρBound : ∀ x ∈ Icc (-Real.pi) Real.pi, |rho Δ x| ≤ M)
    (herror : ∀ x ∈ Icc (-Real.pi) Real.pi,
      |rootStepDensity N (k + 1) p hp (by omega) hs x - rho Δ x| ≤ E)
    (hmesh : ∀ j : Fin (k + 2),
      rootPartitionPoint (k + 1) p (by omega) j.succ -
        rootPartitionPoint (k + 1) p (by omega) j.castSucc ≤ d)
    (hmod : ∀ x ∈ Icc (-Real.pi) Real.pi, ∀ y ∈ Icc (-Real.pi) Real.pi,
      |x - y| ≤ d → |g x - g y| ≤ w) :
    |(∫ x in (-Real.pi)..Real.pi, g x * rho Δ x) - (∑ j, g (p j)) / (N : ℝ)| ≤
      2 * Real.pi * (w * M + G * E) + 2 * G * M * d + G / (N : ℝ) := by
  
  have hN : (0 : ℝ) < N := by exact_mod_cast  by omega 
  have hF : Continuous  fun x => g x * rho Δ x  := hg.mul (continuous_rho hΔ)
  obtain ⟨hleft, hright, hinterior⟩ := root_mesh_consequences hp hmesh
  let C := w * M + G * E
  
  have hcell (j : Fin k) :
      |(∫ x in p j.castSucc..p j.succ, g x * rho Δ x) - g (p j.castSucc) / (N )| ≤
        C * (p j.succ - p j.castSucc) := by
    apply root_cell_quadrature_error hp hs hΔ hg hG hw hgBound hρBound herror j
    intro x hx
    apply hmod x ⟨(hp.1 j.castSucc).1.le.trans hx.1,
      hx.2.trans (hp.1 j.succ).2.le⟩ (p j.castSucc)
      ⟨(hp.1 j.castSucc).1.le, (hp.1 j.castSucc).2.le⟩
    rw [abs_of_nonneg (sub_nonneg.mpr hx.1)]
    exact (sub_le_sub_right hx.2 _).trans (hinterior j)
  have hmiddle : |(∫ x in p 0..p (Fin.last k), g x * rho Δ x) -
      (∑ j : Fin k, g (p j.castSucc)) / (N )| ≤ 2 * Real.pi * C := by
    calc
      _ = |∑ j : Fin k, ((∫ x in p j.castSucc..p j.succ, g x * rho Δ x) -
          g (p j.castSucc) /  N )| := by
        rw [Finset.sum_sub_distrib, sum_fin_integrals_adjacent k p hF, Finset.sum_div]
      _ ≤ ∑ j : Fin k, |(∫ x in p j.castSucc..p j.succ, g x * rho Δ x) -
          g (p j.castSucc) / (N )| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Fin k, C * (p j.succ - p j.castSucc) := Finset.sum_le_sum  fun j _ => hcell j 
      _ = C * (p (Fin.last k) - p 0) := by rw [← Finset.mul_sum, sum_fin_adjacent_sub]
      _ ≤ 2 * Real.pi * C := by
        have hlen : p (Fin.last k) - p 0 ≤ 2 * Real.pi := by
          linarith [(hp.1 0).1, (hp.1 (Fin.last k)).2]
        nlinarith only [mul_le_mul_of_nonneg_left hlen (by  positivity : 0 ≤ C)]
  have hFbound : ∀ x ∈ Icc (-Real.pi) Real.pi, |g x * rho Δ x| ≤ G * M := by
    intro x hx
    rw [abs_mul]
    exact mul_le_mul (hgBound x hx) (hρBound x hx) (abs_nonneg _) hG
  have htleft : |∫ x in (-Real.pi)..p 0, g x * rho Δ x| ≤ G * M * d := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (C := G * M)
      (a := -Real.pi) (b := p 0) (f := fun x => g x * rho Δ x)  fun x hx => ?_ 
    · rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ p 0 - -Real.pi by linarith [(hp.1 0).1])] at hb
      exact hb.trans (mul_le_mul_of_nonneg_left (by linarith )
        (mul_nonneg hG hM))
    · rw [uIoc_of_le (hp.1 0).1.le] at hx
      simpa only [Real.norm_eq_abs] using hFbound x ⟨hx.1.le, hx.2.trans (hp.1 0).2.le⟩
  have htright : |∫ x in p (Fin.last k)..Real.pi, g x * rho Δ x| ≤ G * M * d := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (C := G * M)
      (a := p (Fin.last k)) (b := Real.pi) (f := fun x => g x * rho Δ x)  fun x hx => ?_ 
    · rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ Real.pi - p (Fin.last k) by linarith [(hp.1 (Fin.last k)).2])] at hb
      exact hb.trans (mul_le_mul_of_nonneg_left hright (mul_nonneg hG hM))
    · rw [uIoc_of_le (hp.1 (Fin.last k)).2.le] at hx
      simpa only [Real.norm_eq_abs] using hFbound x
        ⟨(hp.1 (Fin.last k)).1.le.trans hx.1.le, hx.2⟩
  have hlast : |g (p (Fin.last k)) / (N )| ≤ G /  N  := by
    rw [abs_div, abs_of_pos hN]
    exact div_le_div_of_nonneg_right (hgBound _
      ⟨(hp.1 (Fin.last k)).1.le, (hp.1 (Fin.last k)).2.le⟩) hN.le
  have hsplit :  ∫ x in (-Real.pi)..Real.pi, g x * rho Δ x  =
      (∫ x in (-Real.pi)..p 0, g x * rho Δ x) +
      (∫ x in p 0..p (Fin.last k), g x * rho Δ x) +
       ∫ x in p (Fin.last k)..Real.pi, g x * rho Δ x  := by
    rw [integral_add_adjacent_intervals (hF.intervalIntegrable _ _) (hF.intervalIntegrable _ _),
      integral_add_adjacent_intervals (hF.intervalIntegrable _ _) (hF.intervalIntegrable _ _)]
  rw [hsplit, Fin.sum_univ_castSucc, add_div]
  have halg : ∀ a b c s t : ℝ, a + b + c - (s + t) = a + (b - s) + c - t := by
    intros; ring
  rw [halg]
  calc
    _ ≤ |∫ x in (-Real.pi)..p 0, g x * rho Δ x| +
        |(∫ x in p 0..p (Fin.last k), g x * rho Δ x) -
          (∑ j : Fin k, g (p j.castSucc)) / (N )| +
        |∫ x in p (Fin.last k)..Real.pi, g x * rho Δ x| +
        |g (p (Fin.last k)) / (N )| := by
      have htri (a b c t : ℝ) : |a + b + c - t| ≤ |a| + |b| + |c| + |t| := by
        have h1 := abs_sub (a + b + c) t
        have h2 := abs_add_le (a + b) c
        have h3 := abs_add_le a b
        grind
      exact htri _ _ _ _
    _ ≤ G * M * d + 2 * Real.pi * C + G * M * d + G /  N  := by
      gcongr
    _ = _ := by  ring

end PottsDiscontinuity.Bethe
