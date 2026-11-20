module

public import AnalyticESC.Main.Example
public import AnalyticESC.Dimension.Symbolic

@[expose] public section

/-! The mass near zero is controlled by prefixes using only the two maps fixing zero.
Their compositions have derivative `8⁻ⁿ` at zero, and uniform distortion controls their
sizes and Gibbs weights on the whole interval. -/

namespace AnalyticESC

open Set Filter Metric Topology MeasureTheory
open Word (pref shift)

private noncomputable abbrev l : ℝ := 1 / 8

private theorem comp_zero_jet {w : List (Fin 3)} (hw : ∀ i ∈ w, i ≠ 2) :
    exampleIFS.comp w 0 = 0 ∧ deriv (exampleIFS.comp w) 0 = (1 / 8 : ℂ) ^ w.length := by
  induction w with
  | nil => simp
  | cons i w ih =>
    obtain ⟨h₀, h₁⟩ := ih fun j hj => hw j (List.mem_cons_of_mem _ hj)
    have hj := exampleMaps_zero_jet (hw i List.mem_cons_self)
    refine ⟨show exampleIFS.f i (exampleIFS.comp w 0) = 0 by aesop, ?_⟩
    rw [exampleIFS.deriv_comp_cons i w (zero_mem_closure_nbhd (by norm_num)), h₀, h₁,
      show deriv (exampleIFS.f i) 0 = _ from hj.2, List.length_cons, pow_succ']

private theorem comp_le_supDeriv {w : List (Fin 3)} (hw : ∀ i ∈ w, i ≠ 2) {x : ℝ} (hx : x ∈ I) :
    exampleIFS.reComp w x ≤ exampleIFS.supDeriv w := by
  have h := (convex_Icc 0 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun y hy => (exampleIFS.hasDerivAt_re_comp w hy).hasDerivWithinAt)
    (fun y hy => (Complex.abs_re_le_norm _).trans (exampleIFS.norm_deriv_le_supDeriv w hy))
    (by simp : (0 : ℝ) ∈ I) hx
  refine le_trans ?_ (mul_le_of_le_one_right (exampleIFS.supDeriv_pos w).le hx.2)
  simpa [IFS.reComp, Complex.zero_re, (comp_zero_jet hw).1,
    abs_of_nonneg (exampleIFS.re_comp_mem_I w hx).1, abs_of_nonneg hx.1] using h

private def goodWords (n : ℕ) : Finset (Fin n → Fin 3) := Fintype.piFinset fun _ => {0, 1}

private theorem mem_goodWords {n : ℕ} {v : Fin n → Fin 3} : v ∈ goodWords n ↔ ∀ k, v k ≠ 2 := by
  grind [goodWords]

private theorem goodLetters {n : ℕ} {v : Fin n → Fin 3} (hv : v ∈ goodWords n) :
    ∀ i ∈ List.ofFn v, i ≠ 2 := by
  simp_all [mem_goodWords]

private theorem good_prefix_of_small_proj (n : ℕ) (ω : ℕ → Fin 3) (h : exampleIFS.natProj ω ≤ l ^ n) :
    ∀ k < n, ω k ≠ 2 := by
  induction n generalizing ω with
  | zero => omega
  | succ n ih =>
    let y := exampleIFS.natProj (shift ω 1)
    have hy : y ∈ I := exampleIFS.natProj_mem_I _
    have hmap (i : Fin 3) : l * y + (if i = 2 then 1 / 2 else 0) ≤ exampleIFS.realMaps i y := by
      change _ ≤ (exampleMaps i y).re
      rw [exampleMaps_ofReal, Complex.ofReal_re]
      fin_cases i <;> norm_num [l] <;> nlinarith [hy.1, hy.2]
    rw [exampleIFS.natProj_eq_realMap] at h
    have h' := (hmap (ω 0)).trans h
    have hle : l ^ (n + 1) ≤ l := pow_le_of_le_one (by norm_num) (by norm_num) (by omega)
    have hne : ω 0 ≠ 2 := by
      intro he
      simp only [he] at h'
      grind
    rw [ite_eq_right hne, add_zero, pow_succ'] at h'
    have ht := ih (shift ω 1) ((mul_le_mul_iff_right₀ (by norm_num : 0 < l)).1 h')
    rintro (_ | k) hk
    all_goals simp_all

/-- The natural measure charges every ball at zero and has local dimension `s - 1/3` there. -/
theorem example_localDim {s : ℝ} {ν : Measure (ℕ → Fin 3)} [IsProbabilityMeasure ν]
    (hs : 0 ≤ s) (hν : exampleIFS.IsGibbs s ν) :
    (∀ r > 0, 0 < (ν.map exampleIFS.natProj).real (closedBall 0 r)) ∧
    ∀ c ∈ Ioc (0 : ℝ) 1,
      Tendsto (fun r => Real.log ((ν.map exampleIFS.natProj).real (closedBall 0 (c * r))) / Real.log r)
        (𝓝[>] 0) (𝓝 (s - 1 / 3)) := by
  obtain ⟨A, hA, B, hB, hG⟩ := hν
  obtain ⟨R, hR, hdist⟩ := exampleIFS.exists_distortion
  let b := B * R ^ s
  let ρ := 2 * l ^ s
  have hl : 0 < l := by simp
  have hl' : l < 1 := by norm_num
  have hρ : 0 < ρ := by positivity
  have hb : 0 < b := by positivity
  have hpower (w : List (Fin 3)) (hw : ∀ i ∈ w, i ≠ 2) (t : ℝ) (ht : 0 ≤ t) :
      (l ^ w.length) ^ t ≤ exampleIFS.supDeriv w ^ t ∧
        exampleIFS.supDeriv w ^ t ≤ R ^ t * (l ^ w.length) ^ t := by
    simpa [l, (comp_zero_jet hw).2, norm_pow, show ‖(1 / 8 : ℂ)‖ = (1 / 8 : ℝ) by norm_num]
      using hdist w 0 (by simp) t ht
  have hsize (w : List (Fin 3)) (hw : ∀ i ∈ w, i ≠ 2) : exampleIFS.supDeriv w ≤ R * l ^ w.length := by
    simpa using (hpower w hw 1 zero_le_one).2
  have hsum (n : ℕ) :
      A * ρ ^ n ≤ ∑ v ∈ goodWords n, ν.real (wordCylinder v) ∧
        ∑ v ∈ goodWords n, ν.real (wordCylinder v) ≤ b * ρ ^ n := by
    have hterm (v : Fin n → Fin 3) (hv : v ∈ goodWords n) :
        A * (l ^ s) ^ n ≤ ν.real (wordCylinder v) ∧
          ν.real (wordCylinder v) ≤ b * (l ^ s) ^ n := by
      have h := hpower _ (goodLetters hv) s hs
      simp only [List.length_ofFn, ← Real.rpow_pow_comm hl.le] at h
      have h' := hG n v
      dsimp [b]
      rw [mul_assoc]
      exact ⟨(mul_le_mul_of_nonneg_left h.1 hA.le).trans h'.1,
        h'.2.trans (mul_le_mul_of_nonneg_left h.2 hB.le)⟩
    have hd : (∑ _v ∈ goodWords n, (l ^ s) ^ n) = ρ ^ n := by
      simp [goodWords, ρ, mul_pow]
    simpa only [hd] using sum_mul_bounds (goodWords n) hterm
  let m (r : ℝ) := ν.real {ω | exampleIFS.natProj ω ≤ r}
  have hm (r : ℝ) : (ν.map exampleIFS.natProj).real (closedBall 0 r) = m r := by
    rw [map_measureReal_apply exampleIFS.measurable_natProj measurableSet_closedBall]
    congr 1
    ext ω
    simp [mem_closedBall, abs_of_nonneg (exampleIFS.natProj_mem_I ω).1]
  simp_rw [hm]
  have hlo (n : ℕ) : A * ρ ^ n ≤ m (R * l ^ n) := by
    refine (hsum n).1.trans ?_
    rw [IFS.sum_measureReal_wordCylinder]
    refine measureReal_mono fun ω hω => ?_
    change exampleIFS.natProj ω ≤ R * l ^ n
    rw [exampleIFS.natProj_eq_comp_prefix ω n]
    have hw := goodLetters (Finset.mem_coe.1 hω)
    exact (comp_le_supDeriv hw (exampleIFS.natProj_mem_I _)).trans (by simpa using hsize _ hw)
  have hup (n : ℕ) (r : ℝ) (hr : r ≤ l ^ n) : m r ≤ b * ρ ^ n := by
    refine le_trans ?_ (hsum n).2
    rw [IFS.sum_measureReal_wordCylinder]
    refine measureReal_mono fun ω hω => ?_
    rw [mem_preimage, Finset.mem_coe, mem_goodWords]
    exact fun k => good_prefix_of_small_proj n ω (le_trans hω hr) k k.isLt
  have hmono : Monotone m := fun _ _ hr => measureReal_mono fun _ hx => le_trans hx hr
  have hbnd (r : ℝ) (hr : 0 < r) : ∃ n : ℕ, R * l ^ n < r :=
    (((tendsto_pow_atTop_nhds_zero_of_lt_one hl.le hl').const_mul R).eventually
      (by simpa using gt_mem_nhds hr)).exists
  constructor
  · intro r hr
    obtain ⟨n, hn⟩ := hbnd r hr
    exact (mul_pos hA (pow_pos hρ n)).trans_le ((hlo n).trans (hmono hn.le))
  · intro c hc
    have hd : s - 1 / 3 = Real.log ρ / Real.log l := by
      have h₂ := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      have h₈ : Real.log l = -(3 * Real.log 2) := by
        rw [show l = ((2 : ℝ) ^ 3)⁻¹ by norm_num, Real.log_inv, Real.log_pow]; rfl
      dsimp only [ρ]
      rw [Real.log_mul two_ne_zero (Real.rpow_pos_of_pos hl _).ne', Real.log_rpow hl, h₈]
      grind
    rw [hd]
    obtain ⟨k, hk⟩ := hbnd (c * l) (mul_pos hc.1 hl)
    let a := A * ρ ^ k
    have h (n : ℕ) (r : ℝ) (hr₁ : l ^ (n + 1) < r) (hr₂ : r ≤ l ^ n) :
        a * ρ ^ n ≤ m (c * r) ∧ m (c * r) ≤ b * ρ ^ n := by
      refine ⟨?_, hup n (c * r) ((mul_le_of_le_one_left ((pow_pos hl (n + 1)).le.trans hr₁.le) hc.2).trans hr₂)⟩
      dsimp only [a]
      rw [mul_assoc, ← pow_add]
      refine (hlo (k + n)).trans (hmono (le_trans ?_ (mul_le_mul_of_nonneg_left hr₁.le hc.1.le)))
      rw [pow_add, pow_succ', ← mul_assoc, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right hk.le (pow_nonneg hl.le _)
    -- On each geometric annulus, the drift from the limiting log ratio is bounded.
    let d := Real.log ρ / Real.log l
    let K := |Real.log a| + |Real.log b| + |d| * |Real.log l|
    have hre : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioo 0 1 := Ioo_mem_nhdsGT one_pos
    have hbd : ∀ᶠ r in 𝓝[>] (0 : ℝ), |Real.log (m (c * r)) - d * Real.log r| ≤ K := hre.mono fun r hr => by
      obtain ⟨n, h₁, h₂⟩ := exists_nat_pow_near_of_lt_one hr.1 hr.2.le hl hl'
      have hA := log_sub_mem_Icc_of_mul_bounds (pow_pos hρ n) (by positivity) hb (h n r h₁ h₂)
      rw [Real.log_pow] at hA
      have h₃ := Real.log_lt_log (pow_pos hl _) h₁
      have h₄ := Real.log_le_log hr.1 h₂
      simp only [Real.log_pow, Nat.cast_add, Nat.cast_one] at h₃ h₄
      have hB : |(n : ℝ) * Real.log l - Real.log r| ≤ |Real.log l| := by grind
      rw [show Real.log (m (c * r)) - d * Real.log r =
        (Real.log (m (c * r)) - n * Real.log ρ) + d * (n * Real.log l - Real.log r) by grind]
      exact (abs_add_le _ _).trans (add_le_add (by clear * - hA; grind) (by rw [abs_mul]; gcongr))
    apply (zero_add d ▸ (bdd_le_mul_tendsto_zero' K hbd Real.tendsto_log_nhdsGT_zero.inv_tendsto_atBot).add_const d).congr'
    filter_upwards [hre] with r hr
    grind [Pi.inv_apply, Real.log_neg]

end AnalyticESC
