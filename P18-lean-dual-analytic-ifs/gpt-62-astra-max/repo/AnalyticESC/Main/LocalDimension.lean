module
public import AnalyticESC.Main.Example
public import AnalyticESC.Dimension.Geometry

@[expose] public section
namespace AnalyticESC
open Set Metric Filter Topology MeasureTheory

private lemma local_limit {m : ℝ → ℝ} {c ρ a b : ℝ} (hc : 0 < c) (hc' : c < 1)
    (hp : 0 < ρ) (ha : 0 < a) (hb : 0 < b)
    (h : ∀ (n : ℕ) r, c^(n+1) < r → r ≤ c^n → m r ∈ Icc (a*ρ^n) (b*ρ^n)) :
    (∀ r : Scale, 0 < m r) ∧ RatioLimit m (Real.log ρ / Real.log c) := by
  choose n lo hi using fun r : Scale => exists_nat_pow_near_of_lt_one r.2.1 r.2.2.le hc hc'
  have bounds r := h (n r) r (lo r) (hi r)
  refine ⟨fun r => (mul_pos ha (pow_pos hp _)).trans_le (bounds r).1,?_⟩
  let d := Real.log ρ / Real.log c
  have hd : d*Real.log c = Real.log ρ := div_mul_cancel₀ _ (Real.log_neg hc hc').ne
  apply ratio_of_bounded (tendsto_abs_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp tendsto_comap)) (K := (|Real.log a|+|Real.log b|) + |d| * |Real.log c|)
  apply Eventually.of_forall; intro r
  have e := log_gap ha hb (pow_pos hp _) (bounds r)
  have e' := log_gap hc one_pos (pow_pos hc (n r)) (u := r) (by grind)
  simp only [Real.log_pow,Real.log_one,abs_zero,add_zero] at e e'
  change |Real.log (m r) - d*Real.log r| ≤ _
  rw [show Real.log (m r) - d*Real.log r = (Real.log (m r) - n r*Real.log ρ) - d*(Real.log r - n r*Real.log c) by grind]
  exact (abs_sub _ _).trans (add_le_add e (by rw [abs_mul]; gcongr))

/-! A binary prefix of length `n` has derivative exactly `8⁻ⁿ` at the common fixed
point. Its cylinder mass is thus comparable to `8⁻ⁿˢ`, uniformly in the prefix. -/
namespace Example
noncomputable abbrev u := (1/8:ℝ)
noncomputable abbrev π₀ := exampleIFS.natProj
private def binary (n : ℕ) : Finset (Fin n → Fin 3) := Fintype.piFinset fun _ => {0,1}
private lemma mem_binary {n : ℕ} {v : Fin n → Fin 3} : v ∈ binary n ↔ ∀ k, v k ≠ 2 := by
  grind [binary]

private lemma at_zero {w : List (Fin 3)} (hw : 2 ∉ w) : exampleIFS.comp w 0 = 0 ∧
    deriv (exampleIFS.comp w) 0 = (1/8:ℂ)^w.length := by
  induction w with
  | nil => simp
  | cons i w ih =>
    obtain ⟨ez,ed⟩ := ih (by grind)
    rw [exampleIFS.deriv_comp_cons _ _ (z := 0) (by simpa using exampleIFS.closedReal zero_I),IFS.comp_cons,Function.comp_apply,ez,ed]
    change exampleMaps i 0 = _ ∧ deriv (exampleMaps i) 0 * _ = _
    rw [derivative,List.length_cons,pow_succ,mul_comm]
    fin_cases i <;> norm_num [exampleMaps,a] at *

private lemma binary_mass {s} {ν : Measure (ℕ → Fin 3)} [IsProbabilityMeasure ν]
    (hg : exampleIFS.Gibbs s ν) : ∃ A > 0, ∃ B > 0, ∀ n, ν.real (pref n ⁻¹' ↑(binary n)) ∈
      Icc (A*(2*u^s)^n) (B*(2*u^s)^n) := by
  obtain ⟨A,hA,B,hB,H⟩ := hg
  refine ⟨A,hA,B,hB,fun n => ?_⟩
  have h (v) (hv : v ∈ binary n) := H v 0 (by norm_num)
  have h' (v) (hv : v ∈ binary n) : exampleIFS.weight (.ofFn v) 0 = u^n := by
    have hw : 2 ∉ List.ofFn v := by grind [mem_binary]
    simp [IFS.weight,(at_zero hw).2,u]
  have card : (binary n).card = 2^n := by simp [binary]
  have hs := sum_bounds fun v hv => (h' v hv) ▸ h v hv
  rw [sum_cyl] at hs
  simp only [Finset.sum_const,card,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat,←Real.rpow_pow_comm (by norm_num : 0 ≤ u) s n] at hs
  simpa only [mul_pow,mul_left_comm,mul_assoc] using hs

/-- The coordinate `x(1+x)` contracts by at least a factor eight under either
binary letter, while all letters give `f_i(x) ≥ x/8`. -/
private lemma step (i : Fin 3) {x : ℝ} (hx : x ∈ I) :
    let y := exampleIFS.realMap i x
    u*x ≤ y ∧ (i = 2 → 1/4 ≤ y) ∧ (i ≠ 2 → y*(1+y) ≤ u*(x*(1+x))) := by
  simp only [IFS.realMap,exampleIFS,real,Complex.ofReal_re]
  obtain ⟨h0,h1⟩ := hx
  have h2 : x^2 ≤ x := by nlinarith
  fin_cases i <;> norm_num  <;> (try constructor) <;> nlinarith [sq_nonneg x, mul_nonneg (sq_nonneg x) (sub_nonneg.mpr h1), mul_self_le_mul_self (sq_nonneg x) h2]

/-- Two-sided comparison of the binary cylinders with balls around zero. -/
private lemma scales (n : ℕ) (ω : ℕ → Fin 3) :
    (pref n ω ∈ binary n → π₀ ω * (1 + π₀ ω) ≤ 2*u^n) ∧
    (pref n ω ∉ binary n → 2*u^n ≤ π₀ ω) := by
  induction n generalizing ω with
  | zero =>
    have hx := exampleIFS.pi_mem ω
    grind [mem_binary, hx.1, hx.2, mul_self_le_mul_self hx.1 hx.2]
  | succ n ih =>
    let τ := shift 1 ω
    obtain ⟨up,lo⟩ := ih τ
    obtain ⟨low,two,high⟩ := step (ω 0) (exampleIFS.pi_mem τ)
    have e : pref (n+1) ω ∈ binary _ ↔ ω 0 ≠ 2 ∧ pref n τ ∈ binary _ := by
      simp [mem_binary,Fin.forall_fin_succ,pref,τ,shift]
    rw [π₀,e,pow_succ,exampleIFS.natProj_eq_realMap ω]
    grind [pow_le_one₀]

end Example
open Example

/-- The same cylinder sandwich works for balls and for the leftmost grid cell:
for points of the attractor only the right endpoint convention differs. -/
lemma edge_mass {s : ℝ} {ν : Measure (Address 3)} [IsProbabilityMeasure ν] (hg : exampleIFS.Gibbs s ν)
    {S : ℝ → Set ℝ} (hm : ∀ r, MeasurableSet (S r)) (hl : ∀ r, Ico 0 r ⊆ S r)
    (hu : ∀ r, S r ⊆ Iic r) : (∀ r : Scale, 0 < (exampleIFS.natural ν).real (S r)) ∧
    RatioLimit (fun r => (exampleIFS.natural ν).real (S r)) (s - 1/3) := by
  obtain ⟨A,hA,B,hB,H⟩ := binary_mass hg
  set ρ := 2*u^s
  have hp : 0 < ρ := by positivity
  have hd : s-1/3 = Real.log ρ / Real.log u := by
    have h8 : Real.log u = -(3 * Real.log 2) := by
      rw [u,one_div,Real.log_inv,show (8:ℝ) = 2^3 by norm_num,Real.log_pow]; norm_num
    rw [Real.log_mul two_ne_zero (Real.rpow_pos_of_pos (by norm_num : 0<u) s).ne',Real.log_rpow (by norm_num),h8]
    field_simp; ring
  rw [hd]
  apply local_limit (m := fun r => (exampleIFS.natural ν).real (S r)) (by norm_num : 0 < u) (by norm_num) hp (mul_pos hA (pow_pos hp 2)) hB
  intro n r h₁ h₂
  rw [map_measureReal_apply exampleIFS.continuous_natProj.measurable (hm r),
    mul_assoc A,← pow_add,add_comm 2 n]
  constructor
  · refine (H (n+2)).1.trans (measureReal_mono fun ω h => hl r ⟨(exampleIFS.pi_mem ω).1,?_⟩)
    have e := (scales (n+2) ω).1 h
    change π₀ ω < r
    grw [show π₀ ω ≤ π₀ ω * (1+π₀ ω) by nlinarith [sq_nonneg (π₀ ω)],e]; grind [pow_succ]
  · refine (measureReal_mono fun ω h => ?_).trans (H n).2
    by_contra hn
    have := (scales n ω).2 hn
    linarith [show π₀ ω ≤ r from hu r h, pow_pos (by norm_num : 0 < u) n]

end AnalyticESC
