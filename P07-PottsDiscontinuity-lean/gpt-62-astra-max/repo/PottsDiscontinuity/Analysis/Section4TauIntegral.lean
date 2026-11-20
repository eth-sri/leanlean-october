module
public import PottsDiscontinuity.Analysis.Section4Series

/-! Integrate the ordinary partial sums, without Abel damping. After multiplying the
cosine polynomial in their derivative by `cos (x/2)`, it telescopes with monotone
weights `tanh (kλ)`. The resulting secant bound cancels the half-angle factor of `P'`. -/
@[expose] public section
open Filter MeasureTheory Real Topology Set intervalIntegral Finset
namespace PottsDiscontinuity

private theorem weighted_diff_bound (a b : ℕ → ℝ) (ha : ∀ n, |a n| ≤ 1)
    (hb : Monotone b) (hp : 0 ≤ b 0) (N : ℕ) :
    |∑ n ∈ range N, (a (n+1)-a n)*b n| ≤ 2*b N := by
  suffices H : ∀ N, |(∑ n ∈ range N, (a (n+1)-a n)*b n)-a N*b N| ≤ b N by
    have hn := hp.trans (hb (Nat.zero_le N))
    have haN : |a N*b N| ≤ b N := by rw [abs_mul,abs_of_nonneg hn]; simpa using mul_le_mul_of_nonneg_right (ha N) hn
    rw [abs_le]; constructor <;> linarith only [(abs_le.mp (H N)).1,(abs_le.mp (H N)).2,(abs_le.mp haN).1,(abs_le.mp haN).2]
  intro k; induction k with
  | zero => simpa [abs_mul, abs_of_nonneg hp] using mul_le_mul_of_nonneg_right (ha 0) hp
  | succ n ih =>
    rw [sum_range_succ,show _ + (a (n+1)-a n)*b n - a (n+1)*b (n+1) =
      ((∑ j ∈ range n, (a (j+1)-a j)*b j)-a n*b n)-a (n+1)*(b (n+1)-b n) by ring]
    refine (abs_sub ..).trans ?_
    rw [abs_mul,abs_of_nonneg (sub_nonneg.mpr (hb (Nat.le_succ n)))]
    nlinarith [mul_le_mul_of_nonneg_right (ha (n+1)) (sub_nonneg.mpr (hb (Nat.le_succ n)))]

private theorem tanh_mono : Monotone Real.tanh := by
  intro x y h
  apply (strictMonoOn_artanh.le_iff_le ⟨neg_one_lt_tanh _,tanh_lt_one _⟩ ⟨neg_one_lt_tanh _,tanh_lt_one _⟩).mp
  simpa only [artanh_tanh] using h

private theorem tauPartial_bound {lam α : ℝ} (hlam : 0 < lam) (hα : |α| < π) (N : ℕ) :
    |Bethe.tauPartial lam α N| ≤ |α|/(π * Real.cos (α/2)) := by
  let b (n : ℕ) := Real.tanh (lam * (n+1:ℕ))
  let g (x : ℝ) := ∑ n ∈ range N, (-1:ℝ)^(n+1) * Real.cos ((n+1:ℕ)*x) * b n / π
  have hb : Monotone b := fun i j hij => tanh_mono (mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.succ_le_succ hij) hlam.le)
  have hg (x : ℝ) : |(2*π*Real.cos (x/2))*g x| ≤ 2 := by
    let a (n : ℕ) := (-1:ℝ)^n * Real.cos ((n+1/2)*x)
    have ha (n) : |a n| ≤ 1 := by simpa [a,abs_mul,abs_pow] using abs_cos_le_one (((n:ℝ)+1/2)*x)
    have he (n : ℕ) : a (n+1)-a n = (2*Real.cos (x/2))*((-1:ℝ)^(n+1)*Real.cos ((n+1:ℕ)*x)) := by
      have h := Real.cos_add_cos (((n:ℝ)+1+1/2)*x) (((n:ℝ)+1/2)*x)
      dsimp [a]; push_cast; rw [pow_succ]; ring_nf at h ⊢; linear_combination -(-1:ℝ)^n * h
    have h0 := tanh_mono (show 0 ≤ lam*((0+1:ℕ):ℝ) by positivity); rw [Real.tanh_zero] at h0
    have hsum := weighted_diff_bound a b ha hb h0 N
    dsimp [g]; rw [Finset.mul_sum]; simp_rw [he] at hsum
    refine LE.le.trans (b := |∑ j ∈ range N, 2*Real.cos (x/2)*((-1:ℝ)^(j+1)*Real.cos ((j+1:ℕ)*x))*b j|) (le_of_eq ?_) ?_
    · congr 1; apply sum_congr rfl; intros; field_simp <;> ring
    convert hsum.trans (mul_le_mul_of_nonneg_left (Real.tanh_lt_one _).le (by norm_num : (0:ℝ) ≤ 2)) using 1 <;> norm_num
  have hd (x) : HasDerivAt (fun t => Bethe.tauPartial lam t N) (g x) x := by
    apply HasDerivAt.fun_sum; intro n _
    convert (((hasDerivAt_id x).const_mul ((n+1:ℕ):ℝ)).sin.const_mul ((-1:ℝ)^(n+1)/(π*(n+1))*b n)) using 1 <;> simp [b] <;> field_simp <;> ring
  have hc : 0 < Real.cos (α/2) := Real.cos_pos_of_mem_Ioo ⟨by grind [abs_lt.mp hα],by grind [abs_lt.mp hα]⟩
  let X := Icc (-|α|) |α|
  have hbd (x) (hx : x ∈ X) : ‖g x‖ ≤ 1/(π*Real.cos (α/2)) := by
    have hm : Real.cos (α/2) ≤ Real.cos (x/2) := by
      rw [←Real.cos_abs (α/2),←Real.cos_abs (x/2)]; simp only [abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
      exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_pos]) (div_le_div_of_nonneg_right (abs_le.mpr hx) (by norm_num))
    have hh := hg x; rw [abs_mul,abs_of_pos (mul_pos (by positivity) (hc.trans_le hm))] at hh
    rw [Real.norm_eq_abs,le_div_iff₀ (by positivity)]; nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm Real.pi_nonneg) (abs_nonneg (g x))]
  have H := (convex_Icc (-(|α|)) |α|).norm_image_sub_le_of_norm_hasDerivWithin_le (fun x _ => (hd x).hasDerivWithinAt) hbd (x := 0) (y := α) (by constructor <;> grind [abs_nonneg α]) (abs_le.mp le_rfl)
  simpa [Bethe.tauPartial,div_eq_mul_inv,mul_comm] using H

private theorem product_bound {lam α : ℝ} (hlam : 0 < lam) (hα : |α| < π) (N : ℕ) :
    |fourierPPrime lam α * Bethe.tauPartial lam α N| ≤ 1 := by
  by_cases hz : α = 0
  · simp [fourierPPrime,hz]
  let s := Real.sin (α/2); let c := Real.cos (α/2)
  have hj : |α|/π ≤ |s| := by
    have h := Real.mul_abs_le_abs_sin (x := α/2) (by rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]; linarith)
    rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)] at h; dsimp [s]; convert h using 1; ring
  have hs : 0 < |s| := (div_pos (abs_pos.mpr hz) Real.pi_pos).trans_le hj
  have hc : 0 < c := Real.cos_pos_of_mem_Ioo ⟨by grind [abs_lt.mp hα],by grind [abs_lt.mp hα]⟩
  have den : 1-Real.cos α = 2*s^2 := by dsimp [s]; have h := Real.sin_sq_eq_half_sub (α/2); rw [show 2*(α/2) = α by ring] at h; linarith
  have h1 : 0 < 1-Real.cos α := by rw [den]; positivity [abs_pos.mp hs]
  have h2 : 1-Real.cos α ≤ Real.cosh (2*lam)-Real.cos α := sub_le_sub_right (Real.one_le_cosh _) _
  have hp : |fourierPPrime lam α| ≤ c/|s| := by
    rw [fourierPPrime,if_neg hz,show Real.sin α / _ - Real.sin α / (1-Real.cos α) = -Real.sin α *((1-Real.cos α)⁻¹-(Real.cosh (2*lam)-Real.cos α)⁻¹) by ring]
    rw [abs_mul,abs_mul,abs_neg,abs_of_nonneg (sub_nonneg.mpr (inv_anti₀ h1 h2)),abs_of_pos (by norm_num : (0:ℝ)<1/2)]
    calc _ ≤ 1/2*(|Real.sin α| * (1-Real.cos α)⁻¹) := by gcongr; linarith [inv_pos.mpr (h1.trans_le h2)]
         _ ≤ _ := by rw [den,show Real.sin α = 2*s*c by convert Real.sin_two_mul (α/2) using 1 <;> ring_nf,abs_mul,abs_mul,abs_of_pos hc,abs_of_pos (by norm_num : (0:ℝ)<2),←sq_abs s]; field_simp; nlinarith
  rw [abs_mul]; apply (mul_le_mul hp (tauPartial_bound hlam hα N) (abs_nonneg _) (by positivity)).trans
  change c/|s| *(|α|/(π*c)) ≤ 1
  field_simp; nlinarith [(div_le_iff₀ Real.pi_pos).mp hj, mul_nonneg hc.le (sub_nonneg.mpr ((div_le_iff₀ Real.pi_pos).mp hj))]

/-- Termwise integration of the ordered Fourier partial sums against `P'`. -/
theorem fourierPPrime_tauSeries_integral {lam : ℝ} (hlam : 0 < lam) :
    ∃ S : ℝ, Tendsto (altTanhPartial lam) atTop (𝓝 S) ∧
      Tendsto (logCoshTauCorrectionPartial lam) atTop
        (𝓝 (∫ α in (-π)..π, fourierPPrime lam α * Bethe.tauSeries lam α)) := by
  let F N x := fourierPPrime lam x * Bethe.tauPartial lam x N
  have hm (N) : Measurable (F N) := by
    have hp : Measurable (fourierPPrime lam) := Measurable.ite (measurableSet_singleton 0) measurable_const (by fun_prop)
    apply hp.mul; unfold Bethe.tauPartial; fun_prop
  have ha : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ uIoc (-π) π → |x| < π := by
    filter_upwards [Measure.ae_ne volume π] with x hx h
    rw [uIoc_of_le (neg_le_self Real.pi_nonneg)] at h
    exact abs_lt.mpr ⟨h.1,lt_of_le_of_ne h.2 hx⟩
  have hb (N) : ∀ᵐ x ∂volume, x ∈ uIoc (-π) π → ‖F N x‖ ≤ 1 := ha.mono fun x hx h => product_bound hlam (hx h) N
  have hi (N) : IntervalIntegrable (F N) volume (-π) π := by
    rw [intervalIntegrable_iff]; apply Measure.integrableOn_of_bounded (by simp [uIoc]) (hm N).aestronglyMeasurable
    exact (ae_restrict_iff' measurableSet_uIoc).mpr (hb N)
  have hc := intervalIntegral.tendsto_integral_filter_of_dominated_convergence (μ := volume) (a := -π) (b := π)
    (F := F) (f := fun x => fourierPPrime lam x * Bethe.tauSeries lam x) (fun _ => (1:ℝ))
    (.of_forall fun N => (hm N).aestronglyMeasurable.restrict) (.of_forall hb) intervalIntegrable_const
    (ha.mono fun x hx h => by rw [Bethe.tauSeries_eq hlam (hx h)]; exact (Bethe.tendsto_tauPartial hlam (hx h)).const_mul _)
  obtain ⟨S,hS,_⟩ := identity43 lam hlam
  refine ⟨S,hS,hc.congr fun N => ?_⟩
  induction N with
  | zero => simp [F,Bethe.tauPartial,logCoshTauCorrectionPartial]
  | succ n ih =>
    let A := (-1:ℝ)^(n+1)/(π*(n+1))*tanh (lam*(n+1:ℕ))
    let G x := A*(fourierPPrime lam x*Real.sin ((n+1:ℕ)*x))
    have he : F (n+1) - F n = G := by funext x; simp only [Pi.sub_apply,F,Bethe.tauPartial,sum_range_succ,G,A]; ring
    have hg : IntervalIntegrable G volume (-π) π := he ▸ (hi (n+1)).sub (hi n)
    have hFG : F (n+1) = F n + G := by rw [←he]; abel
    rw [hFG]; simp only [Pi.add_apply]; rw [intervalIntegral.integral_add (hi n) hg,ih,logCoshTauCorrectionPartial,logCoshTauCorrectionPartial, sum_Icc_succ_top (by omega)]
    congr 1; dsimp [G,A]; rw [intervalIntegral.integral_const_mul]
    have h := fourierP_prime_sine_integral hlam (Nat.succ_pos n)
    rw [show lam * ((n+1:ℕ):ℝ) = ((n+1:ℕ):ℝ)*lam by ring,←h]; push_cast; simp only [div_eq_mul_inv,mul_inv_rev]; ring
end PottsDiscontinuity
