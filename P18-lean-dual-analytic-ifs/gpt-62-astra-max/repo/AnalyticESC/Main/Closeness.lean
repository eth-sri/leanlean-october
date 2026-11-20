module
public import AnalyticESC.Dual.Recursion
public import AnalyticESC.Analysis

@[expose] public section
/-! # Super-exponential smallness and the mean value theorem

Use samples on arbitrarily small subintervals of a rescaled interval. Two
well-separated samples give a small derivative in between. In particular,
there is no need for quantitative bounds for successive Taylor remainders.
-/
namespace AnalyticESC
open Set Filter Topology

/-- On each subinterval of `[0,1]` there is a sample smaller than any exponential rate. -/
def Flat (n : ℕ → ℕ) (U : ℕ → ℝ → ℝ) := ∀ a b, 0 ≤ a → a < b → b ≤ 1 →
  ∀ δ > 0, ∀ r > 0, ∀ᶠ k in atTop, ∃ x ∈ Icc a b, |U k x| ≤ δ*r^(n k)

/-- Flatness transfers across differentiation, even after an exponential loss. -/
lemma Flat.step {n U V} (h : Flat n U) {c : ℝ} (hc : 0 < c) (D : ∀ k x, x ∈ I → DifferentiableAt ℝ (U k) x ∧ c^(n k) * |V k x| ≤ |deriv (U k) x|) : Flat n V := by
  intro a b ha hab hb δ hδ r hr
  let s := (b-a)/3
  have hs : 0 < s := by dsimp [s]; linarith
  have eqs : 3*s=b-a := by dsimp [s]; ring
  filter_upwards [h a (a+s) ha (by linarith) (by linarith) (δ*s/2) (by positivity) (r*c) (by positivity),
    h (b-s) b (by linarith) (by linarith) hb (δ*s/2) (by positivity) (r*c) (by positivity)] with k hx hy
  obtain ⟨x,hx,ex⟩ := hx; obtain ⟨y,hy,ey⟩ := hy
  have hxy : x < y := by grind
  have hI : Icc x y ⊆ I := by grind
  obtain ⟨t,ht,et⟩ := mean_slope (fun z hz => (D k z hz).1.differentiableWithinAt) (by grind) (by grind) hxy
  refine ⟨t,by grind,?_⟩
  have H := mul_le_mul (D k t (hI ht)).2 (by grind : s ≤ y-x) hs.le (abs_nonneg _)
  rw [← abs_of_pos (sub_pos.mpr hxy),← abs_mul,et] at H
  rw [mul_pow] at ex ey
  exact le_of_mul_le_mul_right (a := c^(n k)*s) (by linarith [abs_sub (U k y) (U k x)]) (by positivity)

/-- Evaluate on a whole cylinder of depth `n k`. Its derivative has an exponential lower bound. -/
structure Window {N : ℕ} (Φ : IFS N) where
  word : ℕ → Letters N

namespace Window
variable {N : ℕ} {Φ : IFS N} (W : Window Φ)

abbrev n (k : ℕ) := (W.word k).length
abbrev point (k : ℕ) := Φ.R (W.word k)
lemma maps (k : ℕ) : MapsTo (W.point k) I I := Φ.re_comp_mem_I _
abbrev small (F : ℕ → ℝ → ℝ) := Flat W.n fun k => F k ∘ W.point k

lemma derive {F G : ℕ → ℝ → ℝ} (h : W.small F) {b : ℝ} (hb : 0 < b)
    (he : ∀ k x, x ∈ I → ∃ m : ℝ, b ^ W.n k ≤ |m| ∧ HasDerivAt (F k) (m * G k x) x) : W.small G := by
  apply h.step (mul_pos hb Φ.cmin_pos); intro k x hx
  obtain ⟨m,hm,hd⟩ := he k _ (W.maps k hx)
  have e := hd.comp x ((Φ.regular_R (W.word k)).1 x hx).differentiableAt.hasDerivAt
  refine ⟨e.differentiableAt,?_⟩; rw [e.deriv,abs_mul,abs_mul,mul_pow,mul_right_comm]
  have lo : Φ.cmin^W.n k ≤ |deriv (W.point k) x| := (Φ.R_bounds (W.word k) hx).1
  dsimp only [Function.comp_apply]; gcongr; exact (pow_pos Φ.cmin_pos _).le

/-- Apply the mean value theorem twice: first to `A-B` to get `A'/B'-1` small,
then to that ratio to get the difference of the two logarithmic derivatives. -/
abbrev revMap (a : ℕ → Address N) (k : ℕ) := Φ.R (block (W.n k) (a k)).reverse
noncomputable abbrev proj (a : ℕ → Address N) (k : ℕ) := restr (Φ.dualProj (W.n k) (a k))

lemma distort {a b} (h : W.small fun k x => W.revMap a k x - W.revMap b k x) :
    W.small fun k x => W.proj a k x - W.proj b k x := by
  have reg c k : Regular (W.revMap c k) := Φ.regular_R _
  have lo c k x (hx : x ∈ I) : Φ.cmin ^ W.n k ≤ |deriv (W.revMap c k) x| := by
    simpa using (Φ.R_bounds (block (W.n k) (c k)).reverse hx).1
  let V k x := deriv (W.revMap a k) x / deriv (W.revMap b k) x - 1
  have hv : W.small V := W.derive h Φ.cmin_pos fun k x hx => by
    refine ⟨_,lo b k x hx,?_⟩
    convert ((reg a k).1 x hx).differentiableAt.hasDerivAt.sub ((reg b k).1 x hx).differentiableAt.hasDerivAt using 1
    dsimp [V]; field_simp [(reg b k).2 x hx]
  apply W.derive hv Φ.cmin_pos; intro k x hx
  refine ⟨deriv (W.revMap a k) x / deriv (W.revMap b k) x,?_,?_⟩
  swap
  ·
    have e c : W.proj c k x = logDer (W.revMap c k) x := by
      change (Φ.dualProj (W.n k) (c k) x).re = _
      rw [Φ.partial_log _ _ (Φ.closedReal hx),← Φ.R_logDer _ (Φ.real_mem hx)]; rfl
    rw [e,e]; exact (ratio_jet (reg a k) (reg b k) hx).sub_const 1
  rw [abs_div,le_div_iff₀ (abs_pos.mpr ((reg b k).2 x hx))]
  exact (mul_le_of_le_one_right (pow_pos Φ.cmin_pos _).le ((Φ.R_bounds _ hx).2.trans (pow_le_one₀ Φ.cmax_nonneg Φ.cmax_lt_one.le))).trans (lo a k x hx)

lemma jets {A B : ℕ → ℝ → ℝ} (ha : ∀ k, AnalyticOnNhd ℝ (A k) I) (hb : ∀ k, AnalyticOnNhd ℝ (B k) I)
    (h : W.small fun k x => A k x - B k x) (r : ℕ) : W.small fun k x => deriv^[r] (A k) x - deriv^[r] (B k) x := by
  induction r with
  | zero => exact h
  | succ r ih =>
    apply W.derive ih one_pos; intro k x hx
    refine ⟨1,by simp,?_⟩; simp only [one_mul,Function.iterate_succ_apply']
    exact ((ha k).iterated_deriv r x hx).differentiableAt.hasDerivAt.sub ((hb k).iterated_deriv r x hx).differentiableAt.hasDerivAt

lemma samples {F} (hn : Tendsto W.n atTop atTop) (h : W.small F) :
    ∃ x : ℕ → I, Tendsto (fun k => F k (W.point k (x k))) atTop (𝓝 0) := by
  classical
  let P k (x : I) := |F k (W.point k x)| ≤ (1/2:ℝ)^W.n k
  refine ⟨fun k => Classical.epsilon (P k),tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero' (by simp) ?_
    ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0 ≤ (1/2:ℝ)) (by norm_num)).comp hn))⟩
  filter_upwards [h 0 1 le_rfl zero_lt_one le_rfl 1 one_pos (1/2) (by norm_num)] with k ⟨x,hx,he⟩
  exact Classical.epsilon_spec (p := P k) ⟨⟨x,hx⟩,by grind⟩

end Window
end AnalyticESC
