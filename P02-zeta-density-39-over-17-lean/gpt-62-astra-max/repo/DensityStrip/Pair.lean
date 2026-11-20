module
public import DensityStrip.Critical
public import LaterPairs.PhysicalDetectorParameters

@[expose] public section
noncomputable section
open Real MeasureTheory Filter Finset Set MathCollab.Density MathCollab.Density.Stronger
open GuthMaynard.Improvement Montgomery.RationalMoment.RightDetector TaoTrudgianYang2025
namespace DensityStrip

/-- An exponent-pair tail at the single threshold `T^q`. -/
private theorem pair_integral {k l s y q e p m : ℝ} (pair : ExponentPair k l) (hk : 0<k)
    (hs : 1/2<s) (hy : 0<y) (he : 0<e) (he' : e≤1) (hq : 1/8<q) (hgap : q+e<y*(s-1/2))
    (h₁ : 1-6*q+e ≤ p+m*e) (h₂ : 1+l/k-(4+(2+4*l)/k)*q+e ≤ p+m*e) :
    IntegralCount s y e (p+m*e) := by
  apply count_of_excess hs hy he' hgap
  let η := (q-1/8)/2
  have hη : 0<η := by dsimp [η]; linarith
  obtain ⟨C,hC,hex⟩ := pair.critical_physical_excess_general hk hη he
  refine ⟨2*C,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (1:ℝ),hex,(tendsto_rpow_atTop hη).eventually_ge_atTop ((3:ℝ)^(1/8+η))] with T hT hex hc
  have ht : 0<T := by linarith
  have hr : (3*T)^(1/8+η) ≤ T^q := calc
    _ ≤ T^η*T^(1/8+η) := by rw [mul_rpow (by norm_num : (0:ℝ)≤3) ht.le]; gcongr
    _ = _ := by rw [← rpow_add ht]; congr 1; dsimp [η]; ring
  apply (hex _ (rpow_pos_of_pos ht q) hr).trans
  have reduce (u v : ℝ) (h : u+q*v+e ≤ q+(p+m*e)) : T^e*(T^u*(T^q)^v) ≤ T^q*T^(p+m*e) := by
    simp only [← rpow_mul ht.le,← rpow_add ht]; apply rpow_le_rpow_of_exponent_le hT; linarith only [h]
  rw [show T*(T^q)^(-5:ℝ) = T^(1:ℝ)*(T^q)^(-5:ℝ) by rw [rpow_one]]
  have hx := reduce 1 (-5) (by linarith only [h₁])
  have hy := reduce (1+l/k) (-3-(2+4*l)/k) (by nlinarith only [h₂])
  convert mul_le_mul_of_nonneg_left (add_le_add hx hy) hC.le using 1 <;> ring

/-- The detector transfer shared by the quadratic, cube, universal and
sharp polynomial bounds. Only the two affine tail budgets and the
separated-polynomial count depend on the particular curve. -/
theorem pair_density {k l s a ε B c : ℝ} (pair : ExponentPair k l) (hk : 0<k) (hw : PhysicalDetectorWindow s a)
    (h₁ : 1-6*((3*a/4)*(s-1/2)) ≤ 3*a*(1-s))
    (h₂ : 1+l/k-(4+(2+4*l)/k)*((3*a/4)*(s-1/2)) ≤ 3*a*(1-s))
    (hB : 0≤B) (hc : 0<c) (hW : ∀ e, 0<e → e≤c → WindowCount s a (3*a*(1-s)) B e) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ T : ℝ, 2≤T → (zetaDensityCount s T:ℝ) ≤ C*T^(3*a*(1-s)+ε) := by
  let θ := (3*a/4)*(s-1/2); let b := 4+(2+4*l)/k; let m := B+2*b+13
  have hθ : 1/8<θ := hw.threshold
  have hl : 0 < l := lt_of_lt_of_le (by norm_num) pair.inTriangle.2.2.1
  have hb : 0<b := by dsimp [b]; positivity
  have hm : 0 < m+4 := by dsimp [m]; linarith
  let e := min c (min (1/8) (min ((θ-1/8)/3) (ε/(m+4))))
  have he : 0<e := lt_min hc (lt_min (by norm_num) (lt_min (by linarith) (div_pos hε hm)))
  obtain ⟨hec,he',hθ',hε'⟩ : e≤c ∧ e≤1/8 ∧ e≤(θ-1/8)/3 ∧ e≤ε/(m+4) := by simpa only [← le_min_iff] using le_refl e
  have heε := (le_div_iff₀ hm).mp hε'
  have he1 : e≤1 := by linarith
  let y := 3*a/4-e; let q := θ-2*e
  have hs := hw.sigma_high; have ha := hw.a_low; have hs' := hw.sigma_low
  have hy : 0<y := by dsimp [y]; linarith
  have hbm : B≤ m := by dsimp [m]; linarith
  apply window_density (u:=1/2) (by linarith) (mul_nonneg (by linarith) (by linarith)) hy (by dsimp [y]; linarith) (by linarith [hw.a_high]) he he1 (k:=m) _ _ hε (by linarith only [heε])
  · obtain ⟨C,hC,hw⟩ := hW e he hec
    refine ⟨C,hC,?_⟩
    filter_upwards [eventually_ge_atTop (1:ℝ),hw] with T hT hw
    intro N Q b W hn hl hh hb hloc hsep hlg
    exact (hw N b W hn hl hh hb hloc hsep hlg).trans (by gcongr)
  · apply pair_integral (q:=q) pair hk (by linarith) hy he he1 (by dsimp [q]; linarith)
    · dsimp [q,θ,y]; nlinarith only [mul_pos he (show 0<3/2-s by linarith)]
    · change 1-6*(θ-2*e)+e ≤ _
      change 1-6*θ ≤ _ at h₁
      nlinarith only [h₁,mul_le_mul_of_nonneg_right (show 13≤ m by dsimp [m]; linarith) he.le]
    · change 1+l/k-b*(θ-2*e)+e ≤ _
      change 1+l/k-b*θ ≤ _ at h₂
      nlinarith only [h₂,mul_le_mul_of_nonneg_right (show 2*b+1≤ m by dsimp [m]; linarith) he.le]
end DensityStrip
