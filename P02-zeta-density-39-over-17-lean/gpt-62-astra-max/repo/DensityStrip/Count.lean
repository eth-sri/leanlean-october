module
public import DensityStrip.Blocks
public import DensityStrip.Low
public import MathCollab.Density.DetectorPoweredPieces

/-! At the upper edge we shift to `Re z = l-k` for the A-transform of
Bourgain's pair. There the contour itself is small, so only the same short
Taylor family as on the other strips has to be counted. -/
@[expose] public section
noncomputable section
open Real Finset Filter MathCollab.Density GuthMaynard.NativeMoment GuthMaynard.Improvement
open scoped ComplexConjugate
namespace DensityStrip

private theorem upper_window {s e : ℝ} (hl : 17/19 ≤ s) (hr : s ≤ 1) (he : 0<e) (he' : 2*e ≤ tiny) :
    WindowCount s (length s) (exponent s) 12 e := by
  refine ⟨1,zero_lt_one,?_⟩
  filter_upwards [eventually_ge_atTop (1:ℝ),short_count hl hr (mul_pos (by norm_num) he) he'] with T ht H
  intro Q N b W hN hlo hhi hb hloc hsep hlarge
  have hn : 0<Q := by exact_mod_cast (show 0<(Q:ℝ) by change 2 ≤ (Q:ℝ) at hN; linarith)
  rw [one_mul,show 12*e=6*(2*e) by ring]
  apply H Q hlo (hhi.trans (rpow_le_rpow_of_exponent_le ht (by linarith))) (fun n => conj (b n)) _ W hsep
  · intro t h; obtain ⟨h₁,h₂⟩ := hloc t h; exact ⟨by linarith,by linarith⟩
  · intro t h
    have H := hlarge t h
    rw [← detectingPolynomial_eq_boundedPolynomial] at H
    have h1 := norm_detectingPolynomial_conj Q (fun n => conj (b n)) t
    simp only [Complex.conj_conj] at h1
    rw [h1,norm_detectingPolynomial_eq_cpow_sum hn] at H
    simpa only [dirichletPoly,dyadicInterval,neg_mul,mul_comm Complex.I] using H
  · intro n hn; rw [Complex.norm_conj]; apply hb n
    exact (sourceRatioIndices_mem (by positivity) n).mpr (by change (Q:ℝ)<n ∧ (n:ℝ) ≤ 2*Q; exact_mod_cast mem_Ioc.mp hn)

/-- A pointwise zeta bound on an intermediate vertical line rules out the
integral branch whenever the smoothing power beats its growth exponent. -/
private theorem no_integral {u s e y q p : ℝ} (hu : 1/2 ≤ u) (hs : u<s) (hy : 0<y)
    (hq : 0 ≤ q) (hq' : q ≤ 1) (hgap : q+e/2<y*(s-u)) (hg : ∃ C : ℝ,0<C ∧
      ∀ t : ℝ, ‖riemannZeta ((u:ℂ)+(t:ℂ)*Complex.I)‖  ≤  C*(1+|t|)^q) : IntegralCount s y e p u := by
  obtain ⟨A,hA,hb⟩ := uniform_integral_on hu hs
  obtain ⟨C,hC,hg⟩ := hg
  refine ⟨1,zero_lt_one,?_⟩
  filter_upwards [eventually_gt_atTop (1:ℝ),(tendsto_rpow_atTop (show 0 < y*(s-u)-q-e/2 by linarith)).eventually_gt_atTop (4*A*C)] with T ht hsmall
  intro W z _ hloc hz hdet
  have ht0 : 0<T := by linarith
  suffices W=∅ by simp [this,Real.rpow_nonneg ht0.le]
  apply eq_empty_iff_forall_notMem.mpr
  intro t htW
  obtain ⟨hγ,hβ,hβ'⟩ := hz t htW
  have H := hb q C T (T^e) (T^y) (z t) hq hq' hC.le ht.le (by positivity) (by positivity)
    hβ hβ' (by rw [hγ,abs_of_nonneg (by linarith [(hloc t htW).1] : 0 ≤ t)]; exact (hloc t htW).2) hg
  rw [sqrt_eq_rpow,← rpow_mul ht0.le,← rpow_mul ht0.le] at H
  have hsc : T^(e*(1/2:ℝ))*T^(y*(u-(z t).re))*T^q  ≤  T^(e/2+y*(u-s)+q) := by
    simp only [← rpow_add ht0]; apply rpow_le_rpow_of_exponent_le ht.le
    nlinarith only [mul_le_mul_of_nonneg_left hβ hy.le]
  have h₁ := mul_le_mul_of_nonneg_left hsc (show 0 ≤ 4*A*C by positivity)
  have h₂ := mul_lt_mul_of_pos_right hsmall (rpow_pos_of_pos ht0 (e/2+y*(u-s)+q))
  rw [← rpow_add ht0, show y*(s-u)-q-e/2+(e/2+y*(u-s)+q)=0 by ring,rpow_zero] at h₂
  nlinarith only [h₁,h₂,H,hdet t htW]

theorem density {s ε : ℝ} (hl : 17/19 ≤ s) (hr : s ≤ 1) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ T : ℝ, 2 ≤ T → (zetaDensityCount s T:ℝ)  ≤  C*T^(exponent s+ε) := by
  let e := min (tiny/2) (ε/16)
  let y := 3*length s/4-tiny
  let u : ℝ := 139/194
  have he : 0<e := lt_min (by norm_num [tiny]) (by positivity)
  have h₁ : e ≤ tiny/2 := min_le_left ..
  have h₂ : e ≤ ε/16 := min_le_right ..
  obtain ⟨ha,ha',_⟩ := length_spec hl hr
  have hy : 0<y := by dsimp [y]; norm_num [tiny] at *; linarith
  have hs : u<s := by dsimp [u]; linarith
  apply window_density hs (mul_nonneg (by linarith : 0 ≤ 3*length s) (sub_nonneg.mpr hr)) hy
    (by dsimp [y]; norm_num [tiny]) (by linarith) he (by norm_num [tiny] at h₁; linarith)
    (upper_window hl hr he ((le_div_iff₀' (by norm_num)).mp h₁)) _ hε (by linarith) (by norm_num [u])
  apply no_integral (q:=13/194+2*tiny) (by norm_num [u]) hs hy (by norm_num [tiny]) (by norm_num [tiny])
  · have hm := long_margin hl hr
    dsimp only [y,u]; norm_num [tiny] at hm h₁ ⊢; nlinarith only [hm,h₁,hl]
  · exact pair_growth pair₁ (by norm_num [tiny]) (by norm_num [u]) (by norm_num [u]) (by norm_num [u])

end DensityStrip
