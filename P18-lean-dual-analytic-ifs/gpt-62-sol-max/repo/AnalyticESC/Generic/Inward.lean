module

public import AnalyticESC.Generic.Class

@[expose] public section

/-! Interpolation toward an interior point gives strict interior images and preserves orientation. -/

namespace AnalyticESC

open Set Filter Topology

noncomputable def inward (f : ℂ → ℂ) (p t : ℝ) (z : ℂ) : ℂ :=
  (t : ℂ) * p + (1 - (t : ℂ)) * f z

theorem re_inward (f : ℂ → ℂ) (p t x : ℝ) :
    (inward f p t x).re = t * p + (1 - t) * (f x).re := by simp [inward]

theorem re_inward_mem {f : ℂ → ℂ} {p t x : ℝ} (ht : t ≤ 1) (hx : (f x).re ∈ I) :
    (inward f p t x).re ∈ Icc (t * p) (1 - t * (1 - p)) := by
  rw [re_inward]
  constructor <;> (simp_all; nlinarith)

theorem _root_.Challenge.InClass.inward {ε p t : ℝ} {f : ℂ → ℂ} (hf : InClass ε f) (hε : 0 < ε)
    (hp : p ∈ Ioo 0 1) (ht : t ∈ Ioo 0 1) : InClass ε (AnalyticESC.inward f p t) := by
  have h (z : ℂ) : deriv (AnalyticESC.inward f p t) z = (1 - (t : ℂ)) * deriv f z := by
    unfold AnalyticESC.inward
    simp
  have ht'  := sub_pos.2 ht.2
  refine Challenge.InClass.of_deriv hε ?_ (fun x hx => by simp [AnalyticESC.inward, Complex.mul_im, hf.im_eq_zero x hx])
    (fun x hx => Icc_subset_Icc (mul_nonneg ht.1.le hp.1.le)
      (sub_le_self _ (mul_nonneg ht.1.le (sub_nonneg.2 hp.2.le))) (re_inward_mem ht.2.le (hf.re_mem_I x hx))) ?_ ?_
  · exact (differentiableOn_const _).add (hf.differentiableOn.const_mul _)
  · intro z hz
    rw [h]
    exact mul_ne_zero (by exact_mod_cast ht'.ne') (hf.deriv_ne_zero z hz)
  · intro z hz
    rw [h, norm_mul, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos ht']
    exact (mul_le_of_le_one_left (norm_nonneg _) (by grind)).trans_lt (hf.norm_deriv_lt_one z hz)

theorem IFS.exists_small_inward {N : ℕ} {ε : ℝ} (Φ : IFS N ε) (p : ℝ) {r : ℝ} (hr : 0 < r) :
    ∃ t ∈ Ioo 0 1, ∀ i, d2Map (Φ.f i) (inward (Φ.f i) p t) < r := by
  have H i : Tendsto (fun t => d2Map (Φ.f i) (inward (Φ.f i) p t)) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (id : ℝ → ℝ) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
    refine ((zero_mul _ : 0 * d2Map (Φ.f i) (fun _ => p) = 0) ▸ h.mul_const _).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    let f := Φ.f i
    have h (j : ℕ) (x : ℂ) : iteratedDeriv j f x - iteratedDeriv j (inward f p t) x =
        (t : ℂ) * (iteratedDeriv j f x - iteratedDeriv j (fun _ => (p : ℂ)) x) := by
      unfold inward
      cases j <;> simp [iteratedDeriv_const_add (Nat.succ_pos _), iteratedDeriv_const] <;> ring
    change t * d2Map f (fun _ => p) = d2Map f (inward f p t)
    simp [d2Map, jetDist, h, abs_of_nonneg (le_of_lt ht), Real.mul_iSup_of_nonneg, Finset.mul_sum, ht.le]
  exact ((show ∀ᶠ t : ℝ in 𝓝[>] 0, t ∈ Ioo 0 1 from Ioo_mem_nhdsGT one_pos).and (eventually_all.2 fun i => (H i).eventually (gt_mem_nhds hr))).exists

end AnalyticESC
