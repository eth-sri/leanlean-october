module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Classical.Incoming

/-! # Joining the two power tails on the outgoing side

The angular diffusion can be large where the profile is strictly concave. Where it
bends back to the right power tail, the transport term is strictly positive, so a
small diffusion works. Both choices are uniform, by compactness of the transition.
-/

@[expose] public noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Angular
open Real Set Filter
open scoped ContDiff Topology

def switch (δ w : ℝ) := smoothTransition ((w-δ)/δ)

def angle (α δ w : ℝ) := (1 - switch δ w) * incoming α w + switch δ w * w ^ α

def drift (α : ℝ) (f : ℝ → ℝ) (w : ℝ) := w * (α * f w - w * deriv f w) / 3

private theorem switch_smooth (δ : ℝ) : ContDiff ℝ ∞ (switch δ) :=
  smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const δ)

variable {α δ w : ℝ}

private theorem angle_left (hδ : 0 < δ) (hw : w ≤ δ) : angle α δ w = incoming α w := by
  simp [angle, switch, smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg
    (sub_nonpos.mpr hw) hδ.le)]

private theorem angle_right (hδ : 0 < δ) (hw : 2 * δ ≤ w) : angle α δ w = w ^ α := by
  have h : 1 ≤ (w-δ)/δ := (le_div_iff₀ hδ).2 (by linarith)
  simp [angle, switch, smoothTransition.one_of_one_le h]

private theorem angle_smooth (hδ : 0 < δ) : ContDiff ℝ ∞ (angle α δ) := by
  apply contDiff_iff_contDiffAt.2
  intro w
  by_cases hw : w < δ
  · exact smooth_incoming.contDiffAt.congr_of_eventuallyEq
      ((gt_mem_nhds hw).mono fun _ h => angle_left hδ h.le)
  · have hp : w ≠ 0 := ne_of_gt (by linarith)
    exact ((contDiffAt_const.sub (switch_smooth δ).contDiffAt).mul smooth_incoming.contDiffAt).add
      ((switch_smooth δ).contDiffAt.mul (contDiffAt_rpow_const_of_ne hp))

/-- On a closed half-line a smooth function agrees with the tail through its second jet,
including at the endpoint. -/
private theorem deriv_on {f g g' : ℝ → ℝ} {K : Set ℝ} (hK : UniqueDiffOn ℝ K)
    (hf : Differentiable ℝ f) (he : EqOn f g K) (hg : ∀ w ∈ K, HasDerivAt g (g' w) w) :
    EqOn (deriv f) g' K := by
  intro w hw
  rw [← (hf w).derivWithin (hK w hw), derivWithin_congr he (he hw)]
  exact (hg w hw).hasDerivWithinAt.derivWithin (hK w hw)

private theorem right_jet (ha : 0 < α) (ha1 : α < 1) (hδ : 0 < δ) {w : ℝ} (hw : 2*δ ≤ w) :
    drift α (angle α δ) w = 0 ∧ deriv (deriv (angle α δ)) w < 0 := by
  have hs := angle_smooth (α := α) hδ
  have hpow (z : ℝ) (hz : z ∈ Ici (2*δ)) : z ≠ 0 := ne_of_gt (by linarith [mem_Ici.mp hz])
  have h1 := deriv_on (uniqueDiffOn_Ici (2*δ)) (hs.differentiable (by simp))
    (fun _ h => angle_right hδ h) (fun z hz => hasDerivAt_rpow_const (p := α) (Or.inl (hpow z hz)))
  have h2 := deriv_on (uniqueDiffOn_Ici (2*δ)) ((contDiff_infty_iff_deriv.mp hs).2.differentiable (by simp)) h1
    (fun z hz => (hasDerivAt_rpow_const (p := α-1) (Or.inl (hpow z hz))).const_mul α)
  have hp : 0 < w := by linarith
  rw [drift, angle_right hδ hw, h1 hw, h2 hw]
  constructor
  · have h := rpow_add_one hp.ne' (α-1)
    rw [sub_add_cancel] at h; rw [h]; ring
  · exact mul_neg_of_pos_of_neg ha (mul_neg_of_neg_of_pos (by linarith) (rpow_pos_of_pos hp _))

private theorem left_jet (ha : 0 < α) (ha1 : α < 1) (hδ : 0 < δ) {w : ℝ} (hw : w < δ) :
    deriv (deriv (angle α δ)) w < 0 ∧ (w < -1 → drift α (angle α δ) w = 0) := by
  have eq : angle α δ =ᶠ[𝓝 w] incoming α := (gt_mem_nhds hw).mono fun _ h => angle_left hδ h.le
  refine ⟨eq.deriv.deriv_eq.trans_lt (incoming_concave ha ha1 w), ?_⟩
  intro hn
  have he : incoming α =ᶠ[𝓝 w] fun z => (-z)^α := (gt_mem_nhds hn).mono fun _ h => incoming_left h.le
  have hd := (hasDerivAt_id w).neg.rpow_const (p := α) (Or.inl (by dsimp; linarith))
  rw [drift, eq.self_of_nhds, eq.deriv_eq, he.self_of_nhds, he.deriv_eq, show deriv (fun z : ℝ => (-z)^α) w = _ from hd.deriv]
  dsimp
  have hp := rpow_add_one (ne_of_gt (by linarith : 0 < -w)) (α-1)
  rw [sub_add_cancel] at hp
  nlinarith [congrArg (α * ·) hp]

private theorem drift_join (hδ : 0 < δ) (ha : 0 < α) (ha1 : α < 1)
    (hgap : ∀ z ∈ Icc 0 (2*δ), z^α < incoming α z) {w : ℝ}
    (hw : 0 < w) (hw' : w < 2*δ) : 0 < drift α (angle α δ) w := by
  let s := switch δ
  have hcs := switch_smooth δ
  have hd := (hcs.differentiable (by simp) w).hasDerivAt
  have hf := (smooth_incoming (α := α)).differentiable (by simp) w
  have h1 := (((hasDerivAt_const w 1).sub hd).mul hf.hasDerivAt).add
    (hd.mul (hasDerivAt_rpow_const (p := α) (Or.inl hw.ne')))
  have hpow := rpow_add_one hw.ne' (α-1)
  rw [sub_add_cancel] at hpow
  have hform : drift α (angle α δ) w = w / 3 *
      ((1 - s w) * (α * incoming α w - w * deriv (incoming α) w) +
        w * deriv s w * (incoming α w - w^α)) := by
    rw [drift, show deriv (angle α δ) w = _ from h1.deriv, angle]
    dsimp only [s, Pi.sub_apply, Pi.add_apply, Pi.mul_apply]
    linear_combination (w * α * switch δ w / 3) * hpow
  rw [hform]
  apply mul_pos (by positivity) (add_pos_of_pos_of_nonneg _ _)
  · apply mul_pos (sub_pos.mpr (smoothTransition.lt_one_of_lt_one ((div_lt_one hδ).2 (by linarith))))
    have hx := hgap w ⟨hw.le, hw'.le⟩
    exact sub_pos.mpr ((mul_neg_of_pos_of_neg hw (incoming_slope_neg ha ha1 (by linarith))).trans
      (mul_pos ha ((rpow_pos_of_pos hw _).trans hx)))
  · have hm : Monotone s := smoothTransition.monotone.comp fun x y h =>
      div_le_div_of_nonneg_right (sub_le_sub_right h _) hδ.le
    exact mul_nonneg (mul_nonneg hw.le hm.deriv_nonneg) (sub_nonneg.mpr (hgap w ⟨hw.le, hw'.le⟩).le)

private theorem compact_ratio {K : Set ℝ} (hK : IsCompact K) (f g : ℝ → ℝ)
    (hf : ContinuousOn f K) (hg : ContinuousOn g K) (hpos : ∀ w ∈ K, 0 < g w) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ w ∈ K, f w ≤ M * g w := by
  obtain ⟨M, hM, hb⟩ := (hK.bddAbove_image (hf.div hg (fun w hw => (hpos w hw).ne'))).exists_ge 1
  exact ⟨M, hM, fun w hw => (div_le_iff₀ (hpos w hw)).1 (hb _ (mem_image_of_mem _ hw))⟩

structure Model (α : ℝ) where
  f : ℝ → ℝ
  a : ℝ → ℝ
  lam : ℝ
  Lam : ℝ
  width : ℝ
  pos : 0 < lam
  bounds : ∀ w, lam ≤ a w ∧ a w ≤ Lam
  measurable : Measurable a
  smooth : ContDiff ℝ ∞ f
  positive : ∀ w, 0 < f w
  power : ∀ w, width < |w| → f w = |w|^α
  super : ∀ w, a w * deriv (deriv f) w ≤ drift α f w

theorem exists_model (ha : 0 < α) (ha1 : α < 1) : Nonempty (Model α) := by
  have hgap := (continuousAt_rpow_const 0 α (Or.inr ha.le)).eventually_lt
    (smooth_incoming (α := α)).continuous.continuousAt
    (by simpa [zero_rpow ha.ne'] using incoming_pos ha ha1 (le_refl 0))
  obtain ⟨l, r, ⟨hl, hr⟩, H⟩ := mem_nhds_iff_exists_Ioo_subset.1 hgap
  let δ := r / 3
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hg (z : ℝ) (hz : z ∈ Icc 0 (2*δ)) : z ^ α < incoming α z :=
    H ⟨hl.trans_le hz.1, hz.2.trans_lt (by dsimp [δ]; linarith)⟩
  let f := angle α δ
  let J := deriv (deriv f)
  let D := drift α f
  have hs := angle_smooth (α := α) hδ
  have hcJ : Continuous J := (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hs).2).2.continuous
  have hcD : Continuous D := (continuous_id.mul ((continuous_const.mul hs.continuous).sub
    (continuous_id.mul (contDiff_infty_iff_deriv.mp hs).2.continuous))).div_const 3
  obtain ⟨B, hB, hb⟩ := compact_ratio (K := Icc (-1) (δ / 2)) isCompact_Icc
    (-D) (-J) hcD.neg.continuousOn hcJ.neg.continuousOn (fun z hz =>
      neg_pos.mpr (left_jet ha ha1 hδ (hz.2.trans_lt (by linarith))).1)
  let K := Icc (δ/2) (2*δ) ∩ {z | 0 ≤ J z}
  have hk : IsCompact K := isCompact_Icc.inter_right (isClosed_le continuous_const hcJ)
  obtain ⟨M, hM, hm⟩ := compact_ratio hk J D hcJ.continuousOn hcD.continuousOn (fun z hz => by
    rcases hz with ⟨⟨hlo,hhi⟩, hj⟩
    apply drift_join hδ ha ha1 hg (by linarith)
    exact lt_of_le_of_ne hhi fun e => hj.not_gt (right_jet ha ha1 hδ e.ge).2)
  have hMpos : 0 < M := by linarith
  have hBpos : 0 < B := by linarith
  let a (w : ℝ) := if w ≤ δ/2 then B else M⁻¹
  have hle : M⁻¹ ≤ B := (inv_le_one_of_one_le₀ hM).trans hB
  refine ⟨⟨f, a, M⁻¹, B, max 1 (2*δ), inv_pos.mpr hMpos, fun w => ?_,
    measurable_const.ite measurableSet_Iic measurable_const, hs, fun w => ?_, fun w hw => ?_, fun w => ?_⟩⟩
  · dsimp [a]; split <;> exact ⟨by first | rfl | assumption, by first | rfl | assumption⟩
  · by_cases h : w ≤ 0
    · rw [show f w = _ from angle_left hδ (by linarith)]; exact incoming_pos ha ha1 h
    by_cases ht : 2*δ ≤ w
    · rw [show f w = _ from angle_right hδ ht]; exact rpow_pos_of_pos (lt_of_not_ge h) _
    have hw := hg w ⟨le_of_not_ge h, le_of_not_ge ht⟩
    have hh := mul_nonneg (sub_nonneg.mpr (smoothTransition.le_one ((w-δ)/δ))) (sub_nonneg.mpr (le_of_lt hw))
    dsimp [f,angle,switch]; nlinarith [rpow_pos_of_pos (lt_of_not_ge h) α]
  · rcases lt_or_ge w 0 with h | h
    · rw [abs_of_neg h] at *
      change angle α δ w = _
      rw [angle_left hδ (by linarith), incoming_left (by linarith [(le_max_left 1 (2*δ)).trans_lt hw])]
    · rw [abs_of_nonneg h] at *
      exact angle_right hδ ((le_max_right _ _).trans hw.le)
  · change a w * J w ≤ D w
    by_cases h : w ≤ δ/2
    · rw [show a w = B by simp [a,h]]
      rcases le_or_gt (-1) w with hl | hl
      · simpa only [Pi.neg_apply, mul_neg, neg_le_neg_iff] using hb w ⟨hl,h⟩
      · obtain ⟨hj, h0⟩ := left_jet ha ha1 hδ (h.trans_lt (by linarith))
        exact (mul_nonpos_of_nonneg_of_nonpos hBpos.le hj.le).trans_eq (h0 hl).symm
    rw [show a w = M⁻¹ by simp [a,h]]
    rcases le_or_gt (2*δ) w with ht | ht
    · obtain ⟨h0, hj⟩ := right_jet ha ha1 hδ ht
      exact (mul_nonpos_of_nonneg_of_nonpos (inv_pos.mpr hMpos).le hj.le).trans_eq h0.symm
    rcases le_or_gt 0 (J w) with hj | hj
    · rw [inv_mul_le_iff₀ hMpos]; exact hm w ⟨⟨(le_of_not_ge h),ht.le⟩,hj⟩
    · exact (mul_nonpos_of_nonneg_of_nonpos (inv_pos.mpr hMpos).le hj.le).trans
        (drift_join hδ ha ha1 hg (by linarith) ht).le

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Angular
