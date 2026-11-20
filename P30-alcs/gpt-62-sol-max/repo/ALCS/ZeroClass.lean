module

public import ALCS.Definitions
public import ALCS.Background.Phillips
public import Mathlib.Topology.Order.Monotone
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.Analysis.Normed.Operator.NNNorm

public section

/-! # Every `L^∞` system is zero-class (Theorem 1.5) -/

open MeasureTheory Filter Topology Set Function
open scoped ENNReal

variable {𝕜 X U : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup U] [NormedSpace 𝕜 U]

namespace ALCS

/-- Every subfamily of disjoint pulses can be played as a single unit input. -/
private lemma exists_pack (f : ℕ → ℝ → U) (hf : ∀ n, StronglyMeasurable (f n))
    (hb : ∀ n t, ‖f n t‖ ≤ 1) (hd : Pairwise (Disjoint on fun n => support (f n))) :
    ∃ P : Set ℕ → Lp U ∞ muPlus, (∀ A, ‖P A‖ ≤ 1) ∧
      (∀ ⦃A B⦄, Disjoint A B → P (A ∪ B) = P A + P B) ∧
      ∀ n, ⇑(P {n}) =ᵐ[muPlus] f n := by
  classical
  have one (s : ℝ) : ∃ i, ∀ j ≠ i, f j s = 0 := by
    by_contra! h
    obtain ⟨i, _, hi⟩ := h 0
    obtain ⟨j, hj, hj'⟩ := h i
    exact disjoint_left.1 (hd hj) hj' hi
  choose i hi using one
  let g (A : Set ℕ) : ℝ → U := ∑' n, A.indicator f n
  have hs (A : Set ℕ) : HasSum (A.indicator f) (fun s => A.indicator f (i s) s) :=
    Pi.hasSum.2 fun s => hasSum_single (i s) fun j hj => by
      simp [indicator, apply_ite (fun v : ℝ → U => v s), hi s j hj]
  have hn A : ∀ᵐ s ∂muPlus, ‖g A s‖ ≤ 1 := .of_forall fun s => by
    rw [show g A = _ from (hs A).tsum_eq]
    simp [indicator, apply_ite (fun v : ℝ → U => ‖v s‖ ≤ 1), hb]
  have hm A : MemLp (g A) ∞ muPlus := memLp_top_of_bound
    (StronglyMeasurable.tsum' (fun n => by
      by_cases h : n ∈ A <;> simp [indicator, h, hf, stronglyMeasurable_zero])).aestronglyMeasurable 1
    (hn A)
  refine ⟨fun A => (hm A).toLp _, fun A => norm_toLp_le (hm A) zero_le_one (hn A), ?_, ?_⟩
  · intro A B h
    rw [← MemLp.toLp_add, MemLp.toLp_eq_toLp_iff]
    exact .of_eq (by simpa only [g, indicator_union_of_disjoint h] using (hs A).summable.tsum_add (hs B).summable)
  · intro n
    refine (hm {n}).coeFn_toLp.trans (.of_forall fun s => ?_)
    simp [g, indicator, tsum_ite_eq]

variable (S : ALCS 𝕜 X U ∞)

/-- A lower bound `L` strictly below all positive-time input norms forces their
right-hand limit to be at least `2L`. Pack pulses with short trailing silences
into disjoint intervals approaching time `1`, then apply Phillips' lemma. -/
private lemma double_lower_bound {L ℓ : ℝ} (hK : ∀ h > 0, L < ‖S.Φ h‖)
    (hk : Tendsto (fun t => ‖S.Φ t‖) (𝓝[>] 0) (𝓝 ℓ)) : 2 * L ≤ ℓ := by
  classical
  have select (c : Ioi (0 : ℝ)) : ∃ r ∈ Ioo 0 (c.val / 2), ∃ (f : ℝ → U) (v : Lp U ∞ muPlus),
      StronglyMeasurable f ∧ (∀ s, ‖f s‖ ≤ 1) ∧ support f ⊆ Iio (c.val / 2) ∧
      ⇑v =ᵐ[muPlus] f ∧ L < ‖S.Φ (c.val / 2 + r) v‖ := by
    let h := c.val / 2
    have hp : 0 < h := half_pos c.2
    obtain ⟨u, hu, hx⟩ := (S.Φ h).exists_lt_apply_of_lt_opNorm (hK h hp)
    have ht := (S.T_cont (S.Φ h u)).mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
    have hR : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioo 0 h := Ioo_mem_nhdsGT hp
    obtain ⟨r, hr, hy⟩ := (hR.and (ht.norm.eventually_const_lt hx)).exists
    let A := Iio h ∩ {s | ‖u s‖ ≤ 1}
    let f := A.indicator ⇑u
    have hu_meas := Lp.stronglyMeasurable u
    have hm : StronglyMeasurable f := hu_meas.indicator (measurableSet_Iio.inter
      (hu_meas.norm.measurableSet_le stronglyMeasurable_const))
    have hb (s : ℝ) : ‖f s‖ ≤ 1 := by
      by_cases hs : s ∈ A <;> simp_all [f, A]
    have H := memLp_top_of_bound (μ := muPlus) hm.aestronglyMeasurable 1 (.of_forall hb)
    refine ⟨r, hr, f, H.toLp f, hm, hb, support_indicator_subset.trans inter_subset_left,
      H.coeFn_toLp, ?_⟩
    have he : f =ᵐ[muPlus] concat h ⇑u 0 := by
      filter_upwards [ae_le_lpNorm_exponent_top (Lp.memLp u)] with s hs
      simp [f, A, indicator, concat, hs.trans hu.le]
    change L < ‖S.Φ (h + r) (H.toLp f)‖
    simpa [S.free hp.le hr.1.le (H.coeFn_toLp.trans he)] using hy
  choose r hr f v hf hb hsupp hv hnear using select
  -- Use half the current budget for the active pulse, and its trailing silence as the next budget.
  let c : ℕ → Ioi (0 : ℝ) := Nat.rec ⟨1, zero_lt_one⟩ (fun _ s => ⟨r s, (hr s).1⟩)
  let h (n : ℕ) := (c n).val / 2
  let t (n : ℕ) := h n + r (c n)
  let a (n : ℕ) := 1 - t n
  have htpos (n : ℕ) : 0 < t n := add_pos (half_pos (c n).2) (hr (c n)).1
  have htc (n : ℕ) : t n ≤ (c n).val := by
    dsimp only [t, h]
    linarith [(hr (c n)).2]
  have hc (n : ℕ) : (c (n + 1)).val ≤ h n := (hr (c n)).2.le
  have hanti : Antitone (fun n => (c n).val) := antitone_nat_of_succ_le fun n =>
    (hc n).trans (half_le_self (c n).2.le)
  have hlim : Tendsto t atTop (𝓝 0) := by
    refine squeeze_zero (fun n => (htpos n).le) (fun n => (htc n).trans ?_)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num))
    simpa only [show (c 0).val = 1 from rfl, mul_one] using
      le_geom (u := fun n => (c n).val) (c := 1 / 2) (by norm_num) n
        (fun j _ => by simpa [h, div_eq_mul_inv, mul_comm] using hc j)
  let g (n : ℕ) := concat (a n) 0 (f (c n))
  have hd : Pairwise (Disjoint on fun n => support (g n)) := by
    refine Pairwise.of_lt fun i j hij => disjoint_left.2 fun s hi hj => ?_
    have hgap : t j ≤ r (c i) := (htc j).trans (hanti (Nat.succ_le_of_lt hij))
    simp only [mem_support, g, concat, Pi.zero_apply] at hi hj
    simp only [Set.subset_def, mem_support, mem_Iio] at hsupp
    grind
  obtain ⟨B, hBn, hBa, hB⟩ := exists_pack g
    (fun n => concat_measurable _ stronglyMeasurable_const (hf (c n))) (fun n s => by
      simp [g, concat, apply_ite (fun v : U => ‖v‖ ≤ 1), hb]) hd
  have heval (n : ℕ) : S.Φ 1 (B {n}) = S.Φ (t n) (v (c n)) := by
    have ha : 0 ≤ a n := sub_nonneg.mpr ((htc n).trans (hanti (Nat.zero_le n)))
    simpa [a] using S.delay ha (htpos n).le
      ((hB n).trans (concat_congr (a n) .rfl (hv (c n))).symm)
  have hmove := Phillips.norm_diagonal_tendsto_zero B hBn hBa
    (fun n => (S.T (t n) - ContinuousLinearMap.id 𝕜 X).comp (S.Φ 1)) fun A => by
      have hc := (S.T_cont (S.Φ 1 (B A))).comp (tendsto_nhdsWithin_iff.2
        ⟨hlim, .of_forall fun n => (htpos n).le⟩)
      simpa [Function.comp_def] using hc.sub_const (S.Φ 1 (B A))
  have k2 := hk.comp (tendsto_nhdsWithin_iff.2
    ⟨by simpa using hlim.add hlim, .of_forall fun n => add_pos (htpos n) (htpos n)⟩)
  rw [← add_zero ℓ]
  refine ge_of_tendsto' (k2.add hmove) fun n => ?_
  -- Play each pulse twice and subtract its (vanishing) semigroup increment.
  let f₂ := concat (t n) (f (c n)) (f (c n))
  have hb₂ : ∀ᵐ s ∂muPlus, ‖f₂ s‖ ≤ 1 := .of_forall fun s => by
    simp [f₂, concat, apply_ite (fun v : U => ‖v‖ ≤ 1), hb]
  have hm₂ := memLp_top_of_bound (concat_measurable _ (hf (c n)) (hf (c n))).aestronglyMeasurable 1 hb₂
  let w := hm₂.toLp f₂
  have hc := hm₂.coeFn_toLp.trans
    (concat_congr (t n) (hv (c n)) (hv (c n))).symm
  let x := S.Φ (t n) (v (c n))
  let z := S.T (t n) x - x
  have heq : (2 : 𝕜) • x = S.Φ (t n + t n) w - z := by
    rw [two_smul, S.composition _ _ (htpos n).le (htpos n).le _ _ _ hc]
    dsimp [x, z]
    abel
  have hn := norm_sub_le (S.Φ (t n + t n) w) z
  rw [← heq, norm_smul, RCLike.norm_ofNat] at hn
  simp only [Function.comp_apply, ContinuousLinearMap.comp_apply, sub_apply, ContinuousLinearMap.id_apply, heval]
  linarith only [hn, hnear (c n), (S.Φ (t n + t n)).unit_le_opNorm w (norm_toLp_le hm₂ zero_le_one hb₂)]

/-- **Theorem 1.5**: every abstract linear control system with `p = ∞` is zero-class. -/
theorem zero_class : S.IsZeroClass := by
  let k (t : ℝ) := ‖S.Φ t‖
  let ℓ := sInf (k '' Ioi 0)
  have hmono : MonotoneOn k (Ioi 0) := fun _ hs _ _ hst => S.norm_Phi_mono hs.le hst
  have hb : BddBelow (k '' Ioi 0) := ⟨0, by simp [lowerBounds, k]⟩
  have hk : Tendsto k (𝓝[>] 0) (𝓝 ℓ) := hmono.tendsto_nhdsGT hb
  have hzero : ℓ = 0 := by
    refine le_antisymm ?_ (ge_of_tendsto' hk fun _ => norm_nonneg _)
    by_contra! hpos
    have := double_lower_bound S (L := 3 * ℓ / 4)
      (fun s hs => lt_of_lt_of_le (by linarith) (csInf_le hb ⟨s, hs, rfl⟩)) hk
    linarith
  rw [IsZeroClass, ← Ioi_insert, nhdsWithin_insert, tendsto_sup]
  exact ⟨by simpa [k, S.Phi_zero] using tendsto_pure_nhds k 0, hzero ▸ hk⟩

end ALCS
