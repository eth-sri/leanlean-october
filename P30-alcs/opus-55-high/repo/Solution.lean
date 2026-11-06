module

public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Data.Nat.Pairing
public import Mathlib.Data.Nat.Nth
public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.RegularityCompacts
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.Instances.Nat
public import Mathlib.Topology.Order.Monotone
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

public section

open MeasureTheory Filter Topology Set
open scoped ENNReal BoundedContinuousFunction

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  {U : Type*} [NormedAddCommGroup U] [NormedSpace 𝕜 U] [CompleteSpace U]

notation "μ" => volume.restrict (Ici (0:ℝ))
set_option hygiene false
notation "L∞" => Lp U ∞ μ
notation "Λ" => ℕ →ᵇ 𝕜
notation "D" Y => Λ →L[𝕜] Y
notation:50 f " ≗ " g:50 => f =ᵐ[μ] g

notation:max "ƒ" x:max b => fun x => b
notation "cat" a:max f:max g:max => ƒ s ite (s < a) (f s) (g (s - a))
notation:max "Fn" b => fun n => b

theorem cc a (hf : f ≗ f') (hg : g ≗ g') :
    cat a f g ≗ cat a f' g' := by
  filter_upwards [hf, ae_restrict_of_ae ((measurePreserving_sub_right volume a).quasiMeasurePreserving.ae ((ae_restrict_iff' measurableSet_Ici).1 hg))]
  grind



theorem rep (u : L∞) : ∃ f, StronglyMeasurable f ∧ (∀ t, ‖f t‖ ≤ ‖u‖) ∧ u ≗ f := by
  have h := Lp.stronglyMeasurable u
  refine ⟨{t | ‖u t‖ ≤ ‖u‖}.indicator u, h.indicator (h.norm.measurableSet_le stronglyMeasurable_const), ƒ t by unfold indicator; split_ifs <;> simp_all, ?_⟩
  filter_upwards [ae_le_lpNorm_exponent_top (Lp.memLp u)] with t (h : ‖u t‖ ≤ ‖u‖)
  grind [indicator]

notation "EW" f => ∃ w : L∞, ‖w‖ ≤ C ∧ w ≗ f
theorem mk (hf : StronglyMeasurable f) (h : ∀ t, ‖f t‖ ≤ C) :
    EW f :=
  ⟨_, by
    simpa [hf.aestronglyMeasurable] using ENNReal.toReal_le_of_le_ofReal ((norm_nonneg _).trans (h 0)) (eLpNormEssSup_le_of_ae_bound (.of_forall h)), (memLp_top_of_bound hf.aestronglyMeasurable C (.of_forall h)).coeFn_toLp⟩

theorem ec a {u v : L∞} (hu : ‖u‖ ≤ C) (hv : ‖v‖ ≤ C) :
    EW cat a u v := by
  have hf := (rep u).choose_spec
  have hg := (rep v).choose_spec
  exact (mk (hf.1.ite measurableSet_Iio (hg.1.comp_measurable (measurable_sub_const a))) ƒ t by grind).imp ƒ w And.imp_right (·.trans (cc a hf.2.2 hg.2.2).symm)
noncomputable def chi (S : Set ℕ) : Λ :=
  .ofNormedAddCommGroupDiscrete (S.indicator 1) 1 ƒ _ (norm_indicator_le_norm_self ..).trans norm_one.le
notation:max "χ" n:max => chi {n}

theorem small (φ : D 𝕜) (hS : Set.Infinite S) (hδ : 0 < δ) :
    ∃ T ⊆ S, T.Infinite ∧ ∀ B ⊆ T, ‖φ (chi B)‖ ≤ δ := by
  by_contra! h
  let g i j := Nat.nth (· ∈ S) (Nat.pair i j)
  have hg {i j i' j'} (h : g i j = g i' j') := Nat.pair_eq_pair.1 (Nat.nth_injective hS h)
  choose B hB hBδ using ƒ i h (range (g i)) (range_subset_iff.2 ƒ j Nat.nth_mem_of_infinite hS _)
    (infinite_range_of_injective fun j k h => (hg h).2)
  have hd {i j x} (hi : x ∈ B i) hj :=
    (hg ((hB i hi).choose_spec.trans (hB j hj).choose_spec.symm)).1
  obtain ⟨N, hN⟩ := exists_nat_gt (‖φ‖ * δ⁻¹)
  have : ‖∑ i ∈ Finset.range N, (φ (chi (B i)))⁻¹ • chi (𝕜 := 𝕜) (B i)‖ ≤ δ⁻¹ := by
    refine BoundedContinuousFunction.norm_le_of_nonempty.2 ƒ x ?_
    rw [BoundedContinuousFunction.sum_apply]
    by_cases hx : ∃ i ∈ Finset.range N, x ∈ B i
    · obtain ⟨i, hi, hx⟩ := hx
      rw [Finset.sum_eq_single_of_mem i hi ƒ j by simp [chi]; grind]
      simpa [chi, hx] using inv_anti₀ hδ (hBδ i).le
    simp_all [chi, Finset.sum_eq_zero]
    grind
  refine hN.not_ge ?_
  grw [← this, ← φ.le_opNorm]
  simp [norm_pos_iff.1 (hδ.trans (hBδ _))]

notation:max "σi" => σ i
notation:max "G" => gt_mem_nhds (a := ε / 4) (by grind)
notation:max "N0" => 𝓝 0
notation "PR" => ℕ × {R : Set ℕ // R.Infinite}
theorem phillips (A : ℕ → D X)
    (hA : ∀ a, Tendsto (Fn A n a) atTop N0) :
    Tendsto (Fn A n χ n) atTop N0 := by
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  by_contra h
  choose φ hφ hφe using Fn exists_dual_vector'' 𝕜 (A n χ n)
  have hμ C := ((tendsto_norm_zero.comp (hA (chi C))).eventually G).mono Fn ƒ h
    ((φ n).le_of_opNorm_le (hφ n) _).trans_lt ((one_mul _).trans_lt h)
  choose n hh hn T hT hTi hs using fun p : PR =>
    (((finite_Iic p.1).finite_subsets.eventually_all.2 Fn ƒ _ hμ n).and_frequently (Nat.frequently_atTop_iff_infinite.2 p.2.2)).exists.imp Fn
      And.imp_right (And.intro · (small ((φ n).comp (A n)) (p.2.2.sdiff (finite_Iic n)) (half_pos hε)))
  let σ : ℕ → PR :=
    Nat.rec (0, ⟨_, Nat.frequently_atTop_iff_infinite.1 (not_eventually.1 h)⟩) fun _ p => (n p, ⟨T p, hTi p⟩)
  let N i := n σi
  have hR : Antitone ƒ i σi.2.1 := antitone_nat_of_succ_le ƒ i (hT _).trans sdiff_subset
  have hN : StrictMono N := strictMono_nat_of_lt_succ ƒ i not_le.1 (hT _ (hn (σ (i + 1)))).2
  have hM : Monotone ƒ i σi.1 := monotone_nat_of_le_succ ƒ i i.casesOn zero_le ƒ k hN.monotone k.le_succ
  obtain ⟨i, hi⟩ := (hN.tendsto_atTop.eventually (hμ (range N))).exists
  have e : chi (𝕜 := 𝕜) {N i} = chi (range N) - chi (N '' Iio i) - chi (N '' Ioi i) := by
    ext x
    rcases em (x ∈ range N) with ⟨k, rfl⟩ | hx <;> simp_all [chi, indicator, Pi.single_apply, hN.injective.eq_iff]
    grind
  grind [norm_sub_le, show ε ≤ ‖φ (N i) (A (N i) χ (N i))‖ by simpa [hφe, σ, N] using hR i.zero_le (hn _),
    hh σi (N '' Iio i) (image_subset_iff.2 ƒ _ Fn hM n),
    hs σi (N '' Ioi i) (image_subset_iff.2 ƒ _ Fn hR n (hn _))]

notation "ℒ" f => Lp.ext (((hw _).2.trans ?_).trans (f ..).symm)
theorem pack (B : ℕ → ℝ → U) (hB : ∀ n, StronglyMeasurable (B n)) (hb : ∀ n t, ‖B n t‖ ≤ 1)
    (hd : ∀ i j t, B i t ≠ 0 → B j t ≠ 0 → i = j) :
    ∃ P : D L∞, ∀ n, P χ n ≗ B n := by
  have hm n t h := hd _ _ _ (Classical.epsilon_spec (p := (B · t ≠ 0)) ⟨n, h⟩) h
  choose w hw using fun a : Λ => mk
    (stronglyMeasurable_of_tendsto _ (ƒ N Finset.stronglyMeasurable_fun_sum _ Fn ƒ _ (hB n).const_smul (a n))
      (tendsto_pi_nhds.2 ƒ t (hasSum_single (Classical.epsilon Fn B n t ≠ 0) Fn ƒ h by simp; grind).tendsto_sum_nat))
    ƒ t by grw [Pi.smul_apply, norm_smul, hb, a.norm_coe_le_norm, mul_comm]
  refine ⟨LinearMap.mkContinuous ⟨⟨w, ƒ a Fn ℒ Lp.coeFn_add⟩, ƒ c Fn ℒ Lp.coeFn_smul⟩ 1 ƒ a (hw a).1, Fn (hw _).2.trans (.of_forall ƒ t ?_)⟩
  · filter_upwards [(hw a).2, (hw n).2]
    simp_all [add_smul]
  · filter_upwards [(hw n).2]
    simp_all [smul_smul]
  simp [chi, Pi.single_apply]
  grind

variable (T : ℝ → X →L[𝕜] X) (Φ : ℝ → L∞ →L[𝕜] X)
    (hT_zero : T 0 = ContinuousLinearMap.id 𝕜 X)
    (hT_semigroup : ∀ t s, 0 ≤ t → 0 ≤ s → T (t + s) = (T t).comp (T s))
    (hT_cont : ∀ x, Tendsto (T · x) (𝓝[≥] 0) (𝓝 x))
    (hΦ_concat : ∀ τ t, 0 ≤ τ → 0 ≤ t →
      ∀ u v w : L∞, w ≗ cat τ u v →
      Φ (τ + t) w = T t (Φ τ u) + Φ t v)
include hT_zero hT_semigroup hT_cont hΦ_concat

notation:max "gn" => g n

notation:max "NΦ" => (‖Φ ·‖)
theorem PalomarALCS.zero_class : Tendsto NΦ (𝓝[≥] 0) N0 := by

  let s := NΦ '' Ioi 0
  have hb : BddBelow s := ⟨0, by simp [s, lowerBounds]⟩
  have hℓ := MonotoneOn.tendsto_nhdsGT (fun s hs t _ hst => (Φ s).opNorm_le_bound (norm_nonneg _) ƒ u by
    have h := (ec (t - s) (norm_zero.trans_le (norm_nonneg u)) le_rfl).choose_spec
    grind [hΦ_concat _ _ (by linarith) hs.le _ _ _ h.2, (Φ t).le_opNorm_of_le h.1]) hb
  set ℓ := sInf s
  choose! u hu r hr hy using ƒ x Fn
    ((Φ (x / 2)).exists_lt_apply_of_lt_opNorm ((sub_lt_self ℓ n).trans_le (csInf_le hb ⟨x / 2, half_pos n, rfl⟩))).imp fun u h =>
      And.intro h.1.le (Filter.Eventually.and (Ioo_mem_nhdsGT (half_pos n)) (((hT_cont _).norm.eventually (lt_mem_nhds h.2)).filter_mono (nhdsWithin_mono _ Ioi_subset_Ici_self))).exists
  let a : ℕ → ℝ := Nat.rec 1 ƒ _ r
  have ha n : 0 < a n := n.rec one_pos ƒ _ Fn (hr _ n).1
  have anti : Antitone a := antitone_nat_of_succ_le Fn by grind
  have ha0 := (summable_of_ratio_norm_eventually_le (f := a) one_half_lt_one (.of_forall Fn by grind [Real.norm_eq_abs])).tendsto_atTop_zero
  let g n := a n / 2 + a (n + 1)
  have hgp n : 0 < gn := by grind
  have hg0 : Tendsto g atTop N0 := by simpa using (ha0.div_const 2).add (ha0.comp (tendsto_add_atTop_nat 1))
  choose f hf hfb hfu using Fn rep (u (a n))
  choose w hw hw' using Fn ec (a n / 2) (hu _ (ha n)) (norm_zero.trans_le zero_le_one)
  let B n := cat (1 - gn) (ƒ _ 0) (cat (a n / 2) (f n) ƒ _ 0)
  obtain ⟨P, hP⟩ := pack (𝕜 := 𝕜) B (Fn stronglyMeasurable_const.ite measurableSet_Iio (((hf n).ite measurableSet_Iio stronglyMeasurable_const).comp_measurable (measurable_sub_const _)))
    (Fn ƒ t by grind [norm_zero])
    ƒ i ƒ j by grind [lt_trichotomy i j, Antitone]
  let S := (Φ 1).comp P
  have hS n : S χ n = Φ gn (w n) := by
    simpa [S] using hΦ_concat _ _ (by grind [show a n ≤ 1 from anti n.zero_le]) (hgp n).le _ _ _
      ((hP n).trans (cc _ (Lp.coeFn_zero ..).symm ((hw' n).trans (cc _ (hfu n) (Lp.coeFn_zero ..))).symm))

  rw [← nhdsGT_sup_nhdsWithin_singleton]
  exact ((show ℓ = 0 by linarith [le_of_tendsto_of_tendsto' ((ha0.const_sub ℓ).const_mul 2) ((hℓ.comp (tendsto_nhdsWithin_iff.2 ⟨by simpa using hg0.add hg0, .of_forall Fn by grind⟩)).add (tendsto_norm_zero.comp (phillips (Fn (T gn - 1).comp S) ƒ b by simpa using ((hT_cont (S b)).comp (tendsto_nhdsWithin_iff.2 ⟨hg0, .of_forall Fn by grind⟩)).sub_const (S b)))) (ƒ n by
    have h := (ec gn (hw n) (hw n)).choose_spec
    set y := Φ gn (w n)
    have := norm_sub_le (T gn y + y) (T gn y - y)
    simp [← two_smul 𝕜, norm_smul] at this ⊢
    grind [(Φ (gn + gn)).le_opNorm_of_le h.1, hΦ_concat _ _ (half_pos (ha n)).le (ha (n + 1)).le _ _ _ (hw' n)]), ge_of_tendsto' hℓ ƒ _ norm_nonneg _]) ▸ hℓ).sup (by simpa [show Φ 0 = 0 by ext u; simpa [hT_zero] using hΦ_concat 0 0 le_rfl le_rfl u u u (by simp)] using tendsto_pure_nhds NΦ 0)



theorem PalomarALCS.continuousOn_Phi (u : L∞) : ContinuousOn (Φ · u) (Ici 0) := by
  obtain ⟨M, hM⟩ : ∃ M, ∀ᶠ t in 𝓝[≥] 0, ‖T t‖ ≤ M := by
    by_contra! h
    have hB := (𝓝[≥] (0:ℝ)).exists_antitone_basis.choose_spec
    choose t ht hM using Fn (Filter.Eventually.and_frequently (hB.mem n) (h n)).exists
    obtain ⟨C, hC⟩ := banach_steinhaus ƒ x by
      simpa [bddAbove_def] using ((hT_cont x).comp (hB.tendsto ht)).norm.bddAbove_range
    grind [exists_nat_gt C]
  obtain ⟨f, hf, hfb, huf⟩ := rep u
  refine Metric.continuousOn_iff.2 fun t₀ ht₀ ε hε => ?_
  obtain ⟨η, hη, hηs⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 ((((PalomarALCS.zero_class T Φ hT_zero hT_semigroup hT_cont hΦ_concat).mul_const ‖u‖).eventually G).and hM)
  set c := max (t₀ - η / 2) 0
  have hv := (mk (hf.comp_measurable (measurable_const_add c)) ƒ t hfb _).choose_spec
  set x := Φ c u
  have hq s (h1 : 0 ≤ s) (h2 : s < η) : dist (T s x) (Φ (c + s) u) < ε / 4 := by
    rw [hΦ_concat _ _ (le_max_right ..) h1 u _ u (huf.trans ((cc c huf hv.2).trans (.of_forall ƒ t by simp)).symm), dist_self_add_right]
    grw [(Φ _).le_opNorm_of_le hv.1]
    exact (hηs ⟨h1, h2⟩).1
  obtain ⟨δ, hδ, hδs⟩ := (mem_nhdsGE_iff_exists_mem_Ioc_Ico_subset (half_pos hη)).1 (((tendsto_iff_dist_tendsto_zero.1 (hT_cont x)).const_mul M).eventually G)
  have orb p q (hp : 0 ≤ p) (hpη : p < η) (hpq : p ≤ q) (hqp : q - p < δ) : dist (T q x) (T p x) < ε / 4 := by
    rw [← add_sub_cancel p q, hT_semigroup _ _ hp, ContinuousLinearMap.comp_apply]
    grw [(T p).dist_le_opNorm, (hηs ⟨hp, hpη⟩).2]
    exact hδs ⟨by linarith, hqp⟩
    linarith
  refine ⟨δ, hδ.1, fun t ht hd => ?_⟩
  grw [dist_triangle4 _ (T (t - c) x) (T (t₀ - c) x)]
  grind [dist_comm, abs_lt.1 hd]
