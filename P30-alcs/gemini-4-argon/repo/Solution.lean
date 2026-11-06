module

public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Nat.Pairing
public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.Instances.Nat

@[expose] public section

open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped ENNReal BigOperators Classical

noncomputable section

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

namespace PalomarALCS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
variable {U : Type*} [NormedAddCommGroup U]

def chi (S : Set ℕ) : ℕ →ᵇ 𝕜 :=
  ofNormedAddCommGroupDiscrete (fun k => if k ∈ S then 1 else 0) 1 fun k => by
    split_ifs <;> simp

abbrev e (k : ℕ) : ℕ →ᵇ 𝕜 := chi {k}

local notation "muPlus" => volume.restrict (Set.Ici (0 : ℝ))
local notation "L∞(ℝ₊; " U ")" => Lp U ∞ muPlus

def concat {U : Type*} (τ : ℝ) (u v : ℝ → U) : ℝ → U :=
  fun s => if s < τ then u s else v (s - τ)

lemma concat_ae {U : Type*} {w u v f g : ℝ → U} {a : ℝ} (hw : w =ᵐ[muPlus] concat a f g)
    (hu : u =ᵐ[muPlus] f) (hv : v =ᵐ[muPlus] g) : w =ᵐ[muPlus] concat a u v := by
  have hmp : MeasurePreserving (· - a) (volume.restrict (Set.Ici a)) muPlus := by
    simpa using (measurePreserving_sub_right volume a).restrict_preimage (measurableSet_Ici (a := (0 : ℝ)))
  filter_upwards [hw, hu, ae_restrict_of_ae ((ae_restrict_iff' measurableSet_Ici).1
    (hmp.quasiMeasurePreserving.ae hv))] with t hwt hft hgt
  rw [hwt]; unfold concat; split_ifs with ht
  · exact hft.symm
  · exact (hgt (not_lt.1 ht)).symm

lemma concat_meas {f g : ℝ → U} (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) (a : ℝ) :
    StronglyMeasurable (concat a f g) :=
  hf.ite measurableSet_Iio (hg.comp_measurable (measurable_id.sub_const a))

lemma memLp_of_bound {f : ℝ → U} (hf : StronglyMeasurable f)
    {C : ℝ} (hb : ∀ t, ‖f t‖ ≤ C) : MemLp f ∞ muPlus :=
  memLp_top_of_bound hf.aestronglyMeasurable C (.of_forall hb)

lemma norm_toLp_le {f : ℝ → U} (hf : MemLp f ∞ muPlus)
    {C : ℝ} (hb : ∀ t, ‖f t‖ ≤ C) : ‖hf.toLp f‖ ≤ C := by
  simpa [eLpNorm_exponent_top hf.aestronglyMeasurable,
    ENNReal.toReal_ofReal ((norm_nonneg _).trans (hb 0))] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top (eLpNormEssSup_le_of_ae_bound (.of_forall hb))

lemma exists_bounded_rep (u : L∞(ℝ₊; U)) :
    ∃ f : ℝ → U, StronglyMeasurable f ∧ (∀ t, ‖f t‖ ≤ ‖u‖) ∧ ⇑u =ᵐ[muPlus] f :=
  ⟨fun t => if ‖u t‖ ≤ ‖u‖ then u t else 0,
    (Lp.stronglyMeasurable u).ite ((Lp.stronglyMeasurable u).norm.measurableSet_le stronglyMeasurable_const)
      stronglyMeasurable_const,
    fun t => by dsimp; split_ifs with h <;> simp [h],
    (ae_le_lpNorm_exponent_top (Lp.memLp u)).mono fun _ ht => (ite_eq_left ht).symm⟩

lemma exists_concat (a : ℝ) (u v : L∞(ℝ₊; U)) :
    ∃ w : L∞(ℝ₊; U), ‖w‖ ≤ max ‖u‖ ‖v‖ ∧ ⇑w =ᵐ[muPlus] concat a ⇑u ⇑v := by
  obtain ⟨f, hf, hfb, huf⟩ := exists_bounded_rep u
  obtain ⟨g, hg, hgb, hvg⟩ := exists_bounded_rep v
  have hb (t) : ‖concat a f g t‖ ≤ max ‖u‖ ‖v‖ := by
    unfold concat; split_ifs <;> [exact (hfb _).trans (le_max_left _ _); exact (hgb _).trans (le_max_right _ _)]
  have hm := memLp_of_bound (concat_meas hf hg a) hb
  exact ⟨hm.toLp _, norm_toLp_le hm hb, concat_ae hm.coeFn_toLp huf hvg⟩

variable [NormedSpace 𝕜 U] [CompleteSpace U]

variable (T : ℝ → X →L[𝕜] X) (Φ : ℝ → L∞(ℝ₊; U) →L[𝕜] X)
  (hT_zero : T 0 = ContinuousLinearMap.id 𝕜 X)
  (hT_semigroup : ∀ t s : ℝ, 0 ≤ t → 0 ≤ s → T (t + s) = (T t).comp (T s))
  (hT_cont : ∀ x : X, Tendsto (fun t => T t x) (𝓝[≥] 0) (𝓝 x))
  (hΦ_concat : ∀ τ t : ℝ, 0 ≤ τ → 0 ≤ t →
    ∀ u v w : L∞(ℝ₊; U),
    (⇑w =ᵐ[volume.restrict (Set.Ici (0 : ℝ))]
      (fun s => if s < τ then u s else v (s - τ))) →
    Φ (τ + t) w = T t (Φ τ u) + Φ t v)

include hT_cont in
theorem exists_bound_near_zero : ∃ τ > 0, ∃ M > 0, ∀ t, 0 ≤ t → t ≤ τ → ‖T t‖ ≤ M := by
  by_contra! h
  choose t ht0 htle htbig using fun n : ℕ =>
    h (1 / (n + 1 : ℝ)) (by positivity) (n + 1) (by positivity)
  have ht_lim : Tendsto t atTop (𝓝[≥] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨squeeze_zero ht0 htle tendsto_one_div_add_atTop_nhds_zero_nat,
      .of_forall ht0⟩
  obtain ⟨C, hC⟩ := banach_steinhaus (g := fun n => T (t n)) fun x => by
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1
      (Metric.isBounded_range_of_tendsto _ ((hT_cont x).comp ht_lim))
    exact ⟨C, fun n => hC _ (Set.mem_range_self n)⟩
  obtain ⟨n, hn⟩ := exists_nat_gt C
  linarith [hC n, htbig n]

abbrev err (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n

include T hT_zero hT_semigroup hT_cont hΦ_concat in
theorem zero_class : Tendsto (fun t => ‖Φ t‖) (𝓝[≥] 0) (𝓝 0) := by
  have err_tendsto : Tendsto err atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have norm_Phi_mono {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) : ‖Φ s‖ ≤ ‖Φ t‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun u => ?_
    obtain ⟨w, hw, hcat⟩ := exists_concat (t - s) 0 u
    have heq : Φ t w = Φ s u := by
      simpa [sub_add_cancel] using hΦ_concat (t - s) s (sub_nonneg.2 hst) hs 0 u w hcat
    exact heq ▸ ((Φ t).le_opNorm w).trans (mul_le_mul_of_nonneg_left (by simpa using hw) (norm_nonneg _))
  have hstep (n : ℕ) (h : ℝ) :
      ∃ (u : L∞(ℝ₊; U)) (r : ℝ), ‖u‖ ≤ 1 ∧
        (0 < h → 0 < r ∧ r ≤ h / 2 ∧ ‖Φ h‖ - err n ≤ ‖Φ h u‖ ∧ ‖T (2 * r) (Φ h u) - Φ h u‖ ≤ err n) := by
    obtain ⟨u, hu, hnear⟩ : ∃ u : L∞(ℝ₊; U), ‖u‖ ≤ 1 ∧ ‖Φ h‖ - err n ≤ ‖Φ h u‖ := by
      by_cases hc : ‖Φ h‖ - err n ≤ 0
      · exact ⟨0, by simp, by simpa using hc⟩
      · by_contra! hn
        linarith [ContinuousLinearMap.opNorm_le_of_unit_norm (not_le.1 hc).le fun u hu => (hn u hu.le).le,
          show 0 < err n by positivity]
    obtain ⟨δ, hδ, hc⟩ := Metric.tendsto_nhdsWithin_nhds.1 (hT_cont (Φ h u)) (err n) (by positivity)
    let r := min (h / 2) (δ / 4)
    refine ⟨u, r, hu, fun hh => ?_⟩
    have hr : 0 < r := lt_min (by linarith) (by positivity)
    refine ⟨hr, min_le_left _ _, hnear, ?_⟩
    simpa [dist_eq_norm] using (@hc (2 * r) (Set.mem_Ici.2 (by positivity)) (by
      rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
      linarith [min_le_right (h / 2) (δ / 4)])).le
  choose u₀ r hu₀ hprop using hstep
  let h : ℕ → ℝ := Nat.rec (1 / 4) r
  have h_pos (n) : 0 < h n := by
    induction n with
    | zero => norm_num [h]
    | succ n ih => exact (hprop n (h n) ih).1
  have hr (n) : r n (h n) = h (n + 1) := rfl
  have h_geom (n) : h n ≤ err n / 4 := by
    induction n with
    | zero => simp [h, err]
    | succ n ih => unfold err at ih ⊢; rw [pow_succ]; linarith [(hprop n (h n) (h_pos n)).2.1]
  clear_value h
  have hp (n) := hr n ▸ (hprop n (h n) (h_pos n)).2
  have h_tendsto : Tendsto h atTop (𝓝 0) :=
    squeeze_zero (fun n => (h_pos n).le) h_geom (by simpa using err_tendsto.div_const 4)
  let u (n : ℕ) : L∞(ℝ₊; U) := u₀ n (h n)
  let x (n : ℕ) : X := Φ (h n) (u n)
  choose g hg hgb hug using fun n => exists_bounded_rep (u n)
  let f (n : ℕ) := concat (h n) (g n) (fun _ => (0 : U))
  let start (n : ℕ) : ℝ := 1 - 2 * h (n + 1) - h n
  let window (n : ℕ) : Set ℝ := Set.Ico (start n) (start n + h n)
  let block (n : ℕ) := concat (start n) (fun _ => (0 : U)) (f n)
  have hf (n) : StronglyMeasurable (f n) := concat_meas (hg n) stronglyMeasurable_const _
  have hfb (n t) : ‖f n t‖ ≤ 1 := by
    dsimp [f, concat]; split_ifs <;> [exact (hgb n _).trans (hu₀ n (h n)); simp]
  have hbb (n t) : ‖block n t‖ ≤ 1 := by dsimp [block, concat]; split_ifs <;> simp [hfb n _]
  have h_anti : Antitone h := antitone_nat_of_succ_le fun n => by linarith [(hp n).1, h_pos n]
  have block_off (n) {t} (ht : t ∉ window n) : block n t = 0 := by
    dsimp [block, f, concat]; split_ifs <;> [rfl; exfalso; rfl]
    exact ht ⟨by linarith, by linarith⟩
  let idx (t : ℝ) : ℕ := if ht : ∃ n, t ∈ window n then ht.choose else 0
  have idx_eq {n t} (ht : t ∈ window n) : idx t = n := by
    have hex : ∃ k, t ∈ window k := ⟨n, ht⟩
    have h1 := hex.choose_spec
    dsimp [window, start] at ht h1
    rcases lt_trichotomy hex.choose n with h | h | h
    · linarith [h_anti h, (hp n).1, h1.2, ht.1]
    · simpa [idx, hex] using h
    · linarith [h_anti h, (hp hex.choose).1, ht.2, h1.1]
  let packRaw (a : ℕ →ᵇ 𝕜) (t : ℝ) : U := a (idx t) • block (idx t) t
  have packRaw_bound (a : ℕ →ᵇ 𝕜) (t : ℝ) : ‖packRaw a t‖ ≤ ‖a‖ := by
    rw [norm_smul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (hbb _ _)).trans (norm_coe_le_norm a (idx t))
  have packRaw_memLp (a : ℕ →ᵇ 𝕜) : MemLp (packRaw a) ∞ muPlus := by
    refine memLp_of_bound (stronglyMeasurable_of_tendsto atTop
      (f := fun N t => ∑ n ∈ Finset.range N, a n • block n t) ?_ ?_) (packRaw_bound a)
    · exact fun N => Finset.stronglyMeasurable_fun_sum _ fun n _ =>
        (concat_meas stronglyMeasurable_const (hf n) _).const_smul (a n)
    · refine tendsto_pi_nhds.2 fun t => tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop (idx t + 1)] with N hN
      rw [Finset.sum_eq_single_of_mem (idx t) (Finset.mem_range.2 hN) fun j _ hj => by
        rw [block_off j (mt idx_eq hj.symm), smul_zero]]
  let packing : (ℕ →ᵇ 𝕜) →L[𝕜] L∞(ℝ₊; U) := LinearMap.mkContinuous
    { toFun := fun a => (packRaw_memLp a).toLp _
      map_add' := fun a b => (MemLp.toLp_congr _ ((packRaw_memLp a).add (packRaw_memLp b))
        (.of_forall fun t => add_smul _ _ _)).trans (MemLp.toLp_add _ _)
      map_smul' := fun c a => (MemLp.toLp_congr _ ((packRaw_memLp a).const_smul c)
        (.of_forall fun t => smul_assoc _ _ _)).trans (MemLp.toLp_const_smul c _) }
    1 fun a => by simpa using norm_toLp_le (packRaw_memLp a) (packRaw_bound a)
  let packedOp : (ℕ →ᵇ 𝕜) →L[𝕜] X := (Φ 1).comp packing
  obtain ⟨τ₀, hτ₀, M, hM, hTbound⟩ := exists_bound_near_zero T hT_cont
  let A (n : ℕ) := T (h n) - ContinuousLinearMap.id 𝕜 X
  let L (n : ℕ) := (A n).comp packedOp
  have hL (B : Set ℕ) : Tendsto (fun n => L n (chi B)) atTop (𝓝 0) := by
    simpa [L, A] using ((hT_cont (packedOp (chi B))).comp (tendsto_nhdsWithin_iff.2
      ⟨h_tendsto, .of_forall fun n => (h_pos n).le⟩)).sub
      (tendsto_const_nhds (x := packedOp (chi B)))
  have hPhillips : Tendsto (fun n => ‖L n (e n)‖) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    by_contra! hnot
    choose φ hφnorm hφeval using fun n => exists_dual_vector'' 𝕜 (L n (e n))
    let μ (n : ℕ) := (φ n).comp (L n)
    have hμle (n x) : ‖μ n x‖ ≤ ‖L n x‖ :=
      ((φ n).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (hφnorm n))
    have hD : {n | ε ≤ ‖L n (e n)‖}.Infinite :=
      Nat.frequently_atTop_iff_infinite.1 (frequently_atTop.2 fun N => by simpa using hnot N)
    let δ := ε / 4
    have hδ : 0 < δ := by positivity
    let S_inf := {S : Set ℕ // S.Infinite}
    have hstep (F : Set ℕ) (S : S_inf) : ∃ (n : ℕ) (T : S_inf),
        n ∈ S.1 ∧ ‖μ n (chi F)‖ < δ ∧ T.1 ⊆ S.1 ∧ (∀ m ∈ T.1, n < m) ∧
        ∀ B ⊆ T.1, ‖μ n (chi B)‖ ≤ δ := by
      obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 (hL F)) δ hδ
      obtain ⟨n, hnS, hnN⟩ := S.2.exists_notMem_finite (Set.finite_lt_nat N)
      refine ⟨n, ?_⟩
      by_contra! h
      let emb := (S.2.sdiff (Set.finite_le_nat n)).natEmbedding
      have hinj {i j k l} (he : (emb (Nat.pair i j)).1 = (emb (Nat.pair k l)).1) :=
        Nat.pair_eq_pair.1 (emb.injective (Subtype.ext he))
      let A (i : ℕ) : S_inf := ⟨Set.range fun j => (emb (Nat.pair i j)).1,
        Set.infinite_range_of_injective fun _ _ he => (hinj he).2⟩
      choose B hBA hBδ using fun i => h (A i) hnS
        ((hμle n _).trans_lt (by simpa using hN n (not_lt.1 hnN)))
        (by rintro _ ⟨j, rfl⟩; exact (emb _).2.1)
        (by rintro _ ⟨j, rfl⟩; exact not_le.1 (emb _).2.2)
      have hdisj {i j x} (hi : x ∈ B i) (hj : x ∈ B j) : i = j := by
        obtain ⟨b, rfl⟩ := hBA j hj
        obtain ⟨a, ha⟩ := hBA i hi
        exact (hinj ha).1
      let v (i : ℕ) : ℕ →ᵇ 𝕜 := (μ n (chi (B i)))⁻¹ • chi (B i)
      obtain ⟨M, hM⟩ := exists_nat_gt (‖μ n‖ * δ⁻¹)
      have hsum : ‖∑ i ∈ Finset.range M, v i‖ ≤ δ⁻¹ := by
        refine (norm_le (by positivity)).2 fun x => ?_
        rw [BoundedContinuousFunction.sum_apply]
        by_cases hx : ∃ i ∈ Finset.range M, x ∈ B i
        · obtain ⟨i, hi, hxi⟩ := hx
          rw [Finset.sum_eq_single_of_mem i hi fun j _ hji => ?_]
          · simpa [v, chi, hxi] using inv_anti₀ hδ (hBδ i).le
          · simp [v, chi, show x ∉ B j from fun hxj => hji (hdisj hxj hxi)]
        · push Not at hx; simp +contextual [v, chi, hx, hδ.le]
      have hup := ((μ n).le_opNorm (∑ i ∈ Finset.range M, v i)).trans
        (mul_le_mul_of_nonneg_left hsum (norm_nonneg _))
      simpa [map_sum, v, inv_mul_cancel₀ (norm_pos_iff.1 (hδ.trans (hBδ _)))] using hup.trans_lt hM
    choose pick tail hpick hhead hsub hgt hsmall using hstep
    let state : ℕ → Set ℕ × S_inf :=
      Nat.rec (∅, ⟨_, hD⟩) fun _ p => (insert (pick p.1 p.2) p.1, tail p.1 p.2)
    let n (i : ℕ) := pick (state i).1 (state i).2
    let F (i : ℕ) := (state i).1
    let R (i : ℕ) := (state i).2.1
    have hnmem (i) : n i ∈ R i := hpick _ _
    have hRanti : Antitone R := antitone_nat_of_succ_le fun i => hsub _ _
    have hnmono : StrictMono n := strictMono_nat_of_lt_succ fun i => hgt _ _ _ (hnmem (i + 1))
    let A := Set.range n
    have hF (i) : F i = n '' Set.Iio i := by
      induction i with
      | zero => ext; simp [F, state]
      | succ i ih =>
        change insert (n i) (F i) = _
        rw [ih, ← Set.image_insert_eq]; congr 1; ext; simp
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 (hL A)) δ hδ
    have hsplit : e (𝕜 := 𝕜) (n N) = chi A - chi (F N) - chi (A \ F (N + 1)) := by
      ext x
      have : x ∈ F N → x ∈ A ∧ x ≠ n N := by
        rw [hF]; rintro ⟨j, hj, rfl⟩; exact ⟨⟨j, rfl⟩, (hnmono hj).ne⟩
      have : n N ∈ A := ⟨N, rfl⟩
      have : F (N + 1) = insert (n N) (F N) := rfl
      simp only [BoundedContinuousFunction.sub_apply, chi, coe_ofNormedAddCommGroupDiscrete, e, this,
        Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
      split_ifs <;> first | tauto | ring
    have hnorm : ‖L (n N) (e (n N))‖ ≤
        ‖μ (n N) (chi A)‖ + ‖μ (n N) (chi (F N))‖ + ‖μ (n N) (chi (A \ F (N + 1)))‖ := by
      have hd : ‖μ (n N) (e (n N))‖ = ‖L (n N) (e (n N))‖ := by
        rw [ContinuousLinearMap.comp_apply, hφeval, RCLike.norm_of_nonneg (norm_nonneg _)]
      rw [← hd, hsplit, map_sub, map_sub]
      exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    linarith [(hμle _ _).trans_lt (by simpa using hN (n N) (hnmono.id_le N)),
      hhead (state N).1 (state N).2,
      hsmall _ _ (A \ F (N + 1)) (by rintro _ ⟨⟨j, rfl⟩, hj⟩; exact hRanti (not_lt.1 fun h => hj (hF (N + 1) ▸ ⟨j, h, rfl⟩)) (hnmem j)),
      show ε ≤ ‖L (n N) (e (n N))‖ from hRanti (Nat.zero_le N) (hnmem N), show δ = ε / 4 from rfl]
  have hmoves : Tendsto (fun n => ‖T (h n) (x n) - x n‖) atTop (𝓝 0) := by
    refine squeeze_zero' (.of_forall fun _ => norm_nonneg _) ?_
      (by simpa using hPhillips.add (err_tendsto.const_mul (M + 1)))
    filter_upwards [h_tendsto.eventually (ge_mem_nhds hτ₀)] with n hn
    let y := packedOp (e n)
    have hy : y = T (2 * h (n + 1)) (x n) := by
      have hfn := memLp_of_bound (hf n) (hfb n)
      have hw := concat_ae ((packRaw_memLp (e n)).coeFn_toLp.trans (.of_forall fun t => show _ = block n t by
        by_cases htn : idx t = n <;>
          [simp [packRaw, chi, htn]; simp [packRaw, chi, htn, block_off n (mt idx_eq htn)]]))
        (Lp.coeFn_zero U ∞ muPlus) hfn.coeFn_toLp
      have h2pos : 0 ≤ 2 * h (n + 1) := by linarith [h_pos (n + 1)]
      change Φ 1 ((packRaw_memLp (e n)).toLp _) = _
      rw [show (1 : ℝ) = start n + (h n + 2 * h (n + 1)) by dsimp [start]; ring,
        hΦ_concat (start n) (h n + 2 * h (n + 1))
          (by dsimp [start]; linarith [(hp n).1, h_anti (Nat.zero_le n), h_geom 0, show err 0 = 1 from rfl])
          (by linarith [h_pos n]) 0 _ _ hw,
        hΦ_concat (h n) (2 * h (n + 1)) (h_pos n).le h2pos (u n) 0 _
          (concat_ae hfn.coeFn_toLp (hug n) (Lp.coeFn_zero U ∞ muPlus))]
      simp [x]
    have hAn : ‖A n‖ ≤ M + 1 := (norm_sub_le _ _).trans
      (add_le_add (hTbound (h n) (h_pos n).le hn) ContinuousLinearMap.norm_id_le)
    have h1 : ‖A n (x n)‖ ≤ ‖A n y‖ + ‖A n (y - x n)‖ := by
      simpa [← map_sub] using norm_sub_le (A n y) (A n (y - x n))
    exact h1.trans (add_le_add le_rfl (((A n).le_opNorm _).trans
      (mul_le_mul hAn (hy.symm ▸ (hp n).2.2) (norm_nonneg _) (by positivity))))
  have hbdd : BddBelow (Set.range fun n => ‖Φ (h n)‖) := by
    refine ⟨0, ?_⟩; rintro _ ⟨n, rfl⟩; exact norm_nonneg _
  let ell := ⨅ n, ‖Φ (h n)‖
  have hell_le (k : ℕ) : 2 * ell ≤ ‖Φ (h k)‖ := by
    refine ge_of_tendsto (by simpa using (tendsto_const_nhds.add hmoves).add (err_tendsto.const_mul 2)) ?_
    filter_upwards [h_tendsto.eventually (ge_mem_nhds (half_pos (h_pos k)))] with n hn
    obtain ⟨w, hw, hcat⟩ := exists_concat (h n) (u n) (u n)
    have hcomp := hΦ_concat (h n) (h n) (h_pos n).le (h_pos n).le (u n) (u n) w hcat
    have hnorm := ((Φ (h n + h n)).le_opNorm w).trans
      (mul_le_of_le_one_right (norm_nonneg _) (hw.trans (by simpa using hu₀ n (h n))))
    have h3 : 2 * ‖x n‖ ≤ ‖Φ (h n + h n) w‖ + ‖T (h n) (x n) - x n‖ := by
      simpa [norm_smul, show Φ (h n + h n) w - (T (h n) (x n) - x n) = (2 : 𝕜) • x n by
        rw [hcomp, two_smul]; dsimp [x]; abel] using norm_sub_le (Φ (h n + h n) w) (T (h n) (x n) - x n)
    linarith [ciInf_le hbdd n, (hp n).2.1,
      norm_Phi_mono (add_nonneg (h_pos n).le (h_pos n).le) (by linarith : h n + h n ≤ h k)]
  have : 2 * ell ≤ ell := le_ciInf hell_le
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨k, hk⟩ := exists_lt_of_ciInf_lt (by linarith : ell < ε)
  refine ⟨h k, h_pos k, fun t (ht : 0 ≤ t) hdist => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg ht] at hdist
  simpa using (norm_Phi_mono ht hdist.le).trans_lt hk

include T hT_zero hT_semigroup hT_cont hΦ_concat in
theorem continuousOn_Phi (u : L∞(ℝ₊; U)) :
    ContinuousOn (fun t => Φ t u) (Set.Ici 0) := by
  obtain ⟨τ, hτ, M, hM, hTbound⟩ := exists_bound_near_zero T hT_cont
  rw [Metric.continuousOn_iff]
  intro t₀ (ht₀ : 0 ≤ t₀) ε hε
  obtain ⟨η, hη, hκ⟩ := Metric.tendsto_nhdsWithin_nhds.1
    (zero_class T Φ hT_zero hT_semigroup hT_cont hΦ_concat) (ε / 4 / (‖u‖ + 1)) (by positivity)
  let δ := min (η / 3) τ
  have hδpos : 0 < δ := by positivity
  have hδη : δ ≤ η / 3 := min_le_left _ _
  let t₁ := max 0 (t₀ - δ)
  have ht₁ : 0 ≤ t₁ := le_max_left _ _
  obtain ⟨f, hf, hfb, huf⟩ := exists_bounded_rep u
  have hm := memLp_of_bound (hf.comp_measurable (measurable_id.add_const t₁)) fun t => hfb _
  let u₁ := hm.toLp _
  have hsmall {r} (hr : 0 ≤ r) (hrη : r < η) : ‖Φ r u₁‖ < ε / 4 := by
    have h1 := hκ (Set.mem_Ici.2 hr) (by rwa [Real.dist_eq, sub_zero, abs_of_nonneg hr])
    exact ((Φ r).le_opNorm u₁).trans_lt
      ((mul_le_mul_of_nonneg_left ((norm_toLp_le hm fun _ => hfb _).trans (lt_add_one _).le) (norm_nonneg _)).trans_lt
      ((lt_div_iff₀ (by positivity)).1 (by simpa using h1)))
  let y := Φ t₁ u
  have hcomp (s) (hs : t₁ ≤ s) : Φ s u = T (s - t₁) y + Φ (s - t₁) u₁ := by
    simpa using hΦ_concat t₁ (s - t₁) ht₁ (sub_nonneg.2 hs) u u₁ u
      (concat_ae (huf.trans (.of_forall fun s => by unfold concat; split_ifs <;> simp)) huf hm.coeFn_toLp)
  obtain ⟨δ', hδ', horbit⟩ := Metric.tendsto_nhdsWithin_nhds.1 (hT_cont y) (ε / 2 / M) (by positivity)
  refine ⟨min δ δ', lt_min hδpos hδ', fun t (ht : 0 ≤ t) hdist => ?_⟩
  let r := t - t₁
  let d := t₀ - t₁
  rw [Real.dist_eq, show t - t₀ = r - d by ring] at hdist
  obtain ⟨hr1, hr2⟩ := abs_lt.1 (hdist.trans_le (min_le_left _ _))
  obtain ⟨hd1, hd2⟩ := abs_lt.1 (hdist.trans_le (min_le_right _ _))
  have ht₁t : t₁ ≤ t := max_le ht (by dsimp [r, d] at hr1; linarith)
  have ht₁₀ : t₁ ≤ t₀ := max_le ht₀ (by linarith)
  have hr : 0 ≤ r := sub_nonneg.2 ht₁t
  have hd0 : 0 ≤ d := sub_nonneg.2 ht₁₀
  have hdδ : d ≤ δ := by dsimp [d]; linarith [le_max_right 0 (t₀ - δ)]
  have hdτ : d ≤ τ := hdδ.trans (min_le_right _ _)
  have horb {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (haτ : a ≤ τ) (hd' : b - a < δ') :
      ‖T b y - T a y‖ < ε / 2 := by
    have hd : 0 ≤ b - a := sub_nonneg.2 hab
    have hb : T b y - T a y = T a (T (b - a) y - y) := by
      rw [← add_sub_cancel a b, hT_semigroup a (b - a) ha hd,
        ContinuousLinearMap.comp_apply, map_sub, add_sub_cancel]
    exact (hb ▸ ((T a).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hTbound a ha haτ) (norm_nonneg _))).trans_lt
      ((lt_div_iff₀' hM).1 (by
        simpa [dist_eq_norm] using horbit (Set.mem_Ici.2 hd) (by rwa [Real.dist_eq, sub_zero, abs_of_nonneg hd])))
  have h1 : ‖T r y - T d y‖ < ε / 2 := by
    rcases le_total d r with h | h
    · exact horb hd0 h hdτ (by linarith)
    · rw [norm_sub_rev]; exact horb hr h (h.trans hdτ) (by linarith)
  rw [dist_eq_norm, hcomp t ht₁t, hcomp t₀ ht₁₀,
    show T r y + Φ r u₁ - (T d y + Φ d u₁) = T r y - T d y + Φ r u₁ - Φ d u₁ by abel]
  linarith [hsmall hr (by linarith), hsmall hd0 (by linarith),
    norm_sub_le (T r y - T d y + Φ r u₁) (Φ d u₁), norm_add_le (T r y - T d y) (Φ r u₁)]

end PalomarALCS
end
