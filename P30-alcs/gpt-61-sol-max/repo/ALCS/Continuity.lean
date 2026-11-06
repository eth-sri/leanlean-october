module

public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Data.Nat.Pairing
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Interval.Finset.Basic
public import Mathlib.Order.SuccPred.IntervalSucc
public import Mathlib.Tactic.GRewrite
public import Mathlib.Tactic.WLOG
public import Mathlib.Tactic.ClearExcept
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.Instances.Nat
public import Mathlib.Topology.Order.Monotone
public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# Continuity for abstract `L^∞` control systems

This file proves Theorem 1.5 and Corollary 1.6 of F. Marbach,
*Continuity of solutions to abstract linear control systems* (2026).

The endpoint argument packs disjoint nearly extremal pulses into one bounded
operator on `ℓ^∞`. Phillips' diagonal lemma and a doubling inequality force the
right limit of the input-map norms to vanish. A locally uniform approximation
by semigroup orbits then gives continuity of every bounded-input response.
No integral representation of the input maps is assumed.
-/

public section

noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X]
  [NormedSpace 𝕜 X]

/-!
## Phillips' diagonal lemma

An infinite reservoir of bad indices is repeatedly thinned so that a selected
functional is small on every subset of the tail. The characteristic sequence of
all selected indices contradicts pointwise convergence. Norming functionals
from Hahn–Banach give the vector-valued formulation needed below.
-/

namespace PalomarALCS
attribute [local simp] Set.indicator_apply

open Classical in

/-- The characteristic sequence of a set of natural numbers. -/
abbrev chi (S : Set ℕ) : BoundedContinuousFunction ℕ 𝕜 :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (S.indicator 1) 1
    (by aesop)

/-- The `k`th canonical vector of `ℓ∞`. -/
abbrev e k := @chi 𝕜 _ {k}

variable [CompleteSpace X] {U} [NormedAddCommGroup U] [NormedSpace 𝕜 U] [CompleteSpace U]

local notation "ν" => volume.restrict (Set.Ici (0 : ℝ))
local notation "L" => Lp U ∞ ν

@[simp] abbrev concat a (u v : ℝ → U) s := if s < a then u s else v (s - a)

variable (T : ℝ → _) (Φ : ℝ → _ →L[𝕜] X)
    (hT_zero : T 0 = ContinuousLinearMap.id 𝕜 X)
    (hT_semigroup : ∀ t s, 0 ≤ t → 0 ≤ s → T (t + s) = T t ∘L T s)
    (hT_cont : ∀ x, Tendsto (T · x) (𝓝[≥] 0) (𝓝 x))
    (hΦ_concat : ∀ τ t, 0 ≤ τ → 0 ≤ t →
      ∀ u v w : Lp U ∞ ν,
      (⇑w =ᵐ[ν]
        fun s => if s < τ then u s else v (s - τ)) →
      Φ (τ + t) w = T t (Φ τ u) + Φ t v)

/-! ## Bounded inputs and concatenation on the half-line -/

abbrev coe_zero := Lp.coeFn_zero U ∞ ν

lemma concat_congr {f f' g g' : ℝ → U} a
    (hf : f =ᵐ[ν] f') (hg : g =ᵐ[ν] g') :
    concat a f g =ᵐ[ν] concat a f' g' := by
  filter_upwards [hf, ae_restrict_of_ae ((measurePreserving_sub_right volume a).quasiMeasurePreserving.ae
    (ae_imp_of_ae_restrict hg))]
  grind

/-- A strongly measurable, everywhere bounded control. -/
structure Control C where
  f : ℝ → U
  measurable : StronglyMeasurable f
  bound : ∀ t, ‖f t‖ ≤ C

variable {C} (Q : @Control U _ C)

def Control.input : L :=
  (memLp_top_of_bound Q.measurable.aestronglyMeasurable C (.of_forall Q.bound)).toLp Q.f

lemma Control.coe_input : ⇑Q.input =ᵐ[ν] Q.f := MemLp.coeFn_toLp _

lemma Control.norm_input_le : ‖Q.input‖ ≤ C := by
  simpa [Control.input, eLpNorm_exponent_top Q.measurable.aestronglyMeasurable] using
    ENNReal.toReal_le_of_le_ofReal ((norm_nonneg _).trans (Q.bound 0))
      (eLpNormEssSup_le_of_ae_bound (.of_forall Q.bound))

lemma exists_bounded_rep (u : L) : ∃ P : Control ‖u‖, ⇑u =ᵐ[ν] P.f := by
  borelize U
  choose f hf hb hu using u.val.aestronglyMeasurable.exists_stronglyMeasurable_range_subset
    (measurableSet_le measurable_norm measurable_const) ⟨0, by simp⟩
    (ae_le_lpNorm_exponent_top u.prop)
  exact ⟨⟨f, hf, hb⟩, hu⟩

attribute [measurability] stronglyMeasurable_zero Control.measurable StronglyMeasurable.ite

/-- A pulse whose norm remains nearly extremal after a short free evolution. -/
structure FrozenPulse extends @Control U _ 1 where
  h : ℝ
  off : ∀ t, h ≤ t → f t = 0
  r : Set.Ioc 0 h
  near : ‖Φ h‖ - h ≤ ‖Φ (h + r) toControl.input‖

attribute [grind!] Control.bound norm_zero FrozenPulse.off

include hT_zero hT_semigroup hT_cont hΦ_concat

/-- Theorem 1.5: every `L^∞` system is zero-class. -/
theorem zero_class : Tendsto (‖Φ ·‖) (𝓝[≥] 0) (𝓝 0) := by
  classical
  let pulse (h : ℝ) (hh : 0 < h) : FrozenPulse Φ := by
    choose u hu hnear using (Φ h).exists_lt_apply_of_lt_opNorm (sub_lt_self _ hh)
    choose g hug using exists_bounded_rep u
    let P : Control 1 :=
      ⟨concat h g.f 0, by measurability, by dsimp; grind⟩
    have heq := hΦ_concat h 0 hh.le le_rfl u 0 P.input
      (P.coe_input.trans (concat_congr h hug coe_zero).symm)
    simp [hT_zero] at heq
    choose r hr he using (Filter.Eventually.and (Ioc_mem_nhdsGT hh)
      (((hT_cont _).norm.eventually_const_lt (heq.symm ▸ hnear)).filter_mono
        (nhdsWithin_mono _ Set.Ioi_subset_Ici_self))).exists
    exact ⟨P, h, by aesop, ⟨r, hr⟩, by
      simpa [P, hΦ_concat h r hh.le hr.1.le P.input 0 P.input (by
          filter_upwards [P.coe_input,
            concat_congr h P.coe_input coe_zero]
          grind)] using he.le⟩
  /- The time scales, defined recursively: `h 0 = 1` and `h (n + 1) = r n / 2`, so that
  the next pulse fits inside the free-evolution interval of the previous one. -/
  let data : ℕ → FrozenPulse Φ :=
    Nat.rec (pulse 1 zero_lt_one)
      (fun _ P => pulse (P.r.1 / 2) (half_pos P.r.2.1))
  let h n := (data n).h

  /- The free-evolution time `r_n ∈ (0, h_n]`. -/
  let r n := (data n).r.1

  /- The sampled state `x_n = Φ_{d_n} u_n`, where `d_n = h_n + r_n`. -/
  let d n := h n + r n
  let x n := Φ (d n) (data n).input

  have hr := forall_and.1 (fun n => (data n).r.2)
  have h_succ n : h (n + 1) = r n / 2 := rfl
  clear_value data

  have h_tendsto :=
    (summable_of_ratio_norm_eventually_le (f := h) one_half_lt_one
      (.of_forall (by grind [Real.norm_eq_abs]))).tendsto_atTop_zero

  have d_tendsto := by simpa using h_tendsto.add (squeeze_zero (by grind) hr.2 h_tendsto)

  /- Packing the pulses into one bounded operator `ℓ^∞ → X`. -/

  /- Pack before the fixed horizon `H = d 0`, leaving the free-evolution gaps empty. -/
  let start n := d 0 - d n

  /- Enlarging the support intervals makes disjointness a standard interval lemma. -/
  let window n := Set.Ico (start n) (start (n + 1))

  /- The `n`-th pulse, delayed so that it is played on `window n`. -/
  let block n :=
    concat (start n) 0 (data n).f

  have start_mono : Monotone start :=
    monotone_nat_of_le_succ (by grind)

  have block_off n {t} (ht : t ∉ window n) : block n t = 0 := by
    dsimp [block]
    grind

  /- The packed control `u^α` (raw function): on `window n` it is `α_n` times the `n`-th
  pulse, and it vanishes outside the windows. -/
  let packRaw (a : BoundedContinuousFunction ℕ 𝕜) t := ∑' n, a n • block n t

  have packRaw_formula a t :
      packRaw a t = if ht : ∃ n, t ∈ window n then a ht.choose • block ht.choose t else 0 := by
    split_ifs with ht
    · apply tsum_eq_single ht.choose
      intro j hj
      simp [block_off j ((start_mono.pairwise_disjoint_on_Ico_succ hj).notMem_of_mem_right ht.choose_spec)]
    · simp_all [packRaw]

  let packInput a : Control ‖a‖ :=
    ⟨packRaw a, by clear packRaw_formula; measurability, by
      intro t
      rw [packRaw_formula]
      dsimp [block]
      split_ifs <;> try simp
      grw [norm_smul, Control.bound, mul_one, a.norm_coe_le_norm]⟩

  /- The contraction from bounded sequences to bounded controls. -/
  let packing := by
    refine LinearMap.mkContinuous (σ := RingHom.id 𝕜)
      { toFun := fun a => (packInput a).input
        map_add' := fun a b => ?_
        map_smul' := fun c a => ?_ } 1
      (fun a => by simpa using (packInput a).norm_input_le)
    all_goals
      simp only [Control.input, ← MemLp.toLp_add, ← MemLp.toLp_const_smul]
      congr
      ext
      simp [packInput, packRaw_formula, dite_add_dite, add_smul, smul_smul]

  /- The operator `S : ℓ^∞ → X`, `S α = Φ_H u^α`. -/
  let packedOperator :=
    Φ (d 0) ∘L packing

  /- Delay identifies each basis image exactly with the sampled state. -/
  have packedOperator_e n :
      packedOperator (e n) = x n := by
    let P := data n
    simpa [packedOperator, start, x] using hΦ_concat (start n) (d n)
      (by simpa [start] using start_mono bot_le) (by grind) 0 P.input (packing (e n))
      ((packInput (e n)).coe_input.trans (by
        simpa [Filter.EventuallyEq, packInput, packRaw, ite_smul, -smul_ite, block] using
          (concat_congr _ coe_zero P.coe_input).symm))

  /- The right-hand limit of the monotone input-map norms. -/
  have norm_Phi_limit :=
    (show MonotoneOn (‖Φ ·‖) (Set.Ioi 0) from by
      clear * - hΦ_concat
      intro s hs t _ hst
      apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
      intro u
      choose g hug using exists_bounded_rep u
      let w : Control ‖u‖ :=
        ⟨concat (t - s) 0 g.f, by measurability, by dsimp; grind⟩
      grind [ContinuousLinearMap.le_opNorm_of_le, w.norm_input_le,
        hΦ_concat _ s (sub_nonneg.2 hst) hs.le 0 u w.input
          (w.coe_input.trans (concat_congr _ coe_zero hug).symm)]).tendsto_nhdsGT
        ⟨0, by simp [mem_lowerBounds]⟩

  /- Phillips’ diagonal argument. -/

  /- Phillips applies directly to `(T(dₙ) - Id) ∘ packedOperator`. -/
  let A n := T (d n) ∘L packedOperator - packedOperator
  have hA a : Tendsto (A · a) atTop (𝓝 0) := by
      simpa [A] using tendsto_sub_nhds_zero_iff.2 ((hT_cont _).comp (tendsto_nhdsWithin_iff.2
        ⟨d_tendsto, .of_forall (by grind)⟩))
  have x_moves_tendsto : Tendsto (fun n => ‖A n (e n)‖) atTop (𝓝 0) := by
    clear_value A
    clear * - hA
    -- Choose a norming functional for each diagonal vector.
    choose φ hφnorm hφeval using fun n => exists_dual_vector'' 𝕜 (A n (e n))
    let μ n := φ n ∘L A n
    have hμ B := tendsto_zero_iff_norm_tendsto_zero.1 (
      squeeze_zero_norm (fun n => by
        simpa [μ] using (φ n).le_of_opNorm_le (hφnorm n) _)
        (tendsto_zero_iff_norm_tendsto_zero.1 (hA (chi B))))
    suffices Tendsto (fun n => μ n (e n)) atTop (𝓝 0) by
      simpa [μ, hφeval] using this.norm
    apply Metric.tendsto_atTop.2
    intro ε hε
    by_contra hnot
    let δ := ε / 4
    have hδ : 0 < δ := by positivity
    -- A reservoir is an infinite subset of the bad indices.
    let Reservoir := {S : Set ℕ // S.Infinite}
    choose pick tail hpick hhead hsub hsmall using fun F (S : Reservoir) => show ∃ n, ∃ T : Reservoir,
        n ∈ S.val ∧
        ‖μ n (chi F)‖ < δ ∧
        T.val ⊆ S.val ∩ Set.Ioi n ∧
        (∀ B ⊆ T.val, ‖μ n (chi B)‖ ≤ δ) from by
      choose n  hnS  hnHead using ((Nat.frequently_atTop_iff_infinite.2 S.property).and_eventually
        ((hμ F).eventually_lt_const hδ)).exists
      let φ := μ n
      -- Partition an infinite subset of S into infinitely many infinite sets.
      let g := Nat.pairEquiv.toEmbedding.trans (Set.Infinite.natEmbedding _ (S.property.sdiff (Set.finite_le_nat n)))
      let A i := Set.range fun j => (g (i, j)).val
      by_contra! h
      choose B hBA hBδ using fun i =>
        h n ⟨A i, Set.infinite_range_of_injective (by grind [Function.Injective, g.injective.eq_iff])⟩ hnS
          hnHead
          (by grind)
      let v i : BoundedContinuousFunction ℕ 𝕜 := (φ (chi (B i)))⁻¹ • chi (B i)
      have hv i : φ (v i) = 1 := by
        simp [v]
        grind [norm_pos_iff]
      -- Disjoint supports give a norm bound independent of the number of terms.
      have hsum s : ‖Finset.sum s v‖ ≤ δ⁻¹ := by
        apply BoundedContinuousFunction.norm_le_of_nonempty.2
        intro x
        rw [BoundedContinuousFunction.sum_apply]
        by_cases hx : ∃ i, x ∈ B i
        · choose i  hi using hx
          have hxj j : x ∈ B j ↔ j = i := by grind [g.injective.eq_iff]
          simp [hxj]
          split_ifs
          · simpa using inv_anti₀ hδ (hBδ i).le
          · simp [hδ.le]
        · simp_all [hδ.le]
      have hN N := by simpa [hv] using φ.le_opNorm_of_le (hsum (Finset.range N))
      grind [exists_nat_gt (‖φ‖ * δ⁻¹)]
    -- State = (already selected indices, current infinite reservoir).
    let state : ℕ → Set ℕ × Reservoir :=
      Nat.rec (∅, ⟨{n | ε ≤ ‖μ n (e n)‖}, Nat.frequently_atTop_iff_infinite.1 (by
            simpa [Filter.Frequently, eventually_atTop] using hnot)⟩)
        (fun _ p => (insert (pick p.1 p.2) p.1, tail p.1 p.2))
    let n i := pick (state i).1 (state i).2
    let F i := (state i).1
    let R i := (state i).2
    have hnmem i := hpick (F i) (R i)
    have hnmono : StrictMono n := by
      apply strictMono_nat_of_lt_succ
      grind
    have hRanti : Antitone R := antitone_nat_of_succ_le
      (fun i => (hsub ..).trans Set.inter_subset_left)
    have hFmem i : F i = n '' Set.Iio i := by
      induction i
      next => aesop
      next i ih =>
        erw [Order.Iio_succ_eq_insert, Set.image_insert_eq, ← ih]
        rfl
    -- The characteristic sequence of all selected indices contradicts hμ.
    choose N  hA_small using
      (hnmono.tendsto_atTop.eventually ((hμ (Set.range n)).eventually_lt_const hδ)).exists
    have := hsmall (F N) (R N) (n '' Set.Ioi N) (Set.image_subset_iff.2 fun j hij => hRanti hij (hnmem j))
    have : ε ≤ _ := hRanti bot_le (hnmem N)
    have : @e 𝕜 _ (n N) = chi (Set.range n) - chi (F N) - chi (n '' Set.Ioi N) := by
      ext
      simp [hFmem]
      split_ifs <;> grind [hnmono.injective.eq_iff]
    clear_value state
    grind [norm_sub_le]
  simp [A, packedOperator_e] at x_moves_tendsto

  rw [← nhdsGT_sup_nhdsWithin_singleton, tendsto_sup]
  refine ⟨?_, by
    suffices Φ 0 = 0 by simp [Filter.Tendsto, this]
    ext u
    simpa [hT_zero] using hΦ_concat 0 0 le_rfl le_rfl u u u
      (by simp)⟩
  convert norm_Phi_limit using 2
  grind [Real.sInf_nonneg, le_of_tendsto_of_tendsto
    (((norm_Phi_limit.comp
      (tendsto_nhdsWithin_iff.2 ⟨h_tendsto, .of_forall (by grind)⟩)).sub h_tendsto).const_mul 2)
    ((norm_Phi_limit.comp (tendsto_nhdsWithin_iff.2
      ⟨by simpa using d_tendsto.const_mul 2, .of_forall (by grind)⟩)).add x_moves_tendsto) (.of_forall fun n => by
      -- Playing the same pulse twice gives the doubling inequality.
      clear * - hΦ_concat hr
      let P := data n
      let w : Control 1 := ⟨concat (d n) P.f P.f, by measurability, by grind⟩
      let v := T (d n) (x n)
      have hn := norm_sub_le (v + x n) (v - x n)
      simp [← two_smul 𝕜, norm_smul] at hn
      rw [← hΦ_concat _ _ (by grind) (by grind) P.input P.input w.input
          (w.coe_input.trans (concat_congr _ P.coe_input P.coe_input).symm),
        ← two_mul] at hn
      linarith! [P.near, (Φ (2 * d n)).le_opNorm_of_le w.norm_input_le])]

/-- Corollary 1.6: every bounded input has a continuous response. -/
theorem continuousOn_Phi (u : L) :
    ContinuousOn (Φ · u) (Set.Ici 0) := by
  choose τ hτ hb using show ∃ τ > 0, ∀ t, 0 ≤ t → t ≤ τ → ‖T t‖ ≤ τ⁻¹ from by
    by_contra! h
    choose t ht0 htle htbig using fun n : ℕ =>
      h (1 / (n + 1)) (by positivity)
    have htlim :=
      tendsto_nhdsWithin_iff.2
        ⟨squeeze_zero ht0 htle tendsto_one_div_add_atTop_nhds_zero_nat, .of_forall ht0⟩
    choose C  hC using banach_steinhaus (fun x => by
      simpa [bddAbove_def] using ((hT_cont x).comp htlim).norm.bddAbove_range)
    grind [exists_nat_gt C]
  apply continuousOn_of_locally_uniform_approx_of_continuousWithinAt
  intro t₀ ht₀ V hV
  choose ε  hε  hVε using Metric.mem_uniformity_dist.1 hV
  choose η  hη  hκ using Metric.tendsto_nhdsWithin_nhds.1 ((zero_class T Φ hT_zero hT_semigroup hT_cont hΦ_concat).mul_const ‖u‖) ε hε
  let a := max 0 (t₀ - min η τ / 2)
  let y := Φ a u
  have horbit : ContinuousOn (T · y) (Set.Icc 0 τ) := by
    rw [Metric.continuousOn_iff]
    intro t₀ ht₀ ε hε
    choose δ  hδ  hc using Metric.tendsto_nhdsWithin_nhds.1
      (hT_cont y) (τ * ε) (by positivity)
    refine ⟨δ, hδ, fun t ht hdist => ?_⟩
    wlog htt : t₀ ≤ t generalizing t₀ t
    · clear hT_semigroup
      grind [dist_comm]
    have hd := sub_nonneg.2 htt
    grind [dist_eq_norm, hT_semigroup t₀ (t - t₀) ht₀.1 hd,
      ((T t₀).le_of_opNorm_le (hb t₀ ht₀.1 ht₀.2) _).trans_lt
        ((inv_mul_lt_iff₀ hτ).2 (by
          simpa [dist_eq_norm] using hc hd (by
            simpa [Real.dist_eq] using hdist)))]
  choose f hu using exists_bounded_rep u
  let hm : Control ‖u‖ := ⟨fun t => f.f (a + t), by measurability, by grind⟩
  refine ⟨Set.Ico a (a + min η τ),
    Metric.mem_nhdsWithin_iff.2 ⟨min η τ / 2, by positivity, by
      clear hT_semigroup hm hκ
      grind [Metric.mem_ball, Real.dist_eq]⟩, fun t => T (Set.projIcc 0 τ hτ.le (t - a)) y,
    (horbit.domRestrict.comp (by fun_prop)).continuousWithinAt, fun t ht => hVε ?_⟩
  have hr := sub_nonneg.2 ht.1
  have he := hΦ_concat a _ (le_max_left ..) hr u hm.input u (by
    filter_upwards [hu, concat_congr a hu hm.coe_input]
    grind)
  simp at he
  simpa [y, he, Set.projIcc_of_mem hτ.le ⟨hr, by grind⟩] using ((Φ (t - a)).le_opNorm_of_le hm.norm_input_le).trans_lt
    (by simpa using hκ hr (by grind [Real.dist_eq]))

end PalomarALCS

end
