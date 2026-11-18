module

public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Nat.Pairing
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

public section

/-!
# Abstract linear control systems with `L^∞` inputs: zero-class property and continuity

Proofs of the two main results of F. Marbach,
*Continuity of solutions to abstract linear control systems* (2026),
<https://hexagonmath.org/2610.00022>:
* `PalomarALCS.zero_class` : **Theorem 1.5** (`thm:p-infty-zero-class`), every system with
  `p = ∞` is zero-class (`‖Φ t‖ → 0` as `t → 0⁺`);
* `PalomarALCS.continuousOn_Phi` : **Corollary 1.6** (`cor:p-infty-solution-continuous`),
  `t ↦ Φ t u` is continuous on `[0, ∞)` for every `u ∈ L^∞(ℝ₊; U)`.
-/

open Set MeasureTheory Filter Topology Classical Nat Lp MemLp
open scoped ENNReal

namespace PalomarALCS

/-- Contradiction form of Phillips' diagonal lemma for bounded finitely additive real set
functions on `ℕ`: if `f n C → 0` for each `C`, then `f n {n}` cannot stay bounded away from `0`. -/
private lemma phillips_contra {f : ℕ → Set ℕ → ℝ} {K : _ → _} {δ} (hδ : 0 < δ)
    (hadd : ∀ n C D, Disjoint C D → f n (C ∪ D) = f n C + f n D)
    (hbdd : ∀ n C, |f n C| ≤ K n)
    (hlim : ∀ C, Tendsto (f · C) atTop (𝓝 0))
    (hdiag : ∀ n, 3 * δ ≤ f n {n}) : False := by
  have hsmall C := Metric.tendsto_atTop.1 (hlim C) δ hδ
  let Res := {s : ℕ → ℕ // StrictMono s}
  have hstep F (s : Res) : ∃ n, ∃ t : Res,
      (n ∈ range s.1 ∧ dist (f n F) 0 < δ) ∧ range t.1 ⊆ range s.1 ∩ Ioi n ∧
      ∀ B ⊆ range t.1, |f n B| ≤ δ := by
    obtain ⟨N, hN⟩ := hsmall F
    let n := s.1 N
    let col i : Res := ⟨fun j => s.1 (N + 1 + pair i j),
      s.2.comp fun _ _ h => add_lt_add_right (pair_lt_pair_right i h) _⟩
    obtain ⟨i, hi⟩ : ∃ i, ∀ B ⊆ range (col i).1, |f n B| ≤ δ := by
      by_contra! H'
      choose B hBA hB using H'
      have {i j x} (hx : x ∈ B i) (hy : x ∈ B j) : i = j := by
        grind [s.2.injective.eq_iff, pair_eq_pair]
      have hind m : ∃ P N, (∀ x, x ∈ P ∨ x ∈ N → ∃ i < m, x ∈ B i) ∧
          m * δ ≤ f n P - f n N := by
        induction m with
        | zero => use ∅, ∅; simp
        | succ m ih =>
          obtain ⟨P, N, _⟩ := ih
          by_cases 0 ≤ f n (B m) <;> [use P ∪ B m, N; use P, N ∪ B m] <;>
            refine ⟨by grind, ?_⟩ <;>
            rw [hadd _ _ _ (by grind)] <;> grind [cast_succ]
      obtain ⟨M, hM⟩ := exists_nat_gt (2 * K n / δ)
      obtain ⟨P, N, _⟩ := hind M
      grind [hbdd n P, hbdd n N, (div_lt_iff₀ hδ).1 hM]
    exact ⟨n, col i, ⟨⟨N, rfl⟩, hN n (s.2.id_le N)⟩,
      forall_mem_range.2 fun _ => ⟨⟨_, rfl⟩, s.2 (by omega)⟩, hi⟩
  choose pick tail hst using hstep
  let st : ℕ → Set ℕ × Res :=
    Nat.rec (∅, ⟨id, strictMono_id⟩) fun _ p => ({pick p.1 p.2} ∪ p.1, tail p.1 p.2)
  let F i := (st i).1
  let n i := pick (F i) (st i).2
  have hi i := hst (F i) (st i).2
  have hnmono : StrictMono n :=
    strictMono_nat_of_lt_succ fun i => ((hi i).2.1 (hi (i + 1)).1.1).2
  have hF i x : x ∈ F i ↔ ∃ j < i, n j = x := by
    induction i <;> simp [F, st, n] at *; grind
  obtain ⟨N, hN⟩ := hsmall (range n)
  have := (hi N).2.2 (range n \ F (N + 1)) <| by
    rintro _ ⟨⟨j, rfl⟩, hnot⟩
    exact antitone_nat_of_succ_le (f := fun i => range (st i).2.1)
      (fun i => (hi i).2.1.trans inter_subset_left)
      (not_lt.1 fun h => hnot ((hF (N + 1) _).2 ⟨j, h, rfl⟩)) (hi j).1.1
  have h1 := hN (n N) (hnmono.id_le N)
  rw [← union_sdiff_cancel (by grind : F (N + 1) ⊆ range n),
    hadd _ _ _ disjoint_sdiff_self_right,
    hadd _ {n N} (F N) (by simp [hF, hnmono.injective.eq_iff])] at h1
  grind [Real.dist_eq, (hi N).1.2, hdiag (n N)]

variable {𝕜 : Type*} [RCLike 𝕜]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  {U : Type*} [NormedAddCommGroup U] [NormedSpace 𝕜 U] [CompleteSpace U]

local notation "μ₊" => volume.restrict (Ici (0 : ℝ))
local notation "E" => Lp U ∞ μ₊

private lemma ae_norm_le (u : E) : ∀ᵐ s ∂μ₊, ‖u s‖ ≤ ‖u‖ := by
  simpa [← enorm_le_iff_norm_le, enorm_def, eLpNorm_exponent_top u.1.aestronglyMeasurable]
    using enorm_ae_le_eLpNormEssSup u μ₊

private lemma exists_lp {f : _ → U} (hf : AEStronglyMeasurable f μ₊) {C} (hC : 0 ≤ C)
    (hb : ∀ᵐ s ∂μ₊, ‖f s‖ ≤ C) : ∃ w : E, ‖w‖ ≤ C ∧ ⇑w =ᵐ[μ₊] f :=
  let hm := memLp_top_of_bound hf C hb
  ⟨hm.toLp f, norm_toLp f hm ▸ ENNReal.toReal_le_of_le_ofReal hC
    (eLpNorm_exponent_top hf ▸ eLpNormEssSup_le_of_ae_bound hb), hm.coeFn_toLp⟩

private lemma ae_sub {P : _ → _} c (hP : ∀ᵐ s ∂μ₊, P s) :
    ∀ᵐ s ∂μ₊, 0 ≤ s - c → P (s - c) :=
  ae_restrict_of_ae <| (eventually_sub_right_iff _ c).2 <| (ae_restrict_iff' measurableSet_Ici).1 hP

private lemma exists_concat (τ : ℝ) (u v : E) :
    ∃ w : E, ‖w‖ ≤ max ‖u‖ ‖v‖ ∧ ⇑w =ᵐ[μ₊] fun s => if s < τ then u s else v (s - τ) :=
  exists_lp (u.1.stronglyMeasurable.ite measurableSet_Iio (by fun_prop)).aestronglyMeasurable
    (by positivity) (by filter_upwards [ae_norm_le u, ae_sub τ (ae_norm_le v)] with _ _ _; grind)

variable (T : ℝ → X →L[𝕜] X) (Φ : ℝ → Lp U ∞ μ₊ →L[𝕜] X)
  (hT_zero : T 0 = .id 𝕜 X)
  (hT_semigroup : ∀ t s, 0 ≤ t → 0 ≤ s → T (t + s) = T t ∘L T s)
  (hT_cont : ∀ x, Tendsto (T · x) (𝓝[≥] 0) (𝓝 x))
  (hΦ_concat : ∀ τ t, 0 ≤ τ → 0 ≤ t → ∀ u v w : Lp U ∞ μ₊,
    (⇑w =ᵐ[μ₊] fun s => if s < τ then u s else v (s - τ)) →
    Φ (τ + t) w = T t (Φ τ u) + Φ t v)

include T Φ hT_zero hT_semigroup hT_cont hΦ_concat

/-- **Theorem 1.5** (`thm:p-infty-zero-class`, zero-class property).
For an abstract linear control system `(T, Φ)` with inputs in `L^∞(ℝ₊; U)`,
`‖Φ_t‖ → 0` as `t → 0⁺` (operator norm of `Φ_t : L^∞(ℝ₊; U) → X`). -/
theorem zero_class : Tendsto (fun t => ‖Φ t‖) (𝓝[≥] 0) (𝓝 0) := by
  have hmono {s t} (hs : 0 ≤ s) (hst : s ≤ t) :=
    (Φ s).opNorm_le_bound (norm_nonneg (Φ t)) fun u => by
      obtain ⟨w, hw, hcat⟩ := exists_concat (t - s) 0 u
      have := hΦ_concat (t - s) s (sub_nonneg.2 hst) hs 0 u w hcat
      simp [sub_add_cancel] at this
      exact this ▸ (Φ t).le_opNorm_of_le (by simpa [norm_nonneg u] using hw)
  let ℓ := ⨅ t : Ioi (0 : ℝ), ‖Φ t.1‖
  have hℓ : ℓ ≤ 0 := by
    by_contra! hℓpos
    obtain ⟨⟨τ, hτ⟩, hτlt⟩ := exists_lt_of_ciInf_lt (show ℓ < ℓ + ℓ / 4 by linarith)
    let S := {t : ℝ // 0 < t ∧ 2 * t ≤ τ}
    have hstep (s : S) : ∃ t' : S, ∃ u,
        ‖u‖ ≤ 1 ∧ 2 * t'.1 ≤ s.1 ∧ ℓ / 4 ≤ ‖(T s.1 - .id 𝕜 X) (T (2 * t'.1) (Φ s.1 u))‖ := by
      obtain ⟨t, ht1, ht2⟩ := s
      have : ℓ ≤ ‖Φ t‖ :=
        ciInf_le ⟨0, forall_mem_range.2 fun _ => norm_nonneg _⟩ (⟨t, ht1⟩ : Ioi _)
      obtain ⟨u, hu, hnear⟩ := (Φ t).exists_lt_apply_of_lt_opNorm (by linarith : ℓ - ℓ / 8 < _)
      let x := Φ t u
      let B := T t - .id 𝕜 X
      obtain ⟨w, hw, hcat⟩ := exists_concat t u u
      have hdb := (norm_sub_le _ (B x)).trans
        (add_le_add_left ((Φ (2 * t)).unit_le_opNorm w (by grind only [max_def])) _)
      rw [show Φ (2 * t) w - B x = (2 : 𝕜) • x by
        simp [two_mul, hΦ_concat _ _ ht1.le ht1.le _ _ _ hcat, two_smul, x, B],
        norm_smul, RCLike.norm_ofNat] at hdb
      obtain ⟨δ, hδ, hc⟩ := mem_nhdsGE_iff_exists_Icc_subset.1
        ((((B.continuous.tendsto x).comp (hT_cont x)).norm).eventually
          (lt_mem_nhds (by linarith [hmono (by positivity) ht2] : ℓ / 4 < _)))
      refine ⟨⟨min t δ / 2, ?_, ?_⟩, u, hu.le, ?_, (hc ⟨?_, ?_⟩).le⟩ <;>
        linarith [lt_min ht1 hδ, min_le_left t δ, min_le_right t δ]
    choose next pu hst using hstep
    let hs : ℕ → S := Nat.rec
      ⟨min 2⁻¹ (τ / 2), by constructor <;> grind only [min_def, mem_Ioi]⟩ fun _ => next
    let h n := (hs n).1
    have hh0 n := (hs n).2.1.le
    have hp n := hst (hs n)
    have hh_pow n : h n ≤ 2⁻¹ ^ n := by
      induction n with
      | zero => exact (min_le_left _ _).trans (by norm_num)
      | succ n => rw [pow_succ]; grind only [(hp n).2.1]
    let r n := 2 * h (n + 1)
    let start n := 1 - r n - h n
    let W n := Ico (start n) (start n + h n)
    let u n := pu (hs n)
    have hstart_mono : Monotone start := monotone_nat_of_le_succ fun n => by
      grind only [(hp (n + 1)).2.1, (hs n).2.1]
    have hstart0 n : 0 ≤ start n := by
      have := hstart_mono n.zero_le; dsimp [start] at this ⊢
      linarith [show r 0 ≤ h 0 from (hp 0).2.1, show h 0 ≤ 2⁻¹ from min_le_left _ _]
    have hW_disj := (pairwise_disjoint_on W).2 fun i j hij => disjoint_left.2 fun _ _ _ => by
      grind only [mem_Ico, hstart_mono hij, (hp (i + 1)).2.1]
    let g₀ s := let k := epsilon (s ∈ W ·); u k (s - start k)
    have hg₀ {n s} (hs : s ∈ W n) : g₀ s = u n (s - start n) := by
      simp [g₀, hW_disj.eq (not_disjoint_iff.2 ⟨_, epsilon_spec (⟨n, hs⟩ : ∃ k, s ∈ W k), hs⟩)]
    clear_value g₀
    choose pack hpnorm hpae using fun C : Set ℕ => exists_lp
      ((aestronglyMeasurable_indicator_iff (.biUnion C.to_countable fun _ _ => measurableSet_Ico)).2
        ((AEStronglyMeasurable.iUnion fun n => (by fun_prop : StronglyMeasurable _).aestronglyMeasurable.congr
          ((ae_restrict_mem measurableSet_Ico).mono fun _ hs => (hg₀ hs).symm)).mono_set
          (iUnion₂_subset fun n _ => subset_iUnion W n))) zero_le_one (by
        filter_upwards [ae_all_iff.2 fun n => ae_sub (start n) (ae_norm_le (u n))] with s hs
        rw [indicator_apply]; split_ifs with hm
        · obtain ⟨n, _, hn⟩ := mem_iUnion₂.1 hm
          grind only [hs n, (hp n).1, mem_Ico]
        · simp)
    let A n := T (h n) - .id 𝕜 X
    have := NormedSpace.restrictScalars ℝ 𝕜 X
    choose g' hgnorm hgeval using fun n => exists_dual_vector'' ℝ (A n (Φ 1 (pack {n})))
    let f n C := g' n (A n (Φ 1 (pack C)))
    exact phillips_contra (f := f) (δ := ℓ / 12) (by positivity)
      (fun n C D hCD => by
        dsimp [f]; rw [Lp.ext ((hpae (C ∪ D)).trans <| by
          rw [biUnion_union, indicator_union_of_disjoint
            (disjoint_iUnion₂_left.2 fun i hi =>
              disjoint_iUnion₂_right.2 fun j hj => @hW_disj i j (hCD.ne_of_mem hi hj))]
          exact ((coeFn_add _ _).trans ((hpae C).add (hpae D))).symm)]; simp)
      (fun n C => (g' n).le_of_opNorm_le_of_le (hgnorm n)
        ((A n ∘L Φ 1).unit_le_opNorm _ (hpnorm C)))
      (fun C =>
        let z := Φ 1 (pack C)
        squeeze_zero_norm (fun n => (g' n).le_of_opNorm_le (hgnorm n) _)
          (by simpa [A] using (((hT_cont z).comp (tendsto_nhdsWithin_iff.2
            ⟨squeeze_zero hh0 hh_pow (by simp; norm_num), .of_forall hh0⟩)).sub_const z).norm))
      fun n => by
        obtain ⟨v, _, hv⟩ := exists_concat (start n) 0 (u n)
        dsimp [f]
        rw [hgeval n, ← sub_add_cancel 1 (r n),
          hΦ_concat (1 - r n) (r n) (by linarith [hstart0 n, hh0 n])
            (mul_nonneg zero_le_two (hh0 (n + 1)))
            v 0 _ (by
              filter_upwards [hpae {n}, hv, coeFn_zero U ∞ μ₊,
                ae_sub (1 - r n) (coeFn_zero U ∞ μ₊)] with s h1 hv' h0 h0'
              simp only [h1, hv', h0, biUnion_singleton, indicator_apply, mem_Ico, Pi.zero_apply]
              split_ifs <;>
                first | rfl | exact hg₀ ‹_› | exact (h0' (by linarith)).symm | grind only),
          ← sub_add_cancel (1 - r n) (h n),
          hΦ_concat _ _ (hstart0 n) (hh0 n) 0 (u n) v hv]
        simp; linarith [(hp n).2.2]
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  obtain ⟨⟨τ, hτ⟩, hτlt⟩ := exists_lt_of_ciInf_lt (hℓ.trans_lt hε)
  filter_upwards [Ico_mem_nhdsGE hτ] with t ht
  simpa using (hmono ht.1 ht.2.le).trans_lt hτlt

/-- **Corollary 1.6** (`cor:p-infty-solution-continuous`), answering Weiss' Problem 2.4.
Under the same hypotheses, for every input `u ∈ L^∞(ℝ₊; U)`, `t ↦ Φ_t u` is continuous on
`[0, ∞)`, including at `t = 0`. -/
theorem continuousOn_Phi u : ContinuousOn (fun t => Φ t u) (Ici 0) := by
  have hzu := zero_mul ‖u‖ ▸ (zero_class T Φ hT_zero hT_semigroup hT_cont hΦ_concat).mul_const ‖u‖
  obtain ⟨M, hTbdd⟩ : ∃ M, ∀ᶠ t in 𝓝[≥] 0, ‖T t‖ ≤ M := by
    by_contra! H
    choose t htgt ht0 ht1 using fun n : ℕ =>
      ((H n).and_eventually (Icc_mem_nhdsGE (one_div_pos_of_nat (n := n)))).exists
    obtain ⟨M, hM⟩ := banach_steinhaus fun x => by
      simpa [bddAbove_def] using ((hT_cont x).comp (tendsto_nhdsWithin_iff.2
        ⟨squeeze_zero ht0 ht1 tendsto_one_div_add_atTop_nhds_zero_nat,
          .of_forall ht0⟩)).norm.bddAbove_range
    obtain ⟨n, hn⟩ := exists_nat_gt M; linarith [htgt n, hM n]
  intro t₀ ht₀
  rcases ht₀.eq_or_lt with rfl | ht₀_pos
  · have h0 := squeeze_zero_norm (fun t => (Φ t).le_opNorm u) hzu
    rw [ContinuousWithinAt,
      tendsto_nhds_unique (tendsto_pure_nhds _ _) (h0.mono_left (pure_le_nhdsWithin le_rfl))]
    exact h0
  · refine (Metric.continuousAt_iff.2 fun ε hε => ?_).continuousWithinAt
    obtain ⟨η, ⟨hη, hηt⟩, hκ⟩ := (mem_nhdsGE_iff_exists_mem_Ioc_Ico_subset ht₀_pos).1
      (hTbdd.and <| hzu.eventually (gt_mem_nhds (by positivity : _ < ε / 4)))
    let δ := η / 2
    have hδη : δ ∈ Ico 0 η := by constructor <;> grind only
    let b := t₀ - δ
    obtain ⟨u₁, hu₁, hsh⟩ := exists_lp
      (by fun_prop : StronglyMeasurable fun s => u (s + b)).aestronglyMeasurable
      (norm_nonneg u) (by
        filter_upwards [ae_restrict_mem measurableSet_Ici, ae_sub (-b) (ae_norm_le u)] with _ _ _
        grind only [mem_Ici])
    have hcomp {r} hr :=
      hΦ_concat b r (by grind only) hr u u₁ u (by filter_upwards [ae_sub b hsh] with _ _; grind only)
    obtain ⟨ρ, hρ, horb⟩ := mem_nhdsGE_iff_exists_Ico_subset.1
      ((tendsto_sub_nhds_zero_iff.2 (hT_cont (Φ b u))).norm.const_mul M |>.eventually
        (gt_mem_nhds (by simp; positivity : _ < ε / 2)))
    refine ⟨min δ ρ, lt_min (half_pos hη) hρ, fun t ht => ?_⟩
    rw [← add_sub_cancel b t, show t₀ = b + δ by ring] at ht ⊢
    generalize t - b = r at *
    simp only [dist_add_left, Real.dist_eq, lt_min_iff] at ht
    have hr : r ∈ Ico 0 η := by constructor <;> grind only [abs_lt]
    replace ht := ht.2
    clear_value b δ
    wlog! h : δ ≤ r generalizing r δ
    · rw [dist_comm]; exact this r hr δ hδη (abs_sub_comm r δ ▸ ht) h.le
    have d := sub_nonneg.2 h
    rw [_root_.dist_eq_norm, hcomp hr.1, hcomp hδη.1, add_sub_add_comm]
    grw [norm_add_le, norm_sub_le (Φ r u₁), (Φ r).le_opNorm_of_le hu₁, (Φ δ).le_opNorm_of_le hu₁,
      (hκ hr).2.le, (hκ hδη).2.le]
    rw [← add_sub_cancel δ r, hT_semigroup _ _ hδη.1 d, ContinuousLinearMap.comp_apply, ← map_sub]
    grw [(T δ).le_opNorm, (hκ hδη).1]
    linarith [(horb ⟨d, abs_of_nonneg d ▸ ht⟩).out]

end PalomarALCS
