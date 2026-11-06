module

public import ALCS.Definitions
public import ALCS.Background.Phillips

@[expose] public section

/-!
# Every `L^∞` system is zero-class (Theorem 1.5)

**Theorem 1.5** (`thm:p-infty-zero-class`). Let `X`, `U` be Banach spaces and `(𝕋, Φ)`
an abstract linear control system with `p = ∞`. Then `‖Φ_t‖ → 0` as `t → 0`.

The final statement is `ALCS.zero_class`. The auxiliary declarations live in the namespace
`ALCS.ZeroClassProof` and follow § 2.3 of the paper:

* `ell` is the limit `ℓ = lim_{t → 0⁺} κ(t) = inf_{t > 0} κ(t)`, and `norm_Phi_tendsto`
  identifies it as the limit along any positive null sequence.
* Step 1, `doubling`: the doubling inequality `2 ‖Φ_h u‖ ≤ κ(2h) + ‖(T_h - 1) Φ_h u‖`
  for `‖u‖ ≤ 1`.
* Step 2, `Pulse`, `exists_pulse`, `hscale`, `data`: nearly extremal pulses `u_n` on rapidly
  decreasing time scales `h_n`, with states `x_n = Φ_{h_n} u_n`, each frozen during its own
  free-evolution time `r_n ∈ (0, h_n]`.
* Step 3, `packRaw`, `packing`, `packedOperator`: the pulses are packed into one bounded
  operator `S : ℓ^∞ → X`, and `packedOperator_close` gives `‖S e_n - x_n‖ ≤ 2^{-n}`.
* Step 4, `x_moves_tendsto`: Lemma 2.3 (`Phillips.uniform`) gives
  `‖(T_{h_n} - 1) x_n‖ → 0`, the second half of the limit in `eq:goal`.

The paper plays the pulses one after the other on consecutive intervals and evaluates at
the accumulated time; here each pulse is played on `[1 - r_n - h_n, 1 - r_n)` and the
operator is evaluated at time `1`, so that `S e_n = T_{r_n} x_n` exactly. This changes the
bookkeeping, not the argument.
-/

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

noncomputable section

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {U : Type*} [NormedAddCommGroup U] [NormedSpace 𝕜 U]

namespace ALCS
namespace ZeroClassProof

variable (S : ALCS 𝕜 X U)

local notation "L∞" => Lp U ∞ muPlus

/-! ### Step 1: the doubling inequality -/

/-- Step 1, the doubling inequality: for `h ≥ 0` and `‖u‖ ≤ 1`,
`2 ‖Φ_h u‖ ≤ κ(2h) + ‖T_h (Φ_h u) - Φ_h u‖`, obtained by playing `u` twice in a row. -/
lemma doubling {h : ℝ} (hh : 0 ≤ h) (u : L∞) (hu : ‖u‖ ≤ 1) :
    2 * ‖S.Φ h u‖ ≤ ‖S.Φ (2 * h)‖ + ‖S.T h (S.Φ h u) - S.Φ h u‖ := by
  obtain ⟨w, hw, hcat⟩ := exists_concat h u u zero_le_one hu hu
  have hcomp := S.composition h h hh hh u u w hcat
  have hb : ‖S.Φ (2 * h) w‖ ≤ ‖S.Φ (2 * h)‖ :=
    ((S.Φ (2 * h)).le_opNorm w).trans (by simpa using mul_le_of_le_one_right (norm_nonneg _) hw)
  have key : (2 : 𝕜) • S.Φ h u = S.Φ (2 * h) w - (S.T h (S.Φ h u) - S.Φ h u) := by
    rw [show 2 * h = h + h by ring, hcomp, two_smul]
    abel
  rw [show (2 : ℝ) * ‖S.Φ h u‖ = ‖(2 : 𝕜) • S.Φ h u‖ by rw [norm_smul, RCLike.norm_two], key]
  linarith [norm_sub_le (S.Φ (2 * h) w) (S.T h (S.Φ h u) - S.Φ h u)]

/-! ### Step 2: nearly extremal pulses on rapidly decreasing time scales -/

/-- An input of norm at most one which almost realizes `κ(h) = ‖Φ h‖`. -/
lemma exists_near_extremal (h ε : ℝ) (hε : 0 < ε) :
    ∃ u : L∞, ‖u‖ ≤ 1 ∧ ‖S.Φ h‖ - ε ≤ ‖S.Φ h u‖ := by
  by_cases hc : ‖S.Φ h‖ - ε ≤ 0
  · exact ⟨0, by simp, by simpa using hc⟩
  · by_contra hn
    have hbound : ‖S.Φ h‖ ≤ ‖S.Φ h‖ - ε := by
      apply ContinuousLinearMap.opNorm_le_of_unit_norm (le_of_lt (lt_of_not_ge hc))
      exact fun u hu => le_of_not_gt fun hlt => hn ⟨u, hu.le, hlt.le⟩
    linarith

/-- A *pulse* of length `h` with accuracy `ε`: an `L^∞` input `u` of norm at most one
whose chosen representative `f` vanishes outside `[0, h)` and is bounded by one
everywhere, which is almost extremal at time `h` and is frozen during a free time
`r ∈ (0, h]`. -/
structure Pulse (h ε : ℝ) where
  u : L∞
  f : ℝ → U
  coe : ⇑u =ᵐ[muPlus] f
  meas : StronglyMeasurable f
  bound : ∀ t, ‖f t‖ ≤ 1
  off : ∀ t, t < 0 ∨ h ≤ t → f t = 0
  norm : ‖u‖ ≤ 1
  r : ℝ
  rpos : 0 < r
  rle : r ≤ h
  near : ‖S.Φ h‖ - ε ≤ ‖S.Φ h u‖
  frozen : ‖S.T r (S.Φ h u) - S.Φ h u‖ ≤ ε

/-- A nearly extremal input can be chosen to be a pulse (by causality, truncating it at
time `h` does not change `Φ_h u`). -/
lemma exists_pulse (h ε : ℝ) (hh : 0 < h) (hε : 0 < ε) : Nonempty (Pulse S h ε) := by
  obtain ⟨u, hu, hnear⟩ := exists_near_extremal S h ε hε
  obtain ⟨g, hg, hgb, hug⟩ := exists_bounded_rep u (by norm_num) hu
  set f : ℝ → U := (Set.Ico 0 h).indicator g with hfdef
  have hf : StronglyMeasurable f := hg.indicator measurableSet_Ico
  have hfb : ∀ t, ‖f t‖ ≤ 1 := by
    intro t
    by_cases ht : t ∈ Set.Ico 0 h
    · simpa [hfdef, Set.indicator_of_mem ht] using hgb t
    · simp [hfdef, Set.indicator_of_notMem ht]
  have hoff : ∀ t, t < 0 ∨ h ≤ t → f t = 0 := by
    rintro t (h1 | h1)
    · exact Set.indicator_of_notMem (fun hin => (not_lt_of_ge hin.1) h1) g
    · exact Set.indicator_of_notMem (fun hin => (not_lt_of_ge h1) hin.2) g
  have hm : MemLp f ∞ muPlus := memLp_top_of_bound hf.aestronglyMeasurable 1 (ae_of_all _ hfb)
  have hraw : f =ᵐ[muPlus] concat h g (fun _ => (0 : U)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    by_cases hth : t < h
    · rw [concat, if_pos hth, hfdef, Set.indicator_of_mem (Set.mem_Ico.2 ⟨ht, hth⟩)]
    · rw [concat, if_neg hth, hfdef, Set.indicator_of_notMem (by simp [Set.mem_Ico, hth])]
  have hcat : ⇑(hm.toLp f) =ᵐ[muPlus] concat h ⇑u ⇑(0 : L∞) :=
    hm.coeFn_toLp.trans (hraw.trans (concat_congr h hug (Lp.coeFn_zero U ∞ muPlus)).symm)
  obtain ⟨δ, hδ, hcont⟩ := Metric.tendsto_nhdsWithin_nhds.1 (S.T_cont (S.Φ h (hm.toLp f))) ε hε
  have hr : 0 < min h (δ / 2) := lt_min hh (by positivity)
  refine ⟨⟨hm.toLp f, f, hm.coeFn_toLp, hf, hfb, hoff, norm_toLp_le hm (by norm_num) hfb,
    min h (δ / 2), hr, min_le_left _ _, ?_, ?_⟩⟩
  · rwa [show S.Φ h (hm.toLp f) = S.Φ h u from by
      simpa [S.T_zero, S.Phi_zero] using S.composition h 0 hh.le le_rfl u 0 (hm.toLp f) hcat]
  · have hrδ : min h (δ / 2) < δ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have h2 := hcont (Set.mem_Ici.2 hr.le) (by simpa [Real.dist_eq, abs_of_pos hr] using hrδ)
    rw [dist_eq_norm] at h2
    exact h2.le

/-- The accuracy `2^{-n}` of the `n`-th selection. -/
def err (n : ℕ) : ℝ := (2 : ℝ)⁻¹ ^ n

lemma err_pos (n : ℕ) : 0 < err n := by unfold err; positivity

lemma err_tendsto : Tendsto err atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- The time scales, defined recursively: `h 0 = 1/4` and `h (n + 1) = r n / 4`. -/
def hscale : ℕ → {h : ℝ // 0 < h} :=
  Nat.rec ⟨1 / 4, by norm_num⟩ fun n h =>
    let P := Classical.choice (exists_pulse S h.1 (err n) h.2 (err_pos n))
    ⟨P.r / 4, by have := P.rpos; positivity⟩

/-- The time scale `h_n`. -/
def h (n : ℕ) : ℝ := (hscale S n).1

/-- The data selected at step `n`. -/
def data (n : ℕ) : Pulse S (h S n) (err n) :=
  Classical.choice (exists_pulse S (h S n) (err n) (hscale S n).2 (err_pos n))

lemma h_pos (n : ℕ) : 0 < h S n := (hscale S n).2
lemma r_le_h (n : ℕ) : (data S n).r ≤ h S n := (data S n).rle
lemma h_succ (n : ℕ) : h S (n + 1) = (data S n).r / 4 := rfl

lemma h_le_quarter (n : ℕ) : h S n ≤ 1 / 4 := by
  induction n with
  | zero => rw [show h S 0 = 1 / 4 from rfl]
  | succ n ih => rw [h_succ]; have := r_le_h S n; linarith

lemma h_tendsto : Tendsto (h S) atTop (𝓝 0) := by
  have hb : ∀ n, h S n ≤ (1 / 4 : ℝ) ^ n := by
    intro n
    induction n with
    | zero => rw [show h S 0 = 1 / 4 from rfl]; norm_num
    | succ n ih => rw [pow_succ, h_succ]; have := r_le_h S n; linarith
  exact squeeze_zero (fun n => (h_pos S n).le) hb
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))

/-- The state `x_n = Φ_{h_n} u_n`. -/
def x (n : ℕ) : X := S.Φ (h S n) (data S n).u

/-! ### Step 3: packing the pulses into one bounded operator `ℓ^∞ → X` -/

/-- The `n`-th pulse is played on `window n = [start n, start n + h n)`, where
`start n = 1 - r n - h n`. These windows are pairwise disjoint subsets of `[0, 1)`. -/
def start (n : ℕ) : ℝ := 1 - (data S n).r - h S n

def window (n : ℕ) : Set ℝ := Set.Ico (start S n) (start S n + h S n)

def block (n : ℕ) (t : ℝ) : U := (data S n).f (t - start S n)

lemma finish_le_next (n : ℕ) : start S n + h S n ≤ start S (n + 1) := by
  have h1 := r_le_h S (n + 1)
  have h2 := h_succ S n
  have h3 := (data S n).rpos.le
  simp only [start]
  linarith

lemma start_mono : Monotone (start S) := by
  refine monotone_nat_of_le_succ fun n => ?_
  have h1 := finish_le_next S n
  have h2 := (h_pos S n).le
  linarith

lemma window_unique {i j : ℕ} {t : ℝ} (hi : t ∈ window S i) (hj : t ∈ window S j) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · have := start_mono S (Nat.succ_le_of_lt h)
    simp only [window, Set.mem_Ico] at hi hj
    linarith [hi.2, hj.1, finish_le_next S i]
  · exact h
  · have := start_mono S (Nat.succ_le_of_lt h)
    simp only [window, Set.mem_Ico] at hi hj
    linarith [hi.1, hj.2, finish_le_next S j]

lemma block_bound (n : ℕ) (t : ℝ) : ‖block S n t‖ ≤ 1 := (data S n).bound _

lemma block_off (n : ℕ) {t : ℝ} (ht : t ∉ window S n) : block S n t = 0 := by
  apply (data S n).off
  by_cases hs : t < start S n
  · exact Or.inl (by linarith)
  · refine Or.inr ?_
    by_contra hh
    exact ht ⟨not_lt.1 hs, by simp only [window] at *; linarith⟩

/-- The packed control `u^α` (raw function): on `window n` it is `α_n` times the `n`-th
pulse, and it vanishes outside the windows. -/
def packRaw (a : Phillips.Linfty 𝕜) : ℝ → U := by
  classical
  exact fun t => if ht : ∃ n, t ∈ window S n then
    a (Classical.choose ht) • block S (Classical.choose ht) t else 0

lemma packRaw_on (a : Phillips.Linfty 𝕜) {n : ℕ} {t : ℝ}
    (ht : t ∈ window S n) : packRaw S a t = a n • block S n t := by
  classical
  have hex : ∃ j, t ∈ window S j := ⟨n, ht⟩
  rw [packRaw, dite_eq_left hex, window_unique S (Classical.choose_spec hex) ht]

lemma packRaw_off (a : Phillips.Linfty 𝕜) {t : ℝ} (ht : ¬ ∃ n, t ∈ window S n) :
    packRaw S a t = 0 := by
  classical
  simp [packRaw, ht]

lemma packRaw_bound (a : Phillips.Linfty 𝕜) (t : ℝ) : ‖packRaw S a t‖ ≤ ‖a‖ := by
  classical
  by_cases ht : ∃ n, t ∈ window S n
  · obtain ⟨n, hn⟩ := ht
    rw [packRaw_on S a hn, norm_smul]
    calc ‖a n‖ * ‖block S n t‖ ≤ ‖a n‖ * 1 := by gcongr; exact block_bound S n t
      _ ≤ ‖a‖ := by simpa using (BoundedContinuousFunction.norm_le (norm_nonneg a)).1 le_rfl n
  · rw [packRaw_off S a ht, norm_zero]
    exact norm_nonneg _

lemma packRaw_measurable (a : Phillips.Linfty 𝕜) : StronglyMeasurable (packRaw S a) := by
  classical
  have hpartial : ∀ N : ℕ, StronglyMeasurable (fun t => ∑ n ∈ Finset.range N, a n • block S n t) :=
    fun N => Finset.stronglyMeasurable_fun_sum _ fun n _ => ((data S n).meas.comp_measurable
      (measurable_id.sub_const _)).const_smul (a n)
  refine stronglyMeasurable_of_tendsto atTop
    (f := fun N t => ∑ n ∈ Finset.range N, a n • block S n t) hpartial ?_
  apply tendsto_pi_nhds.2
  intro t
  have hev : (fun N => ∑ n ∈ Finset.range N, a n • block S n t) =ᶠ[atTop] fun _ => packRaw S a t := by
    by_cases ht : ∃ n, t ∈ window S n
    · obtain ⟨n, hn⟩ := ht
      filter_upwards [eventually_ge_atTop (n + 1)] with N hN
      rw [packRaw_on S a hn]
      refine Finset.sum_eq_single n (fun j _ hjn => ?_) fun hnN => absurd (Finset.mem_range.2 (by omega)) hnN
      rw [block_off S j fun hj => hjn (window_unique S hj hn), smul_zero]
    · filter_upwards with N
      rw [packRaw_off S a ht]
      exact Finset.sum_eq_zero fun n _ => by
        rw [block_off S n fun hn => ht ⟨n, hn⟩, smul_zero]
  exact tendsto_const_nhds.congr' hev.symm

lemma packRaw_memLp (a : Phillips.Linfty 𝕜) : MemLp (packRaw S a) ∞ muPlus :=
  memLp_top_of_bound (packRaw_measurable S a).aestronglyMeasurable _ (ae_of_all _ (packRaw_bound S a))

/-- The packed control `u^α ∈ L^∞(ℝ₊; U)`. -/
def packedInput (a : Phillips.Linfty 𝕜) : L∞ := (packRaw_memLp S a).toLp (packRaw S a)

lemma packedInput_ae (a : Phillips.Linfty 𝕜) : ⇑(packedInput S a) =ᵐ[muPlus] packRaw S a :=
  (packRaw_memLp S a).coeFn_toLp

/-- The contraction `α ↦ u^α` from `ℓ^∞` to `L^∞(ℝ₊; U)`. -/
def packing : Phillips.Linfty 𝕜 →L[𝕜] L∞ :=
  LinearMap.mkContinuous
    { toFun := packedInput S
      map_add' := fun a b => by
        have h : packRaw S (a + b) =ᵐ[muPlus] packRaw S a + packRaw S b := by
          filter_upwards with t
          show packRaw S (a + b) t = packRaw S a t + packRaw S b t
          classical
          by_cases ht : ∃ n, t ∈ window S n
          · obtain ⟨n, hn⟩ := ht
            rw [packRaw_on S (a + b) hn, packRaw_on S a hn, packRaw_on S b hn]
            simp only [BoundedContinuousFunction.add_apply, add_smul]
          · rw [packRaw_off S (a + b) ht, packRaw_off S a ht, packRaw_off S b ht, add_zero]
        simp only [packedInput]
        rw [← MemLp.toLp_add]
        exact MemLp.toLp_congr _ _ h
      map_smul' := fun c a => by
        have h : packRaw S (c • a) =ᵐ[muPlus] c • packRaw S a := by
          filter_upwards with t
          show packRaw S (c • a) t = c • packRaw S a t
          classical
          by_cases ht : ∃ n, t ∈ window S n
          · obtain ⟨n, hn⟩ := ht
            rw [packRaw_on S (c • a) hn, packRaw_on S a hn]
            simp only [BoundedContinuousFunction.smul_apply, smul_eq_mul, smul_smul]
          · rw [packRaw_off S (c • a) ht, packRaw_off S a ht, smul_zero]
        simp only [packedInput, RingHom.id_apply]
        rw [← MemLp.toLp_const_smul c]
        exact MemLp.toLp_congr _ _ h }
    1 fun a => by
      show ‖(packRaw_memLp S a).toLp (packRaw S a)‖ ≤ 1 * ‖a‖
      rw [one_mul]
      exact norm_toLp_le (packRaw_memLp S a) (norm_nonneg a) (packRaw_bound S a)

lemma packing_ae (a : Phillips.Linfty 𝕜) : ⇑(packing S a) =ᵐ[muPlus] packRaw S a :=
  packedInput_ae S a

lemma packRaw_e (n : ℕ) (t : ℝ) : packRaw S (Phillips.e n) t = block S n t := by
  classical
  by_cases hn : t ∈ window S n
  · rw [packRaw_on S _ hn]; simp
  · rw [block_off S n hn]
    by_cases ht : ∃ j, t ∈ window S j
    · obtain ⟨j, hj⟩ := ht
      rw [packRaw_on S _ hj]
      have hjn : j ≠ n := fun heq => hn (heq ▸ hj)
      simp [Phillips.e_apply, hjn, block_off S n hn]
    · exact packRaw_off S _ ht

/-- The operator `S : ℓ^∞ → X`, `S α = Φ_1 u^α`. -/
def packedOperator : Phillips.Linfty 𝕜 →L[𝕜] X := (S.Φ 1).comp (packing S)

/-- `S e_n = T_{r_n} x_n`, by `delay` and then `free`. -/
lemma packedOperator_e (n : ℕ) : packedOperator S (Phillips.e n) = S.T (data S n).r (x S n) := by
  have hraw : packRaw S (Phillips.e n) = concat (start S n) (fun _ => (0 : U)) (data S n).f := by
    funext t
    rw [packRaw_e]
    by_cases ht : t < start S n
    · rw [concat, if_pos ht, block]
      exact (data S n).off _ (Or.inl (by linarith))
    · simp only [concat, if_neg ht, block]
  have hw : ⇑(packing S (Phillips.e n)) =ᵐ[muPlus]
      concat (start S n) ⇑(0 : L∞) ⇑(data S n).u :=
    (packing_ae S _).trans ((Filter.EventuallyEq.of_eq hraw).trans
      (concat_congr (start S n) (Lp.coeFn_zero U ∞ muPlus) (data S n).coe).symm)
  have hnn : 0 ≤ start S n := by
    have h1 := r_le_h S n; have h2 := h_le_quarter S n; simp only [start]; linarith
  have hsum : start S n + (h S n + (data S n).r) = 1 := by simp only [start]; ring
  change S.Φ 1 (packing S (Phillips.e n)) = _
  rw [← hsum, S.delay (start S n) (h S n + (data S n).r) hnn
    (add_pos (h_pos S n) (data S n).rpos).le (data S n).u _ hw]
  have hfree : ⇑(data S n).u =ᵐ[muPlus] concat (h S n) ⇑(data S n).u ⇑(0 : L∞) := by
    have hraw2 : (data S n).f = concat (h S n) (data S n).f (fun _ => (0 : U)) :=
      funext fun t => by
        by_cases ht : t < h S n
        · simp [concat, ht]
        · simp [concat, ht, (data S n).off t (Or.inr (not_lt.1 ht))]
    exact (data S n).coe.trans ((Filter.EventuallyEq.of_eq hraw2).trans
      (concat_congr (h S n) (data S n).coe (Lp.coeFn_zero U ∞ muPlus)).symm)
  simpa [x] using S.composition (h S n) (data S n).r (h_pos S n).le (data S n).rpos.le
    (data S n).u 0 (data S n).u hfree

lemma packedOperator_close (n : ℕ) : ‖packedOperator S (Phillips.e n) - x S n‖ ≤ err n := by
  rw [packedOperator_e]
  exact (data S n).frozen

/-! ### The limit `ℓ` of `κ(t)` as `t → 0⁺` -/

def normRange : Set ℝ := (fun t : ℝ => ‖S.Φ t‖) '' Set.Ioi 0

lemma normRange_nonempty : (normRange S).Nonempty := ⟨‖S.Φ 1‖, 1, one_pos, rfl⟩

lemma normRange_bddBelow : BddBelow (normRange S) :=
  ⟨0, by rintro _ ⟨t, _, rfl⟩; exact norm_nonneg _⟩

/-- `ℓ = inf_{t > 0} κ(t)`. -/
def ell : ℝ := sInf (normRange S)

lemma ell_nonneg : 0 ≤ ell S := by
  apply le_csInf (normRange_nonempty S)
  rintro y ⟨t, _, rfl⟩
  exact norm_nonneg _

lemma ell_le (t : ℝ) (ht : 0 < t) : ell S ≤ ‖S.Φ t‖ :=
  csInf_le (normRange_bddBelow S) ⟨t, ht, rfl⟩

lemma exists_norm_lt (ε : ℝ) (hε : 0 < ε) : ∃ t : ℝ, 0 < t ∧ ‖S.Φ t‖ < ell S + ε := by
  by_contra hn
  have hbad : ell S + ε ≤ ell S := by
    refine le_csInf (normRange_nonempty S) ?_
    rintro y ⟨t, ht, rfl⟩
    exact le_of_not_gt fun hlt => hn ⟨t, ht, hlt⟩
  linarith

/-- Monotonicity identifies the norm limit along every positive null sequence. -/
lemma norm_Phi_tendsto (t : ℕ → ℝ) (htpos : ∀ n, 0 < t n) (ht : Tendsto t atTop (𝓝 0)) :
    Tendsto (fun n => ‖S.Φ (t n)‖) atTop (𝓝 (ell S)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨τ, hτ, hτnorm⟩ := exists_norm_lt S ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 ht τ hτ
  refine ⟨N, fun n hn => ?_⟩
  have htn : t n < τ := by simpa [Real.dist_eq, sub_zero, abs_of_pos (htpos n)] using hN n hn
  have h1 := ell_le S (t n) (htpos n)
  have h2 := norm_Phi_mono S (htpos n).le htn.le
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.2 h1)]
  linarith

/-- First half of `eq:goal`: `‖x_n‖ → ℓ`. -/
lemma x_norm_tendsto : Tendsto (fun n => ‖x S n‖) atTop (𝓝 (ell S)) := by
  have h1 := norm_Phi_tendsto S (h S) (h_pos S) (h_tendsto S)
  have h2 : Tendsto (fun n => ‖S.Φ (h S n)‖ - err n) atTop (𝓝 (ell S)) := by
    simpa using h1.sub err_tendsto
  refine h2.squeeze h1 (fun n => (data S n).near) fun n => ?_
  exact ((S.Φ (h S n)).le_opNorm _).trans
    (by simpa using mul_le_of_le_one_right (norm_nonneg (S.Φ (h S n))) (data S n).norm)

/-! ### Step 4: conclusion with Lemma 2.3 -/

/-- Second half of `eq:goal`: `‖T_{h_n} x_n - x_n‖ → 0`, by Lemma 2.3 applied to the
packed operator and the frozen states. -/
lemma x_moves_tendsto [CompleteSpace X] :
    Tendsto (fun n => ‖S.T (h S n) (x S n) - x S n‖) atTop (𝓝 0) := by
  -- Banach–Steinhaus: the norms `‖T (h n)‖` are bounded
  obtain ⟨K, hK⟩ : ∃ K, ∀ n, ‖S.T (h S n)‖ ≤ K := by
    have hbdd : ∀ z : X, ∃ C, ∀ n, ‖S.T (h S n) z‖ ≤ C := by
      intro z
      have hz : Tendsto (fun n => S.T (h S n) z) atTop (𝓝 z) :=
        (S.T_cont z).comp (tendsto_nhdsWithin_iff.2
          ⟨h_tendsto S, Filter.Eventually.of_forall fun n => (h_pos S n).le⟩)
      obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 (Metric.isBounded_range_of_tendsto _ hz)
      exact ⟨C, fun n => hC _ (Set.mem_range_self n)⟩
    exact banach_steinhaus hbdd
  set A : ℕ → X →L[𝕜] X := fun n => S.T (h S n) - ContinuousLinearMap.id 𝕜 X with hA
  have hAb : ∀ n, ‖A n‖ ≤ K + 1 := fun n => by
    simpa [hA] using (norm_sub_le (S.T (h S n)) (ContinuousLinearMap.id 𝕜 X)).trans
      (by linarith [hK n, ContinuousLinearMap.norm_id_le (𝕜 := 𝕜) (E := X)])
  have hP := Phillips.uniform (packedOperator S) S.T S.T_cont (h S)
    (fun n => (h_pos S n).le) (h_tendsto S)
  have herr : ∀ n, ‖S.T (h S n) (x S n) - x S n‖ ≤ ‖A n (packedOperator S (Phillips.e n))‖ +
      (K + 1) * err n := by
    intro n
    have h1 : ‖x S n - packedOperator S (Phillips.e n)‖ ≤ err n := by
      rw [norm_sub_rev]; exact packedOperator_close S n
    have h2 : S.T (h S n) (x S n) - x S n =
        A n (packedOperator S (Phillips.e n)) + A n (x S n - packedOperator S (Phillips.e n)) := by
      simp only [hA, sub_apply, ContinuousLinearMap.id_apply, map_sub]
      abel
    rw [h2]
    refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
    calc ‖A n (x S n - packedOperator S (Phillips.e n))‖
        ≤ ‖A n‖ * ‖x S n - packedOperator S (Phillips.e n)‖ := (A n).le_opNorm _
      _ ≤ (K + 1) * err n := by
          nlinarith [hAb n, h1, norm_nonneg (A n), norm_nonneg (x S n - packedOperator S (Phillips.e n)),
            err_pos n]
  refine squeeze_zero (fun n => norm_nonneg _) herr ?_
  have := hP.add (err_tendsto.const_mul (K + 1))
  simpa only [hA, mul_zero, add_zero, sub_apply, ContinuousLinearMap.id_apply] using this

end ZeroClassProof

open ZeroClassProof

/-- **Theorem 1.5**. Let `X`, `U` be real or complex Banach spaces and `S = (𝕋, Φ)` an
abstract linear control system with `p = ∞`. Then `S` is of the zero-class:
`‖Φ t‖ → 0` as `t → 0⁺`.

Proof: by Steps 2–4, `‖x_n‖ → ℓ` and `‖T_{h_n} x_n - x_n‖ → 0`; passing to the limit in
the doubling inequality of Step 1 gives `2ℓ ≤ ℓ`, hence `ℓ = 0`. -/
theorem zero_class [CompleteSpace X] [CompleteSpace U] (S : ALCS 𝕜 X U) : S.IsZeroClass := by
  have hx := x_norm_tendsto S
  have hm := x_moves_tendsto S
  have htwo : Tendsto (fun n => ‖S.Φ (2 * h S n)‖) atTop (𝓝 (ell S)) :=
    norm_Phi_tendsto S (fun n => 2 * h S n) (fun n => by have := h_pos S n; positivity)
      (by simpa only [mul_zero] using (h_tendsto S).const_mul 2)
  have hlimit : 2 * ell S ≤ ell S := by
    have := le_of_tendsto_of_tendsto (hx.const_mul 2) (htwo.add hm)
      (Filter.Eventually.of_forall fun n => doubling S (h_pos S n).le (data S n).u (data S n).norm)
    simpa using this
  have hell : ell S = 0 := by have := ell_nonneg S; linarith
  rw [IsZeroClass, Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨τ, hτ, hτnorm⟩ := exists_norm_lt S ε hε
  rw [hell, zero_add] at hτnorm
  refine ⟨τ, hτ, fun t ht hdist => ?_⟩
  have htτ : t < τ := by simpa [Real.dist_eq, sub_zero, abs_of_nonneg ht] using hdist
  simpa using lt_of_le_of_lt (norm_Phi_mono S ht htτ.le) hτnorm

end ALCS

end
