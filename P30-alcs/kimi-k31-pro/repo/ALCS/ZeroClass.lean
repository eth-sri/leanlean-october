module

public import ALCS.Definitions
public import ALCS.Background.Phillips

@[expose] public section

/-!
# Every `L^∞` system is zero-class (Theorem 1.5)

**Theorem 1.5** (`thm:p-infty-zero-class`). Let `X`, `U` be Banach spaces and `(𝕋, Φ)`
an abstract linear control system with `p = ∞`. Then the system is of the zero-class,
i.e. `‖Φ_t‖ → 0` as `t → 0`.

The final statement is `ALCS.zero_class`, at the end of this file. The auxiliary
declarations live in the namespace `ALCS.ZeroClassProof` and follow § 2.3 of the paper:

* `ell` is the limit `ℓ = lim_{t → 0⁺} κ(t) = inf_{t > 0} κ(t)` (`eq:ell`), and
  `norm_Phi_tendsto` identifies it as the limit along any positive null sequence.
* Step 1, `doubling`: the doubling inequality `eq:doubling`,
  `2 ‖Φ_h u‖ ≤ κ(2h) + ‖(T_h - Id) Φ_h u‖` for `‖u‖ ≤ 1`.
* Step 2, `data`, `h`, `x`: nearly extremal pulses `u_n` on rapidly decreasing time
  scales `h_n`, with states `x_n = Φ_{h_n} u_n` (`eq:xn-extremal`, `eq:hn-fast`).
* Step 3, `packing`, `packedOperator`: the pulses are packed into one bounded operator
  `S : ℓ^∞ → X`, and `packedOperator_close` is `eq:Sen-xn`.
* Step 4, `x_moves_tendsto`: Lemma 2.3 (`Phillips.uniform`) gives
  `‖(T_{h_n} - Id) x_n‖ → 0`, which is the second half of `eq:goal`.

## Difference with the paper in Step 3

The paper plays the pulses one after the other on consecutive intervals
`[s_n, s_{n+1})` and evaluates at the accumulated time `H = Σ h_k`. Here each pulse
gets its own *free-evolution time* `r_n ∈ (0, h_n]`, chosen in Step 2 so that
`‖T_{r_n} x_n - x_n‖ ≤ 2^{-n}`, and the `n`-th pulse is played on
`[1 - r_n - h_n, 1 - r_n)`, with zero input in the gaps; the operator is evaluated at
time `1`. Then `S e_n = T_{r_n} x_n` exactly. This changes the bookkeeping, not the
argument. The scalar field is `ℝ` or `ℂ` (`RCLike 𝕜`), as required by Phillips' lemma.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

section Endpoint

open scoped BigOperators

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {U : Type*} [NormedAddCommGroup U] [NormedSpace 𝕜 U]

namespace ALCS
namespace ZeroClassProof

/-! ### Step 1: the doubling inequality -/

variable (S : ALCS 𝕜 X U ∞)

/-! ### Step 2: nearly extremal pulses on rapidly decreasing time scales -/

/-- A *pulse* of length `h`: a control of norm at most one, given by an actual
(everywhere defined) representative vanishing outside `[0, h)`. -/
structure Pulse (U : Type*) [NormedAddCommGroup U] (h : ℝ) where
  /-- the representative -/
  f : ℝ → U
  measurable : StronglyMeasurable f
  bound : ∀ t, ‖f t‖ ≤ 1
  off : ∀ t, t < 0 ∨ h ≤ t → f t = 0

namespace Pulse

variable {h : ℝ} (P : Pulse U h)

/-- The pulse, as an element of `L^∞(ℝ₊; U)`. -/
def input : Lp U ∞ muPlus :=
  (memLp_of_bound P.measurable P.bound).toLp P.f

lemma coe_input : ⇑P.input =ᵐ[muPlus] P.f :=
  (memLp_of_bound P.measurable P.bound).coeFn_toLp

lemma norm_input : ‖P.input‖ ≤ 1 :=
  norm_toLp_le _ (by norm_num) P.bound

end Pulse

/-- A nearly extremal input can be chosen to be a pulse (by causality `eq:causality`,
truncating it at time `h` does not change `Φ_h u`). -/
lemma exists_pulse (h : ℝ) (hh : 0 ≤ h) (ε : ℝ) (hε : 0 < ε) :
    ∃ P : Pulse U h, ‖S.Φ h‖ - ε ≤ ‖S.Φ h P.input‖ := by
  obtain ⟨u, hu, hnear⟩ := (S.Φ h).exists_lt_apply_of_lt_opNorm
    (r := ‖S.Φ h‖ - ε) (by linarith)
  replace hu := hu.le
  replace hnear := hnear.le
  obtain ⟨g, hg, hgb, hug⟩ := exists_bounded_rep u (by norm_num) hu
  let f := (Set.Ico 0 h).indicator g
  have hf : StronglyMeasurable f := hg.indicator measurableSet_Ico
  have hb : ∀ t, ‖f t‖ ≤ 1 := fun t => (norm_indicator_le_norm_self g t).trans (hgb t)
  have hoff : ∀ t, t < 0 ∨ h ≤ t → f t = 0 := fun t ht =>
    Set.indicator_of_notMem (by simpa only [Set.mem_Ico, not_and_or, not_lt, not_le] using ht) g
  let P : Pulse U h := ⟨f, hf, hb, hoff⟩
  have hraw : f =ᵐ[muPlus] concat h g (fun _ => (0 : U)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    have ht0 : 0 ≤ t := ht
    by_cases hth : t < h
    · simp [f, concat, hth, Set.mem_Ico, ht0]
    · simp [f, concat, hth, Set.mem_Ico]
  have hcat : ⇑P.input =ᵐ[muPlus] concat h ⇑u ⇑(0 : Lp U ∞ muPlus) :=
    P.coe_input.trans (hraw.trans (concat_congr h hug (Lp.coeFn_zero U ∞ muPlus)).symm)
  refine ⟨P, ?_⟩
  rwa [S.causality h hh u 0 P.input hcat]

/-- The accuracy `2^{-n}` of the `n`-th selection. -/
def err (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n

lemma err_pos (n : ℕ) : 0 < err n := by
  unfold err
  positivity

lemma err_tendsto : Tendsto err atTop (𝓝 0) := by
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- The data selected at step `n` of Step 2: a nearly extremal pulse of length `h`
(`eq:xn-extremal`), and a free-evolution time `r ∈ (0, h]` during which its state is
essentially frozen by the semigroup (the analogue of `eq:hn-fast`). -/
structure FrozenPulse (S : ALCS 𝕜 X U ∞) (n : ℕ) (h : ℝ) where
  pulse : Pulse U h
  near : ‖S.Φ h‖ - err n ≤ ‖S.Φ h pulse.input‖
  /-- the free-evolution time -/
  r : ℝ
  r_pos : 0 < r
  r_le : r ≤ h
  close : ‖S.T r (S.Φ h pulse.input) - S.Φ h pulse.input‖ ≤ err n

/-- Classical choice is used only to choose actual witnesses to proved existences. -/
def choosePulse (n : ℕ) (h : ℝ) (hh : 0 < h) : FrozenPulse S n h :=
  Classical.choice (by
    obtain ⟨P, hP⟩ := exists_pulse S h hh.le (err n) (err_pos n)
    obtain ⟨δ, hδ, hc⟩ := Metric.tendsto_nhdsWithin_nhds.1
      (S.T_cont (S.Φ h P.input)) (err n) (err_pos n)
    let r := min h (δ / 2)
    have hr : 0 < r := lt_min hh (by positivity)
    have hrh : r ≤ h := min_le_left _ _
    have hrδ : r < δ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    refine ⟨⟨P, hP, r, hr, hrh, ?_⟩⟩
    simpa only [dist_eq_norm] using (hc hr.le
      (show dist r 0 < δ by simpa [Real.dist_eq, abs_of_pos hr] using hrδ)).le)

/-- The time scales, defined recursively: `h 0 = 1/4` and `h (n + 1) = r n / 4`, so that
the next pulse fits inside the free-evolution interval of the previous one. -/
def positiveTimes : ℕ → {h : ℝ // 0 < h} :=
  Nat.rec ⟨1 / 4, by norm_num⟩
    (fun n h =>
      let P := choosePulse S n h.1 h.2
      ⟨P.r / 4, div_pos P.r_pos (by norm_num)⟩)

/-- The time scale `h_n`. -/
def h (n : ℕ) : ℝ := (positiveTimes S n).1

/-- The pulse `u_n` and the free-evolution time `r_n` selected at step `n`. -/
def data (n : ℕ) : FrozenPulse S n (h S n) :=
  choosePulse S n (h S n) (positiveTimes S n).2

/-- The free-evolution time `r_n ∈ (0, h_n]`. -/
def r (n : ℕ) : ℝ := (data S n).r

/-- The state `x_n = Φ_{h_n} u_n`. -/
def x (n : ℕ) : X := S.Φ (h S n) (data S n).pulse.input

lemma h_pos (n : ℕ) : 0 < h S n := (positiveTimes S n).2
lemma r_pos (n : ℕ) : 0 < r S n := (data S n).r_pos
lemma r_le_h (n : ℕ) : r S n ≤ h S n := (data S n).r_le
lemma h_succ (n : ℕ) : h S (n + 1) = r S n / 4 := rfl

lemma h_geometric (n : ℕ) : h S n ≤ err n / 4 := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    dsimp [err] at ih ⊢
    rw [pow_succ]
    linarith [h_succ S n, r_le_h S n, (h_pos S n).le]

lemma h_tendsto : Tendsto (h S) atTop (𝓝 0) :=
  squeeze_zero (fun n => (h_pos S n).le) (h_geometric S) (by simpa using err_tendsto.div_const 4)

/-! ### Step 3: packing the pulses into one bounded operator `ℓ^∞ → X` -/

/-- The `n`-th pulse is played on `window n = [start n, start n + h n)`, where
`start n = 1 - r n - h n`. These windows are pairwise disjoint subsets of `[0, 1)`. -/
def start (n : ℕ) : ℝ := 1 - r S n - h S n

/-- The interval on which the `n`-th pulse is played. -/
def window (n : ℕ) : Set ℝ := Set.Ico (start S n) (start S n + h S n)

/-- The `n`-th pulse, delayed so that it is played on `window n`. -/
def block (n : ℕ) (t : ℝ) : U := (data S n).pulse.f (t - start S n)

lemma finish_le_next (n : ℕ) : start S n + h S n ≤ start S (n + 1) := by
  dsimp [start]
  linarith [r_le_h S (n + 1), h_succ S n, (r_pos S n).le]

lemma finish_le_start {i j : ℕ} (hij : i < j) :
    start S i + h S i ≤ start S j :=
  (finish_le_next S i).trans ((monotone_nat_of_le_succ fun n =>
    (le_add_of_nonneg_right (h_pos S n).le).trans (finish_le_next S n))
      (Nat.succ_le_of_lt hij))

lemma window_unique {i j : ℕ} {t : ℝ}
    (hi : t ∈ window S i) (hj : t ∈ window S j) : i = j := by
  rcases lt_trichotomy i j with hij | hij | hji
  · linarith [finish_le_start S hij, hi.2, hj.1]
  · exact hij
  · linarith [finish_le_start S hji, hj.2, hi.1]

lemma block_off (n : ℕ) {t : ℝ} (ht : t ∉ window S n) : block S n t = 0 := by
  apply (data S n).pulse.off
  by_cases hs : t < start S n
  · left
    linarith
  · right
    by_contra hh
    exact ht ⟨not_lt.1 hs, by linarith⟩

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
  simp only [packRaw, dite_eq_left hex, window_unique S (Classical.choose_spec hex) ht]

lemma packRaw_off (a : Phillips.Linfty 𝕜) {t : ℝ}
    (ht : ¬ ∃ n, t ∈ window S n) : packRaw S a t = 0 := by
  classical
  simp [packRaw, ht]

lemma packRaw_bound (a : Phillips.Linfty 𝕜) (t : ℝ) :
    ‖packRaw S a t‖ ≤ ‖a‖ := by
  classical
  by_cases ht : ∃ n, t ∈ window S n
  · obtain ⟨n, hn⟩ := ht
    rw [packRaw_on S a hn, norm_smul]
    calc
      ‖a n‖ * ‖block S n t‖ ≤ ‖a n‖ * 1 :=
        mul_le_mul_of_nonneg_left ((data S n).pulse.bound _) (norm_nonneg _)
      _ ≤ ‖a‖ := by simpa using a.norm_coe_le_norm n
  · simp [packRaw_off S a ht]

lemma packRaw_memLp (a : Phillips.Linfty 𝕜) : MemLp (packRaw S a) ∞ muPlus :=
  memLp_of_bound (by
    classical
    apply stronglyMeasurable_of_tendsto atTop
      (f := fun N t => ∑ n ∈ Finset.range N, a n • block S n t)
    · exact fun N => Finset.stronglyMeasurable_fun_sum (Finset.range N)
        (fun n _ => ((data S n).pulse.measurable.comp_measurable
          (measurable_id.sub_const _)).const_smul (a n))
    · apply tendsto_pi_nhds.2
      intro t
      apply tendsto_const_nhds.congr'
      apply Filter.EventuallyEq.symm
      by_cases ht : ∃ n, t ∈ window S n
      · obtain ⟨n, hn⟩ := ht
        filter_upwards [eventually_ge_atTop (n + 1)] with N hN
        rw [packRaw_on S a hn, Finset.sum_eq_single_of_mem n (Finset.mem_range.2 (by omega))
          (fun j _ hjn => by simp [block_off S j (fun hj => hjn (window_unique S hj hn))])]
      · filter_upwards [] with N
        rw [packRaw_off S a ht]
        exact Finset.sum_eq_zero fun n _ => by simp [block_off S n (fun hn => ht ⟨n, hn⟩)])
    (packRaw_bound S a)

/-- The packed control `u^α ∈ L^∞(ℝ₊; U)`. -/
def packedInput (a : Phillips.Linfty 𝕜) : Lp U ∞ muPlus :=
  (packRaw_memLp S a).toLp (packRaw S a)

lemma packedInput_ae (a : Phillips.Linfty 𝕜) :
    ⇑(packedInput S a) =ᵐ[muPlus] packRaw S a :=
  (packRaw_memLp S a).coeFn_toLp

/-- The contraction `α ↦ u^α` from `ℓ^∞` to `L^∞(ℝ₊; U)`. -/
def packing : Phillips.Linfty 𝕜 →L[𝕜] Lp U ∞ muPlus :=
  LinearMap.mkContinuous
    { toFun := packedInput S
      map_add' := by
        intro a b
        apply Lp.ext
        filter_upwards [packedInput_ae S (a + b), packedInput_ae S a,
          packedInput_ae S b, Lp.coeFn_add (packedInput S a) (packedInput S b)]
            with t hab ha hb hsum
        rw [hab, hsum]
        simp only [Pi.add_apply, ha, hb]
        classical
        by_cases ht : ∃ n, t ∈ window S n
        · obtain ⟨n, hn⟩ := ht
          rw [packRaw_on S (a + b) hn, packRaw_on S a hn, packRaw_on S b hn]
          simp only [BoundedContinuousFunction.add_apply, add_smul]
        · simp [packRaw_off, ht]
      map_smul' := by
        intro c a
        apply Lp.ext
        filter_upwards [packedInput_ae S (c • a), packedInput_ae S a,
          Lp.coeFn_smul c (packedInput S a)] with t hca ha hsmul
        rw [RingHom.id_apply, hca, hsmul]
        simp only [Pi.smul_apply, ha]
        classical
        by_cases ht : ∃ n, t ∈ window S n
        · obtain ⟨n, hn⟩ := ht
          rw [packRaw_on S (c • a) hn, packRaw_on S a hn]
          simp only [BoundedContinuousFunction.smul_apply, smul_eq_mul, smul_smul]
        · simp [packRaw_off, ht] }
    1 (fun a => by simpa [packedInput] using
      (norm_toLp_le (packRaw_memLp S a) (norm_nonneg _) (packRaw_bound S a)))

/-- The operator `S : ℓ^∞ → X`, `S α = Φ_1 u^α`. -/
def packedOperator : Phillips.Linfty 𝕜 →L[𝕜] X :=
  (S.Φ 1).comp (packing S)

/-- `S e_n = T_{r_n} x_n`: the `n`-th state, after it has evolved freely during the
time `r_n` (by `eq:delay` and then `eq:free`). -/
lemma packedOperator_e (n : ℕ) :
    packedOperator S (Phillips.e n) = S.T (r S n) (x S n) := by
  let P := (data S n).pulse
  have hraw : packRaw S (Phillips.e n) =
      concat (start S n) (fun _ => (0 : U)) P.f := by
    funext t
    rw [show packRaw S (Phillips.e n) t = block S n t from by
      classical
      by_cases ht : ∃ j, t ∈ window S j
      · obtain ⟨j, hj⟩ := ht
        rw [packRaw_on S _ hj]
        by_cases hjn : j = n
        · subst j
          simp
        · simp [Phillips.e_apply, hjn, block_off S n (fun hn => hjn (window_unique S hj hn))]
      · rw [packRaw_off S _ ht, block_off S n (fun hn => ht ⟨n, hn⟩)]]
    by_cases ht : t < start S n
    · simpa [concat, ht, block, P] using P.off _ (Or.inl (by linarith))
    · simp [concat, ht, block, P]
  have hw : ⇑(packing S (Phillips.e n)) =ᵐ[muPlus]
      concat (start S n) ⇑(0 : Lp U ∞ muPlus) ⇑P.input :=
    (packedInput_ae S _).trans
      ((Filter.EventuallyEq.of_eq hraw).trans
        (concat_congr (start S n) (Lp.coeFn_zero U ∞ muPlus) P.coe_input).symm)
  change S.Φ 1 (packing S (Phillips.e n)) = _
  rw [show (1 : ℝ) = start S n + (h S n + r S n) by dsimp [start]; ring,
    S.delay (start S n) (h S n + r S n) (by
      have he : err n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      dsimp [start]
      linarith [r_le_h S n, h_geometric S n])
      (add_nonneg (h_pos S n).le (r_pos S n).le) P.input _ hw,
    S.free (h S n) (r S n) (h_pos S n).le (r_pos S n).le P.input P.input (by
      have hraw : P.f = concat (h S n) P.f (fun _ => (0 : U)) := by
        funext t
        by_cases ht : t < h S n
        · simp [concat, ht]
        · simp [concat, ht, P.off t (Or.inr (not_lt.1 ht))]
      exact P.coe_input.trans ((Filter.EventuallyEq.of_eq hraw).trans
        (concat_congr (h S n) P.coe_input (Lp.coeFn_zero U ∞ muPlus)).symm))]
  rfl

/-! ### The limit `ℓ` of `κ(t)` as `t → 0⁺` (`eq:ell`) -/

/-- The possible input-map norms at strictly positive times. -/
def normRange : Set ℝ := (fun t : ℝ => ‖S.Φ t‖) '' Set.Ioi 0

/-- `ℓ = inf_{t > 0} κ(t)`, equation `eq:ell`. -/
def ell : ℝ := sInf (normRange S)

lemma exists_norm_lt (ε : ℝ) (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ ‖S.Φ t‖ < ell S + ε := by
  obtain ⟨_, ⟨t, ht, rfl⟩, h⟩ := exists_lt_of_csInf_lt
    (show (normRange S).Nonempty from ⟨‖S.Φ 1‖, 1, by norm_num, rfl⟩)
    (show ell S < ell S + ε by linarith)
  exact ⟨t, ht, h⟩

/-- Monotonicity identifies the norm limit along every positive null sequence. -/
lemma norm_Phi_tendsto (t : ℕ → ℝ) (htpos : ∀ n, 0 < t n)
    (ht : Tendsto t atTop (𝓝 0)) :
    Tendsto (fun n => ‖S.Φ (t n)‖) atTop (𝓝 (ell S)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨τ, hτ, hτnorm⟩ := exists_norm_lt S ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 ht τ hτ
  refine ⟨N, fun n hn => ?_⟩
  have htn : t n < τ := by
    simpa only [Real.dist_eq, sub_zero, abs_of_pos (htpos n)] using hN n hn
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.2
    (show ell S ≤ ‖S.Φ (t n)‖ from csInf_le (by
      refine ⟨0, ?_⟩
      rintro y ⟨t, _, rfl⟩
      exact norm_nonneg _) ⟨t n, htpos n, rfl⟩))]
  linarith [norm_Phi_mono S (htpos n).le htn.le]

/-- First half of `eq:goal`: `‖x_n‖ → ℓ`. -/
lemma x_norm_tendsto : Tendsto (fun n => ‖x S n‖) atTop (𝓝 (ell S)) := by
  have hk := norm_Phi_tendsto S (h S) (h_pos S) (h_tendsto S)
  have hl : Tendsto (fun n => ‖S.Φ (h S n)‖ - err n) atTop (𝓝 (ell S)) := by
    simpa using hk.sub err_tendsto
  exact hl.squeeze hk (fun n => (data S n).near) fun n => by
    simpa only [x, mul_one] using
      (S.Φ (h S n)).le_opNorm_of_le (data S n).pulse.norm_input

/-! ### Step 4: conclusion with Lemma 2.3 -/

/-- Second half of `eq:goal`: `‖T_{h_n} x_n - x_n‖ → 0`. By Lemma 2.3
(`Phillips.uniform`), `‖(T_{h_n} - Id) S e_n‖ → 0`, and `S e_n` is `2^{-n}`-close to `x_n`. -/
lemma x_moves_tendsto [CompleteSpace X] :
    Tendsto (fun n => ‖S.T (h S n) (x S n) - x S n‖) atTop (𝓝 0) := by
  let A : ℕ → X →L[𝕜] X := fun n => S.T (h S n) - ContinuousLinearMap.id 𝕜 X
  obtain ⟨M, hM⟩ := S.toC0Semigroup.exists_bound_of_tendsto_zero (h S)
    (fun n => (h_pos S n).le) (h_tendsto S)
  have hK (n : ℕ) : ‖A n‖ ≤ M + 1 :=
    (norm_sub_le _ _).trans (add_le_add (hM n) ContinuousLinearMap.norm_id_le)
  have hPhillips : Tendsto (fun n => ‖A n (packedOperator S (Phillips.e n))‖) atTop (𝓝 0) :=
    Phillips.uniform (packedOperator S) S.T S.T_cont (h S)
      (fun n => (h_pos S n).le) (h_tendsto S)
  have herror (n : ℕ) : ‖S.T (h S n) (x S n) - x S n‖ ≤
      ‖A n (packedOperator S (Phillips.e n))‖ + (M + 1) * err n := by
    let y := packedOperator S (Phillips.e n)
    have hxy : ‖x S n - y‖ ≤ err n := by
      dsimp [y]
      rw [norm_sub_rev, packedOperator_e]
      exact (data S n).close
    change ‖A n (x S n)‖ ≤ _
    rw [show x S n = y + (x S n - y) by abel, map_add]
    calc
      _ ≤ ‖A n y‖ + ‖A n (x S n - y)‖ := norm_add_le _ _
      _ ≤ ‖A n y‖ + (M + 1) * err n :=
        add_le_add le_rfl ((A n).le_of_opNorm_le_of_le (hK n) hxy)
  apply squeeze_zero (fun n => norm_nonneg _) herror
  simpa only [mul_zero, add_zero] using hPhillips.add (err_tendsto.const_mul (M + 1))

end ZeroClassProof

open ZeroClassProof

/-- **Theorem 1.5** (`thm:p-infty-zero-class`). Let `X`, `U` be real or complex Banach
spaces and `S = (𝕋, Φ)` an abstract linear control system with `p = ∞`. Then `S` is of
the zero-class: `‖Φ t‖ → 0` as `t → 0⁺`.

Proof: by Steps 2–4, `‖x_n‖ → ℓ` and `‖T_{h_n} x_n - x_n‖ → 0`; passing to the limit in
the doubling inequality of Step 1 gives `2ℓ ≤ ℓ`, hence `ℓ = 0`. -/
theorem zero_class [CompleteSpace X] [CompleteSpace U] (S : ALCS 𝕜 X U ∞) :
    S.IsZeroClass := by
  have htwo : Tendsto (fun n => ‖S.Φ (2 * h S n)‖) atTop (𝓝 (ell S)) :=
    norm_Phi_tendsto S (fun n => 2 * h S n)
      (fun n => mul_pos (by norm_num) (h_pos S n))
      (by simpa only [mul_zero] using (h_tendsto S).const_mul 2)
  have hlimit : 2 * ell S ≤ ell S := by
    simpa only [add_zero] using le_of_tendsto_of_tendsto
      ((x_norm_tendsto S).const_mul 2) (htwo.add (x_moves_tendsto S))
      (.of_forall fun n => by
        let P := (data S n).pulse
        obtain ⟨w, hw, hcat⟩ := exists_concat (h S n) P.input P.input (by norm_num)
          P.norm_input P.norm_input
        have hcomp := S.composition (h S n) (h S n) (h_pos S n).le (h_pos S n).le
          P.input P.input w hcat
        let y := S.Φ (h S n) P.input
        have hid : y + y = S.Φ (2 * h S n) w - (S.T (h S n) y - y) := by
          rw [show 2 * h S n = h S n + h S n by ring, hcomp]
          dsimp [y]
          abel
        calc
          2 * ‖x S n‖ = ‖y + y‖ := by
            dsimp [y, ZeroClassProof.x, P]
            rw [← two_smul 𝕜, norm_smul]
            norm_num
          _ ≤ ‖S.Φ (2 * h S n) w‖ + ‖S.T (h S n) y - y‖ := by
            rw [hid]
            exact norm_sub_le _ _
          _ ≤ ‖S.Φ (2 * h S n)‖ + ‖S.T (h S n) y - y‖ := add_le_add
            (by simpa using (S.Φ (2 * h S n)).le_opNorm_of_le hw) le_rfl)
  have hnonneg : 0 ≤ ell S := ge_of_tendsto (x_norm_tendsto S)
    (.of_forall fun n => norm_nonneg _)
  have hell : ell S = 0 := by linarith
  rw [IsZeroClass, Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨τ, hτ, hnormτ⟩ := exists_norm_lt S ε hε
  rw [hell, zero_add] at hnormτ
  refine ⟨τ, hτ, fun t ht hdist => ?_⟩
  have htτ : t < τ := by
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg ht] using hdist
  simpa using (norm_Phi_mono S ht htτ.le).trans_lt hnormτ

end ALCS

end Endpoint

end
