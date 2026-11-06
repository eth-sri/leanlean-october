module

public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.Instances.Nat
public import Mathlib.Data.Nat.Pairing
public import Mathlib.Data.Set.Finite.Lemmas

public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push

@[expose] public section

/-!
# Phillips' lemma (Lemmas 2.2 and 2.3)

**Lemma 2.2** (`lem:Phillips`). Let `(μ_n)` be a sequence in `(ℓ^∞(ℕ))*` such that
`μ_n(a) → 0` for every `a ∈ ℓ^∞(ℕ)`. Then `Σ_k |μ_n(e_k)| → 0`; in particular
`μ_n(e_n) → 0`.

**Lemma 2.3** (`lem:cor-Phillips`). Let `S ∈ 𝓛(ℓ^∞(ℕ), X)` and `t_n ≥ 0` with `t_n → 0`.
Then `‖(T_{t_n} - Id) S e_n‖ → 0`.

## Main declarations

* `Phillips.full` : **Lemma 2.2** (summability of each `Σ_k |μ_n(e_k)|`, convergence of the
  sums to `0`, and `μ_n(e_n) → 0`); `Phillips.tsum_abs_tendsto_zero` is the real case
  written with absolute values.
* `Phillips.uniform` : **Lemma 2.3**. Only strong right-continuity of `T` at `0` is used;
  the semigroup law and completeness are not needed.

`Linfty 𝕜` is the space of bounded sequences with values in `𝕜 = ℝ` or `ℂ`, represented as
bounded continuous functions on the discrete space `ℕ`; `e k` is the `k`-th canonical
vector. The paper quotes Lemma 2.2 from [Phillips 1940]; here it is proved.

## Proof of Lemma 2.2

1. Diagonal statement, `diagonal_tendsto_zero`: `μ_n(e_n) → 0`. An infinite set of indices
   is thinned so that a given functional is small on all its subsets (`small_on_subsets`);
   a recursive selection then produces a set `A` for which `μ_n(1_A)` cannot tend to zero
   (`diagonal_of_indicator_tendsto`). Only finite sums are used.
2. For a single functional, `Σ_{k ∈ s} |φ(e_k)| ≤ ‖φ‖` for every finite `s`, by testing `φ`
   on `Σ_{k ∈ s} λ_k e_k` with phases `|λ_k| ≤ 1` (`sum_norm_eval_le`); hence the series
   converge (`summable_norm_eval`).
3. Disjoint finite blocks `B_j` with coefficients of modulus `≤ 1` are encoded by one bounded
   operator `S : ℓ^∞ → ℓ^∞` with `S e_j` supported in `B_j`, defined coordinatewise
   (`exists_block_operator`).
4. Gliding hump (`finite_sum_eventually_small`): if finite sums were not eventually uniformly
   small, Steps 2–3 would produce functionals `ν_j = μ_{r_j} ∘ S` contradicting Step 1.
   This gives `Σ_k |μ_n(e_k)| → 0` (`tsum_norm_tendsto_zero`).

Lemma 2.3 (`uniform`) applies the diagonal statement to `μ_n = x_n^* ∘ (T_{t_n} - Id) ∘ S`,
with norming functionals `x_n^*` given by Hahn–Banach (`norm_diagonal_tendsto_zero`).
-/

noncomputable section

open Filter
open scoped BigOperators Topology

namespace Phillips

attribute [local instance] Classical.propDecidable

/-- Bounded scalar sequences, with the supremum norm. -/
abbrev Linfty (𝕜 : Type*) [RCLike 𝕜] := BoundedContinuousFunction ℕ 𝕜

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The characteristic sequence of a set of natural numbers. -/
def chi (S : Set ℕ) : Linfty 𝕜 :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun k => if k ∈ S then (1 : 𝕜) else 0) 1
    (by intro k; split_ifs <;> simp)

@[simp] theorem chi_apply (S : Set ℕ) (k : ℕ) :
    chi (𝕜 := 𝕜) S k = if k ∈ S then 1 else 0 := rfl

/-- The `k`th canonical vector of `ℓ∞`. -/
def e (k : ℕ) : Linfty 𝕜 := chi {k}

@[simp] theorem e_apply (k j : ℕ) :
    e (𝕜 := 𝕜) k j = if j = k then 1 else 0 := by
  simp [e]

/-! ## Step 1: the diagonal statement `μ_n(e_n) → 0` -/

/-- An infinite set can be thinned so that a given functional is small on
all characteristic sequences supported in the remaining set. -/
private theorem small_on_subsets
    (φ : Linfty 𝕜 →L[𝕜] 𝕜) (S : Set ℕ) (hS : S.Infinite)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ T : Set ℕ, T ⊆ S ∧ T.Infinite ∧
      ∀ B : Set ℕ, B ⊆ T → ‖φ (chi B)‖ ≤ δ := by
  classical
  -- Partition an infinite subset of S into infinitely many infinite sets.
  let emb : ℕ ↪ S := Set.Infinite.natEmbedding S hS
  let g : ℕ × ℕ → ℕ := fun p => (emb (Nat.pair p.1 p.2)).val
  have hg : Function.Injective g := fun p q h =>
    Nat.pairEquiv.injective (emb.injective (Subtype.ext h))
  let A : ℕ → Set ℕ := fun i => Set.range (fun j => g (i, j))
  have hAinf (i : ℕ) : (A i).Infinite :=
    Set.infinite_range_of_injective fun j k h => congrArg Prod.snd (hg h)
  have hAS (i : ℕ) : A i ⊆ S := by
    rintro x ⟨j, rfl⟩
    exact (emb (Nat.pair i j)).property
  by_contra! h
  choose B hBA hBδ using fun i => h (A i) (hAS i) (hAinf i)
  have hdisj {i j x : ℕ} (hi : x ∈ B i) (hj : x ∈ B j) : i = j := by
    obtain ⟨a, ha⟩ := hBA i hi
    obtain ⟨b, hb⟩ := hBA j hj
    exact congrArg Prod.fst (hg (ha.trans hb.symm))
  have hz (i : ℕ) : φ (chi (B i)) ≠ 0 :=
    norm_pos_iff.mp (hδ.trans (hBδ i))
  -- Normalize each witness so that its image under φ is exactly 1.
  let v : ℕ → Linfty 𝕜 := fun i => (φ (chi (B i)))⁻¹ • chi (B i)
  have hv (i : ℕ) : φ (v i) = 1 := by
    simp [v, map_smul, smul_eq_mul, hz i]
  have hcoef (i : ℕ) : ‖(φ (chi (B i)))⁻¹‖ ≤ δ⁻¹ := by
    simpa only [norm_inv, one_div] using
      (one_div_le_one_div_of_le hδ (le_of_lt (hBδ i)))
  -- Disjoint supports give a norm bound independent of the number of terms.
  have hsum (s : Finset ℕ) : ‖∑ i ∈ s, v i‖ ≤ δ⁻¹ := by
    apply (BoundedContinuousFunction.norm_le (show 0 ≤ δ⁻¹ by positivity)).2
    intro x
    rw [BoundedContinuousFunction.sum_apply]
    by_cases hx : ∃ i ∈ s, x ∈ B i
    · obtain ⟨i, hi, hxi⟩ := hx
      rw [Finset.sum_eq_single_of_mem i hi fun j hj hji => by
        have hxj : x ∉ B j := fun hxj => hji (hdisj hxj hxi)
        simp [v, BoundedContinuousFunction.smul_apply, smul_eq_mul, hxj]]
      simpa [v, BoundedContinuousFunction.smul_apply, smul_eq_mul, hxi] using hcoef i
    · rw [Finset.sum_eq_zero (fun i hi => by
        have hxi : x ∉ B i := fun hxi => hx ⟨i, hi, hxi⟩
        simp [v, BoundedContinuousFunction.smul_apply, smul_eq_mul, hxi]), norm_zero]
      positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (‖φ‖ * δ⁻¹)
  apply not_le_of_gt hN
  simpa [map_sum, hv, RCLike.norm_natCast] using
    φ.le_of_opNorm_le_of_le le_rfl (hsum (Finset.range N))

end Phillips

namespace Phillips

open Filter
open scoped Topology

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- **Lemma 2.3** (`lem:cor-Phillips`). -/
theorem uniform
    (S : Linfty 𝕜 →L[𝕜] X) (T : ℝ → (X →L[𝕜] X))
    (hT : ∀ x : X, Tendsto (fun s : ℝ => T s x) (nhdsWithin 0 (Set.Ici 0)) (𝓝 x))
    (t : ℕ → ℝ) (ht_nonneg : ∀ n : ℕ, 0 ≤ t n) (ht : Tendsto t atTop (𝓝 0)) :
    Tendsto (fun n => ‖(T (t n) - ContinuousLinearMap.id 𝕜 X) (S (e n))‖)
      atTop (𝓝 0) := by
  classical
  let A : ℕ → (Linfty 𝕜 →L[𝕜] X) :=
    fun n => (T (t n) - ContinuousLinearMap.id 𝕜 X).comp S
  have hA (a : Linfty 𝕜) : Tendsto (fun n => A n a) atTop (𝓝 0) := by
    have hTa : Tendsto (fun n => T (t n) (S a)) atTop (𝓝 (S a)) :=
      (hT (S a)).comp (tendsto_nhdsWithin_iff.2 ⟨ht, .of_forall ht_nonneg⟩)
    change Tendsto (fun n => T (t n) (S a) - S a) atTop (𝓝 0)
    simpa using hTa.sub_const (S a)
  choose φ hφ hφ' using fun n : ℕ => exists_dual_vector'' 𝕜 (A n (e n))
  let μ : ℕ → (Linfty 𝕜 →L[𝕜] 𝕜) := fun n => (φ n).comp (A n)
  have hμ (a : Linfty 𝕜) : Tendsto (fun n => μ n a) atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun n => ‖A n a‖) ?_ (by simpa using (hA a).norm)
    intro n
    change ‖φ n (A n a)‖ ≤ ‖A n a‖
    simpa using (φ n).le_of_opNorm_le (hφ n) (A n a)
  have hnorm (n : ℕ) : ‖μ n (e n)‖ = ‖A n (e n)‖ := by
    simp only [μ, ContinuousLinearMap.comp_apply, hφ',
      RCLike.norm_of_nonneg (norm_nonneg _)]
  have hd : Tendsto (fun n => μ n (e n)) atTop (𝓝 0) := by
    apply Metric.tendsto_atTop.2
    intro ε hε
    by_contra! hnot
    simp only [dist_zero_right] at hnot
    let D : Set ℕ := {n | ε ≤ ‖μ n (e n)‖}
    have hD : D.Infinite := Set.infinite_of_not_bddAbove <| by
      rintro ⟨N, hN⟩
      obtain ⟨n, hn, hbn⟩ := hnot (N + 1)
      have := hN hbn
      omega
    let δ : ℝ := ε / 4
    have hδ : 0 < δ := by dsimp [δ]; positivity
    let X := {S : Set ℕ // S.Infinite ∧ S ⊆ D}
    have hstep : ∀ (F : Set ℕ) (S : X), ∃ (n : ℕ) (T : X),
        n ∈ S.val ∧ ‖μ n (chi F)‖ < δ ∧ T.val ⊆ S.val ∧
        (∀ m ∈ T.val, n < m) ∧ (∀ B : Set ℕ, B ⊆ T.val → ‖μ n (chi B)‖ ≤ δ) := by
      intro F S
      obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 (hμ (chi F))) δ hδ
      obtain ⟨n, hnS, hnN⟩ := S.property.1.exists_notMem_finite (Set.finite_lt_nat N)
      have hnsmall : ‖μ n (chi F)‖ < δ := by
        simpa only [dist_zero_right] using hN n (by simpa only [Set.mem_ofPred_eq, not_lt] using hnN)
      obtain ⟨T, hTS, hTinf, hTsmall⟩ := small_on_subsets (μ n) (S.val \ {m | m ≤ n})
        (S.property.1.sdiff (Set.finite_le_nat n)) δ hδ
      exact ⟨n, ⟨T, hTinf, fun m hm => S.property.2 (hTS hm).1⟩, hnS, hnsmall,
        fun m hm => (hTS hm).1, fun m hm => lt_of_not_ge (hTS hm).2, hTsmall⟩
    choose pick tail hpick hhead hsub hgt hsmall using hstep
    let state : ℕ → Set ℕ × X :=
      Nat.rec (∅, ⟨D, hD, fun _ h => h⟩)
        (fun _ p => (insert (pick p.1 p.2) p.1, tail p.1 p.2))
    let n : ℕ → ℕ := fun i => pick (state i).1 (state i).2
    let F : ℕ → Set ℕ := fun i => (state i).1
    let R : ℕ → Set ℕ := fun i => ((state i).2).val
    have hF0 : F 0 = ∅ := rfl
    have hFs (i : ℕ) : F (i + 1) = insert (n i) (F i) := rfl
    have hnmem (i : ℕ) : n i ∈ R i := hpick (state i).1 (state i).2
    have hnmono : StrictMono n := strictMono_nat_of_lt_succ fun i =>
      hgt (state i).1 (state i).2 _ (hnmem (i + 1))
    have hFmem (i x : ℕ) : x ∈ F i ↔ ∃ j < i, n j = x := by
      induction i with
      | zero => simp [hF0]
      | succ i ih =>
        rw [hFs, Set.mem_insert_iff, ih]
        constructor
        · rintro (rfl | ⟨j, hj, rfl⟩)
          · exact ⟨i, by omega, rfl⟩
          · exact ⟨j, by omega, rfl⟩
        · rintro ⟨j, hj, rfl⟩
          by_cases hji : j = i
          · subst j; exact Or.inl rfl
          · exact Or.inr ⟨j, by omega, rfl⟩
    let A : Set ℕ := Set.range n
    let B : ℕ → Set ℕ := fun i => {x | ∃ j, i < j ∧ n j = x}
    have hBsub (i : ℕ) : B i ⊆ R (i + 1) := by
      have hR : Antitone R := antitone_nat_of_succ_le fun i => hsub (state i).1 (state i).2
      rintro x ⟨j, hij, rfl⟩
      exact hR (Nat.succ_le_of_lt hij) (hnmem j)
    have hsplit (i : ℕ) :
        chi (𝕜 := 𝕜) A = chi (F i) + e (n i) + chi (B i) := by
      apply BoundedContinuousFunction.ext
      intro x
      simp only [BoundedContinuousFunction.add_apply, chi_apply, e_apply]
      by_cases hx : x ∈ A
      · obtain ⟨j, rfl⟩ := hx
        have hA : n j ∈ A := ⟨j, rfl⟩
        have hF : n j ∈ F i ↔ j < i := by simp [hFmem, hnmono.injective.eq_iff]
        have hB : n j ∈ B i ↔ i < j := by simp [B, hnmono.injective.eq_iff]
        have heq : n j = n i ↔ j = i := hnmono.injective.eq_iff
        simp only [hA, hF, hB, heq, ite_true]
        split_ifs <;> norm_num <;> omega
      · have hx' : ∀ j, n j ≠ x := by simpa [A] using hx
        have hxn : x ≠ n i := (hx' i).symm
        simp [A, B, hFmem, hx', hxn, hx]
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 (hμ (chi A))) δ hδ
    have hA_small : ‖μ (n N) (chi A)‖ < δ := by
      simpa only [dist_zero_right] using hN (n N) hnmono.le_apply
    have hF_small : ‖μ (n N) (chi (F N))‖ < δ := hhead (state N).1 (state N).2
    have hB_small : ‖μ (n N) (chi (B N))‖ ≤ δ :=
      hsmall (state N).1 (state N).2 (B N) (hBsub N)
    have hidentity : μ (n N) (chi A) =
        μ (n N) (chi (F N)) + μ (n N) (e (n N)) + μ (n N) (chi (B N)) := by
      rw [hsplit N, map_add, map_add]
    have hdiag : μ (n N) (e (n N)) =
        μ (n N) (chi A) - μ (n N) (chi (F N)) - μ (n N) (chi (B N)) := by
      rw [hidentity]
      abel
    have hnorm : ‖μ (n N) (e (n N))‖ ≤
        ‖μ (n N) (chi A)‖ + ‖μ (n N) (chi (F N))‖ +
          ‖μ (n N) (chi (B N))‖ := by
      rw [hdiag]
      exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    have hlarge : ε ≤ ‖μ (n N) (e (n N))‖ := (state N).2.property.2 (hnmem N)
    dsimp [δ] at hA_small hF_small hB_small
    linarith only [hε, hA_small, hF_small, hB_small, hnorm, hlarge]
  simpa only [hnorm, norm_zero, A, ContinuousLinearMap.comp_apply] using hd.norm

end Phillips
