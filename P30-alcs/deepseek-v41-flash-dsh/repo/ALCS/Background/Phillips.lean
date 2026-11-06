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

**Lemma 2.2**. Let `(μ_n)` be a sequence in `(ℓ^∞(ℕ))*` such that `μ_n(a) → 0` for every
`a ∈ ℓ^∞(ℕ)`. Then `μ_n(e_n) → 0`.

**Lemma 2.3**. Let `S ∈ 𝓛(ℓ^∞(ℕ), X)` and `t_n ≥ 0` with `t_n → 0`. Then
`‖(T_{t_n} - Id) S e_n‖ → 0`.

## Main declarations

* `Phillips.diagonal_tendsto_zero` : **Lemma 2.2**, proved by the gliding hump method.
  `small_on_subsets` thins an infinite set so that a fixed functional is small on all its
  subsets (using `card_mul_le_norm`: a bounded functional sums to at most its norm over
  pairwise disjoint sets); a recursion on reservoirs then produces indices `n_i` with
  `μ_{n_i}` large on `e_{n_i}` but small on the past and on the future, contradicting the
  pointwise convergence on the set of all `n_i`.
* `Phillips.uniform` : **Lemma 2.3**. Only strong right-continuity of `T` at `0` is used.
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
    (by intro k; by_cases hk : k ∈ S <;> simp [hk])

@[simp] theorem chi_apply (S : Set ℕ) (k : ℕ) :
    chi (𝕜 := 𝕜) S k = if k ∈ S then 1 else 0 := rfl

/-- The `k`th canonical vector of `ℓ∞`. -/
def e (k : ℕ) : Linfty 𝕜 := chi {k}

@[simp] theorem e_apply (k j : ℕ) :
    e (𝕜 := 𝕜) k j = if j = k then 1 else 0 := by
  simp [e]

lemma chi_union {s t : Set ℕ} (h : Disjoint s t) :
    chi (𝕜 := 𝕜) (s ∪ t) = chi s + chi t := by
  ext x
  simp only [chi_apply, BoundedContinuousFunction.add_apply, Set.mem_union]
  by_cases hx : x ∈ s
  · simp [hx, fun h' => (Set.disjoint_left.1 h) hx h']
  · by_cases hx' : x ∈ t <;> simp [hx, hx']

/-- For pairwise disjoint sets, a bounded functional has summable values on their
characteristic sequences, with total variation at most its norm. -/
lemma card_mul_le_norm (φ : Linfty 𝕜 →L[𝕜] 𝕜) {B : ℕ → Set ℕ}
    (hdisj : ∀ i j, i ≠ j → Disjoint (B i) (B j)) {δ : ℝ} (hδ : 0 < δ)
    (hlarge : ∀ i, δ < ‖φ (chi (B i))‖) (s : Finset ℕ) :
    (s.card : ℝ) * δ ≤ ‖φ‖ := by
  classical
  -- normalized test vectors, with `φ (v i) = 1`
  set v : ℕ → Linfty 𝕜 := fun i => (φ (chi (B i)))⁻¹ • chi (B i) with hv
  have hz : ∀ i, 0 < ‖φ (chi (B i))‖ := fun i => hδ.trans (hlarge i)
  have hφv : ∀ i, φ (v i) = 1 := fun i => by
    simp only [hv, map_smul, smul_eq_mul]
    exact inv_mul_cancel₀ (norm_pos_iff.mp (hz i))
  have hsum : ‖∑ i ∈ s, v i‖ ≤ δ⁻¹ := by
    apply (BoundedContinuousFunction.norm_le (inv_nonneg.2 hδ.le)).2
    intro x
    rw [BoundedContinuousFunction.sum_apply]
    by_cases hx : ∃ i ∈ s, x ∈ B i
    · obtain ⟨i, hi, hxi⟩ := hx
      rw [Finset.sum_eq_single i]
      · rw [show (v i) x = (φ (chi (B i)))⁻¹ from by simp [hv, chi_apply, hxi], norm_inv]
        exact (inv_le_inv₀ (hz i) hδ).2 (hlarge i).le
      · intro j hj hji
        have hxj : x ∉ B j := fun h => (Set.disjoint_left.1 (hdisj j i hji)) h hxi
        simp [hv, chi_apply, hxj]
      · exact fun h => absurd hi h
    · rw [Finset.sum_eq_zero]
      · simp only [norm_zero]
        exact inv_nonneg.2 hδ.le
      · intro i hi
        have hxi : x ∉ B i := fun h => hx ⟨i, hi, h⟩
        simp [hv, chi_apply, hxi]
  have h2 : (s.card : ℝ) ≤ ‖φ‖ / δ := by
    calc (s.card : ℝ) = ‖φ (∑ i ∈ s, v i)‖ := by
          rw [map_sum, Finset.sum_congr rfl fun i _ => hφv i]
          simp [RCLike.norm_natCast]
      _ ≤ ‖φ‖ * ‖∑ i ∈ s, v i‖ := φ.le_opNorm _
      _ ≤ ‖φ‖ * δ⁻¹ := by gcongr
      _ = ‖φ‖ / δ := by ring
  rwa [le_div_iff₀ hδ] at h2

/-- An infinite set can be thinned so that a given functional is small on
all characteristic sequences supported in the remaining set. -/
theorem small_on_subsets (φ : Linfty 𝕜 →L[𝕜] 𝕜) (S : Set ℕ) (hS : S.Infinite)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ T : Set ℕ, T ⊆ S ∧ T.Infinite ∧ ∀ B : Set ℕ, B ⊆ T → ‖φ (chi B)‖ ≤ δ := by
  classical
  -- partition an infinite subset of `S` into infinitely many infinite pieces
  set emb := fun n => (Set.Infinite.natEmbedding S hS n).val with hemb
  have hinj : Function.Injective emb := fun a b h =>
    (Set.Infinite.natEmbedding S hS).injective (Subtype.ext h)
  set A : ℕ → Set ℕ := fun i => Set.range fun j => emb (Nat.pair i j)
  have hAinf : ∀ i, (A i).Infinite := fun i =>
    Set.infinite_range_of_injective fun a b h => (Nat.pair_eq_pair.1 (hinj h)).2
  have hAS : ∀ i, A i ⊆ S := by
    rintro i _ ⟨j, rfl⟩
    exact (Set.Infinite.natEmbedding S hS _).property
  by_contra h
  have hbad : ∀ i, ∃ B ⊆ A i, δ < ‖φ (chi B)‖ := by
    intro i
    by_contra hi
    push Not at hi
    exact h ⟨A i, hAS i, hAinf i, fun B hB => hi B hB⟩
  choose B hBA hBδ using hbad
  have hdisj : ∀ i j, i ≠ j → Disjoint (B i) (B j) := by
    intro i j hij
    rw [Set.disjoint_left]
    rintro x hxi hxj
    obtain ⟨a, ha⟩ := hBA i hxi
    obtain ⟨b, hb⟩ := hBA j hxj
    exact hij ((Nat.pair_eq_pair.1 (hinj (ha.trans hb.symm))).1)
  obtain ⟨N, hN⟩ := exists_nat_gt (‖φ‖ / δ)
  have h1 := card_mul_le_norm φ hdisj hδ hBδ (Finset.range N)
  rw [Finset.card_range] at h1
  rw [div_lt_iff₀ hδ] at hN
  linarith

/-- **Lemma 2.2** (diagonal statement): if `μ_n(a) → 0` for every `a ∈ ℓ^∞`, then
`μ_n(e_n) → 0`. -/
theorem diagonal_tendsto_zero (μ : ℕ → (Linfty 𝕜 →L[𝕜] 𝕜))
    (hμ : ∀ a : Linfty 𝕜, Tendsto (fun n => μ n a) atTop (𝓝 0)) :
    Tendsto (fun n => μ n (e n)) atTop (𝓝 0) := by
  classical
  rw [Metric.tendsto_atTop]
  intro ε hε
  by_contra h
  have hδ : 0 < ε / 4 := by positivity
  -- the set of bad indices is infinite
  set D : Set ℕ := {n | ε ≤ ‖μ n (e n)‖} with hD
  have hDinf : D.Infinite := by
    by_contra hfin
    rw [Set.not_infinite] at hfin
    obtain ⟨N, hN⟩ := Set.exists_upper_bound_image D (fun n : ℕ => n) hfin
    refine h ⟨N + 1, fun n hn => ?_⟩
    by_contra hcon
    have h2 : n ≤ N := hN n (by simpa [hD, dist_zero_right] using le_of_not_gt hcon)
    omega
  -- one step: from the past `P` and a reservoir `R`, produce a new index and reservoir
  let X := {S : Set ℕ // S.Infinite ∧ S ⊆ D}
  have key : ∀ (P : Finset ℕ) (R : X), ∃ n ∈ R.val, (∀ a ∈ P, a < n) ∧
      ‖μ n (chi ↑P)‖ ≤ ε / 4 ∧ ∃ R' : X, R'.val ⊆ R.val ∧ (∀ a ∈ R'.val, n < a) ∧
        ∀ B : Set ℕ, B ⊆ R'.val → ‖μ n (chi B)‖ ≤ ε / 4 := by
    intro P R
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (hμ (chi ↑P)) (ε / 4) hδ
    obtain ⟨M, hM⟩ := Set.exists_upper_bound_image (↑P : Set ℕ) id P.finite_toSet
    obtain ⟨n, hnR, hn⟩ := R.property.1.exists_notMem_finite (Set.finite_le_nat (max N M))
    have hnm : max N M < n := by simpa using hn
    obtain ⟨T, hTR, hTinf, hTsm⟩ := small_on_subsets (μ n) R.val R.property.1 (by positivity : (0:ℝ) < ε / 4)
    refine ⟨n, hnR, fun a ha => lt_of_le_of_lt (hM a ha) (lt_of_le_of_lt (le_max_right N M) hnm),
      le_of_lt (by simpa [dist_zero_right] using hN n (le_trans (le_max_left N M) hnm.le)),
      ⟨T \ {a | a ≤ n}, hTinf.sdiff (Set.finite_le_nat n),
        fun x hx => R.property.2 (hTR hx.1)⟩, fun x hx => hTR hx.1, ?_, ?_⟩
    · rintro a ⟨ha, hna⟩
      simpa using hna
    · rintro B hB
      exact hTsm B fun x hx => (hB hx).1
  -- the recursion
  choose ns hmemR hlt hpast Rs hsub hgt hsmall using key
  let st : ℕ → Finset ℕ × X :=
    Nat.rec (∅, ⟨D, hDinf, subset_refl D⟩) fun _ p => (insert (ns p.1 p.2) p.1, Rs p.1 p.2)
  let n : ℕ → ℕ := fun i => ns (st i).1 (st i).2
  have hstP (i : ℕ) : (st (i + 1)).1 = insert (n i) (st i).1 := rfl
  have hmem' (i : ℕ) : n i ∈ (st i).2.val := hmemR _ _
  have hlt' (i : ℕ) : ∀ a ∈ (st i).1, a < n i := hlt _ _
  have hpast' (i : ℕ) : ‖μ (n i) (chi ↑(st i).1)‖ ≤ ε / 4 := hpast _ _
  have hsub' (i : ℕ) : (st (i + 1)).2.val ⊆ (st i).2.val := hsub _ _
  have hRinf' (i : ℕ) : (st i).2.val.Infinite := (st i).2.property.1
  have hgt' (i : ℕ) : ∀ a ∈ (st (i + 1)).2.val, n i < a := hgt _ _
  have hsmall' (i : ℕ) : ∀ B ⊆ (st (i + 1)).2.val, ‖μ (n i) (chi B)‖ ≤ ε / 4 := hsmall _ _
  have hanti : Antitone fun i => (st i).2.val := antitone_nat_of_succ_le hsub'
  -- the past is exactly the set of previously chosen indices
  have hP : ∀ i, (st i).1 = (Finset.range i).image n := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih => rw [hstP, ih, Finset.range_add_one, Finset.image_insert]
  have hmono : StrictMono n := by
    refine strictMono_nat_of_lt_succ fun i => ?_
    refine hlt' (i + 1) (n i) ?_
    rw [hP (i + 1), Finset.range_add_one]
    exact Finset.mem_image_of_mem n (Finset.mem_insert_self _ _)
  have hinj : Function.Injective n := hmono.injective
  have hge : ∀ i, i ≤ n i := by
    intro i
    induction i with
    | zero => omega
    | succ i ih => exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (hmono (Nat.lt_succ_self i)))
  -- the set of all selected indices
  set A : Set ℕ := Set.range n with hA
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.1 (hμ (chi A)) (ε / 4) hδ
  set k := n (N₀ + 1) with hk
  set F : Set ℕ := ↑(st (N₀ + 1)).1 with hF
  set B : Set ℕ := n '' Set.Ioi (N₀ + 1) with hB
  set ν : Linfty 𝕜 →L[𝕜] 𝕜 := μ k with hν
  have hlarge : ε ≤ ‖ν (e k)‖ := by
    have h1 : k ∈ D := (st (N₀ + 1)).2.property.2 (hmem' (N₀ + 1))
    simpa [hD] using h1
  have hAsmall : ‖ν (chi A)‖ ≤ ε / 4 := by
    have h1 : N₀ ≤ k := by have := hge (N₀ + 1); omega
    simpa [dist_zero_right] using (hN₀ k h1).le
  have hpastsmall : ‖ν (chi F)‖ ≤ ε / 4 := hpast' (N₀ + 1)
  have hfuturesmall : ‖ν (chi B)‖ ≤ ε / 4 := by
    refine hsmall' (N₀ + 1) _ ?_
    rintro x ⟨j, hj, rfl⟩
    simp only [Set.mem_Ioi] at hj
    exact hanti (show N₀ + 1 + 1 ≤ j by omega) (hmem' j)
  -- the decomposition of `chi A`
  have hcoe : n '' Set.Iio (N₀ + 1) = F := by
    rw [hF, hP (N₀ + 1), Finset.coe_image, Finset.coe_range]
  have huniv : (Set.univ : Set ℕ) = Set.Iio (N₀ + 1) ∪ {N₀ + 1} ∪ Set.Ioi (N₀ + 1) := by
    ext j
    simp only [Set.mem_univ, Set.mem_union, Set.mem_Iio, Set.mem_singleton_iff, Set.mem_Ioi,
      iff_true]
    rcases lt_trichotomy j (N₀ + 1) with h | h | h <;> simp [h]
  have hAeq : A = F ∪ {k} ∪ B := by
    rw [hA, ← Set.image_univ, huniv, Set.image_union, Set.image_union, Set.image_singleton, hcoe,
      hk, hB]
  have hchi : chi (𝕜 := 𝕜) A = chi F + e k + chi B := by
    rw [hAeq, chi_union, chi_union]
    · rfl
    · rw [Set.disjoint_left]
      rintro x hx hx'
      rw [Set.mem_singleton_iff] at hx'
      rw [hx', hF, hP (N₀ + 1)] at hx
      simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio] at hx
      obtain ⟨j, hj, hjn⟩ := hx
      exact (ne_of_lt (hmono hj)) hjn
    · rw [Set.disjoint_left]
      rintro x hx ⟨j, hj, hxj⟩
      simp only [Set.mem_Ioi] at hj
      rcases hx with hx | hx
      · rw [hF, hP (N₀ + 1)] at hx
        simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio] at hx
        obtain ⟨i, hi, hin⟩ := hx
        exact (ne_of_lt (lt_trans (hmono hi) (hmono hj))) (hin.trans hxj.symm)
      · rw [Set.mem_singleton_iff] at hx
        rw [hx] at hxj
        exact (ne_of_lt (hmono hj)) hxj.symm
  -- conclusion
  have hdiag : ν (e k) = ν (chi A) - ν (chi F) - ν (chi B) := by
    rw [hchi, map_add, map_add]
    abel
  have hbound : ‖ν (e k)‖ ≤ ‖ν (chi A)‖ + ‖ν (chi F)‖ + ‖ν (chi B)‖ := by
    rw [hdiag]
    have h1 := norm_sub_le (ν (chi A) - ν (chi F)) (ν (chi B))
    have h2 := norm_sub_le (ν (chi A)) (ν (chi F))
    linarith
  linarith

end Phillips

namespace Phillips

open Filter
open scoped Topology

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- **Lemma 2.3**. Let `S : ℓ^∞ → X` be a bounded operator and `t n ≥ 0` with `t n → 0`.
Then `‖(T (t n) - Id) (S (e n))‖ → 0`.

Only strong right-continuity of `T` at zero is required; the semigroup law and
completeness of `X` are not used. -/
theorem uniform
    (S : Linfty 𝕜 →L[𝕜] X)
    (T : ℝ → (X →L[𝕜] X))
    (hT : ∀ x : X, Tendsto (fun s : ℝ => T s x) (nhdsWithin 0 (Set.Ici 0)) (𝓝 x))
    (t : ℕ → ℝ)
    (ht_nonneg : ∀ n : ℕ, 0 ≤ t n)
    (ht : Tendsto t atTop (𝓝 0)) :
    Tendsto (fun n => ‖(T (t n) - ContinuousLinearMap.id 𝕜 X) (S (e n))‖) atTop (𝓝 0) := by
  classical
  have htWithin : Tendsto t atTop (nhdsWithin (0 : ℝ) (Set.Ici 0)) :=
    tendsto_nhdsWithin_iff.2 ⟨ht, Filter.Eventually.of_forall ht_nonneg⟩
  -- diagonal statement for `A n = (T (t n) - 1) ∘ S`
  set A : ℕ → (Linfty 𝕜 →L[𝕜] X) := fun n => (T (t n) - ContinuousLinearMap.id 𝕜 X).comp S with hAdef
  have hA : ∀ a : Linfty 𝕜, Tendsto (fun n => A n a) atTop (𝓝 0) := by
    intro a
    have hTa : Tendsto (fun n => T (t n) (S a)) atTop (𝓝 (S a)) := (hT (S a)).comp htWithin
    change Tendsto (fun n => T (t n) (S a) - S a) atTop (𝓝 0)
    simpa only [sub_self] using hTa.sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => S a) atTop (𝓝 (S a)))
  -- choose norming functionals and apply the scalar diagonal statement
  choose φ hφnorm hφeval using fun n : ℕ => exists_dual_vector'' 𝕜 (A n (e n))
  have hμ : ∀ a : Linfty 𝕜, Tendsto (fun n => (φ n).comp (A n) a) atTop (𝓝 0) := by
    intro a
    refine squeeze_zero_norm (a := fun n => ‖A n a‖) (fun n => ?_) ?_
    · calc ‖φ n (A n a)‖ ≤ ‖φ n‖ * ‖A n a‖ := (φ n).le_opNorm _
        _ ≤ 1 * ‖A n a‖ := by gcongr; exact hφnorm n
        _ = ‖A n a‖ := one_mul _
    · simpa only [norm_zero] using (hA a).norm
  have hnorm (n : ℕ) : ‖φ n ((A n) (e n))‖ = ‖(A n) (e n)‖ := by
    rw [hφeval n, RCLike.norm_of_nonneg (norm_nonneg _)]
  have hfin : Tendsto (fun n => ‖(A n) (e n)‖) atTop (𝓝 0) := by
    simpa only [ContinuousLinearMap.comp_apply, hnorm, norm_zero] using
      (diagonal_tendsto_zero (fun n => (φ n).comp (A n)) hμ).norm
  simpa only [hAdef, ContinuousLinearMap.comp_apply, sub_apply] using hfin

end Phillips
