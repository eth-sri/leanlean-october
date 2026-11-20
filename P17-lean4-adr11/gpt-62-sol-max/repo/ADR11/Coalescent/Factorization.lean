module

public import ADR11.Coalescent.Forest

/-! Factor Kingman's transition into path counts and a scalar weight for each number of mergers. Counting paths cancels the products of rates in Tavaré’s
partial-fraction formula. -/

@[expose] public section

namespace ADR11

open Finset Real
open scoped Matrix

variable {L : Type*} [DecidableEq L]

/-- Find maximal clusters by scanning the given family, not all possible subsets. -/
def maximalClusters (F : ClusterFamily L) : ClusterFamily L :=
  F.filter fun A => ∀ B ∈ F, A ⊆ B → B = A


/-- Enumerate the endpoints of all histories of `n` mergers, with multiplicity. -/
def mergeHistories : ℕ → ClusterFamily L → Multiset (ClusterFamily L)
  | 0, F => {F}
  | n + 1, F => ((maximalClusters F).powersetCard 2).val.bind fun P => mergeHistories n (mergeAt F P)

noncomputable def mergeCount (n : ℕ) (F G : ClusterFamily L) : ℝ :=
  (mergeHistories n F).count G

@[simp] theorem mergeCount_zero (F G : ClusterFamily L) :
    mergeCount 0 F G = if G = F then 1 else 0 := by
  simp [mergeCount, mergeHistories, Multiset.count_singleton, apply_ite]

variable [Fintype L]

@[simp] theorem maximalClusters_eq (F : ClusterFamily L) : maximalClusters F = roots F := by
  ext A
  simp [maximalClusters, roots]

/-! ### The jump chain -/

/-- First-step analysis, summing over unordered pairs of roots. -/
theorem mergeCount_succ (F G : ClusterFamily L) (n : ℕ) :
    mergeCount (n + 1) F G =
      ∑ P ∈ mergePairs F, mergeCount n (mergeAt F P) G := by
  simp only [mergeCount, mergeHistories, maximalClusters_eq, Multiset.count_bind, Nat.cast_multiset_sum,
    sum_eq_multiset_sum, Multiset.map_map, Function.comp_def]

/-- The jump chain only adds clusters, keeps the lineages, and removes one root per step until
one root is left. -/
theorem mergeCount_support {F G : ClusterFamily L} (hF : IsForest F) {n : ℕ}
    (h : mergeCount n F G ≠ 0) :
    IsForest G ∧ F ⊆ G ∧ lineages G = lineages F := by
  induction n generalizing F with
  | zero =>
    obtain rfl : G = F := by simpa using h
    exact ⟨hF, Subset.rfl, rfl⟩
  | succ n ih =>
    rw [mergeCount_succ] at h
    obtain ⟨P, hP, hne⟩ := exists_ne_zero_of_sum_ne_zero h
    obtain ⟨hf, -, hsub, -, hlin⟩ := hF.merge_pair hP
    obtain ⟨a, b, c⟩ := ih hf hne
    exact ⟨a, hsub.trans b, c.trans hlin⟩

/-! ### The matrix exponential, entrywise -/

set_option backward.isDefEq.respectTransparency false in
/-- The entries of the exponential of a real matrix are given by the exponential series. -/
theorem hasSum_matrix_exp {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (i j : ι) :
    HasSum (fun n : ℕ => ((n.factorial : ℝ))⁻¹ * (A ^ n) i j) (NormedSpace.exp A i j) := by
  open scoped Matrix.Norms.Operator in
  simpa using Pi.hasSum.mp (Pi.hasSum.mp (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) A) i) j

private theorem hasSum_exp_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Matrix ι ι ℝ) (t : ℝ) (i : ι) (v : ι → ℝ) :
    HasSum (fun m : ℕ => (m.factorial : ℝ)⁻¹ * (t ^ m * ((Q ^ m) *ᵥ v) i))
      ((NormedSpace.exp (t • Q) *ᵥ v) i) := by
  simpa only [Matrix.mulVec, dotProduct, smul_pow, Matrix.smul_apply, smul_eq_mul,
    mul_assoc, mul_sum] using hasSum_sum (s := univ) fun j _ =>
      (hasSum_matrix_exp (t • Q) i j).mul_right (v j)

theorem kingmanTransition_add (s t : ℝ) :
    kingmanTransition (L := L) (s + t) = kingmanTransition s * kingmanTransition t := by
  unfold kingmanTransition
  rw [add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl _).smul_left s).smul_right t)

theorem kingmanTransition_nonneg {t : ℝ} (ht : 0 ≤ t) (F G : ClusterFamily L) :
    0 ≤ kingmanTransition t F G := by
  -- Shift the generator by a scalar matrix to make it entrywise nonnegative.
  let Q := kingmanGenerator (L := L)
  let c := rate (Fintype.card (Finset L))
  let P := Q + c • 1
  have hP (i j : ClusterFamily L) : 0 ≤ (t • P) i j := by
    refine mul_nonneg ht ?_
    have h : ((#(roots i)).choose 2 : ℝ) ≤ c := by
      dsimp [c, rate]
      exact_mod_cast Nat.choose_le_choose 2 (card_le_univ (roots i))
    simp only [P, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, eq_comm (a := i) (b := j), Q, kingmanGenerator]
    split_ifs <;> simp_all
  have hp := (hasSum_matrix_exp (t • P) F G).nonneg fun m => mul_nonneg (by positivity)
    (Matrix.pow_apply_nonneg hP m F G)
  have he (r : ℝ) :
      NormedSpace.exp (r • (1 : Matrix (ClusterFamily L) (ClusterFamily L) ℝ)) = exp r • 1 := by
    simp only [Matrix.smul_one_eq_diagonal, Matrix.exp_diagonal, Pi.exp_def, ← Real.exp_eq_exp_ℝ]
  simp only [P, smul_add, smul_smul] at hp
  rw [Matrix.exp_add_of_commute _ _ ((Commute.one_right _).smul_right _), he, Matrix.mul_smul, mul_one] at hp
  exact nonneg_of_mul_nonneg_right hp (exp_pos _)

/-- Tavaré's coefficient divided by the number of ordered jump histories. -/
def spectralCoeff (R : Type*) [Field R] (i j k : ℕ) : R :=
  (∏ l ∈ (Icc j i).erase k, ((l.choose 2 : R) - k.choose 2))⁻¹

noncomputable abbrev tavareCoeff := spectralCoeff ℝ
abbrev tavareRat := spectralCoeff ℚ

private theorem rate_strict : StrictMonoOn rate (Set.Ici 1) := by
  refine strictMonoOn_of_lt_succ Set.ordConnected_Ici fun a _ ha _ => ?_
  simpa [rate, Nat.choose_succ_succ', Nat.choose_one_right] using (show 0 < a from ha)

private theorem tavare_sum {i j : ℕ} (hj : 1 ≤ j) (hji : j ≤ i) :
    ∑ k ∈ Icc j i, tavareCoeff i j k = if i = j then 1 else 0 := by
  have hm k (hk : k ∈ Icc j i) : k ∈ Set.Ici 1 := hj.trans (mem_Icc.1 hk).1
  have hp : 0 < #(Icc j i) := card_pos.2 ⟨j, mem_Icc.2 ⟨le_rfl, hji⟩⟩
  have h := Lagrange.coeff_eq_sum (s := Icc j i) (v := fun k => -rate k)
    (fun a ha b hb e => rate_strict.injOn (hm a ha) (hm b hb) (neg_injective e))
    (P := (1 : Polynomial ℝ)) (by simpa using (show (0 : WithBot ℕ) < #(Icc j i) from by exact_mod_cast hp))
  have hc : #(Icc j i) - 1 = 0 ↔ i = j := by rw [Nat.card_Icc]; omega
  simpa only [Polynomial.coeff_one, hc, Polynomial.eval_one, neg_sub_neg, rate, one_div, spectralCoeff] using h.symm

/-- Apply the spectral weights to an arbitrary function of the rates. -/
noncomputable def spectralMix (i j : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Icc j i, f k * tavareCoeff i j k

private theorem erase_rank {j i : ℕ} (hj : 1 ≤ j) : (Icc j i).erase i = Icc j (i - 1) := by
  ext k
  simp only [mem_erase, mem_Icc]
  omega

private theorem spectralMix_step (i j : ℕ) (hj : 1 ≤ j) (hji : j ≤ i) (f : ℕ → ℝ) :
    spectralMix i j (fun k => -rate k * f k) = spectralMix (i - 1) j f - rate i * spectralMix i j f := by
  have he := erase_rank (i := i) hj
  rw [eq_sub_iff_add_eq, spectralMix, spectralMix, spectralMix, mul_sum, ← sum_add_distrib,
    ← sum_erase _ (a := i) (by ring)]
  refine sum_congr he fun k hk => ?_
  obtain ⟨hki, hk⟩ := mem_erase.1 (he.symm ▸ hk)
  have hd : (↑(i.choose 2) - ↑(k.choose 2) : ℝ) ≠ 0 :=
    (sub_pos.2 (rate_strict (hj.trans (mem_Icc.1 hk).1) (hj.trans hji) (by grind))).ne'
  have hc : tavareCoeff (i - 1) j k = (rate i - rate k) * tavareCoeff i j k := by
    unfold tavareCoeff spectralCoeff
    rw [← he, erase_right_comm, ← mul_prod_erase _ _ (mem_erase.2 ⟨hki.symm, mem_Icc.2 ⟨hji, le_rfl⟩⟩),
      mul_inv]
    simp [rate, hd]
  rw [hc]
  ring

noncomputable def pathWeight (i j : ℕ) (t : ℝ) : ℝ := spectralMix i j fun k => exp (-(rate k * t))

@[simp] theorem tavareRat_cast (i j k : ℕ) : (tavareRat i j k : ℝ) = tavareCoeff i j k := by
  simp [spectralCoeff, Rat.cast_prod]

omit [Fintype L] in
/-- Count the empty forest as one lineage in the scalar process: either population is stationary. -/
def deathRank (F : ClusterFamily L) := max #(maximalClusters F) 1

@[simp] theorem deathRank_eq (F : ClusterFamily L) : deathRank F = max #(roots F) 1 := by
  simp [deathRank]

private theorem rate_deathRank (F : ClusterFamily L) : rate (deathRank F) = rate #(roots F) := by
  rw [deathRank_eq, max_def]
  split_ifs with h <;> first | rfl | simp [rate_eq_zero.2 h]

private theorem rank_merge {F P : ClusterFamily L} (hF : IsForest F) (hp : P ∈ mergePairs F) :
    deathRank (mergeAt F P) = deathRank F - 1 := by
  have := (hF.merge_pair hp).2.1
  have := card_le_card (mem_powersetCard.1 hp).1
  grind [deathRank_eq]

set_option maxHeartbeats 1000000 in
private theorem kingmanGenerator_pow_mix {F : ClusterFamily L} (hF : IsForest F) (G : ClusterFamily L) (m : ℕ) :
    (kingmanGenerator ^ m) F G = ∑ j ∈ Icc 1 (deathRank F),
      spectralMix (deathRank F) j (fun k => (-rate k)^m) * mergeCount (deathRank F - j) F G := by
  induction m generalizing F with
  | zero =>
    let k := deathRank F
    have hk : 1 ≤ k := le_max_right ..
    change _ = ∑ j ∈ Icc 1 k, spectralMix k j (fun q => (-rate q)^0) * mergeCount (k-j) F G
    simp only [pow_zero, spectralMix, one_mul]
    rw [sum_congr rfl fun j hj => congrArg (· * mergeCount (k-j) F G)
      (tavare_sum (mem_Icc.1 hj).1 (mem_Icc.1 hj).2)]
    simp [-deathRank_eq, Matrix.one_apply, ite_mul, eq_comm (a := k), eq_comm (a := F), hk]
  | succ m ih =>
    let k := deathRank F
    have hk : 1 ≤ k := le_max_right ..
    let s i j := spectralMix i j fun q => (-rate q)^m
    rw [pow_succ', Matrix.mul_apply, hF.sum_generator_pairs, sum_sub_distrib, sum_const,
      nsmul_eq_mul, card_powersetCard, ← rate, ← rate_deathRank F, ih hF,
      sum_congr rfl (fun P hp => by rw [ih (hF.merge_pair hp).1, rank_merge hF hp]), sum_comm]
    simp_rw [← mul_sum, ← mergeCount_succ]
    change (∑ j ∈ Icc 1 (k - 1), s (k - 1) j * mergeCount (k - 1 - j + 1) F G) -
      rate k * (∑ j ∈ Icc 1 k, s k j * mergeCount (k-j) F G) = _
    rw [sum_congr rfl (fun j hj => by rw [show k - 1 - j + 1 = k - j by grind]),
      ← erase_rank le_rfl, sum_erase_eq_sub (mem_Icc.2 ⟨hk, le_rfl⟩)]
    simp only [s, spectralMix, Icc_eq_empty (by omega : ¬ k ≤ k - 1), sum_empty, zero_mul, sub_zero]
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun j hj => ?_
    change s (k-1) j * _ - rate k * (s k j * _) = spectralMix k j _ * _
    rw [← mul_assoc, ← sub_mul]
    congr 1
    simpa only [s, pow_succ'] using (spectralMix_step k j (mem_Icc.1 hj).1 (mem_Icc.1 hj).2
      (fun q => (-rate q)^m)).symm

/-- Kingman's kernel is the mixture over the possible numbers of remaining lineages. -/
theorem kingmanTransition_eq_sum_Icc {F : ClusterFamily L} (hF : IsForest F) (t : ℝ) (G : ClusterFamily L) :
    kingmanTransition t F G = ∑ j ∈ Icc 1 (deathRank F), pathWeight (deathRank F) j t * mergeCount (deathRank F - j) F G := by
  let k := deathRank F
  refine (hasSum_matrix_exp (t • kingmanGenerator) F G).unique ?_
  simp_rw [pathWeight, spectralMix, ← neg_mul]
  simpa only [spectralMix, smul_pow, Matrix.smul_apply, smul_eq_mul, kingmanGenerator_pow_mix hF,
    k, mul_sum, sum_mul, mul_assoc, mul_left_comm, mul_comm, mul_pow, div_eq_mul_inv,
    ← Real.exp_eq_exp_ℝ] using
    hasSum_sum (s := Icc 1 k) (fun j _ => (hasSum_sum (s := Icc j k) (fun i _ =>
      (NormedSpace.expSeries_div_hasSum_exp (-rate i * t)).mul_right (tavareCoeff k j i))).mul_right (mergeCount (k-j) F G))

theorem kingmanTransition_support {F G : ClusterFamily L} (hF : IsForest F)
    {t : ℝ} (h : kingmanTransition t F G ≠ 0) : IsForest G ∧ F ⊆ G ∧ lineages G = lineages F := by
  rw [kingmanTransition_eq_sum_Icc hF] at h
  obtain ⟨j, -, h⟩ := exists_ne_zero_of_sum_ne_zero h
  exact mergeCount_support hF (right_ne_zero_of_mul h)

/-- Push a finite distribution through a deterministic map. -/
noncomputable def pushD {α β : Type*} [Fintype α] [DecidableEq β]
    (f : α → β) (p : α → ℝ) (b : β) : ℝ := ∑ a, if f a = b then p a else 0

theorem pushD_test {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (p : α → ℝ) (w : β → ℝ) : ∑ b, pushD f p b * w b = ∑ a, p a * w (f a) := by
  simp_rw [pushD, sum_mul, ite_mul, zero_mul]
  rw [sum_comm]
  simp_rw [sum_ite_eq, mem_univ, ite_true]

section Lumping

variable {M : Type*} [Fintype M] [DecidableEq M]
variable (Q : Matrix M M ℝ) (r : ClusterFamily L → M)
variable (hQ : ∀ {F}, IsForest F → ∀ u : M → ℝ,
  ∑ G, kingmanGenerator F G * u (r G) = (Q *ᵥ u) (r F))
include hQ

private theorem push_pow (m : ℕ) {F : ClusterFamily L} (hF : IsForest F) (u : M → ℝ) :
    ((kingmanGenerator ^ m) *ᵥ (u ∘ r)) F = ((Q ^ m) *ᵥ u) (r F) := by
  induction m generalizing F with
  | zero => simp [Matrix.one_mulVec]
  | succ m ih =>
    rw [pow_succ', pow_succ', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hQ hF]
    exact sum_mul_congr fun G _ h => ih (hF.generator_preserves h)

/-- Intertwining the generators also intertwines the finite-time transitions. -/
theorem transition_push {F : ClusterFamily L} (hF : IsForest F) (t : ℝ) (G : M) :
    pushD r (kingmanTransition t F) G = NormedSpace.exp (t • Q) (r F) G := by
  let v := fun H => if H = G then (1 : ℝ) else 0
  have h := hasSum_exp_mulVec kingmanGenerator t F (v ∘ r)
  simp_rw [push_pow Q r hQ _ hF] at h
  simpa only [v, Matrix.mulVec, dotProduct, Function.comp_apply, mul_ite, mul_one, mul_zero,
    pushD, kingmanTransition, sum_ite_eq', mem_univ, ite_true] using h.unique (hasSum_exp_mulVec Q t (r F) v)

end Lumping

theorem kingmanTransition_sum {F : ClusterFamily L} (hF : IsForest F) (t : ℝ) :
    ∑ G, kingmanTransition t F G = 1 := by
  simpa [pushD, Matrix.one_apply] using
    transition_push (0 : Matrix Unit Unit ℝ) (fun _ : ClusterFamily L => ())
      (fun h _ => by simp [h.sum_generator_pairs, Matrix.zero_mulVec]) hF t ()

end ADR11
