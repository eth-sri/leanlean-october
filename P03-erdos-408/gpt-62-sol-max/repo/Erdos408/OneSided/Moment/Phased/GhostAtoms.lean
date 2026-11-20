module

public import Erdos408.OneSided.Moment.Phased.Rows

/-!
# Ghost rows with prescribed births

PD `mem:ghost-atoms`: a ghost row with prescribed batch primes. If `s` ordered coordinates of
a batch are prescribed, the creation sum `∑_n ∏_x (|cre| ν v₀)^{n_x} / n_x!` only runs over
the batches containing each prescribed prime with its multiplicity, and each prescribed
coordinate costs one atom `|cre| ν v₀ ≤ c ν(p)`.

* `sum_binom_exp_req_le`, `ghost_row_req`: the row sums of the ghost operation of
  `Memory/Ghost.lean` restricted to `n ≥ m` are at most
  `∏_{x hit} (|cre x| ν x v₀)^{m x} exp(v₀ ∑_{hits} |cre| ν) v₀^{size}`, since
  `∑_{n ≥ m} e^n / n! ≤ e^m exp(e)`.
* `card_le_count_of_getElem`, `count_batchPrimes`: if a list takes the value `p` at the
  indices of `T`, then `p` occurs at least `|T|` times; the batch primes count the created
  particles of each prime.
* `sum_chainGhost_pres_le`: the weighted row sums of a chain ghost against the prescription
  indicators `∏_k [β_k = π_k]` of its batch indices are at most `∏_k atomCost(π_k)` times the
  row factor `exp(v₀ ∑_{hits} |cre| ν)`. A hitting particle is determined by its prime, so the
  required multiplicities live on the hitting particles.
-/

@[expose] public section

noncomputable section

namespace Erdos408.OneSided

open Finset

/-! ### Prescribed indices of a list -/

/-- If a list takes the value `p` at every index of `T`, then `p` occurs at least `|T|`
times. -/
theorem card_le_count_of_getElem {p : ℕ} :
    ∀ (l : List ℕ) (T : Finset ℕ), (∀ k ∈ T, l[k]? = some p) → T.card ≤ l.count p
  | [], T, hT => by
    have hT0 : T = ∅ := eq_empty_of_forall_notMem fun k hk => by simpa using hT k hk
    simp [hT0]
  | a :: l, T, hT => by
    -- the indices after the head shift down by one
    have hT' : ∀ k ∈ (T.erase 0).image (· - 1), l[k]? = some p := by
      intro k hk
      obtain ⟨k₀, hk₀, rfl⟩ := mem_image.1 hk
      obtain ⟨hk₀0, hk₀T⟩ := mem_erase.1 hk₀
      have := hT k₀ hk₀T
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk₀0
      simpa using this
    have hinj : Set.InjOn (· - 1) ((T.erase 0 : Finset ℕ) : Set ℕ) := fun k hk k' hk' h => by
      rw [mem_coe, mem_erase] at hk hk'
      simp only at h
      omega
    have ih := card_le_count_of_getElem l _ hT'
    rw [card_image_of_injOn hinj] at ih
    rw [List.count_cons]
    by_cases h0 : 0 ∈ T
    · have ha : a = p := by simpa using hT 0 h0
      have := card_erase_add_one h0
      simp only [ha, beq_self_eq_true, ite_true]
      omega
    · rw [erase_eq_of_notMem h0] at ih
      omega

variable {K : ℕ}

section Chain

variable {q x : ℝ} {d : Data K} {Y d₀ u v r : ℝ} {B : ℕ}

/-- The batch primes count the created particles of each prime:
`#{p in the batch} = ∑_{x : x.prime = p} n(x)`. -/
theorem count_batchPrimes (n : Particle x d → ℕ) (p : ℕ) :
    (batchPrimes x d n).count p = ∑ xp : Particle x d, if xp.1.1 = p then n xp else 0 := by
  rw [batchPrimes, ← Multiset.coe_count, Multiset.sort_eq, Multiset.count_sum']
  exact sum_congr rfl fun xp _ => Multiset.count_replicate _ _ _

/-- For a valid ghost choice, the batch contains each prime with the multiplicity of the
hitting particle of that prime, or not at all. -/
theorem count_batchPrimes_of_valid {z : ℤ × ℤ} {S : Particle x d → ℕ}
    {c : GhostChoice x d} (hc : GhostValid (HitsAt x d z) B S c) (p : ℕ) :
    (batchPrimes x d c.2).count p ≤ 0 ∨
      ∃ xp, HitsAt x d z xp ∧ xp.1.1 = p ∧ (batchPrimes x d c.2).count p = c.2 xp := by
  rw [count_batchPrimes]
  by_cases hex : ∃ xp, HitsAt x d z xp ∧ xp.1.1 = p
  · obtain ⟨xp, hxp, rfl⟩ := hex
    refine Or.inr ⟨xp, hxp, rfl, ?_⟩
    rw [sum_eq_single xp]
    · rw [ite_eq_left rfl]
    · intro yp _ hne
      refine ite_eq_right_iff.2 fun hp => ?_
      by_cases hyp : HitsAt x d z yp
      · exact absurd (hitsAt_eq_of_prime hyp hxp hp) hne
      · exact hc.2.1 yp hyp
    · intro h
      exact absurd (mem_univ _) h
  · refine Or.inl (le_of_eq (sum_eq_zero fun yp _ => ite_eq_right_iff.2 fun hp => ?_))
    by_contra hne
    exact hex ⟨yp, by_contra fun hyp => hne (hc.2.1 yp hyp), hp⟩

/-- **The ghost rows with prescribed batch primes** (PD `mem:ghost-atoms`): the weighted row
sums of a chain ghost against `∏_k [β_k = π_k]`, over the batch indices `k`, are at most
`∏_k atomCost(π_k)` times the row factor `exp(v₀ ∑_{hits} |cre| ν) v₀^{size}`, once each
creation atom `|cre| ν v₀` is at most `c₀ ν`. -/
theorem sum_chainGhost_pres_le {N j : ℕ} (hν : ∀ p, 0 ≤ primeWeight q x d N p)
    (hsurv : 0 ≤ (1 - dampDefect q N j) / pendingWeight q ^ 2) {v₀ c₀ : ℝ} (hv₀ : 0 < v₀)
    (hc₀0 : 0 ≤ c₀)
    (hdel : (1 - dampDefect q N j) / pendingWeight q ^ 2 +
      |-dampDefect q N j / pendingWeight q| / v₀ ≤ 1)
    (hc₀ : ∀ xp : Particle x d, |-dampDefect q N j * primeMass x d xp.1.1 / pendingWeight q| *
      primeWeight q x d N xp.1.1 * v₀ ≤ c₀ * primeWeight q x d N xp.1.1)
    (π : Fin B → Option ℕ) (t : ChainState x d Y d₀ u v r B) :
    ∑ c ∈ multBox B ×ˢ multBox B, ‖chainGhostCoef q x d Y d₀ u v r B N j t c‖ *
        (∏ k : Fin B, presInd (π k) (batchPrimes x d c.2)[k.1]?) *
        v₀ ^ memSize (chainGhostOut x d Y d₀ u v r B t c).2.2.1 ≤
      (∏ k, atomCost c₀ (primeWeight q x d N) (π k)) *
        (Real.exp (v₀ * ∑ xp with HitsAt x d t.1.1 xp,
          |-dampDefect q N j * primeMass x d xp.1.1 / pendingWeight q| *
            primeWeight q x d N xp.1.1) * v₀ ^ memSize t.2.2.1) := by
  classical
  set z := t.1.1 with hz
  set ν : ℕ → ℝ := primeWeight q x d N with hνdef
  set cre : Particle x d → ℝ :=
    fun xp => -dampDefect q N j * primeMass x d xp.1.1 / pendingWeight q with hcre
  have hRHS0 : 0 ≤ (∏ k, atomCost c₀ ν (π k)) *
      (Real.exp (v₀ * ∑ xp with HitsAt x d z xp, |cre xp| * ν xp.1.1) * v₀ ^ memSize t.2.2.1) :=
    mul_nonneg (prod_nonneg fun k _ => atomCost_nonneg hc₀0 hν _)
      (mul_nonneg (Real.exp_pos _).le (pow_nonneg hv₀.le _))
  -- the prescriptions met by a valid choice: each prescribed prime occurs with multiplicity
  have hmet : ∀ c : GhostChoice x d, GhostValid (HitsAt x d z) B t.2.2.1 c →
      (∏ k : Fin B, presInd (π k) (batchPrimes x d c.2)[k.1]?) ≠ 0 →
      ∀ p, (univ.filter fun k : Fin B => π k = some p).card ≤ (batchPrimes x d c.2).count p := by
    intro c _ hW p
    rw [← card_image_of_injective _ Fin.val_injective]
    refine card_le_count_of_getElem _ _ fun k hk => ?_
    obtain ⟨k', hk', rfl⟩ := mem_image.1 hk
    have hkp := (mem_filter.1 hk').2
    have hne := (prod_ne_zero_iff.1 hW) k' (mem_univ _)
    unfold presInd at hne
    rw [hkp] at hne
    by_contra h
    exact hne (ite_eq_right (by simp [h]))
  by_cases hall : ∀ k p, π k = some p → ∃ xp, HitsAt x d z xp ∧ xp.1.1 = p
  · -- the required multiplicities on the hitting particles
    set m : Particle x d → ℕ := fun xp =>
      if HitsAt x d z xp then (univ.filter fun k : Fin B => π k = some xp.1.1).card else 0
      with hm
    have hle : ∀ c ∈ multBox B ×ˢ multBox B, ‖chainGhostCoef q x d Y d₀ u v r B N j t c‖ *
        (∏ k : Fin B, presInd (π k) (batchPrimes x d c.2)[k.1]?) *
        v₀ ^ memSize (chainGhostOut x d Y d₀ u v r B t c).2.2.1 ≤
        ‖ghostCoef (HitsAt x d z) (fun xp : Particle x d => ν xp.1.1)
            (-dampDefect q N j / pendingWeight q) ((1 - dampDefect q N j) / pendingWeight q ^ 2)
            cre B t.2.2 c‖ * (∏ xp, if m xp ≤ c.2 xp then (1 : ℝ) else 0) *
          v₀ ^ memSize (ghostOut (HitsAt x d z) B t.2.2 c).1 := by
      intro c _
      refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hv₀.le _)
      by_cases hc : GhostValid (HitsAt x d z) B t.2.2.1 c
      · by_cases hW : (∏ k : Fin B, presInd (π k) (batchPrimes x d c.2)[k.1]?) = 0
        · rw [hW, mul_zero]
          exact mul_nonneg (norm_nonneg _) (prod_nonneg fun xp _ => by split_ifs <;> norm_num)
        · -- every requirement holds, and the prescriptions are at most one
          have hreq : ∀ xp, m xp ≤ c.2 xp := by
            intro xp
            simp only [hm]
            split_ifs with hxp
            · have h₁ := hmet c hc hW xp.1.1
              rcases count_batchPrimes_of_valid hc xp.1.1 with h₂ | ⟨yp, hyp, hp, h₂⟩
              · omega
              · have hxy := hitsAt_eq_of_prime hxp hyp hp.symm
                subst hxy
                omega
            · exact Nat.zero_le _
          rw [prod_eq_one fun xp _ => ite_eq_left (hreq xp), mul_one]
          exact mul_le_of_le_one_right (norm_nonneg _)
            (prod_le_one₀ (fun k _ => presInd_nonneg _ _) fun k _ => presInd_le_one _ _)
      · change ‖ghostCoef (HitsAt x d z) _ _ _ _ B t.2.2 c‖ * _ ≤ _
        rw [ghostCoef, ite_eq_right hc, norm_zero, zero_mul, zero_mul]
    -- convert the hitting atoms into the atoms of the prescriptions
    have hconv : (∏ xp : Particle x d, if HitsAt x d z xp then
        (|cre xp| * ν xp.1.1 * v₀) ^ m xp else 1) ≤ ∏ k, atomCost c₀ ν (π k) := by
      have hk : ∀ k, atomCost c₀ ν (π k) = ∏ xp : Particle x d,
          if HitsAt x d z xp ∧ π k = some xp.1.1 then c₀ * ν xp.1.1 else 1 := by
        intro k
        cases hπ : π k with
        | none => simp [atomCost]
        | some p =>
          obtain ⟨x₀, hx₀, rfl⟩ := hall k _ hπ
          rw [prod_eq_single x₀]
          · simp [atomCost, hx₀]
          · intro xp _ hne
            refine ite_eq_right fun h => absurd (hitsAt_eq_of_prime h.1 hx₀ ?_) hne
            exact (Option.some_injective _ h.2).symm
          · intro h
            exact absurd (mem_univ _) h
      simp only [hk]
      rw [prod_comm]
      have he0 : ∀ xp : Particle x d, 0 ≤ |cre xp| * ν xp.1.1 * v₀ := fun xp =>
        mul_nonneg (mul_nonneg (abs_nonneg _) (hν _)) hv₀.le
      refine prod_le_prod₀ (fun xp _ => by
        split_ifs
        exacts [pow_nonneg (he0 xp) _, zero_le_one]) fun xp _ => ?_
      by_cases hxp : HitsAt x d z xp
      · simp only [hxp, true_and, ite_true, hm]
        rw [prod_ite, prod_const, prod_const_one, mul_one]
        exact pow_le_pow_left₀ (he0 xp) (hc₀ xp) _
      · simp [hxp]
    calc _ ≤ ∑ c ∈ multBox B ×ˢ multBox B,
          ‖ghostCoef (HitsAt x d z) (fun xp : Particle x d => ν xp.1.1)
              (-dampDefect q N j / pendingWeight q) ((1 - dampDefect q N j) / pendingWeight q ^ 2)
              cre B t.2.2 c‖ * (∏ xp, if m xp ≤ c.2 xp then (1 : ℝ) else 0) *
            v₀ ^ memSize (ghostOut (HitsAt x d z) B t.2.2 c).1 := sum_le_sum hle
      _ ≤ (∏ xp : Particle x d, if HitsAt x d z xp then
            (|cre xp| * ν xp.1.1 * v₀) ^ m xp else 1) *
          (Real.exp (v₀ * ∑ xp with HitsAt x d z xp, |cre xp| * ν xp.1.1) *
            v₀ ^ memSize t.2.2.1) :=
          ghost_row_req (fun xp => hν _) hsurv hv₀ hdel m t.2.2
      _ ≤ _ := mul_le_mul_of_nonneg_right hconv
          (mul_nonneg (Real.exp_pos _).le (pow_nonneg hv₀.le _))
  · -- some prescribed prime has no hitting particle, so every valid choice misses it
    push Not at hall
    obtain ⟨k₀, p, hk₀, hp⟩ := hall
    refine le_trans (le_of_eq (sum_eq_zero fun c _ => ?_)) hRHS0
    by_cases hc : GhostValid (HitsAt x d z) B t.2.2.1 c
    · by_cases hW : (∏ k : Fin B, presInd (π k) (batchPrimes x d c.2)[k.1]?) = 0
      · rw [hW, mul_zero, zero_mul]
      · have h₁ := hmet c hc hW p
        have h₀ : 1 ≤ (univ.filter fun k : Fin B => π k = some p).card :=
          card_pos.2 ⟨k₀, mem_filter.2 ⟨mem_univ _, hk₀⟩⟩
        rcases count_batchPrimes_of_valid hc p with h₂ | ⟨yp, hyp, hyp', -⟩
        · omega
        · exact absurd hyp' (hp yp hyp)
    · change ‖ghostCoef (HitsAt x d z) _ _ _ _ B t.2.2 c‖ * _ * _ = 0
      rw [ghostCoef, ite_eq_right hc, norm_zero, zero_mul, zero_mul]

end Chain

end Erdos408.OneSided
