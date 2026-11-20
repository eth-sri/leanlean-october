module

public import Erdos408.OneSided.Moment.Chain
public import Erdos408.OneSided.Bands

/-!
# The ghost bound on the chain states

The ingredients of M4 for the ghost (`exists_phasedGhost_normLe` in `Moment/Phased.lean`,
PD `mem:ghost-norm`).

* `normLe_ghostChoiceOp`: a choice operator on the chain states with the ghost output and
  coefficients bounded by the ghost coefficients has norm at most `√(R C)`, where `R` and `C`
  bound the row and column factors `exp(v₀ ∑_{hits} |cre| ν)` and `exp(v₀ |del| ∑_{hits} ν)` of
  `ghostOp_normLe` at every position. The ghost acts fiberwise in the position and the lists,
  and the factor `∏ ν(act)` of the chain measure is common to both sides.
* `eventually_harmonicMass_band` (`Bands.lean`), `eventually_two_mul_add_one_le` and
  `half_le_baseline`: eventually every band has harmonic mass in `[1/2, 1]`, and every band
  prime is at least `2N + 1`, so has baseline `b'_p ≥ 1/2`, for `N = 2R`.
* `sum_hits_le_sum_bandPrimes` and `sum_one_div_bandPrimes_le`: the hitting particles have at
  most one line per band prime, and `∑_{p band prime} 1/p ≤ ∑_i V_i ≤ K`.
-/

@[expose] public section

noncomputable section

namespace Erdos408.OneSided

open Filter Finset Real

variable {K : ℕ}

section Ghost

variable {q x : ℝ} {d : Data K} {Y d₀ u v r : ℝ} {B : ℕ}

/-- **The fiberwise ghost bound**: a choice operator with the ghost output, whose coefficients
are bounded by the ghost coefficients, has norm at most `√(R C)` for the chain measure, once
`v₀` makes both bases of `ghostOp_normLe` at most one and `R`, `C` bound its row and column
factors at every position. -/
theorem normLe_ghostChoiceOp {N j : ℕ} {a : ChainState x d Y d₀ u v r B → GhostChoice x d → ℂ}
    (ha : ∀ s c, ‖a s c‖ ≤ ‖chainGhostCoef q x d Y d₀ u v r B N j s c‖)
    (hν : ∀ p, 0 ≤ primeWeight q x d N p)
    (hsurv : 0 ≤ (1 - dampDefect q N j) / pendingWeight q ^ 2) {v₀ R C : ℝ} (hv₀ : 0 < v₀)
    (hdel : (1 - dampDefect q N j) / pendingWeight q ^ 2 +
      |-dampDefect q N j / pendingWeight q| / v₀ ≤ 1)
    (hcre : ∀ xp : Particle x d, (1 - dampDefect q N j) / pendingWeight q ^ 2 +
      |-dampDefect q N j * primeMass x d xp.1.1 / pendingWeight q| / v₀ ≤ 1)
    (hR : ∀ z : ℤ × ℤ, Real.exp (v₀ * ∑ xp with HitsAt x d z xp,
      |-dampDefect q N j * primeMass x d xp.1.1 / pendingWeight q| *
        primeWeight q x d N xp.1.1) ≤ R)
    (hC : ∀ z : ℤ × ℤ, Real.exp (v₀ * |-dampDefect q N j / pendingWeight q| *
      ∑ xp with HitsAt x d z xp, primeWeight q x d N xp.1.1) ≤ C) :
    NormLe (fun s => chainMeasure q x d Y d₀ u v r B N s)
      (fun s => chainMeasure q x d Y d₀ u v r B N s)
      (choiceOp (multBox B ×ˢ multBox B) a (chainGhostOut x d Y d₀ u v r B))
      (Real.sqrt (R * C)) := by
  classical
  have hν' : ∀ xp : Particle x d, 0 ≤ primeWeight q x d N xp.1.1 := fun xp => hν _
  refine normLe_choiceOp (h := fun s => v₀ ^ memSize s.2.2.1)
    (h' := fun s => v₀ ^ memSize s.2.2.1) ((Real.exp_pos _).le.trans (hR 0))
    ((Real.exp_pos _).le.trans (hC 0))
    (fun s => mul_nonneg (prod_nonneg fun i _ => prod_nonneg fun h _ => hν _)
      (memWeight_nonneg hν' _))
    (fun s => pow_pos hv₀ _) (fun s => ?_) (fun T => ?_)
  · -- the row sum is the row sum of the ghost at the position of `s`
    calc ∑ c ∈ multBox B ×ˢ multBox B,
          ‖a s c‖ * v₀ ^ memSize (chainGhostOut x d Y d₀ u v r B s c).2.2.1
        ≤ ∑ c ∈ multBox B ×ˢ multBox B,
          ‖chainGhostCoef q x d Y d₀ u v r B N j s c‖ *
            v₀ ^ memSize (chainGhostOut x d Y d₀ u v r B s c).2.2.1 :=
          sum_le_sum fun c _ => mul_le_mul_of_nonneg_right (ha s c) (pow_nonneg hv₀.le _)
      _ ≤ Real.exp (v₀ * ∑ xp with HitsAt x d s.1.1 xp,
            |-dampDefect q N j * primeMass x d xp.1.1 / pendingWeight q| *
              primeWeight q x d N xp.1.1) * v₀ ^ memSize s.2.2.1 :=
          ghost_row hν' hsurv hv₀ hdel s.2.2
      _ ≤ R * v₀ ^ memSize s.2.2.1 := mul_le_mul_of_nonneg_right (hR _) (pow_nonneg hv₀.le _)
  · -- only inputs at the position and lists of `T` reach `T`
    have hpos : ∀ (z : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r))
        (y : ↥(lists x d (padCount x)) × MemState (Particle x d) B) (c : GhostChoice x d),
        chainGhostOut x d Y d₀ u v r B (z, y) c = T → z = T.1 :=
      fun z y c h => congrArg Prod.fst h
    have hlist : ∀ (l : ↥(lists x d (padCount x))) (S : MemState (Particle x d) B)
        (c : GhostChoice x d), chainGhostOut x d Y d₀ u v r B (T.1, l, S) c = T → l = T.2.1 :=
      fun l S c h => congrArg (fun t => t.2.1) h
    have hmem : ∀ (S : MemState (Particle x d) B) (c : GhostChoice x d),
        chainGhostOut x d Y d₀ u v r B (T.1, T.2.1, S) c = T ↔
          ghostOut (HitsAt x d T.1.1) B S c = T.2.2 := by
      intro S c
      refine ⟨fun h => congrArg (fun t => t.2.2) h, fun h => ?_⟩
      change (T.1, T.2.1, ghostOut (HitsAt x d T.1.1) B S c) = T
      rw [h]
    set P := ∏ i, ∏ h, primeWeight q x d N (T.2.1.1 i h) with hP
    have hP0 : 0 ≤ P := prod_nonneg fun i _ => prod_nonneg fun h _ => hν _
    calc ∑ s, ∑ c ∈ multBox B ×ˢ multBox B with chainGhostOut x d Y d₀ u v r B s c = T,
          chainMeasure q x d Y d₀ u v r B N s * ‖a s c‖ * v₀ ^ memSize s.2.2.1
        ≤ ∑ s, ∑ c ∈ multBox B ×ˢ multBox B with chainGhostOut x d Y d₀ u v r B s c = T,
          chainMeasure q x d Y d₀ u v r B N s * ‖chainGhostCoef q x d Y d₀ u v r B N j s c‖ *
            v₀ ^ memSize s.2.2.1 := by
          refine sum_le_sum fun s _ => sum_le_sum fun c _ => ?_
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (ha s c) ?_)
            (pow_nonneg hv₀.le _)
          exact mul_nonneg (prod_nonneg fun i _ => prod_nonneg fun h _ => hν _)
            (memWeight_nonneg hν' _)
      _ = P * ∑ S : MemState (Particle x d) B,
          ∑ c ∈ multBox B ×ˢ multBox B with ghostOut (HitsAt x d T.1.1) B S c = T.2.2,
            memWeight (fun xp : Particle x d => primeWeight q x d N xp.1.1) S.1 *
              ‖ghostCoef (HitsAt x d T.1.1)
                (fun xp : Particle x d => primeWeight q x d N xp.1.1)
                (-dampDefect q N j / pendingWeight q)
                ((1 - dampDefect q N j) / pendingWeight q ^ 2)
                (fun xp : Particle x d => -dampDefect q N j * primeMass x d xp.1.1 /
                  pendingWeight q) B S c‖ * v₀ ^ memSize S.1 := by
          rw [Fintype.sum_prod_type, sum_eq_single T.1, Fintype.sum_prod_type,
            sum_eq_single T.2.1, mul_sum]
          · refine sum_congr rfl fun S _ => ?_
            rw [filter_congr fun c _ => hmem S c, mul_sum]
            refine sum_congr rfl fun c _ => ?_
            simp only [chainMeasure, chainGhostCoef, hP]
            ring
          · intro l _ hl
            refine sum_eq_zero fun S _ => sum_eq_zero fun c hc => ?_
            exact absurd (hlist l S c (mem_filter.1 hc).2) hl
          · intro h
            exact absurd (mem_univ _) h
          · intro z _ hz
            refine sum_eq_zero fun y _ => sum_eq_zero fun c hc => ?_
            exact absurd (hpos z y c (mem_filter.1 hc).2) hz
          · intro h
            exact absurd (mem_univ _) h
      _ ≤ P * (Real.exp (v₀ * |-dampDefect q N j / pendingWeight q| *
            ∑ xp with HitsAt x d T.1.1 xp, primeWeight q x d N xp.1.1) *
          (memWeight (fun xp : Particle x d => primeWeight q x d N xp.1.1) T.2.2.1 *
            v₀ ^ memSize T.2.2.1)) :=
          mul_le_mul_of_nonneg_left (ghost_col hν' hsurv hv₀ hcre T.2.2) hP0
      _ ≤ P * (C * (memWeight (fun xp : Particle x d => primeWeight q x d N xp.1.1) T.2.2.1 *
            v₀ ^ memSize T.2.2.1)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hC _)
            (mul_nonneg (memWeight_nonneg hν' _) (pow_nonneg hv₀.le _))) hP0
      _ = C * (chainMeasure q x d Y d₀ u v r B N T * v₀ ^ memSize T.2.2.1) := by
          simp only [chainMeasure, hP]
          ring

/-! ### Band weights -/

/-! ### The ghost bound -/

/-- **The ghost bound on the chain states** (PD `mem:ghost-norm`): there is a `C₀`, depending
only on `q` and `K`, such that eventually every choice operator with the ghost output and
coefficients bounded by those of a ghost `𝒢_j` with `N = 2R` has norm at most `C₀` for the
chain measure. Here `v₀ = (K + 1)/(ρ (1 - ρ²))`, the hitting particles carry
`∑ |cre| ν ≤ 2K/ρ` and `∑ ν ≤ 4K`, and `|del| ≤ 1/ρ`. -/
theorem exists_ghostChoiceOp_normLe {q C CX alo ahi g : ℝ} (hq : 0 < q) (hq₁ : q < 1)
    (halo : 1 / 10 < alo) :
    ∃ C₀ : ℝ, ∀ᶠ x : ℝ in atTop, ∀ d : Data K, Admissible C CX alo ahi g x d →
      ∀ (Y d₀ u v r : ℝ) (B j : ℕ) (a : ChainState x d Y d₀ u v r B → GhostChoice x d → ℂ),
        (∀ s c, ‖a s c‖ ≤ ‖chainGhostCoef q x d Y d₀ u v r B (2 * momentPower x) j s c‖) →
        NormLe (fun s => chainMeasure q x d Y d₀ u v r B (2 * momentPower x) s)
          (fun s => chainMeasure q x d Y d₀ u v r B (2 * momentPower x) s)
          (choiceOp (multBox B ×ˢ multBox B) a (chainGhostOut x d Y d₀ u v r B)) C₀ := by
  set ρ := pendingWeight q with hρ
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos hq _
  have hρ2 : ρ ^ 2 < 1 := pow_lt_one₀ hρ0.le (Real.rpow_lt_one hq.le hq₁ (by norm_num)) (by norm_num)
  set w := 1 - ρ ^ 2 with hw
  have hw0 : 0 < w := by linarith
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  set v₀ := ((K : ℝ) + 1) / (ρ * w) with hv
  have hv₀ : 0 < v₀ := by positivity
  -- `M/ρ/v₀ ≤ w` for `M ≤ K + 1`
  have hdiv : ∀ M : ℝ, 0 ≤ M → M ≤ K + 1 → M / ρ / v₀ ≤ w := by
    intro M hM0 hM
    rw [div_div, show ρ * v₀ = ((K : ℝ) + 1) / w by rw [hv]; field_simp, div_div_eq_mul_div,
      div_le_iff₀ (by positivity)]
    calc M * w ≤ ((K : ℝ) + 1) * w := mul_le_mul_of_nonneg_right hM hw0.le
      _ = w * ((K : ℝ) + 1) := mul_comm _ _
  refine ⟨Real.sqrt (Real.exp (v₀ * (2 * K / ρ)) * Real.exp (v₀ * (1 / ρ) * (4 * K))), ?_⟩
  filter_upwards [eventually_harmonicMass_band halo.le, eventually_two_mul_add_one_le halo]
    with x hV hbig d hd Y d₀ u v r B j a ha
  set N := 2 * momentPower x with hN
  have hV₀ : d.BandsLower x := fun i => (hV _ (hd.window i).1).1
  have hV₁ := fun i => (hV _ (hd.window i).1).2
  have hb :=
    fun p hp => half_le_baseline hq.le (hbig d hd p hp)
  have hν := primeWeight_nonneg_of_baseline hb
  obtain ⟨hη0, hη1⟩ := dampDefect_mem_Icc hq hq₁ N j
  -- `0 ≤ surv ≤ ρ²`, since `q_j ≤ √q = ρ⁴`
  have hsurv1 : (1 - dampDefect q N j) / ρ ^ 2 ≤ ρ ^ 2 := by
    have hqs : q ≤ Real.sqrt q := by
      have h₁ := Real.mul_self_sqrt hq.le
      have h₂ : Real.sqrt q ≤ 1 := Real.sqrt_le_one.2 hq₁.le
      calc q = Real.sqrt q * Real.sqrt q := h₁.symm
        _ ≤ Real.sqrt q * 1 := mul_le_mul_of_nonneg_left h₂ (Real.sqrt_nonneg q)
        _ = Real.sqrt q := mul_one _
    have hqj : 1 - dampDefect q N j ≤ ρ ^ 4 := by
      rw [hρ, pendingWeight_pow_four hq]
      unfold dampDefect
      split_ifs <;> linarith
    rw [div_le_iff₀ (by positivity)]
    calc 1 - dampDefect q N j ≤ ρ ^ 4 := hqj
      _ = ρ ^ 2 * ρ ^ 2 := by ring
  -- `|del| ≤ 1/ρ`, and `|cre| ν ≤ (2/ρ)(1/p)`, `|cre| ≤ K/ρ` at the band primes
  have hdel : |-dampDefect q N j / ρ| ≤ 1 / ρ := by
    rw [abs_div, abs_neg, abs_of_nonneg hη0, abs_of_pos hρ0]
    exact div_le_div_of_nonneg_right hη1 hρ0.le
  have hcre : ∀ p, |-dampDefect q N j * primeMass x d p / ρ| =
      dampDefect q N j / ρ * primeMass x d p := by
    intro p
    rw [abs_div, abs_mul, abs_neg, abs_of_nonneg hη0, abs_of_nonneg (primeMass_nonneg p),
      abs_of_pos hρ0]
    ring
  have hη : dampDefect q N j / ρ ≤ 1 / ρ := div_le_div_of_nonneg_right hη1 hρ0.le
  have hη' : 0 ≤ dampDefect q N j / ρ := div_nonneg hη0 hρ0.le
  refine normLe_ghostChoiceOp ha hν (div_nonneg (by linarith) (by positivity)) hv₀ ?_ (fun xp => ?_) (fun z => ?_) (fun z => ?_)
  · calc (1 - dampDefect q N j) / ρ ^ 2 + |-dampDefect q N j / ρ| / v₀
        ≤ ρ ^ 2 + 1 / ρ / v₀ := add_le_add hsurv1 (div_le_div_of_nonneg_right hdel hv₀.le)
      _ ≤ ρ ^ 2 + w := add_le_add le_rfl (hdiv 1 zero_le_one (by linarith))
      _ = 1 := by rw [hw]; ring
  · have hcreK : |-dampDefect q N j * primeMass x d xp.1.1 / ρ| ≤ K / ρ := by
      rw [hcre]
      calc dampDefect q N j / ρ * primeMass x d xp.1.1 ≤ 1 / ρ * K :=
            mul_le_mul hη (primeMass_le hV₁ _) (primeMass_nonneg _) (by positivity)
        _ = K / ρ := by ring
    calc (1 - dampDefect q N j) / ρ ^ 2 + |-dampDefect q N j * primeMass x d xp.1.1 / ρ| / v₀
        ≤ ρ ^ 2 + K / ρ / v₀ := add_le_add hsurv1 (div_le_div_of_nonneg_right hcreK hv₀.le)
      _ ≤ ρ ^ 2 + w := add_le_add le_rfl (hdiv K hK0 (by linarith))
      _ = 1 := by rw [hw]; ring
  · refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ hv₀.le)
    calc ∑ xp with HitsAt x d z xp,
          |-dampDefect q N j * primeMass x d xp.1.1 / ρ| * primeWeight q x d N xp.1.1
        ≤ ∑ xp with HitsAt x d z xp, 2 / ρ * (1 / (xp.1.1 : ℝ)) := by
          refine sum_le_sum fun xp _ => ?_
          have h := (primeWeight_le hV₀ hb (particle_mem_bandPrimes xp)).2
          rw [hcre]
          calc dampDefect q N j / ρ * primeMass x d xp.1.1 * primeWeight q x d N xp.1.1
              = dampDefect q N j / ρ * (primeMass x d xp.1.1 * primeWeight q x d N xp.1.1) :=
                mul_assoc _ _ _
            _ ≤ 1 / ρ * (2 * (1 / (xp.1.1 : ℝ))) :=
                mul_le_mul hη h (mul_nonneg (primeMass_nonneg _) (hν _)) (by positivity)
            _ = 2 / ρ * (1 / (xp.1.1 : ℝ)) := by ring
      _ ≤ ∑ p ∈ bandPrimes x d, 2 / ρ * (1 / (p : ℝ)) :=
          sum_hits_le_sum_bandPrimes z (f := fun p => 2 / ρ * (1 / (p : ℝ))) fun p => by positivity
      _ = 2 / ρ * ∑ p ∈ bandPrimes x d, (1 : ℝ) / p := (mul_sum _ _ _).symm
      _ ≤ 2 / ρ * K := mul_le_mul_of_nonneg_left (sum_one_div_bandPrimes_le hV₁) (by positivity)
      _ = 2 * K / ρ := by ring
  · refine Real.exp_le_exp.2 (mul_le_mul (mul_le_mul_of_nonneg_left hdel hv₀.le) ?_
      (sum_nonneg fun xp _ => hν _) (by positivity))
    calc ∑ xp with HitsAt x d z xp, primeWeight q x d N xp.1.1
        ≤ ∑ xp with HitsAt x d z xp, 4 * (1 / (xp.1.1 : ℝ)) :=
          sum_le_sum fun xp _ => (primeWeight_le hV₀ hb (particle_mem_bandPrimes xp)).1
      _ ≤ ∑ p ∈ bandPrimes x d, 4 * (1 / (p : ℝ)) :=
          sum_hits_le_sum_bandPrimes z (f := fun p => 4 * (1 / (p : ℝ))) fun p => by positivity
      _ = 4 * ∑ p ∈ bandPrimes x d, (1 : ℝ) / p := (mul_sum _ _ _).symm
      _ ≤ 4 * K := mul_le_mul_of_nonneg_left (sum_one_div_bandPrimes_le hV₁) (by norm_num)

end Ghost

end Erdos408.OneSided
