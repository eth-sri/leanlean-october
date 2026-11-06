module

public import Mathlib.Tactic
public import ImprovedExponents.Cost8X.Dominated
public import ImprovedExponents.Optimum.PerCBasic
public import ImprovedExponents.Pipeline.Fits
public import ImprovedExponents.PrunedEncoding.Counts
public import ThreeSumApsp.Sec2.Orders
import all ThreeSumApsp.Sec4.Corollary31

@[expose] public section

/-!
# The cost of the method with pruned encodings

The second summand `N 10^L/(√K N₀)` of the paper's expression (8) (and of `cost8X`) is the cost of
encoding the input arrays of the `≈ N/(√K N₀)` bands: all `10^L` leaves for each band. The pruned
Yates recursion of `ImprovedExponents.PrunedEncoding.Pruned` computes the entries that the method
reads with at most `(27/2) M/(1 - ρ)` multiplications (`prunedMults_le_M`), each with `L` index
operations. This gives the preprocessing cost

  `cost8P L m t N := L m tailX(L, m, t) N² + N L (27/2) M/(1 - ρ)/(√K N₀)`,

whose second summand is `(27/2) N L √K N₀/(1 - ρ)`, as `M = (√K N₀)²` (`encodingP_eq`).

With `L = ⌈cm⌉`, `√K N₀ ≤ e^{m A(L/m)}` for `A(c) = (c/2) H(1/c) + (c - 1) ln 3` (`basePruned`).
So `D^γ L √K N₀ ≤ N` for all large `m` as soon as `ε < R'_c(γ) = ln 4/(A(c) + γ ln 4)` (`RcP`,
`eq_10P`); this takes the place of the paper's inequality (10), which needs `ε < R_c(γ)`.
`costsP` is the analogue of `costsX` with `cost8P` and `R'_c`. The new bound is weaker than the
paper's: `R_c(γ) ≤ R'_c(γ)` (`Rc_le_RcP`), because `A(c) ≤ ln Λ` at `γ = 0`
(`basePruned_le_baseFull`), which is the limit form of `M ≤ 10^L`.
-/

namespace ImprovedExponents

open ThreeSumApsp Real

open private levelsOf_le from ThreeSumApsp.Sec4.Corollary31

/-! ### The cost -/

/-- The preprocessing cost with pruned encodings:
`L m tailX(L, m, t) N² + N L (27/2) M/(1 - ρ)/(√K N₀)`. The first summand is that of `cost8X`;
the second has the `(27/2) M/(1 - ρ)` multiplications of the pruned recursion, with `L` index
operations each, in the place of the `10^L` leaves of a band. -/
noncomputable def cost8P (L m t N : ℕ) :=
  (L : ℝ) * (m : ℝ) * tailX L m t * (N : ℝ) ^ 2
    + (N : ℝ) * (L : ℝ) * (27 / 2 * (M L m : ℝ) / (1 - rho L m)) / sqrtKN0 L m

/-- The second summand of `cost8P` is `(27/2) N L √K N₀/(1 - ρ)`, because `M = (√K N₀)²`. -/
theorem encodingP_eq {L m : ℕ} (hmL : m ≤ L) (N : ℕ) :
    (N : ℝ) * (L : ℝ) * (27 / 2 * (M L m : ℝ) / (1 - rho L m)) / sqrtKN0 L m
      = 27 / 2 * (N : ℝ) * ((L : ℝ) * sqrtKN0 L m) / (1 - rho L m) := by
  grind [sqrtKN0_sq]

/-! ### The two thinness bounds -/

/-! ### The encodings fit: the analogue of inequality (10) -/

/-- The analogue of inequality (10) for pruned encodings: `D^γ · L √K N₀ ≤ N` at `L = ⌈cm⌉`, for
every exponent `γ ≥ 0` and `0 < ε < R'_c(γ)`, once `m` exceeds a constant. Here `D₀` is the
original inner dimension with `4^{m-1} < D₀ ≤ N^ε`, and `D` is the padded `4^m`. -/
theorem eq_10P {c γ ε} (hc : 10 < c) (hγ : 0 ≤ γ) (hε0 : 0 < ε) (hε : ε < RcP c γ) :
    ∃ m₀ : ℕ, ∀ m , m₀ ≤ m → ∀ D₀ N : ℕ, 4 ^ (m - 1) < D₀ → D₀ ≤ (N : ℝ) ^ ε →
      D m ^ γ * (levelsOf c m * sqrtKN0 (levelsOf c m) m) ≤ N := by


  have hε' := hε
  -- `ε < R'_c(γ)` says that `A(c) + γ ln 4 < ln 4/ε =: G`
  set G : ℝ := log 4 / ε with hGdef
  have  : basePruned c + γ * log 4 < G := by
    rw [hGdef, lt_div_iff₀ hε0]
    have := (lt_div_iff₀ (thinR_den_pos (basePruned_pos (by linarith) : 0 < basePruned c) hγ)).1 hε'
    linarith
  -- a constant `B > A(c)` with `B + γ ln 4 < G`, and the room `η` that is left
  set B : ℝ := (basePruned c + (G - γ * log 4)) / 2 with hBdef

  set η : ℝ := G - γ * log 4 - B with hηdef
  have hη : 0 < η := by rw [hηdef, hBdef]; linarith
  -- near `c` the constant stays below `B`
  have hcont :=
    basePruned_continuousOn.continuousAt (Ioi_mem_nhds hc)
  obtain ⟨δ₀, hδ₀, hnear⟩ := Metric.eventually_nhds_iff.1
    (hcont.eventually (gt_mem_nhds (by rw [hBdef]; linarith : basePruned c < B)))
  refine ⟨max 1 max ⌈1 / δ₀⌉₊ ⌈2 * (c + 1) * exp G / η ^ 2⌉₊,
    fun m hm D₀ N hgt hthin => ?_⟩
  have hm1 := (le_max_left _ _).trans hm
  have hm0 : (0 : ℝ) < m := mod_cast hm1

  have hmη : 2 * (c + 1) * exp G / η ^ 2 ≤ (m : ℝ) := (Nat.le_ceil _).trans
    (by simp_all)
  -- the levels: `c ≤ L/m < c + δ₀`
  -- adapted from `ImprovedExponents/Pipeline/Fits.lean` (`exists_fits18`)
  have  : c * m ≤ (levelsOf c m : ℝ) := Nat.le_ceil _
  have  : (levelsOf c m : ℝ) < c * m + 1 := Nat.ceil_lt_add_one (by positivity)
  have hmL : m < levelsOf c m := by
    have h : (m : ℝ) < (levelsOf c m : ℝ) := by nlinarith
    exact_mod_cast h
  have  : c ≤ (levelsOf c m : ℝ) / m := by rwa [le_div_iff₀ hm0]
  have  : (levelsOf c m : ℝ) / m < c + δ₀ := by
    rw [div_lt_iff₀ hm0]
    have : 1 ≤ δ₀ * m := by
      have := (div_le_iff₀ hδ₀).1 ((Nat.le_ceil _).trans
        (by simp_all)
       : 1 / δ₀ ≤ (m : ℝ))
      linarith
    nlinarith

  have  := levelsOf_le hc hm1
  have  :=
    (sqrtKN0_le_exp hm1 hmL).trans (exp_le_exp.2 (mul_le_mul_of_nonneg_left (by
      grind [Real.dist_eq]
     : basePruned (levelsOf c m / m) < B).le hm0.le))
  -- `N ≥ 4^{(m-1)/ε} = e^{(m-1) G}`
  have hN := by
    have h := Corollary31.hypothesis hm1 hε0 hgt hthin
    rwa [rpow_def_of_pos (by norm_num),
      show log 4 * (((m : ℝ) - 1) / ε) = ((m : ℝ) - 1) * (log 4 / ε) by ring] at h
  -- the room `η` pays for the factor `L ≤ (c + 1) m` and for `e^G`

  have hE : exp (γ * (m * log 4)) * exp (m * B)
      = exp G * exp (m * (B + γ * log 4) - G) := by
    rw [← exp_add, ← exp_add]
    congr 1
    ring
  calc (D m : ℝ) ^ γ * ((levelsOf c m : ℝ) * sqrtKN0 (levelsOf c m) m)
      ≤ exp (γ * (m * log 4)) * ((c + 1) * m * exp (m * B)) := by
        grind [cast_D_rpow, mul_le_mul_of_nonneg_left, mul_le_mul, sqrtKN0_pos, exp_pos]
    _ = (c + 1) * m * (exp (γ * (m * log 4)) * exp (m * B)) := by ring
    _ = (c + 1) * m * exp G * exp (m * (B + γ * log 4) - G) := by
        rw [hE]
        ring
    _ ≤ exp (m * η) * exp (m * (B + γ * log 4) - G) :=
        mul_le_mul_of_nonneg_right (by
          have  := quadratic_le_exp_of_nonneg (mul_nonneg hm0.le hη.le)

          have  := mul_le_mul_of_nonneg_left (by
            have := (div_le_iff₀ (pow_pos hη 2)).1 hmη
            linarith
           : 2 * (c + 1) * exp G ≤ (m : ℝ) * η ^ 2) hm0.le
          have  := mul_nonneg hm0.le hη.le
          linarith
        ) (exp_pos _).le
    _ = exp ((m - 1) * G) := by
        rw [← exp_add, hηdef]
        congr 1
        ring
    _ ≤ (N : ℝ) := hN

/-! ### The two terms together -/

/-- `cost8P` is `O(N² log² D/D^γ)`, in the given `D`, wherever `D^γ L √K N₀ ≤ N` holds with the
exponent `γ < γX(c, θ)`. This takes the place of `dominated_cost8X`. -/
theorem dominated_cost8P {c θ γ} (hc : 10 < c) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hγ : γ < gammaX c θ) {dom : Sizes → Prop} (hset : ∀ p, dom p → p.SetUp)
    (h10 : ∀ p, dom p →
      (D p.m : ℝ) ^ γ * ((levelsOf c p.m : ℝ) * sqrtKN0 (levelsOf c p.m) p.m) ≤ p.N) :
    Dominated dom (fun p => cost8P (levelsOf c p.m) p.m (switchOf θ p.m) p.N)
      fun p => p.N ^ 2 * Real.log p.D₀ ^ 2 / p.D₀ ^ γ := by
  have hρ := rhoC_lt_one hc
  -- the first term, with its factor `N²`
  have hboxes :=
    ((first_termX hc hθ0 hθ1 hγ).comp Sizes.m fun p hp => (hset p hp).m_pos).mul_right
      (k := fun p => (p.N : ℝ) ^ 2) fun _ _ => sq_nonneg _
  -- the encodings
  have hencodings : Dominated dom
      (fun p => p.N * levelsOf c p.m
        * (27 / 2 * M (levelsOf c p.m) p.m / (1 - rho (levelsOf c p.m) p.m))
        / sqrtKN0 (levelsOf c p.m) p.m)
      fun p => D p.m ^ (-γ) * Real.log (D p.m) ^ 2 * p.N ^ 2 := by
    refine .of_le_const_mul (C := 27 / 2 / (1 - rhoC c))
      (div_nonneg (by norm_num) (sub_pos.2 hρ).le) fun p hp => ?_

    have hmL : p.m ≤ levelsOf c p.m := by grind [ten_mul_le_levelsOf]
    have  := Corollary31.rho_lt hc p.m

    have hLs0 : 0 ≤ (levelsOf c p.m : ℝ) * sqrtKN0 (levelsOf c p.m) p.m :=
      mul_nonneg (Nat.cast_nonneg _) (sqrtKN0_pos hmL).le
    have hLs : (levelsOf c p.m : ℝ) * sqrtKN0 (levelsOf c p.m) p.m
        ≤ (D p.m : ℝ) ^ (-γ) * p.N := by
      rw [rpow_neg (cast_D_pos p.m).le, inv_mul_eq_div, le_div_iff₀ (rpow_pos_of_pos (cast_D_pos p.m) γ), mul_comm]
      exact h10 p hp
    have hlog : (1 : ℝ) ≤ Real.log (D p.m) ^ 2 :=
      one_le_pow₀ ((Nat.one_le_cast.2 ((hset p hp).m_pos)).trans (cast_le_log_cast_D p.m))

    rw [encodingP_eq hmL]
    calc 27 / 2 * (p.N : ℝ) * ((levelsOf c p.m : ℝ) * sqrtKN0 (levelsOf c p.m) p.m)
          / (1 - rho (levelsOf c p.m) p.m)
        ≤ 27 / 2 * (p.N : ℝ) * ((levelsOf c p.m : ℝ) * sqrtKN0 (levelsOf c p.m) p.m)
          / (1 - rhoC c) :=
          div_le_div_of_nonneg_left (mul_nonneg (by positivity) hLs0) (sub_pos.2 hρ)
            (by linarith)
      _ ≤ 27 / 2 * (p.N : ℝ) * ((D p.m : ℝ) ^ (-γ) * p.N) / (1 - rhoC c) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hLs (by positivity))
            (sub_pos.2 hρ).le
      _ = 27 / 2 / (1 - rhoC c) * ((D p.m : ℝ) ^ (-γ) * 1 * (p.N : ℝ) ^ 2) := by ring
      _ ≤ 27 / 2 / (1 - rhoC c)
            * ((D p.m : ℝ) ^ (-γ) * Real.log (D p.m) ^ 2 * (p.N : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hlog (rpow_nonneg (Nat.cast_nonneg _) _)) (sq_nonneg _))
            (div_nonneg (by norm_num) (sub_pos.2 hρ).le)
  have hpadded :=
    hboxes.add hencodings
  refine (hpadded.trans (((padded_le (-γ) 2).mono_dom hset).mul_right
    fun _ _ => sq_nonneg _)).congr (fun _ _ => rfl) fun p _ => ?_
  rw [Real.rpow_neg (Nat.cast_nonneg _)]
  ring

/-- **The cost bounds with pruned encodings**, for all large `m`. For `c > 10`, `0 < θ < 0.9`,
`0 ≤ γ < γX(c, θ)` and `0 < ε < R'_c(γ)` there are a constant `C` and a threshold `m₀` such that
for all `2 ≤ D ≤ N^ε` with `m = ⌈log_4 D⌉ ≥ m₀`, `L = ⌈cm⌉`, `t = ⌈θm⌉`: the hypothesis
`N ≥ √K N₀` of Theorem 30 holds, `cost8P` is at most `C N² log² D/D^γ`, and the query cost is at
most `C D^q log D`. This is `costsX` with pruned encodings: `cost8P` in the place of `cost8X` and
the thinness bound `R'_c` in the place of `R_c`. -/
theorem costsP {c θ γ ε} (hc : 10 < c) (hθ0 : 0 < θ) (hθ1 : θ < 0.9) (hγ0 : 0 ≤ γ)
    (hγ : γ < gammaX c θ) (hε0 : 0 < ε) (hε : ε < RcP c γ) :
    ∃ (C : ℝ) (m₀ : ℕ), 0 ≤ C ∧ ∀ D₀ N m : ℕ, 2 ≤ D₀ → D₀ ≤ (N : ℝ) ^ ε →
      m = ⌈Real.logb 4 D₀⌉₊ → m₀ ≤ m →
      sqrtKN0 (levelsOf c m) m ≤ N ∧
      cost8P (levelsOf c m) m (switchOf θ m) N
        ≤ C * (N ^ 2 * Real.log D₀ ^ 2 / D₀ ^ γ) ∧
      costQuery (levelsOf c m) m (switchOf θ m) ≤ C * (D₀ ^ qOf θ * Real.log D₀) := by
  obtain ⟨m₀, heq10⟩ := eq_10P hc hγ0 hε0 hε
  -- the encodings fit for the instances from the threshold on
  have h10 : ∀ p : Sizes, p.Corollary31 ε m₀ →
      (D p.m : ℝ) ^ γ * ((levelsOf c p.m : ℝ) * sqrtKN0 (levelsOf c p.m) p.m) ≤ p.N :=
    fun p hp => heq10 p.m hp.large p.D₀ p.N ((Corollary26.setting_up p.D₀ p.m hp.setUp.two_le hp.setUp.m_eq).right.right : 4 ^ (p.m - 1) < p.D₀) hp.thin

  have hquery : Dominated (Sizes.Corollary31 ε m₀)
      (fun p => costQuery (levelsOf c p.m) p.m (switchOf θ p.m))
      fun p => p.D₀ ^ qOf θ * Real.log p.D₀ :=
    (((Corollary31.query_cost hc hθ0 hθ1).comp Sizes.m fun _ (hp : Sizes.SetUp _) => hp.m_pos).trans
      (by simpa only [pow_one] using padded_le (qOf θ) 1)).mono_dom fun p hp => hp.setUp
  obtain ⟨C, hC, hboth⟩ := (dominated_cost8P hc hθ0.le (by linarith) hγ
    (fun p (hp : p.Corollary31 ε m₀) => hp.setUp) h10
  ).exists_const_and hquery
    (fun p _ => div_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    fun p hp => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (Real.log_nonneg (Nat.one_le_cast.2 (one_le_two.trans hp.setUp.two_le)))
  refine ⟨C, m₀, hC, fun D₀ N m hD hDN hm hm₀ => ?_⟩
  have hp : Sizes.Corollary31 ε m₀ ⟨D₀, N, m⟩ := ⟨⟨hD, hm⟩, hDN, hm₀⟩
  have  : 1 ≤ m := hp.setUp.m_pos
  have  := ten_mul_le_levelsOf hc m
  -- `√K N₀ ≤ D^γ L √K N₀ ≤ N`


  have hs : 0 ≤ sqrtKN0 (levelsOf c m) m := (sqrtKN0_pos (by omega)).le
  have hfit :=
    calc sqrtKN0 (levelsOf c m) m
        ≤ (levelsOf c m : ℝ) * sqrtKN0 (levelsOf c m) m := le_mul_of_one_le_left hs (Nat.one_le_cast.2 (by omega))
      _ ≤ (D m : ℝ) ^ γ * ((levelsOf c m : ℝ) * sqrtKN0 (levelsOf c m) m) :=
          le_mul_of_one_le_left (mul_nonneg (by positivity) hs) (Real.one_le_rpow (one_le_cast_D m) hγ0)
      _ ≤ N := h10 ⟨D₀, N, m⟩ hp
  exact ⟨hfit, hboth ⟨D₀, N, m⟩ hp⟩

end ImprovedExponents
