module

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

  `cost8P L m t N := L m tailX(L, m, t) N² + (27/2) N L √K N₀/(1 - ρ)`,

using `M = (√K N₀)²`.

With `L = ⌈cm⌉`, `√K N₀ ≤ e^{m A(L/m)}` for `A(c) = (c/2) H(1/c) + (c - 1) ln 3` (`basePruned`).
So `D^γ L √K N₀ ≤ N` for all large `m` as soon as `ε < R'_c(γ) = ln 4/(A(c) + γ ln 4)` (`RcP`,
`eq_10P`); this takes the place of the paper's inequality (10), which needs `ε < R_c(γ)`.
`costsP` is the analogue of `costsX` with `cost8P` and `R'_c`. The new bound is weaker than the
paper's: `R_c(γ) ≤ R'_c(γ)` (`Rc_le_RcP`), because `A(c) ≤ ln Λ` at `γ = 0`
(`basePruned_le_baseFull`), which is the limit form of `M ≤ 10^L`.
-/

namespace ImprovedExponents

open ThreeSumApsp Real

/-! ### The cost -/

/-- The first summand pays for the boxes and the second for the pruned encodings. -/
noncomputable def cost8P (L m t N : ℕ) : ℝ :=
  (L : ℝ) * m * tailX L m t * (N : ℝ) ^ 2
    + 27 / 2 * ((N : ℝ) * ((L : ℝ) * sqrtKN0 L m)) / (1 - rho L m)

/-! ### The encodings fit: the analogue of inequality (10) -/

/-- The analogue of inequality (10) for pruned encodings: `D^γ · L √K N₀ ≤ N` at `L = ⌈cm⌉`, for
every exponent `γ ≥ 0` and `0 < ε < R'_c(γ)`, once `m` exceeds a constant. Here `D₀` is the
original inner dimension with `4^{m-1} < D₀ ≤ N^ε`, and `D` is the padded `4^m`. -/
theorem eq_10P {c γ ε : ℝ} (hc : 10 < c) (hγ : 0 ≤ γ) (hε0 : 0 < ε) (hε : ε < RcP c γ) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ D₀ N : ℕ, 4 ^ (m - 1) < D₀ → (D₀ : ℝ) ≤ (N : ℝ) ^ ε →
      (D m : ℝ) ^ γ * ((levelsOf c m : ℝ) * sqrtKN0 (levelsOf c m) m) ≤ (N : ℝ) := by
  have hden := thinR_den_pos (basePruned_pos (by linarith : 1 < c)) hγ
  apply Filter.eventually_atTop.mp (eventually_tile_bound hc hε0 ?_)
  exact (lt_div_iff₀ hε0).2 (mul_comm ε _ ▸ (lt_div_iff₀ hden).1 hε)

/-! ### The two terms together -/

/-- `cost8P` is `O(N² log² D/D^γ)`, in the given `D`, wherever `D^γ L √K N₀ ≤ N` holds with the
exponent `γ < γX(c, θ)`. This takes the place of `dominated_cost8X`. -/
theorem dominated_cost8P {c θ γ : ℝ} (hc : 10 < c) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hγ : γ < gammaX c θ) {dom : Sizes → Prop} (hset : ∀ p, dom p → p.SetUp)
    (h10 : ∀ p, dom p →
      (D p.m : ℝ) ^ γ * ((levelsOf c p.m : ℝ) * sqrtKN0 (levelsOf c p.m) p.m) ≤ p.N) :
    Dominated dom (fun p => cost8P (levelsOf c p.m) p.m (switchOf θ p.m) p.N)
      fun p => (p.N : ℝ) ^ 2 * Real.log p.D₀ ^ 2 / (p.D₀ : ℝ) ^ γ := by
  have hρ : rhoC c < 1 := rhoC_lt_one hc
  -- the first term, with its factor `N²`
  have hboxes : Dominated dom
      (fun p => (levelsOf c p.m : ℝ) * p.m * tailX (levelsOf c p.m) p.m (switchOf θ p.m)
        * (p.N : ℝ) ^ 2)
      fun p => (D p.m : ℝ) ^ (-γ) * Real.log (D p.m) ^ 2 * (p.N : ℝ) ^ 2 :=
    ((first_termX hc hθ0 hθ1 hγ).comp Sizes.m fun p hp => (hset p hp).m_pos).mul_right
      (k := fun p => (p.N : ℝ) ^ 2) fun _ _ => sq_nonneg _
  have hencodings : Dominated dom
      (fun p => 27 / 2 * ((p.N : ℝ) * ((levelsOf c p.m : ℝ) * sqrtKN0 (levelsOf c p.m) p.m))
        / (1 - rho (levelsOf c p.m) p.m))
      fun p => (D p.m : ℝ) ^ (-γ) * Real.log (D p.m) ^ 2 * (p.N : ℝ) ^ 2 := by
    refine .of_le_const_mul (C := 27 / 2 / (1 - rhoC c))
      (div_nonneg (by norm_num) (sub_pos.2 hρ).le) fun p hp => ?_
    have hmL : p.m ≤ levelsOf c p.m := by have := ten_mul_le_levelsOf hc p.m; omega
    have hrho := Corollary31.rho_lt hc p.m
    have hDγ := rpow_pos_of_pos (cast_D_pos p.m) γ
    have hLs : (levelsOf c p.m : ℝ) * sqrtKN0 (levelsOf c p.m) p.m
        ≤ (D p.m : ℝ) ^ (-γ) * p.N := by
      rw [rpow_neg (cast_D_pos p.m).le, inv_mul_eq_div, le_div_iff₀ hDγ, mul_comm]
      exact h10 p hp
    have hlog : (1 : ℝ) ≤ Real.log (D p.m) ^ 2 :=
      one_le_pow₀ ((Nat.one_le_cast.2 (hset p hp).m_pos).trans (cast_le_log_cast_D p.m))
    calc
      _ ≤ 27 / 2 * ((p.N : ℝ) * ((D p.m : ℝ) ^ (-γ) * p.N)) / (1 - rhoC c) := by
        gcongr <;> linarith
      _ = 27 / 2 / (1 - rhoC c) * ((D p.m : ℝ) ^ (-γ) * 1 * (p.N : ℝ) ^ 2) := by ring
      _ ≤ _ := by gcongr
  have hpadded := hboxes.add hencodings
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
theorem costsP {c θ γ ε : ℝ} (hc : 10 < c) (hθ0 : 0 < θ) (hθ1 : θ < 0.9) (hγ0 : 0 ≤ γ)
    (hγ : γ < gammaX c θ) (hε0 : 0 < ε) (hε : ε < RcP c γ) :
    ∃ (C : ℝ) (m₀ : ℕ), 0 ≤ C ∧ ∀ D₀ N m : ℕ, 2 ≤ D₀ → (D₀ : ℝ) ≤ (N : ℝ) ^ ε →
      m = ⌈Real.logb 4 (D₀ : ℝ)⌉₊ → m₀ ≤ m →
      sqrtKN0 (levelsOf c m) m ≤ N ∧
      cost8P (levelsOf c m) m (switchOf θ m) N
        ≤ C * ((N : ℝ) ^ 2 * Real.log (D₀ : ℝ) ^ 2 / (D₀ : ℝ) ^ γ) ∧
      costQuery (levelsOf c m) m (switchOf θ m) ≤ C * ((D₀ : ℝ) ^ qOf θ * Real.log (D₀ : ℝ)) := by
  obtain ⟨m₀, heq10⟩ := eq_10P hc hγ0 hε0 hε
  -- the encodings fit for the instances from the threshold on
  have h10 : ∀ p : Sizes, p.Corollary31 ε m₀ →
      (D p.m : ℝ) ^ γ * ((levelsOf c p.m : ℝ) * sqrtKN0 (levelsOf c p.m) p.m) ≤ p.N :=
    fun p hp => heq10 p.m hp.large p.D₀ p.N hp.setUp.gt hp.thin
  have hpre := dominated_cost8P hc hθ0.le (by linarith) hγ
    (fun p (hp : p.Corollary31 ε m₀) => hp.setUp) h10
  have hquery : Dominated (Sizes.Corollary31 ε m₀)
      (fun p => costQuery (levelsOf c p.m) p.m (switchOf θ p.m))
      fun p => (p.D₀ : ℝ) ^ qOf θ * Real.log p.D₀ :=
    (((Corollary31.query_cost hc hθ0 hθ1).comp Sizes.m fun _ (hp : Sizes.SetUp _) => hp.m_pos).trans
      (by simpa only [pow_one] using padded_le (qOf θ) 1)).mono_dom fun p hp => hp.setUp
  obtain ⟨C, hC, hboth⟩ := hpre.exists_const_and hquery
    (fun p _ => div_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    fun p hp => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (Real.log_nonneg (Nat.one_le_cast.2 (one_le_two.trans hp.setUp.two_le)))
  refine ⟨C, m₀, hC, fun D₀ N m hD hDN hm hm₀ => ?_⟩
  have hp : Sizes.Corollary31 ε m₀ ⟨D₀, N, m⟩ := ⟨⟨hD, hm⟩, hDN, hm₀⟩
  have hm1 : 1 ≤ m := hp.setUp.m_pos
  have hL10 : 10 * m ≤ levelsOf c m := ten_mul_le_levelsOf hc m
  -- `√K N₀ ≤ D^γ L √K N₀ ≤ N`
  have hD1 : (1 : ℝ) ≤ (D m : ℝ) ^ γ := Real.one_le_rpow (one_le_cast_D m) hγ0
  have hL1 : (1 : ℝ) ≤ (levelsOf c m : ℝ) := Nat.one_le_cast.2 (by omega)
  have hs : 0 ≤ sqrtKN0 (levelsOf c m) m := (sqrtKN0_pos (by omega)).le
  have hfit : sqrtKN0 (levelsOf c m) m ≤ N :=
    calc sqrtKN0 (levelsOf c m) m
        ≤ (levelsOf c m : ℝ) * sqrtKN0 (levelsOf c m) m := le_mul_of_one_le_left hs hL1
      _ ≤ (D m : ℝ) ^ γ * ((levelsOf c m : ℝ) * sqrtKN0 (levelsOf c m) m) :=
          le_mul_of_one_le_left (mul_nonneg (by positivity) hs) hD1
      _ ≤ N := h10 ⟨D₀, N, m⟩ hp
  grind

end ImprovedExponents
