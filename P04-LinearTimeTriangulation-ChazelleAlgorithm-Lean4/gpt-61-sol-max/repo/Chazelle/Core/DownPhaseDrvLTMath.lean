module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.DownPhaseDrvLMMain
public import Chazelle.Core.DownPhaseDrvRTailSpec
public import Chazelle.Core.DownPhaseDrvLCMain

/-!
# Down-phase level tail (D12), part 1: the arithmetic

* `le_lvNch`: a kept list has at most `lvNch μ` triples (`LevelMathSpec` (3));
* `flat_length_le`: the gathered list has at most `R M` triples;
* **`i3_step`**: (I3) at `μ = nextLvl λ` for the count `lvCnt`, from (I3) at `λ`, the count of
  the spliced list (`LevelMathSpec` (4)) and the rounds (`K' + 1 ≤ 2^(regCap+4) (K₁ + 1)`)
  (`DownMath.level_bound`, `DownMath.cnt_step`).
-/

namespace Chazelle.Core

namespace DrvLT

@[expose] public section

/-- A kept list has at most `lvNch μ` triples. -/
theorem le_lvNch {μ ℓ : ℕ} (h : ℓ * (3 * 2 ^ (Cost.ceilBeta μ + 10) + 1) ≤
    140 * (DrvR.regCap + 2) * (20 * 2 ^ μ + 17)) : ℓ ≤ DrvR.lvNch μ := by
  unfold DrvR.lvNch
  exact (Nat.le_div_iff_mul_le (by positivity)).2 h

section
variable (Lx : ℕ → List (ℕ × ℕ × ℕ))
/-- The gathered list has at most `R M` triples. -/
theorem flat_length_le (R M : ℕ)
    (h : ∀ r, r < R → (Lx r).length ≤ M) : ((List.range R).flatMap Lx).length ≤ R * M := by
  rw [DrvLM.length_flatMap_range]
  calc ∑ r ∈ Finset.range R, (Lx r).length ≤ ∑ r ∈ Finset.range R, M :=
        Finset.sum_le_sum fun r hr => h r (Finset.mem_range.1 hr)
    _ = R * M := by simp

/-- A prefix of the gathered list is no longer than the list. -/
theorem flat_length_mono {j R : ℕ} (h : j ≤ R) :
    ((List.range j).flatMap Lx).length ≤ ((List.range R).flatMap Lx).length := by
  rw [DrvLM.length_flatMap_range, DrvLM.length_flatMap_range]
  exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 h)

/-- The gathered list grows by one kept list. -/
theorem flat_succ (j : ℕ) :
    (List.range (j + 1)).flatMap Lx = (List.range j).flatMap Lx ++ Lx j := by
  grind [List.range_succ, List.flatMap_append]


end

/-- **(I3) at the next level.** -/
theorem i3_step {lam K K₁ K' n p γ₀ : ℕ} (h16 : 16 ≤ lam) (hlp : lam ≤ p)
    (hK : K * 2 ^ Cost.ceilBeta lam ≤ DrvR.lvCnt lam * (2 ^ p + 2 ^ Cost.ceilBeta lam))
    (hn : n ≤ 2 ^ p + 1) (hγ : γ₀ = 3 * 2 ^ (Cost.ceilBeta (DrvR.nextLvl lam) + 10))
    (h1 : K₁ * (γ₀ + 1) ≤ K * (γ₀ + 1) + 1120 * (DrvR.regCap + 2) * (n + 4 * K))
    (h2 : K' + 1 ≤ 2 ^ (DrvR.regCap + 4) * (K₁ + 1)) :
    K' * 2 ^ Cost.ceilBeta (DrvR.nextLvl lam) ≤
      DrvR.lvCnt (DrvR.nextLvl lam) * (2 ^ p + 2 ^ Cost.ceilBeta (DrvR.nextLvl lam)) := by
  have hG : 2 ^ Cost.ceilBeta (Cost.ceilBeta lam + 11) ≤ γ₀ + 1 := by
    grind [DrvR.nextLvl]
  exact DownMath.cnt_step (A := 2 ^ (DrvR.regCap + 4)) (B := 1120 * (DrvR.regCap + 2))
    (Nat.one_le_two_pow) h16 hlp hK hn hG (DownMath.level_bound h1 h2)

/-- **The cost of the tail** against the budget `κ (K + 1) (lemma41Nat μ + 1)`: the gather (with
the reservation), the splice, the rounds, with `|Lx r| ≤ M ≤ ν = lvNch μ` and the three bounds of
`LvCostSpec`. -/
theorem cost_le {R K K₂ M ν Λ κc κS κr X : ℕ} (hR : R = K + 1) (hK₂ : K₂ ≤ R * M) (hM : M ≤ ν)
    (hΛ : 1 ≤ Λ) (h1 : ν ≤ κc * Λ) (h2 : (ν + 1) * (Nat.clog 2 (4 * ν + 4) + 1) ≤ κc * Λ)
    (h3 : (ν + 1) * X ≤ κc * Λ) :
    (8 * K₂ + (35 * M + 32) * R + 26) + (5 * K₂ + 1) +
      κS * (K + K₂ + (4 * K + 3) + 1) * (Nat.clog 2 (4 * M) + 1) + 2 +
        κr * (K + K₂ + 1) * X ≤
      (300 + 48 * κc + 5 * κS * κc + κr * κc) * R * Λ := by
  have hRν : K₂ ≤ R * ν := hK₂.trans (Nat.mul_le_mul_left _ hM)
  have hMR : M * R ≤ R * ν := by simp_all [Nat.mul_comm] <;> omega_nf
  have hz : R * ν ≤ κc * (R * Λ) := by
    calc R * ν ≤ R * (κc * Λ) := Nat.mul_le_mul_left _ h1
      _ = κc * (R * Λ) := by ring
  have hy : R ≤ R * Λ := Nat.le_mul_of_pos_right _ hΛ
  
  -- the gather
  
  -- the splice
  have hc : Nat.clog 2 (4 * M) + 1 ≤ Nat.clog 2 (4 * ν + 4) + 1 :=
    Nat.add_le_add_right (Nat.clog_mono_right 2 (by omega)) 1
  have hs1 : K + K₂ + (4 * K + 3) + 1 ≤ 5 * (R * (ν + 1)) := by
    ring_nf <;> omega
  have hs : κS * (K + K₂ + (4 * K + 3) + 1) * (Nat.clog 2 (4 * M) + 1) ≤
      5 * κS * κc * (R * Λ) := by
    calc κS * (K + K₂ + (4 * K + 3) + 1) * (Nat.clog 2 (4 * M) + 1)
        ≤ κS * (5 * (R * (ν + 1))) * (Nat.clog 2 (4 * ν + 4) + 1) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ hs1) hc
      _ = 5 * κS * R * ((ν + 1) * (Nat.clog 2 (4 * ν + 4) + 1)) := by ring
      _ ≤ 5 * κS * R * (κc * Λ) := Nat.mul_le_mul_left _ h2
      _ = 5 * κS * κc * (R * Λ) := by ring
  -- the rounds
  have hr1 : K + K₂ + 1 ≤ R * (ν + 1) := by
    ring_nf <;> omega
  have hr : κr * (K + K₂ + 1) * X ≤ κr * κc * (R * Λ) := by
    calc κr * (K + K₂ + 1) * X ≤ κr * (R * (ν + 1)) * X :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hr1)
      _ = κr * R * ((ν + 1) * X) := by ring
      _ ≤ κr * R * (κc * Λ) := Nat.mul_le_mul_left _ h3
      _ = κr * κc * (R * Λ) := by ring
  grind

/-- The word bounds the tail needs below its budget. -/
theorem room_small {R K M ν Λ κc κS κr : ℕ} (hR : R = K + 1) (hM : M ≤ ν) (hΛ : 1 ≤ Λ)
    (h1 : ν ≤ κc * Λ) :
    134 ≤ (300 + 48 * κc + 5 * κS * κc + κr * κc) * R * Λ ∧
      4 * K + 3 ≤ (300 + 48 * κc + 5 * κS * κc + κr * κc) * R * Λ ∧
      4 * M ≤ (300 + 48 * κc + 5 * κS * κc + κr * κc) * R * Λ := by
  have hy : R ≤ R * Λ := Nat.le_mul_of_pos_right _ hΛ
  have hz : M ≤ κc * (R * Λ) := by
    calc M ≤ κc * Λ := hM.trans h1
      _ ≤ κc * (R * Λ) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega))
  ram_grind

end

end DrvLT

end Chazelle.Core
