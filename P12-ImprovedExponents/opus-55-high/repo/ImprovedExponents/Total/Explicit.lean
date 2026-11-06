
import ImprovedExponents.Total.Params
import ImprovedExponents.Total.Terms


/-!
# The total time of the reduction, for arbitrary parameters

From the bound of Theorem 17 with the calls charged at the dimension `Dc(n)` (`HostBound`) and a
solver for Lop-AE-SparseTri (`LopClaim`), the calculation of the proof of Theorem 19, for
`D = ⌊n^d⌋`, `g = ⌈D^η⌉` and `Dc = Θ(D^a)`:

  calls × preprocessing   `n g n² (log n + 1)²/Dc^γ   ≲ n^{3 + dη - dγa} (log n + 1)²`
  calls × queries         `n g (n²/√D) Dc^q (log n + 1) ≲ n^{3 + dη + dqa - d/2} (log n + 1)`
  calls × reading         `n g n²/√D                  ≲ n^{3 + dη - d/2}`
  scans                   `κ n³ log n/g               ≲ κ n^{3 - dη} log n`
  prime                   `n^{log₂ 7} D^{3/2}         ≤ n^{2.81 + 3d/2}`
  build                   `n² D g                     ≲ n^{2 + d + dη}`

The first four are `O(κ n^{3-s} (log n + 1)³)` with `s = d min(η, min(γa, 1/2 - qa) - η)`, hence
`O(κ n^{3-δ})` for every `δ < s`; the last two are `O(n^{3-δ})` if `3d/2 + δ ≤ 0.19`.

* `explicitFrom_of_hostBound`: the general statement;
* `explicitFrom_original`: calls at the dimension `D` (`a = 1`), from `Claim.Theorem_17`;
* `explicitFrom_mid`: calls at the dimension `⌈⌊√D⌋/g⌉ ⌊√D⌋` of the middle part (`a = 1 - η`).
-/

namespace ImprovedExponents

open ThreeSumApsp ThreeSumApsp.Spec Light.Sec4 Filter

variable {a γ η d δ ε q : ℝ} {g Dc D : ℕ → ℕ}

variable (M : DetTimeModel)

/-- `explicitFrom_of_hostBound` with the three inequalities for the exponent `s` as hypotheses. -/
theorem explicitFrom_of_hostBound_aux {s : ℝ}
    (hd0 : 0 < d) (hη0 : 0 < η) (hη1 : η < 1 / 2) (ha0 : 0 < a) (ha1 : a ≤ 1)
    (hγ : 0 ≤ γ) (hq : 0 ≤ q) (hδ0 : 0 ≤ δ) (hsmall : 3 / 2 * d + δ ≤ 19 / 100)
    (hD : ∀ n, D n = ⌊(n : ℝ) ^ d⌋₊) (hg : ∀ n, g n = ⌈(D n : ℝ) ^ η⌉₊)
    (hDc : ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ ∀ᶠ n : ℕ in Filter.atTop,
        c₁ * (D n : ℝ) ^ a ≤ (Dc n : ℝ) ∧ (Dc n : ℝ) ≤ c₂ * (D n : ℝ) ^ a)
    (hthin : d * a < ε)
    (hhost : HostBound M strassen D g Dc) (hlop : LopClaim M ε γ q)
    (hs1 : s ≤ d * η) (hs2 : s ≤ d * (γ * a - η)) (hs3 : s ≤ d * (1 / 2 - q * a - η))
    (hδ : δ < s) : ExplicitFrom M δ 1 := by
  obtain ⟨C, hC, hhost⟩ := hhost
  obtain ⟨CL, Td, hTd, hlop⟩ := hlop
  obtain ⟨T, hT, hhost⟩ := hhost Td hTd
  obtain ⟨c₁, c₂, hc₁, hDc⟩ := hDc
  have hd1 : d ≤ 1 := by linarith
  have hda := mul_le_mul_of_nonneg_left ha1 hd0.le
  have hP := eventually_hostParams hd0 hd1 hη0 hη1 hD hg
  obtain ⟨K₁, K₂, hK₁, hK₂, hQ⟩ := eventually_callParams ha0
    (by linarith) hγ hq hthin hc₁ hP hDc
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (hP.and hQ)
  have hτ := sub_pos.2 hδ
  obtain ⟨K', hK'⟩ : ∃ K' : ℝ, K' = (3 / (s - δ) + 1) ^ 3 := ⟨_, rfl⟩
  have hK'0 : 0 ≤ K' := by rw [hK']; positivity
  refine ⟨max n₀ 3, 4 * |CL| * (2 * K₁ * K') + 4 * |CL| * (4 * K₂ * K') + 4 * C * (4 * K')
    + C * (2 * K') + C + C * 2, T, hT, fun n κ u hn hκ hu => ?_⟩
  obtain ⟨P, Q⟩ := hn₀ n (by omega)
  have hn3 : 3 ≤ n := by omega
  have hN1 : (1 : ℝ) ≤ n := by exact_mod_cast P.one_le_n
  have hN0 : (0 : ℝ) < n := by linarith
  have hY1 : (1 : ℝ) ≤ Dc n := by exact_mod_cast Q.one_le
  have hY0 : (0 : ℝ) < Dc n := by linarith
  have hG0 : (0 : ℝ) ≤ g n := Nat.cast_nonneg _
  have hX0 : (0 : ℝ) ≤ D n := Nat.cast_nonneg _
  have hlogn := Real.one_le_log_natCast_of_three_le hn3
  have hlogY0 := Real.log_nonneg hY1
  have hlogY := Real.log_le_log hY0 Q.le_n
  have hL1 : 1 ≤ Real.log n + 1 := by linarith
  have hL3 : (Real.log n + 1) ^ 3 ≤ K' * n ^ (s - δ) := by
    grind [log_add_one_pow_three_le]
  -- the logarithmic factors
  have hlam2 : (Real.log _ + 1) ^ 2 ≤ K' * n ^ (s - δ) :=
    ((pow_le_pow_left₀ (by linarith) (by linarith) 2).trans
      (pow_le_pow_right₀ hL1 (by norm_num))).trans hL3
  have hlam1 : Real.log (Dc n) + 1 ≤ K' * n ^ (s - δ) :=
    by grind [le_self_pow₀]
  have hlam0 : 1 ≤ K' * n ^ (s - δ) := by grind
  have hlamn : Real.log n ≤ K' * n ^ (s - δ) :=
    by grind [le_self_pow₀]
  -- the factors, as powers of `n`
  have fN : n ≤ 1 * (n : ℝ) ^ (1 : ℝ) := by simp
  have fN2 : n ^ 2 ≤ 1 * (n : ℝ) ^ (2 : ℝ) := by simp
  have fN3 : (n : ℝ) ^ 3 ≤ 1 * (n : ℝ) ^ (3 : ℝ) := by
    simp
  have f1 : (1 : ℝ) ≤ 1 * (n : ℝ) ^ (0 : ℝ) := by simp
  have fG := P.g_le hη0.le
  have hw : (queryCap n _ : ℝ) ≤ (n : ℝ) ^ 2 / Real.sqrt (D n) :=
    Nat.floor_le (by positivity)
  have fW : (n : ℝ) ^ 2 / Real.sqrt (D n) ≤ 2 * (n : ℝ) ^ (2 + -(d / 2)) := by
    rw [Real.rpow_add hN0, Real.rpow_two, div_eq_mul_one_div]
    calc (n : ℝ) ^ 2 * (1 / Real.sqrt _) ≤ (n : ℝ) ^ 2 * (2 * (n : ℝ) ^ (-(d / 2))) :=
          mul_le_mul_of_nonneg_left P.inv_sqrt_le (by positivity)
      _ = 2 * ((n : ℝ) ^ 2 * (n : ℝ) ^ (-(d / 2))) := by ring
  have fX : (D n : ℝ) ≤ 1 * (n : ℝ) ^ d := by rw [one_mul]; exact P.D_le
  have fX32 : (D n : ℝ) ^ (3 / 2 : ℝ) ≤ 1 * (n : ℝ) ^ (d * (3 / 2)) := by
    grind [one_mul, Real.rpow_mul, Real.rpow_le_rpow]
  have fMM : strassen n ≤ 1 * (n : ℝ) ^ (2.81 : ℝ) := by
    rw [one_mul]
    exact Real.rpow_le_rpow_of_exponent_le hN1 logb_two_seven_le
  have hdη := mul_le_mul_of_nonneg_left hη1.le hd0.le
  have hdqa : 0 ≤ d * (q * a) := by positivity
  -- the six terms
  have t1 : (n : ℝ) * g n * preBound31 γ n (Dc n) ≤ 2 * K₁ * K' * (n : ℝ) ^ (3 - δ) := by
    have e : (n : ℝ) * g n * preBound31 γ n (Dc n)
        = (n : ℝ) * g n * (n : ℝ) ^ 2 * (Dc n : ℝ) ^ (-γ) * (Real.log (Dc n) + 1) ^ 2 := by
      grind [preBound31, Real.rpow_neg]
    rw [e]
    exact (prod5_le (E := 3 - δ) hN1 hG0 (by positivity) (by positivity) (by positivity)
      (by norm_num) (by norm_num) (by norm_num) hK₁ hK'0 fN fG fN2 Q.neg_rpow_le hlam2
      (by linarith)).trans_eq (by ring)
  have t2 : (n : ℝ) * g n * ((queryCap n (D n) : ℝ) * queryBound31 q (Dc n))
      ≤ 4 * K₂ * K' * (n : ℝ) ^ (3 - δ) := by
    have e : (n : ℝ) * g n * ((queryCap n (D n) : ℝ) * queryBound31 q (Dc n))
        = (n : ℝ) * g n * (queryCap n (D n) : ℝ) * (Dc n : ℝ) ^ q * (Real.log (Dc n) + 1) := by
      grind [queryBound31]
    rw [e]
    exact (prod5_le (E := 3 - δ) hN1 hG0 (by positivity) (by positivity) (by linarith)
      (by norm_num) (by norm_num) (by norm_num) hK₂ hK'0 fN fG (hw.trans fW) Q.rpow_le hlam1
      (by linarith)).trans_eq (by ring)
  have t3 : (n : ℝ) * g n * ((n : ℝ) ^ 2 / Real.sqrt (D n)) ≤ 4 * K' * (n : ℝ) ^ (3 - δ) := by
    have e : (n : ℝ) * g n * ((n : ℝ) ^ 2 / Real.sqrt (D n))
        = (n : ℝ) * g n * ((n : ℝ) ^ 2 / Real.sqrt (D n)) * 1 * 1 := by ring
    rw [e]
    exact (prod5_le (E := 3 - δ) hN1 hG0 (by positivity) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hK'0 fN fG fW f1 hlam0
      (by linarith)).trans_eq (by ring)
  have t4 : termScans n (g n) κ ≤ κ * (2 * K' * (n : ℝ) ^ (3 - δ)) := by
    have e : termScans n (g n) κ
        = κ * ((n : ℝ) ^ 3 * (1 / (g n : ℝ)) * 1 * 1 * Real.log n) := by
      grind [termScans]
    rw [e]
    exact mul_le_mul_of_nonneg_left ((prod5_le (E := 3 - δ) hN1 (by positivity) (by norm_num)
      (by norm_num) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hK'0
      fN3 (P.inv_g_le hη0.le) f1 f1 hlamn (by linarith)).trans_eq (by ring)) (by linarith)
  have t5 : termPrime strassen n (D n) ≤ (n : ℝ) ^ (3 - δ) := by
    have e : termPrime strassen n (D n) = strassen n * (D n : ℝ) ^ (3 / 2 : ℝ) * 1 * 1 * 1 := by
      grind [termPrime]
    rw [e]
    exact (prod5_le (E := 3 - δ) hN1 (by positivity) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) fMM fX32 f1 f1 f1
      (by linarith)).trans_eq (by ring)
  have t6 : termBuild n (D n) (g n) ≤ 2 * (n : ℝ) ^ (3 - δ) := by
    have e : termBuild n (D n) (g n) = (n : ℝ) ^ 2 * (D n : ℝ) * (g n : ℝ) * 1 * 1 := by
      grind [termBuild]
    rw [e]
    exact (prod5_le (E := 3 - δ) hN1 hX0 hG0 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) fN2 fX fG f1 f1
      (by linarith)).trans_eq (by ring)
  -- the sum
  have hS0 : 0 ≤ (n : ℝ) ^ (3 - δ) := by positivity
  have hpre0 : 0 ≤ preBound31 γ n (Dc n) := by rw [preBound31]; positivity
  have hquery0 : 0 ≤ queryBound31 q (Dc n) := by
    rw [queryBound31]
    positivity
  have hS : (n : ℝ) ^ (3 - δ) ≤ κ * ((n : ℝ) ^ (3 - δ) * Real.log n ^ 1) := by
    rw [pow_one]
    calc (n : ℝ) ^ (3 - δ) = 1 * ((n : ℝ) ^ (3 - δ) * 1) := by ring
      _ ≤ κ * ((n : ℝ) ^ (3 - δ) * Real.log n) :=
          mul_le_mul hκ (mul_le_mul_of_nonneg_left hlogn hS0) (by positivity) (by linarith)
  have hκS : κ * (n : ℝ) ^ (3 - δ) ≤ κ * ((n : ℝ) ^ (3 - δ) * Real.log n ^ 1) := by
    grind [pow_one, mul_le_mul_of_nonneg_left, le_mul_of_one_le_right]
  exact total_le (hhost n κ u P.sixteen_le P.le_n P.one_le_g P.g_le_sqrt hκ hu) (hlop n _ (queryCap n (D n)) P.one_le_n Q.one_le Q.le_rpow) (by positivity)
    (mul_nonneg hN0.le hG0) hC (by positivity) (by positivity) (by positivity) (by positivity)
    t1 t2 t3 t4 t5 t6 hS hκS

/-- **The total time, for arbitrary parameters.** Let `D = ⌊n^d⌋`, `g = ⌈D^η⌉` with `0 < η < 1/2`,
and let the calls of the reduction of Theorem 17 be charged at a dimension `Dc = Θ(D^a)`,
`0 < a ≤ 1`, at which the solver of Lop-AE-SparseTri applies (`d a < ε`). Then Exact Triangle is
solved in time `O(κ n^{3-δ} log n)` for every `0 ≤ δ < d min(η, min(γa, 1/2 - qa) - η)` with
`3d/2 + δ ≤ 0.19`. -/
theorem explicitFrom_of_hostBound     (hd0 : 0 < d) (hη0 : 0 < η) (hη1 : η < 1 / 2) (ha0 : 0 < a) (ha1 : a ≤ 1)
    (hγ : 0 ≤ γ) (hq : 0 ≤ q) (hδ0 : 0 ≤ δ) (hsmall : 3 / 2 * d + δ ≤ 19 / 100)
    (hD : ∀ n, D n = ⌊(n : ℝ) ^ d⌋₊) (hg : ∀ n, g n = ⌈(D n : ℝ) ^ η⌉₊)
    (hDc : ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ ∀ᶠ n : ℕ in Filter.atTop,
        c₁ * (D n : ℝ) ^ a ≤ (Dc n : ℝ) ∧ (Dc n : ℝ) ≤ c₂ * (D n : ℝ) ^ a)
    (hthin : d * a < ε)
    (hhost : HostBound M strassen D g Dc) (hlop : LopClaim M ε γ q)
    (hδ : δ < d * min η (min (γ * a) (1 / 2 - q * a) - η)) :
    ExplicitFrom M δ 1 :=
  explicitFrom_of_hostBound_aux M hd0 hη0 hη1 ha0 ha1 hγ hq hδ0 hsmall hD hg hDc hthin hhost hlop
    (by simp_all)
    (by simp_all)
    (by simp_all) hδ

/-- **The reduction with the calls at the dimension of the middle part**,
`⌈⌊√D⌋/g⌉ ⌊√D⌋ = Θ(D^{1-η})`. -/
theorem explicitFrom_mid     (hd0 : 0 < d) (hη0 : 0 < η) (hη1 : η < 1 / 2) (hγ : 0 ≤ γ) (hq : 0 ≤ q) (hδ0 : 0 ≤ δ)
    (hsmall : 3 / 2 * d + δ ≤ 19 / 100)
    (hD : ∀ n, D n = ⌊(n : ℝ) ^ d⌋₊) (hg : ∀ n, g n = ⌈(D n : ℝ) ^ η⌉₊)
    (hhost : HostBound M strassen D g (fun n => pieceSizeNat (D n) (g n) * Nat.sqrt (D n)))
    (hlop : LopClaim M ε γ q) (hthin : d * (1 - η) < ε)
    (hδ : δ < d * min η (min (γ * (1 - η)) (1 / 2 - q * (1 - η)) - η)) : ExplicitFrom M δ 1 :=
  explicitFrom_of_hostBound M hd0 hη0 hη1 (by linarith) (by linarith) hγ hq hδ0
    hsmall hD hg
    (exists_bounds_pieceSize hd0 (by linarith) hη0 hη1 hD hg) hthin hhost hlop hδ
