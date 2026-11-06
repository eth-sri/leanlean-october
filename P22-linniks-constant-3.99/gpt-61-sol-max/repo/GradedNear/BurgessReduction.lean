
import GradedNear.CharacterSums
import GradedNear.Tactics

/-!
# Burgess's bound: from the printed primitive statement to all non-principal characters

`GradedNear.BurgessBound` (in `GradedNear/Defs.lean`) is Burgess's bound with `r = 3` for every
non-principal Dirichlet character and every `N ≥ 0`. The printed source, [HB, Lemma 2.1, p. 7],
states it for primitive characters and `N ≥ 1` only. `BurgessPrimitive` (in `GradedNear/Defs.lean`)
states the printed form, and this file proves `BurgessPrimitive → BurgessBound`
(`burgessBound_of_primitive`), so that the hypothesis is a statement matching the print.

The reduction is the standard one. If `χ` mod `q` is induced by the primitive `χ*` mod `q*`, then
`χ(n) = χ*(n)` for `(n, q) = 1` and `χ(n) = 0` otherwise, and Möbius inversion gives
`Σ_{N < n ≤ N+H} χ(n) = Σ_{d ∣ q} μ(d) χ*(d) Σ_{⌊N/d⌋ < m ≤ ⌊(N+H)/d⌋} χ*(m)`.
Each inner sum has length at most `H`; complete periods of `χ*` are removed (they vanish since
`χ* ≠ 1`) and the interval is shifted by `q*`, which lands in the printed range `N ≥ 1`,
`1 ≤ H ≤ q*`. Finally `q* ≤ q` and the number of squarefree divisors costs `≪_ε q^ε`
(proved directly in the reduction).

References: [HB] D. R. Heath-Brown, *Zero-free regions for Dirichlet L-functions, and the least
prime in an arithmetic progression*, Proc. London Math. Soc. (3) 64 (1992) 265–338 (Lemma 2.1 is on
p. 7 of the preprint `literature/heath-brown-1992-zero-free-regions-and-least-prime.pdf`).
-/

open scoped ArithmeticFunction.Moebius

namespace GradedNear

/-! ## Reduction to the primitive character -/

/-- **Burgess's bound for all non-principal characters** (`BurgessBound`, with `N ≥ 0`) follows
from the printed primitive statement [HB, Lemma 2.1, k = 3] (`BurgessPrimitive`). -/
theorem burgessBound_of_primitive (hB : BurgessPrimitive) : BurgessBound := by
  intro ε hε
  let e := ε / 2
  have he : 0 < e := by positivity
  obtain ⟨C₁, hC₁⟩ := hB e he
  -- Only squarefree divisors occur in the Möbius expansion; bound their count.
  let K : ℕ := ⌈(2 : ℝ) ^ (1 / e)⌉₊

  set C₂ : ℝ := 2 ^ K

  have hτ (n : ℕ) (hn : n ≠ 0) :
      ↑ (n.divisors.filter Squarefree).card ≤ C₂ * ↑n ^ e := by
    let g (p : ℕ) : ℝ := if p < K then 2 else 1
    have hp (p : ℕ) (hp : p ∈ n.primeFactors) :
        (2 : ℝ) ≤ g p * ↑p ^ e := by
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      dsimp only [g]
      split_ifs with h
      · grind [Real.one_le_rpow]
      · rw [one_mul]
        apply (Real.rpow_inv_le_iff_of_pos (by norm_num) (by positivity) he).mp
        aesop (add simp [one_div])
    have hg : ∏ p ∈ n.primeFactors, g p ≤ (2 : ℝ) ^ K := by
      simp only [g, Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
      apply pow_le_pow_right₀ (by norm_num)
      simpa using Finset.card_le_card (show n.primeFactors.filter (· < K) ⊆ Finset.range K by grind)
    have hcard : (n.divisors.filter Squarefree).card = 2 ^ n.primeFactors.card := by
      simpa [Nat.factors_eq, ← Finset.filter_val] using congrArg Multiset.card (Nat.divisors_filter_squarefree hn)
    rw [hcard, Nat.cast_pow, Nat.cast_ofNat, ← Finset.prod_const]
    refine (Finset.prod_le_prod₀ (by bound) hp).trans ?_
    rw [Finset.prod_mul_distrib, Real.finsetProd_rpow _ _ (by bound), ← Nat.cast_prod]
    gcongr
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.prod_primeFactors_dvd n)
  clear_value C₂
  set C₁' := max C₁ 0

  refine ⟨C₁' * C₂, ?_⟩
  intro q χ hχ N H hH hHq
  have hq1 := hH.trans hHq

  have : NeZero q := ⟨ by omega ⟩



  have hcond := by
    exact_mod_cast Nat.le_of_dvd (by omega) χ.conductor_dvd_level
  set B : ℝ := C₁' * ↑q ^ (⅑ + e) * ↑H ^ ⅔ with hBdef
  have hB0 : 0 ≤ B := by positivity

  have hc := Nat.pos_of_ne_zero χ.conductor_ne_zero

  -- Möbius inversion expresses the induced character through its primitive source.
  have key (n : ℕ) : χ n =
      ∑ d ∈ q.divisors, if d ∣ n then ↑(μ d) * χ.primitiveCharacter n else 0 := by
    rw [← Finset.sum_filter]
    have hfilt : q.divisors.filter (· ∣ n) = (Nat.gcd n q).divisors := by
      grind [Nat.dvd_gcd_iff]
    rw [hfilt, ← Finset.sum_mul, ← Int.cast_sum]
    have hmu := congrArg (fun f : ArithmeticFunction ℤ => f (Nat.gcd n q))
      ArithmeticFunction.moebius_mul_coe_zeta
    simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at hmu
    rw [hmu]
    push_cast
    change χ n = (if n.Coprime q then 1 else 0) * χ.primitiveCharacter n
    split_ifs with h
    · have := χ.primitiveCharacter_apply_of_isCoprime (Nat.isCoprime_iff_coprime.mpr h)
      simp_all
    grind [MulChar.map_nonunit, ZMod.isUnit_iff_coprime]
  rw [Finset.sum_congr rfl fun n _ => key n, Finset.sum_comm]
  simp_rw [← Finset.sum_filter, ← Finset.mul_sum]
  rw [← Finset.sum_subset (Finset.filter_subset (p := Squarefree) (s := q.divisors)) ?_]
  swap
  · intro d hd hnot
    simp_all [ArithmeticFunction.moebius_eq_zero_of_not_squarefree]
  refine (norm_sum_le_of_le _ (n := fun _ => B) ?_).trans ?_
  ·
      intro d hd
      replace hd := (Finset.mem_filter.1 hd).1
      have hd0 := Nat.pos_of_mem_divisors hd
      rw [Finset.sum_filter, sum_Ioc_ite_dvd _ hd0]
      simp only [Nat.cast_mul, map_mul, ← Finset.mul_sum]
      have hle : N / d ≤ (N + H) / d := Nat.div_le_div_right (by omega)
      have hH' : (N + H) / d - N / d ≤ H := by
        have h1 : (N + H) / d ≤ (N + H * d) / d := Nat.div_le_div_right (by nlinarith)
        grind [Nat.add_mul_div_right]
      rw [← Nat.add_sub_of_le hle]
      have hμ : ‖(μ d : ℂ)‖ ≤ 1 := by

        exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      grw [norm_mul, norm_mul, hμ, DirichletCharacter.norm_le_one χ.primitiveCharacter _,  burgess_any_length (K := C₁' * ↑χ.conductor ^ (⅑ + e))
        hc χ.primitiveCharacter (by
          grind [DirichletCharacter.changeLevel_primitiveCharacter]
        ) (by positivity) (by
          intro N H hH hHq
          have h := hC₁ _ hc _ χ.primitiveCharacter_isPrimitive (N + χ.conductor) H (by omega) hH hHq
          simp [← Finset.Ico_add_one_add_one_eq_Ioc, Finset.sum_Ico_eq_sum_range] at h ⊢
          exact h.trans (by bound))
       ]
      simp only [one_mul]
      rw [hBdef]
      gcongr

  simp only [Finset.sum_const, nsmul_eq_mul]
  calc _ ≤ C₂ * ↑q ^ e * B := by
        bound
    _ = C₁' * C₂ * ↑q ^ (⅑ + ε) * ↑H ^ ⅔ := by
        rw [hBdef]
        dsimp only [e]
        rpow_ring

end GradedNear
