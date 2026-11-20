module

public import GradedNear.Defs

/-!
# Burgess's bound: from the printed primitive statement to all non-principal characters

`GradedNear.BurgessBound` (in `GradedNear/Defs.lean`) is Burgess's bound with `r = 3` for every
non-principal Dirichlet character and every `N ≥ 0`. The printed source, [HB, Lemma 2.1, p. 7],
states it for primitive characters and `N ≥ 1` only. `BurgessPrimitive` (in `GradedNear/Defs.lean`)
states the printed form, and this file proves `BurgessPrimitive → BurgessBound`
(`burgessBound_of_primitive`), so that the hypothesis is a statement matching the print.

The reduction is the standard one. If `χ` mod `q` is induced by the primitive `χ*` mod `q*`, then
`χ(n) = χ*(n)` for `(n, q) = 1` and `χ(n) = 0` otherwise, so successively removing the multiples of each
prime dividing `q` expresses the sum in terms of `χ*` on progressions with step `d ∣ q`.
Each inner sum has length at most `H`; complete periods of `χ*` are removed (they vanish since
`χ* ≠ 1`) and the interval is shifted by `q*`, which lands in the printed range `N ≥ 1`,
`1 ≤ H ≤ q*`. Finally `q* ≤ q` and sifting by the distinct primes costs `2^ω(q) ≪_ε q^ε`.

References: [HB] D. R. Heath-Brown, *Zero-free regions for Dirichlet L-functions, and the least
prime in an arithmetic progression*, Proc. London Math. Soc. (3) 64 (1992) 265–338 (Lemma 2.1 is on
p. 7 of the preprint `literature/heath-brown-1992-zero-free-regions-and-least-prime.pdf`).
-/

@[expose] public section

open Finset

noncomputable section

namespace GradedNear

/-- Large prime factors cost `2 ≤ p^ε` each, and there are boundedly many small ones. -/
lemma prime_cost {ε : ℝ} (hε : 0 < ε) : ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℕ, q ≠ 0 →
    (2 : ℝ)^q.primeFactors.card ≤ C * (q : ℝ)^ε := by
  let K := ⌈(2 : ℝ)^ε⁻¹⌉₊
  refine ⟨2^K, by positivity, fun q hq => ?_⟩
  let P := q.primeFactors
  let small := P.filter (· < K)
  let large := P.filter (¬ · < K)
  have hK := card_range K ▸ card_le_card (fun i hi => mem_range.mpr (mem_filter.mp hi).2 : small ⊆ range K)
  have hprod : (∏ p ∈ large, p) ≤ q := Nat.le_of_dvd (by omega) <|
    (prod_dvd_prod_of_subset _ _ _ (filter_subset ..)).trans (Nat.prod_primeFactors_dvd q)
  rw [← card_filter_add_card_filter_not (s := P) (· < K), pow_add]
  apply mul_le_mul (pow_le_pow_right₀ (by norm_num) hK) _ (by positivity) (by positivity)
  calc _ = ∏ p ∈ large, (2 : ℝ) := by aesop
       _ ≤ ∏ p ∈ large, (p : ℝ)^ε := by
         refine prod_le_prod₀ (by simp) fun p hp => ?_
         apply (Real.rpow_inv_le_iff_of_pos (by norm_num) (by positivity) hε).mp
         aesop
       _ ≤ _ := by rw [Real.finsetProd_rpow _ _ (by simp)]; gcongr; rw [← Nat.cast_prod]; exact_mod_cast hprod

/-! ## Complete periods -/

abbrev charSum {q : ℕ} (χ : DirichletCharacter ℂ q) (a H : ℕ) :=
  ∑ n ∈ Ioc a (a + H), χ n

lemma charSum_range {q : ℕ} (χ : DirichletCharacter ℂ q) (a H : ℕ) :
    charSum χ a H = ∑ i ∈ range H, χ ((a + 1 + i : ℕ) : ZMod q) := by
  rw [charSum, ← Ico_add_one_add_one_eq_Ioc, sum_Ico_eq_sum_range]
  simp

/-- A full period cancels, since translation permutes all residues. -/
lemma charSum_period {q : ℕ} (hq : 0 < q) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (a : ℕ) : charSum χ a q = 0 := by
  cases q with
  | zero => omega
  | succ q =>
    rw [charSum_range, ← Fin.sum_univ_eq_sum_range]
    change ∑ x : ZMod (q+1), χ ((a+1+x.val : ℕ) : ZMod (q+1)) = 0
    simpa [Nat.cast_add, add_assoc] using (Equiv.sum_comp (Equiv.addLeft ((a : ZMod (q+1)) + 1)) χ).trans
      (MulChar.sum_eq_zero_of_ne_one hχ)

/-- Burgess's interval bound with no restriction on length. -/
abbrev CharBound {q : ℕ} (χ : DirichletCharacter ℂ q) (K : ℝ) :=
  ∀ N H, ‖charSum χ N H‖ ≤ K * (H : ℝ) ^ (2/3 : ℝ)

/-- After a complete period, the interval sum returns to its previous value. -/
lemma charSum_periodic {q : ℕ} (hq : 0 < q) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (N : ℕ) : Function.Periodic (charSum χ N) q := by
  intro H
  have h := sum_Ioc_consecutive (fun n : ℕ => χ n) (Nat.le_add_right N H) (Nat.le_add_right (N+H) q)
  change charSum χ N H + charSum χ (N+H) q = _ at h
  rw [charSum_period hq χ hχ, add_zero] at h
  simpa [charSum, add_assoc] using h.symm

/-! ## Reduction to the primitive character -/

/-- A character agrees with its primitive character on integers prime to the level and vanishes
on the others. -/
private lemma apply_eq_ite_primitive {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) :
    χ n = if n.Coprime q then χ.primitiveCharacter n else 0 := by
  split_ifs with h
  · 
    have := χ.primitiveCharacter_apply_of_isCoprime (Nat.isCoprime_iff_coprime.mpr h)
    aesop
  · exact χ.map_nonunit (by rwa [ZMod.isUnit_iff_coprime])

private abbrev sift (f : ℕ → ℂ) (P : Finset ℕ) (d n : ℕ) :=
  if d ∣ n ∧ ∀ p ∈ P, ¬p ∣ n then f n else 0

/-- Deleting the multiples of `p` subtracts one sum over multiples of `[d,p]`.
Thus each removed prime costs at most a factor of two. -/
private lemma sift_bound {A : Finset ℕ} {f : ℕ → ℂ} {B : ℝ}
    (h : ∀ d : ℕ, ‖∑ n ∈ A, (if d ∣ n then f n else 0)‖ ≤ B) (P : Finset ℕ) (d : ℕ) :
    ‖∑ n ∈ A, sift f P d n‖ ≤ 2^P.card * B := by
  induction P using Finset.induction_on generalizing d with
  | empty => simpa [sift] using h d
  | insert p P hp ih =>
    have cut n : sift f (insert p P) d n = sift f P d n - sift f P (d.lcm p) n := by
      simp [sift, h, Nat.lcm_dvd_iff] <;> aesop
    simp_rw [cut, sum_sub_distrib, card_insert_of_notMem hp, pow_succ]
    grw [norm_sub_le, ih, ih]; linarith

/-- Reindex a sum on the multiples of `d` by their quotients. -/
lemma sum_multiples {M : Type*} [AddCommMonoid M] (f : ℕ → M) {d : ℕ} (hd : 0 < d)
    (a b : ℕ) : ∑ n ∈ Ioc a b, (if d ∣ n then f n else 0) =
      ∑ m ∈ Ioc (a / d) (b / d), f (d * m) := by
  rw [← sum_filter]
  have e : (Ioc a b).filter (d ∣ ·) = (Ioc (a/d) (b/d)).image (d * ·) := by
    ext n
    simp [mem_filter, mem_Ioc, mem_image, Nat.div_lt_iff_lt_mul hd, Nat.le_div_iff_mul_le hd]
    constructor
    · rintro ⟨h, m, rfl⟩; bound
    · bound
  exact e ▸ sum_image (fun _ _ _ _ => (Nat.mul_right_inj hd.ne').mp)

/-- Burgess on multiples of `d`: the induced interval has length `⌊b/d⌋-⌊a/d⌋`. -/
lemma CharBound.multiples {q : ℕ} {χ : DirichletCharacter ℂ q} {K : ℝ} (h : CharBound χ K)
    {d : ℕ} (hd : 0 < d) (a b : ℕ) : ‖∑ n ∈ Ioc a b, (if d ∣ n then χ n else 0)‖ ≤
      K * ((b/d - a/d : ℕ) : ℝ) ^ (2/3 : ℝ) := by
  rw [sum_multiples _ hd]; simp; rw [← mul_sum, norm_mul]
  grw [χ.norm_le_one, one_mul]
  have he : Ioc (a/d) (a/d + (b/d - a/d)) = Ioc (a/d) (b/d) := by ext; simp; omega
  simpa only [charSum, he] using h (a/d) (b/d-a/d)

/-- The number of multiples of `d ≥ 1` in `(N, N + H]` is at most `H`. -/
private lemma div_sub_div_le {d : ℕ} (hd : 0 < d) (N H : ℕ) : (N + H) / d - N / d ≤ H := by
  have h1 : (N + H) / d ≤ (N + H * d) / d :=
    Nat.div_le_div_right (by nlinarith)
  rw [Nat.add_mul_div_right N H hd] at h1
  omega

/-- The unrestricted interval estimate, uniform in the character and modulus. -/
lemma burgess_uniform (hB : BurgessPrimitive) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {q : ℕ}, 0 < q → ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      CharBound χ (C * (q:ℝ)^(1/9 + ε)) := by
  obtain ⟨C₁, hC₁⟩ := hB (ε/2) (by positivity)
  obtain ⟨C₂, hc₂, hτ⟩ := prime_cost (show 0 < ε/2 by positivity)
  let C := max C₁ 0
  refine ⟨C*C₂, by positivity, fun {q} hq χ hχ N H => ?_⟩
  have : NeZero q := ⟨by omega⟩
  let ψ := χ.primitiveCharacter
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hc := NeZero.pos χ.conductor
  have hψ : ψ ≠ 1 := by
    intro he; dsimp [ψ] at he; apply hχ; rw [← χ.changeLevel_primitiveCharacter, he, map_one]
  have hqq : (χ.conductor : ℝ) ≤ q := by exact_mod_cast Nat.le_of_dvd hq χ.conductor_dvd_level
  have hb : CharBound ψ (C * (q : ℝ) ^ (1/9 + ε/2)) := by
    intro a H
    rw [← (charSum_periodic hc ψ hψ a).map_mod_nat H]
    rcases Nat.eq_zero_or_pos (H % χ.conductor) with he | he
    · simp [he, charSum]; positivity
    have := hC₁ _ hc _ χ.primitiveCharacter_isPrimitive (a + χ.conductor) _ (by omega) he (Nat.mod_lt H hc).le
    simp [charSum_range, Nat.cast_add] at this ⊢
    apply this.trans; gcongr <;> first | positivity | bound | exact Nat.mod_le .. | assumption
  let B := C * (q : ℝ) ^ (1/9 + ε/2) * (H : ℝ) ^ (2/3 : ℝ)
  have bound (d : ℕ) : ‖∑ n ∈ Ioc N (N+H), (if d ∣ n then ψ n else 0)‖ ≤ B := by
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp [B]; positivity
    · apply (hb.multiples hd ..).trans; dsimp [B]; gcongr
      exact_mod_cast div_sub_div_le hd N H
  have hc n : (∀ p ∈ q.primeFactors, ¬p ∣ n) ↔ n.Coprime q := by
    rw [← not_not (a := n.Coprime q), Nat.Prime.not_coprime_iff_dvd]
    aesop
  have h := sift_bound bound q.primeFactors 1
  apply le_trans (by simpa only [sift, one_dvd, true_and, hc, ψ, ← apply_eq_ite_primitive] using h : _ ≤ _)
  grw [hτ q (by omega)]
  rw [show (1 : ℝ)/9 + ε = ε/2 + (1/9 + ε/2) by ring, Real.rpow_add (by positivity : (0 : ℝ) < q) (ε/2) _]
  linarith

/-- **Burgess for all non-principal characters**, in particular on the printed range of lengths. -/
theorem burgessBound_of_primitive (hB : BurgessPrimitive) : BurgessBound := by
  intro ε hε
  obtain ⟨C, _, h⟩ := burgess_uniform hB hε
  bound

end GradedNear
