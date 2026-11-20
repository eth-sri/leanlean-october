module
public import Mathlib.NumberTheory.MulChar.Lemmas

public import Mathlib.NumberTheory.JacobiSum.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

@[expose] public section

namespace DedekindZetaZeroFree.FiniteGauss

variable {k : Type*} [Field k] [Fintype k]

section

variable (χ : MulChar k ℂ) (ψ : AddChar k ℂ) (j : ℕ)

noncomputable def gaussPower : ℂ :=
  gaussSum (χ ^ j) ψ

noncomputable def normalizedGaussPower : ℂ :=
  gaussPower χ ψ j / (Real.sqrt (Fintype.card k) : ℂ)

end

section

variable (χ : MulChar k ℂ) (ψ : AddChar k ℂ) (hQ : Fintype.card k % 12 = 1) (hχ : orderOf χ = 6)
    (hψ : ψ ≠ 1)

include hQ hχ hψ in
theorem gaussPower_two_mul_four :
    gaussPower χ ψ 2 * gaussPower χ ψ 4 = (Fintype.card k : ℂ) := by
  have ho : orderOf (χ ^ 2) = 3 := by
    rw [orderOf_pow' _ (by norm_num : (2 : ℕ) ≠ 0), hχ]
    norm_num
  have hn : χ ^ 2 ≠ 1 :=
    pow_ne_one_of_lt_orderOf (by norm_num) (by omega)
  have hv : (χ ^ 2) (-1) = 1 :=
    MulChar.val_neg_one_eq_one_of_odd_order (by decide : Odd 3) (by
      grind [pow_orderOf_eq_one])
  have H := gaussSum_mul_gaussSum_pow_orderOf_sub_one hn
    (AddChar.IsPrimitive.of_ne_one hψ)
  simpa [gaussPower, ho, ← pow_mul, hv] using H

include hQ hχ hψ in
theorem gaussPower_two_sq :
    gaussPower χ ψ 2 ^ 2 = jacobiSum (χ ^ 2) (χ ^ 2) * gaussPower χ ψ 4 := by
  have hn : χ ^ 2 * χ ^ 2 ≠ 1 := by
    rw [← pow_add]
    exact pow_ne_one_of_lt_orderOf (by norm_num) (by omega)
  have H := (jacobiSum_mul_nontrivial hn ψ).symm
  rw [← pow_add] at H
  simp_all [gaussPower, pow_two, mul_comm]

include hQ hχ hψ in
theorem normalizedGaussPower_two_cube :
    normalizedGaussPower χ ψ 2 ^ 3 =
      jacobiSum (χ ^ 2) (χ ^ 2) / (Real.sqrt (Fintype.card k) : ℂ) := by
  have hpos : (0 : ℝ) < Fintype.card k := by
    exact_mod_cast Fintype.card_pos
  have hs : (Real.sqrt (Fintype.card k) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hpos).ne'
  have hs2 : (Real.sqrt (Fintype.card k) : ℂ) ^ 2 = Fintype.card k := by
    norm_cast
    exact Real.sq_sqrt hpos.le
  have hg : gaussPower χ ψ 2 ^ 3 =
      jacobiSum (χ ^ 2) (χ ^ 2) * Fintype.card k := by
    calc
      _ = gaussPower χ ψ 2 ^ 2 * gaussPower χ ψ 2 := by ring
      _ = _ := by rw [(gaussPower_two_sq χ ψ hQ hχ hψ), mul_assoc, mul_comm (gaussPower χ ψ 4), (gaussPower_two_mul_four χ ψ hQ hχ hψ)]
  unfold normalizedGaussPower
  grind

end

private lemma quad_unique (η θ : MulChar k ℂ) (hη : η ^ 2 = 1) (hθ : θ ^ 2 = 1)
    (hnη : η ≠ 1) (hnθ : θ ≠ 1) : η = θ := by
 obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := kˣ)
 have hv (ξ : MulChar k ℂ) (hs : ξ ^ 2 = 1) (hn : ξ ≠ 1) : ξ g = -1 := by
  have h1 : ξ g ≠ 1 := by
   intro h
   apply hn
   exact (MulChar.eq_iff hg ξ 1).mpr (by simpa using h)
  have h2 : ξ g ^ 2 = 1 := by rw [← MulChar.pow_apply_coe, hs, MulChar.one_apply_coe]
  exact (sq_eq_one_iff.mp h2).resolve_left h1
 exact (MulChar.eq_iff hg η θ).mpr ((hv η hη hnη).trans (hv θ hθ hnθ).symm)
private lemma char_ne_two (hQ : Fintype.card k % 12 = 1) : ringChar k ≠ 2 := by
 grind [FiniteField.even_card_of_char_two]
section

variable (χ : MulChar k ℂ) (hQ : Fintype.card k % 12 = 1) (hχ : orderOf χ = 6)

include hQ hχ in
private lemma count (t : k) [DecidableEq k] :
 ((Finset.univ.filter fun x : k => x ^ 2 = t).card : ℂ) = (χ ^ 3) t + 1 := by
 classical
 let θ := (quadraticChar k).ringHomComp (Int.castRingHom ℂ)
 have hθ : θ ^ 2 = 1 := by
  dsimp [θ]
  rw [MulChar.ringHomComp_pow, (quadraticChar_isQuadratic k).sq_eq_one, MulChar.ringHomComp_one]
 rw [(quad_unique (χ ^ 3) θ (by rw [← pow_mul]; norm_num; exact hχ ▸ pow_orderOf_eq_one χ) hθ (pow_ne_one_of_lt_orderOf (by norm_num) (by omega)) ((MulChar.ringHomComp_ne_one_iff (by intro a b h; change (a : ℂ) = b at h; exact_mod_cast h)).mpr (quadraticChar_ne_one (char_ne_two hQ))))]
 simpa [θ] using (congrArg (fun z : ℤ => (z : ℂ)) (quadraticChar_card_sqrts (char_ne_two hQ) t))

include hQ hχ in
private lemma jac_dup :
 jacobiSum χ χ = star (χ (4 : k)) * jacobiSum (χ ^ 3) χ := by
 classical
 have h2 : (2 : k) ≠ 0 := fun h => char_ne_two hQ (CharP.ringChar_of_prime_eq_zero Nat.prime_two h)
 have h4 : (4 : k) ≠ 0 := by
  have : (4 : k) = 2 * 2 := by ring
  rw [this]; exact mul_ne_zero h2 h2
 have hχ4 : χ (4 : k) ≠ 0 := χ.apply_ne_zero_iff.mpr (isUnit_iff_ne_zero.mpr h4)
 have hs : (∑ y : k, χ (1 - y ^ 2)) = jacobiSum (χ ^ 3) χ := by
  have H := Finset.sum_fiberwise Finset.univ (fun y : k => y ^ 2)
    (fun y : k => χ (1 - y ^ 2))
  have hf (t : k) : (∑ y ∈ Finset.univ.filter (fun y : k => y ^ 2 = t), χ (1 - y ^ 2)) =
       ((χ ^ 3) t + 1) * χ (1 - t) := by
   calc
    _ = ∑ y ∈ Finset.univ.filter (fun y : k => y ^ 2 = t), χ (1 - t) := by
      grind [Finset.sum_congr]
    _ = _ := by simp [count χ hQ hχ t]
  simp_rw [hf] at H
  rw [← H]
  simp only [add_mul]
  simp only [Finset.sum_add_distrib, one_mul, jacobiSum]
  have hz : (∑ t : k, χ (1 - t)) = 0 := by
   rw [show (∑ t : k, χ (1 - t)) = ∑ t : k, χ t from (Equiv.subLeft (1 : k)).sum_comp χ]
   exact MulChar.sum_eq_zero_of_ne_one (pow_one χ ▸ pow_ne_one_of_lt_orderOf (by norm_num) (by omega))
  rw [hz, add_zero]
 have ha : jacobiSum χ χ = star (χ (4 : k)) * ∑ y : k, χ (1 - y ^ 2) := by
  rw [jacobiSum, Finset.mul_sum]
  have he : ∑ x : k, χ x * χ (1 - x) = ∑ y : k, χ ((1 - y) / 2) * χ (1 - (1 - y) / 2) := by
   let e := (Equiv.subLeft 1).trans (Equiv.mulRight₀ (2 : k)⁻¹ (inv_ne_zero h2))
   simpa [e, div_eq_mul_inv] using (e.sum_comp (fun x : k => χ x * χ (1 - x))).symm
  rw [he]
  apply Finset.sum_congr rfl
  intro y _
  rw [← map_mul]
  have hr : (1 - y) / 2 * (1 - (1 - y) / 2) = (1 - y ^ 2) / 4 := by
   field_simp
   <;> ring
  rw [hr, div_eq_mul_inv, map_mul, MulChar.star_apply', MulChar.inv_apply']
  ring
 rw [ha, hs]

end
variable (χ : MulChar k ℂ) (ψ : AddChar k ℂ) (hQ : Fintype.card k % 12 = 1) (hχ : orderOf χ = 6)
    (hψ : ψ ≠ 1)

include hQ hχ hψ in
private lemma gauss_dup :
 gaussPower χ ψ 1 * gaussPower χ ψ 4 = star (χ (4 : k)) * gaussPower χ ψ 2 * gaussPower χ ψ 3 := by
 have hn : χ ≠ 1 := by
  intro h; simp [h] at hχ
 have hn2 : χ * χ ≠ 1 := by
  rw [← pow_two]
  exact pow_ne_one_of_lt_orderOf (by norm_num) (by omega)
 have hn4 : χ ^ 3 * χ ≠ 1 := by
  rw [← pow_succ]
  exact pow_ne_one_of_lt_orderOf (by norm_num) (by omega)
 have H1 := jacobiSum_mul_nontrivial hn2 ψ
 have H2 := jacobiSum_mul_nontrivial hn4 ψ
 rw [← pow_two, jac_dup χ hQ hχ] at H1
 rw [← pow_succ] at H2
 have hQ0 : (Fintype.card k : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_pos.ne'
 have hg := gaussSum_ne_zero_of_nontrivial hQ0 hn (AddChar.IsPrimitive.of_ne_one hψ)
 unfold gaussPower
 simp only [pow_one]
 apply mul_right_cancel₀ hg
 let gaussSum₀ := gaussSum (χ ^ 4) ψ
 calc
  gaussSum χ ψ * gaussSum₀ * gaussSum χ ψ =
   gaussSum₀ * (gaussSum χ ψ * gaussSum χ ψ) := by ring
  _ = gaussSum₀ * (gaussSum (χ ^ 2) ψ * (star (χ (4:k)) * jacobiSum (χ ^ 3) χ)) := by rw [H1]
  _ = star (χ (4:k)) * gaussSum (χ ^ 2) ψ * (gaussSum₀ * jacobiSum (χ ^ 3) χ) := by ring
  _ = _ := by rw [H2]; ring

include hQ hχ hψ in
theorem normalizedGaussPower_sextic_duplication :
    normalizedGaussPower χ ψ 1 * normalizedGaussPower χ ψ 2 =
      star (χ (4 : k)) * normalizedGaussPower χ ψ 3 *
        normalizedGaussPower χ ψ 2 ^ 3 := by
 have hpos : (0 : ℝ) < Fintype.card k := by exact_mod_cast Fintype.card_pos
 have hs2 : (Real.sqrt (Fintype.card k) : ℂ) ^ 2 = Fintype.card k := by
  norm_cast; exact Real.sq_sqrt hpos.le
 have H : gaussPower χ ψ 1 * gaussPower χ ψ 2 * (Fintype.card k : ℂ) =
    star (χ (4:k)) * gaussPower χ ψ 3 * gaussPower χ ψ 2 ^ 3 := by
  calc
   _ = gaussPower χ ψ 1 * gaussPower χ ψ 4 * gaussPower χ ψ 2 ^ 2 := by rw [← (gaussPower_two_mul_four χ ψ hQ hχ hψ)]; ring
   _ = _ := by rw [(gauss_dup χ ψ hQ hχ hψ)]; ring
 unfold normalizedGaussPower
 field_simp
 rw [hs2]
 linear_combination H

end DedekindZetaZeroFree.FiniteGauss
