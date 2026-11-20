/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module
public import CCDN.Surface.PowerPrimeWindow
public import CCDN.Surface.CongruenceFamily
import CCDN.ForMathlib.MvPolynomial
@[expose] public section
namespace CCDN.SurfaceWindow
noncomputable section
open Finset MvPolynomial

variable {N : ℕ} {A B : ℝ} (W : SurfaceWindow N B)

/-- The nodes needed in the residue cover have depth at most nine. -/
abbrev nodes := W.primes.powerset.filter fun P => P.card ≤ 9
abbrev lies (R : W.nodes) : R.val ⊆ W.primes := mem_powerset.mp (mem_filter.mp R.2).1
abbrev depth (R : W.nodes) : R.val.card ≤ 9 := (mem_filter.mp R.2).2
abbrev prime (R : W.nodes) (p : ℕ) (hp : p ∈ R.val) := (W.bounds p (W.lies R hp)).1
abbrev node (P : Finset ℕ) (h : P ⊆ W.primes) (k : P.card ≤ 9) : W.nodes := ⟨P,mem_filter.mpr ⟨mem_powerset.mpr h,k⟩⟩
abbrev parent (R : W.nodes) (p : ℕ) := W.node (R.val.erase p) ((erase_subset p _).trans (W.lies R)) ((card_le_card (erase_subset p _)).trans (W.depth R))

variable {f : IntegerPolynomial 3} (F : SurfaceCongruenceFamily f B A)

abbrev equation (R : W.nodes) (r : SmoothAffineResidueFamily f R.val) := rationalEquation (F.auxiliary R.val (W.prime R) r)
abbrev levelCost (N : ℕ) (A : ℝ) := 2*A*(1+9*((N:ℝ)+1))

lemma degree_at_node (hB : 1 ≤ B) (hA : 0 ≤ A) (hd : 5 ≤ f.totalDegree) (R : W.nodes) (r : SmoothAffineResidueFamily f R.val) :
    ((W.equation F R r).totalDegree : ℝ) ≤ levelCost N A * boxLog B * windowUnit B ^ (9-R.val.card) := by
  let Y := windowUnit B
  let T := boxLog B
  let Q := ∑ p ∈ R.val, Real.log p
  have ht : 1 ≤ T := boxLog_one_le hB
  have hy : 1 ≤ Y := windowUnit_one_le hB
  have hp (p) (hp : p ∈ R.val) := (W.bounds p (W.lies R hp)).2
  have hlo : Y^R.val.card ≤ Real.exp Q := by
    dsimp only [Y,windowUnit]; rw [← Real.exp_nat_mul, Real.exp_le_exp]
    have hl (p) (h : p ∈ R.val) := (Real.le_log_iff_exp_le (by exact_mod_cast (W.prime R p h).pos)).mpr (hp p h).1.le
    simpa using sum_le_sum hl
  have hub : Q ≤ 9*((N:ℝ)+1)*T := by
    have hb (p) (h : p ∈ R.val) : Real.log p ≤ ((N:ℝ)+1)*T := by
      have := Real.log_le_log (by exact_mod_cast (W.prime R p h).pos) (hp p h).2
      rw [Real.log_mul (by positivity) (Real.exp_ne_zero _),Real.log_pow,Real.log_exp] at this
      have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
      nlinarith [mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg (α := ℝ) N),le_mul_of_one_le_right (Nat.cast_nonneg (α := ℝ) N) ht]
    calc _ ≤ (R.val.card:ℝ)*(((N:ℝ)+1)*T) := by simpa using sum_le_sum hb
         _ ≤ 9*(((N:ℝ)+1)*T) := by gcongr; exact_mod_cast W.depth R
         _ = _ := by ring
  have hQ : 0 ≤ Q := sum_nonneg (fun p _ => Real.log_natCast_nonneg p)
  have hlog := Real.log_nonneg hB
  let U := Y^(9-R.val.card)
  have hu : 1 ≤ U := one_le_pow₀ hy
  have hr : B^(1/Real.sqrt (f.totalDegree:ℝ))/Real.exp Q ≤ U := by
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    calc _ ≤ Y^9 := surface_root_le_window hB hd
         _ = U*Y^R.val.card := by dsimp only [U]; rw [← pow_add,Nat.sub_add_cancel (W.depth R)]
         _ ≤ _ := by gcongr
  rw [equation, rational_map_totalDegree]
  apply (F.degree_le R.val (W.prime R) r).trans
  change A*(_+1)*(1+Real.log B+Q) ≤ levelCost N A * T * U
  calc _ ≤ A*(2*U)*((1+9*((N:ℝ)+1))*T) := by
             gcongr <;> dsimp only [T] at * <;> linarith
       _ = _ := by ring

abbrev residueCost (d N : ℕ) := ((d:ℝ)*(2^N)^2)^9

lemma residue_card (hB : 1 ≤ B) (hd : 1 ≤ f.totalDegree) (R : W.nodes) :
    (Nat.card (SmoothAffineResidueFamily f R.val):ℝ) ≤ residueCost f.totalDegree N * (windowUnit B ^ R.val.card)^2 := by
  let U := (2:ℝ)^N
  let Y := windowUnit B
  let k := R.val.card
  have hu : 1 ≤ U := one_le_pow₀ (by norm_num)
  have hy : 1 ≤ Y := windowUnit_one_le hB
  have hdR : (1:ℝ) ≤ f.totalDegree := by exact_mod_cast hd
  have hq : (∏ p ∈ R.val, (p:ℝ)) ≤ (U*Y)^k := by
    simpa using Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun p hp => (W.bounds p (W.lies R hp)).2.2)
  calc _ ≤ (f.totalDegree:ℝ)^k*(∏ p ∈ R.val, (p:ℝ))^2 := by rw [← Nat.cast_prod]; exact_mod_cast smoothAffineResidueFamily_card_le (n:=2) f R.val (W.prime R)
       _ ≤ (f.totalDegree:ℝ)^k*((U*Y)^k)^2 := by gcongr
       _ = ((f.totalDegree:ℝ)*U^2)^k*(Y^k)^2 := by rw [mul_pow,mul_pow]; ring
       _ ≤ _ := by gcongr; exact pow_le_pow_right₀ (one_le_mul_of_one_le_of_one_le hdR (one_le_pow₀ hu)) (W.depth R)

end
end CCDN.SurfaceWindow
