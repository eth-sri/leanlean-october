module

public import NearlyMinimax.ActualSeparatedPacket
public import NearlyMinimax.PacketAbsoluteMoments

@[expose] public section

/-! The genuine fine-pair three-point modulation rule and exterior density
packet from (new-pair-packet). The field mark is retained explicitly. -/
noncomputable section
open Set MeasureTheory Polynomial
open scoped BigOperators ENNReal
namespace NearlyMinimax

def fineModulationNode (i : Fin 3) : ℝ := if i = 0 then -1 else if i = 1 then 0 else 1
def fineModulationWeight (i : Fin 3) : ℝ := if i = 1 then -1 else 1 / 2

theorem fineModulation_eval (f : ℝ → ℝ) :
    (∑ i : Fin 3, fineModulationWeight i * f (fineModulationNode i)) =
      f (-1) / 2 - f 0 + f 1 / 2 := by
  simp [Fin.sum_univ_succ, fineModulationWeight, fineModulationNode]
  ring

theorem fineModulationNode_bound (i : Fin 3) : |fineModulationNode i| ≤ 1 := by
  fin_cases i <;> norm_num [fineModulationNode]

theorem fineModulationWeight_variation : (∑ i : Fin 3, |fineModulationWeight i|) = 2 := by
  norm_num [Fin.sum_univ_succ, fineModulationWeight]

theorem fineModulation_moment_zero :
    (∑ i : Fin 3, fineModulationWeight i * fineModulationNode i ^ 0) = 0 := by
  rw [fineModulation_eval (fun z => z ^ 0)]
  norm_num

section
variable (n : ℕ)

theorem fineModulation_moment_odd (hn : Odd n) :
    (∑ i : Fin 3, fineModulationWeight i * fineModulationNode i ^ n) = 0 := by
  rw [fineModulation_eval (fun z => z ^ n)]
  have hn0 : n ≠ 0 := by intro h; subst n; exact Nat.not_odd_zero hn
  simp [hn.neg_one_pow, zero_pow hn0]
  norm_num

theorem fineModulation_moment_even (hn : Even n) (hn0 : n ≠ 0) :
    (∑ i : Fin 3, fineModulationWeight i * fineModulationNode i ^ n) = 1 := by
  rw [fineModulation_eval (fun z => z ^ n)]
  simp [hn.neg_one_pow, zero_pow hn0]
  norm_num

theorem fineModulation_moment :
    (∑ i : Fin 3, fineModulationWeight i * fineModulationNode i ^ n) =
      if n = 0 then 0 else if Even n then 1 else 0 := by
  by_cases hn0 : n = 0
  · subst n; simp only [ite_true]; exact fineModulation_moment_zero
  · rw [ite_eq_right hn0]
    rcases Nat.even_or_odd n with hn | hn
    · rw [ite_eq_left hn]; exact fineModulation_moment_even n hn hn0
    · rw [ite_eq_right (Nat.not_even_iff_odd.mpr hn)]; exact fineModulation_moment_odd n hn

end

abbrev FinePairDensityIndex (M : ℕ) := Fin (M + 3) × Fin 3

def finePairDensityPrefactor (a b : ℝ) : ℝ := b ^ 2 / densityMargin a b 0 ^ 2

def finePairDensityAtom (a b : ℝ) (M : ℕ) (i : FinePairDensityIndex M) : ℝ × ℝ :=
  (exteriorNode a b (M + 2) i.1, fineModulationNode i.2)

def finePairDensityWeight (a b : ℝ) (M : ℕ) (i : FinePairDensityIndex M) : ℝ :=
  finePairDensityPrefactor a b * exteriorWeight a b (M + 2) i.1 * fineModulationWeight i.2

def finePairDensitySignedRule (a b : ℝ) (M : ℕ) : SignedMeasure (ℝ × ℝ) :=
  atomicSignedRule (finePairDensityAtom a b M) (finePairDensityWeight a b M)

variable (a b : ℝ) (M : ℕ)

theorem finePairDensityWeight_variation (ha : 0 < a) (hab : a < b) (M : ℕ) :
    (∑ i : FinePairDensityIndex M, |finePairDensityWeight a b M i|) =
      2 * |finePairDensityPrefactor a b| *
        Real.cosh ((M + 2 : ℕ) * exteriorTau ((a + b) / (b - a))) := by
  simp only [finePairDensityWeight, abs_mul, Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, fineModulationWeight_variation]
  rw [← Finset.sum_mul, ← Finset.mul_sum, exterior_rule_variation a b ha hab (M + 2) (by omega)]
  ring

section
variable {U : Type*}

def finePairDensityReset (a b : ℝ) (z eps : ℝ) (p ψ : U → ℝ) (u : U) : ℝ :=
  z + densityMargin a b z / b * p u * eps * ψ u

section
variable (a b : ℝ)

theorem finePairDensityReset_mem_interval (ha : 0 < a) (hab : a < b)
    (z eps : ℝ) (hz : z ∈ Icc a b) (heps : |eps| ≤ 1)
    (p ψ : U → ℝ) (u : U) (hp : p u ∈ Icc a b) (hψ : |ψ u| ≤ 1) :
    finePairDensityReset a b z eps p ψ u ∈ Icc a b := by
  have hh := localDensityReset_mem_interval a b ha hab 1 (by omega) z hz (fun _ => eps)
    (fun _ => heps) p (fun u _ => ψ u) u hp (fun _ => hψ)
  simpa [localDensityReset, finePairDensityReset, mul_comm, mul_left_comm, mul_assoc] using hh

theorem finePairDensityReset_slope_bound (ha : 0 < a) (hab : a < b)
    (z eps : ℝ) (hz : z ∈ Icc a b) (heps : |eps| ≤ 1)
    (ψ : U → ℝ) (u : U) (hψ : |ψ u| ≤ 1) :
    |densityMargin a b z / b * eps * ψ u| ≤ (b - a) / (4 * b) := by
  have hh := localDensityReset_slope_bound a b ha hab 1 (by omega) z hz (fun _ => eps)
    (fun _ => heps) (fun u _ => ψ u) u (fun _ => hψ)
  simpa [mul_assoc] using hh

end

end

theorem fineModulation_affine_zero (z c : ℝ) :
    (∑ i : Fin 3, fineModulationWeight i * (z + c * fineModulationNode i)) = 0 := by
  rw [fineModulation_eval (fun eps => z + c * eps)]
  ring

theorem fineModulation_quadratic (z c c' : ℝ) :
    (∑ i : Fin 3, fineModulationWeight i *
      ((z + c * fineModulationNode i) * (z + c' * fineModulationNode i))) = c * c' := by
  rw [fineModulation_eval (fun eps => (z + c * eps) * (z + c' * eps))]
  ring

theorem fineModulation_product {ι : Type*} [DecidableEq ι] (S : Finset ι) (z : ℝ) (c : ι → ℝ) :
    (∑ h : Fin 3, fineModulationWeight h * ∏ i ∈ S, (z + c i * fineModulationNode h)) =
      ∑ U ∈ S.powerset, z ^ (S.card - U.card) * (∏ i ∈ U, c i) *
        (if U.card = 0 then 0 else if Even U.card then 1 else 0) := by
  simp_rw [add_comm z, Finset.prod_add, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro U hU
  simp only [Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_sdiff_of_subset (Finset.mem_powerset.mp hU)]
  have he (h : Fin 3) : fineModulationWeight h *
      ((∏ i ∈ U, c i) * fineModulationNode h ^ U.card * z ^ (S.card - U.card)) =
      z ^ (S.card - U.card) * (∏ i ∈ U, c i) *
        (fineModulationWeight h * fineModulationNode h ^ U.card) := by ring
  simp_rw [he]
  rw [← Finset.mul_sum, fineModulation_moment]

def finePairCountCoefficient (a b : ℝ) (M k j : ℕ) : ℝ :=
  finePairDensityPrefactor a b * ∑ h : Fin (M + 3), exteriorWeight a b (M + 2) h *
    (exteriorNode a b (M + 2) h ^ (k - j) * (densityMargin a b (exteriorNode a b (M + 2) h) / b) ^ j)

theorem finePairCountCoefficient_two (ha : 0 < a) (hab : a < b) (M k : ℕ) :
    finePairCountCoefficient a b M k 2 = densityCountCoefficient a b M 2 k := by
  unfold finePairCountCoefficient finePairDensityPrefactor densityCountCoefficient
  rw [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro h _
  field_simp [densityMargin_zero_ne a b ha hab, (ha.trans hab).ne']

theorem finePairCountCoefficient_two_exact (ha : 0 < a) (hab : a < b)
    (M k : ℕ) (hk : 2 ≤ k) (hM : k ≤ M) :
    finePairCountCoefficient a b M k 2 = if k = 2 then 1 else 0 := by
  rw [finePairCountCoefficient_two a b ha hab M k]
  exact densityCountCoefficient_exact a b ha hab M 2 k (by omega) hk hM

theorem finePairCountCoefficient_abs_bound (ha : 0 < a) (hab : a < b)
    (M k j : ℕ) :
    |finePairCountCoefficient a b M k j| ≤
      |finePairDensityPrefactor a b| * (b ^ (k - j) * ((b - a) / (4 * b)) ^ j) *
        Real.cosh ((M + 2 : ℕ) * exteriorTau ((a + b) / (b - a))) := by
  have hb : 0 < b := ha.trans hab
  have hβ : 0 ≤ (b - a) / (4 * b) := by positivity
  have hterm (h : Fin (M + 3)) :
      |exteriorNode a b (M + 2) h ^ (k - j) *
        (densityMargin a b (exteriorNode a b (M + 2) h) / b) ^ j| ≤
      b ^ (k - j) * ((b - a) / (4 * b)) ^ j := by
    have hz := exteriorNode_mem a b hab.le (M + 2) h
    have ht := densityMargin_bounds a b hab _ hz
    have ht0 : 0 ≤ densityMargin a b (exteriorNode a b (M + 2) h) / b := div_nonneg ht.1 hb.le
    have htle : densityMargin a b (exteriorNode a b (M + 2) h) / b ≤ (b - a) / (4 * b) := (div_le_div_of_nonneg_right ht.2.2.2 hb.le).trans_eq (by ring)
    rw [abs_mul, abs_pow, abs_pow, abs_of_nonneg (ha.le.trans hz.1), abs_of_nonneg ht0]
    exact mul_le_mul (pow_le_pow_left₀ (ha.le.trans hz.1) hz.2 _)
      (pow_le_pow_left₀ ht0 htle _) (pow_nonneg ht0 _) (pow_nonneg hb.le _)
  unfold finePairCountCoefficient
  rw [abs_mul]
  apply (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg _)).trans
  calc
    _ ≤ |finePairDensityPrefactor a b| *
        ∑ h : Fin (M + 3), |exteriorWeight a b (M + 2) h| *
          (b ^ (k - j) * ((b - a) / (4 * b)) ^ j) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply Finset.sum_le_sum
      intro h _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hterm h) (abs_nonneg _)
    _ = _ := by
      rw [← Finset.sum_mul, exterior_rule_variation a b ha hab (M + 2) (by omega)]
      ring

theorem finePairDensityWeight_exponential_cost (ha : 0 < a) (hab : a < b) (M : ℕ) :
    (∑ h : FinePairDensityIndex M, |finePairDensityWeight a b M h|) ≤
      (2 * |finePairDensityPrefactor a b| * Real.exp (2 * exteriorTau ((a + b) / (b - a)))) *
        Real.exp ((M : ℝ) * exteriorTau ((a + b) / (b - a))) := by
  rw [finePairDensityWeight_variation a b ha hab M]
  have he : Real.cosh ((M + 2 : ℕ) * exteriorTau ((a + b) / (b - a))) ≤
      Real.exp ((M + 2 : ℕ) * exteriorTau ((a + b) / (b - a))) := by
    rw [← exterior_rule_variation a b ha hab (M + 2) (by omega)]
    exact exterior_rule_variation_le_exp a b ha hab (M + 2) (by omega)
  apply (mul_le_mul_of_nonneg_left he (by positivity)).trans_eq
  rw [Nat.cast_add, Nat.cast_ofNat, add_mul, Real.exp_add]
  ring

theorem finePairDensitySignedRule_integral (f : ℝ → ℝ → ℝ) :
    (∫ᵛ e, f e.1 e.2 ∂<•finePairDensitySignedRule a b M) =
      finePairDensityPrefactor a b * ∑ j : Fin (M + 3), exteriorWeight a b (M + 2) j *
        ∑ i : Fin 3, fineModulationWeight i * f (exteriorNode a b (M + 2) j) (fineModulationNode i) := by
  rw [finePairDensitySignedRule, atomicSignedRule_integral]
  simp only [finePairDensityAtom, finePairDensityWeight, Fintype.sum_prod_type]
  simp_rw [mul_assoc, ← Finset.mul_sum]

theorem finePairDensitySignedRule_product_expansion {U : Type*} [DecidableEq U]
    (a b : ℝ) (M : ℕ) (S : Finset U) (p ψ : U → ℝ) :
    (∫ᵛ e, ∏ u ∈ S, finePairDensityReset a b e.1 e.2 p ψ u
      ∂<•finePairDensitySignedRule a b M) =
      ∑ W ∈ S.powerset, finePairCountCoefficient a b M S.card W.card * (∏ u ∈ W, p u * ψ u) *
        (if W.card = 0 then 0 else if Even W.card then 1 else 0) := by
  rw [finePairDensitySignedRule_integral a b M (fun z eps => ∏ u ∈ S, finePairDensityReset a b z eps p ψ u)]
  have he (z eps : ℝ) (u : U) : finePairDensityReset a b z eps p ψ u =
      z + (densityMargin a b z / b * (p u * ψ u)) * eps := by
    unfold finePairDensityReset
    ring
  have hprod (z : ℝ) (W : Finset U) :
      (∏ u ∈ W, densityMargin a b z / b * (p u * ψ u)) =
      (densityMargin a b z / b) ^ W.card * (∏ u ∈ W, p u * ψ u) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const]
  simp_rw [he, fineModulation_product, hprod]
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro W hW
  unfold finePairCountCoefficient
  have hterm (h : Fin (M + 3)) : finePairDensityPrefactor a b *
      (exteriorWeight a b (M + 2) h *
       (exteriorNode a b (M + 2) h ^ (S.card - W.card) *
        ((densityMargin a b (exteriorNode a b (M + 2) h) / b) ^ W.card * ∏ u ∈ W, p u * ψ u) *
        (if W.card = 0 then 0 else if Even W.card then 1 else 0))) =
      finePairDensityPrefactor a b *
        (exteriorWeight a b (M + 2) h * (exteriorNode a b (M + 2) h ^ (S.card - W.card) *
          (densityMargin a b (exteriorNode a b (M + 2) h) / b) ^ W.card)) *
        ((∏ u ∈ W, p u * ψ u) * (if W.card = 0 then 0 else if Even W.card then 1 else 0)) := by ring
  simp_rw [hterm]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  ring

theorem finePairDensitySignedRule_mass_zero :
    (∫ᵛ _e, (1 : ℝ) ∂<•finePairDensitySignedRule a b M) = 0 := by
  rw [finePairDensitySignedRule_integral a b M (fun _ _ => 1)]
  have hw : (∑ i : Fin 3, fineModulationWeight i) = 0 := by
    simpa only [pow_zero, mul_one] using fineModulation_moment_zero
  simp [hw]

section
variable {U : Type*} (a b : ℝ)

theorem finePairDensitySignedRule_linear_zero (M : ℕ)
    (p ψ : U → ℝ) (u : U) :
    (∫ᵛ e, finePairDensityReset a b e.1 e.2 p ψ u
      ∂<•finePairDensitySignedRule a b M) = 0 := by
  rw [finePairDensitySignedRule_integral a b M (fun z eps => finePairDensityReset a b z eps p ψ u)]
  have he (z eps : ℝ) : finePairDensityReset a b z eps p ψ u =
      z + (densityMargin a b z / b * p u * ψ u) * eps := by
    unfold finePairDensityReset
    ring
  simp_rw [he, fineModulation_affine_zero]
  simp

theorem finePairDensitySignedRule_pair_exact (ha : 0 < a) (hab : a < b)
    (M : ℕ) (hM : 2 ≤ M) (p ψ : U → ℝ) (u v : U) :
    (∫ᵛ e, finePairDensityReset a b e.1 e.2 p ψ u * finePairDensityReset a b e.1 e.2 p ψ v
      ∂<•finePairDensitySignedRule a b M) = p u * p v * ψ u * ψ v := by
  rw [finePairDensitySignedRule_integral a b M
    (fun z eps => finePairDensityReset a b z eps p ψ u * finePairDensityReset a b z eps p ψ v)]
  have he (z eps : ℝ) (u : U) : finePairDensityReset a b z eps p ψ u =
      z + (densityMargin a b z / b * p u * ψ u) * eps := by
    unfold finePairDensityReset
    ring
  simp_rw [he, fineModulation_quadratic]
  have hc := densityCountCoefficient_exact a b ha hab M 2 2 (by omega) (by omega) hM
  simp only [densityCountCoefficient, Nat.sub_self, pow_zero, one_mul, ite_true] at hc
  have hθ : densityMargin a b 0 ^ 2 ≠ 0 := pow_ne_zero _ (densityMargin_zero_ne a b ha hab)
  have hs : (∑ j : Fin (M + 3), exteriorWeight a b (M + 2) j *
      densityMargin a b (exteriorNode a b (M + 2) j) ^ 2) = densityMargin a b 0 ^ 2 := (div_eq_iff hθ).mp hc |>.trans (one_mul _)
  have hterm (j : Fin (M + 3)) : exteriorWeight a b (M + 2) j *
      ((densityMargin a b (exteriorNode a b (M + 2) j) / b * p u * ψ u) *
       (densityMargin a b (exteriorNode a b (M + 2) j) / b * p v * ψ v)) =
      exteriorWeight a b (M + 2) j * densityMargin a b (exteriorNode a b (M + 2) j) ^ 2 *
      ((p u * p v * ψ u * ψ v) / b ^ 2) := by ring
  simp_rw [hterm]
  rw [← Finset.sum_mul, hs]
  unfold finePairDensityPrefactor
  field_simp [hθ, densityMargin_zero_ne a b ha hab, (ha.trans hab).ne']

end

section Field
variable {Z : Type*} [MeasurableSpace Z]

variable {U : Type*} (a b : ℝ)

def finePairFieldReset (a b : ℝ) (M : ℕ) (p : U → ℝ) (ψ : Z → U → ℝ)
    (e : Z × FinePairDensityIndex M) (u : U) : ℝ :=
  finePairDensityReset a b (finePairDensityAtom a b M e.2).1
    (finePairDensityAtom a b M e.2).2 p (ψ e.1) u

theorem finePairFieldReset_mem_interval (ha : 0 < a) (hab : a < b)
    (M : ℕ) (p : U → ℝ) (hp : ∀ u, p u ∈ Icc a b) (ψ : Z → U → ℝ)
    (hψ : ∀ ζ u, |ψ ζ u| ≤ 1) (e : Z × FinePairDensityIndex M) (u : U) :
    finePairFieldReset a b M p ψ e u ∈ Icc a b :=
  finePairDensityReset_mem_interval a b ha hab _ _
    (exteriorNode_mem a b hab.le (M + 2) e.2.1) (fineModulationNode_bound e.2.2)
    p (ψ e.1) u (hp u) (hψ e.1 u)

theorem finePairFieldReset_abs_le (ha : 0 < a) (hab : a < b)
    (M : ℕ) (p : U → ℝ) (hp : ∀ u, p u ∈ Icc a b) (ψ : Z → U → ℝ)
    (hψ : ∀ ζ u, |ψ ζ u| ≤ 1) (e : Z × FinePairDensityIndex M) (u : U) :
    |finePairFieldReset a b M p ψ e u| ≤ b := by
  have hh := finePairFieldReset_mem_interval a b ha hab M p hp ψ hψ e u
  rw [abs_of_nonneg (ha.le.trans hh.1)]
  exact hh.2

end Field

end NearlyMinimax
