module

public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.GroupTheory.Perm.DomMulAct
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Fin.Rev
public import Mathlib.Tactic.FinCases
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Character.Basic

public section

@[expose] section

namespace OAI

noncomputable section

open Filter MatrixMultiplication.Foundation Polynomial
open scoped BigOperators Topology Classical

namespace MatrixMultiplication.Foundation

variable {A I J : Type*} [Fintype A] [DecidableEq A] [Fintype I] [Fintype J] [DecidableEq I]

def wordPopulation (w : I → A) (a : A) : ℕ := Fintype.card {i // w i = a}

omit [Fintype A] [DecidableEq I] in
theorem wordPopulation_reindex (w : I → A) (e : J ≃ I) (a : A) :
    wordPopulation (w ∘ e) a = wordPopulation w a :=
  Fintype.card_congr (Equiv.subtypeEquiv e fun _ => Iff.rfl)

abbrev ExactWords (counts : A → ℕ) :=
  {w : Fin (∑ a, counts a) → A // ∀ a, wordPopulation w a = counts a}

theorem exactWords_nonempty (counts : A → ℕ) : Nonempty (ExactWords counts) := by
  let e : Fin (∑ a, counts a) ≃ (Σ a, Fin (counts a)) := Fintype.equivOfCardEq (by simp)
  refine ⟨⟨(fun i : Σ a, Fin (counts a) => i.1) ∘ e, fun a => ?_⟩⟩
  rw [wordPopulation_reindex]
  let ea : {i : Σ b, Fin (counts b) // i.1 = a} ≃ Fin (counts a) :=
    ⟨fun i => i.property ▸ i.val.2, fun i => ⟨⟨a, i⟩, rfl⟩,
      by rintro ⟨⟨b, i⟩, rfl⟩; rfl, fun _ => rfl⟩
  exact (Fintype.card_congr ea).trans (Fintype.card_fin _)

theorem exactWords_card (counts : A → ℕ) :
    Fintype.card (ExactWords counts) = Nat.multinomial Finset.univ counts := by
  obtain ⟨w⟩ := exactWords_nonempty counts
  let I₀ := Fin (∑ a, counts a)
  let G := DomMulAct (Equiv.Perm I₀)
  let : Fintype G := Fintype.ofEquiv (Equiv.Perm I₀) DomMulAct.mk
  let eOrbit : ExactWords counts ≃ MulAction.orbit G w.val :=
    Equiv.subtypeEquivRight fun v => by
      rw [show (∀ a, wordPopulation v a = counts a) ↔ ∀ a, wordPopulation v a = wordPopulation w.val a by
        simp only [w.property], MulAction.mem_orbit_iff]
      exact ⟨fun h => ⟨DomMulAct.mk (Equiv.ofFiberEquiv fun a => Fintype.equivOfCardEq (h a)),
          funext fun i => Equiv.ofFiberEquiv_map _ i⟩,
        fun ⟨g, hg⟩ a => hg ▸ wordPopulation_reindex w.val (DomMulAct.mk.symm g) a⟩
  let eStab : MulAction.stabilizer G w.val ≃ {e : Equiv.Perm I₀ // w.val ∘ e = w.val} :=
    Equiv.subtypeEquiv DomMulAct.mk.symm fun _ => DomMulAct.mem_stabilizer_iff
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group G w.val
  rw [← Fintype.card_congr eOrbit, Fintype.card_congr eStab, DomMulAct.stabilizer_card w.val,
    (Fintype.card_congr DomMulAct.mk.symm).trans Fintype.card_perm] at h
  simp only [I₀, show ∀ i, Fintype.card {a // w.val a = i} = counts i from w.property, Fintype.card_fin] at h
  exact Nat.eq_div_of_mul_eq_left (ne_of_gt (Nat.prod_factorial_pos Finset.univ counts)) h

theorem exactWords_card_pos (counts : A → ℕ) : 0 < Fintype.card (ExactWords counts) := by
  rw [exactWords_card]; exact Nat.multinomial_pos Finset.univ counts

def entropyTerm (p : ℝ) : ℝ := -p * Real.log p

def finiteEntropy {A : Type*} [Fintype A] (p : A → ℝ) : ℝ := ∑ a, entropyTerm (p a)

@[simp] theorem entropyTerm_zero : entropyTerm 0 = 0 := by simp [entropyTerm]

structure FiniteLaw (A : Type*) [Fintype A] where
  mass : A → ℝ
  nonneg : ∀ a, 0 ≤ mass a
  total : ∑ a, mass a = 1

@[fun_prop] theorem continuous_entropyTerm : Continuous entropyTerm :=
  Real.continuous_negMulLog

@[fun_prop] theorem continuous_finiteEntropy {A : Type*} [Fintype A] :
    Continuous (finiteEntropy : (A → ℝ) → ℝ) :=
  continuous_finsetSum _ fun value _ => continuous_entropyTerm.comp (continuous_apply value)

namespace FiniteLaw

def uniform (A : Type*) [Fintype A] [Nonempty A] : FiniteLaw A where
  mass _a := (Fintype.card A : ℝ)⁻¹
  nonneg _a := inv_nonneg.mpr (Nat.cast_nonneg _)
  total := by
    have hn : (Fintype.card A : ℝ) ≠ 0 := (Nat.cast_pos.mpr Fintype.card_pos).ne'
    simp [Finset.sum_const, nsmul_eq_mul, hn]

end FiniteLaw

def factorialLogRemainder (n : ℕ) : ℝ :=
  Real.log (Nat.factorial n : ℝ) - ((n : ℝ) * Real.log n - n)

@[simp] theorem factorialLogRemainder_zero : factorialLogRemainder 0 = 0 := by
  simp [factorialLogRemainder]

theorem tendsto_factorialLogRemainder_div :
    Tendsto (fun n : ℕ => factorialLogRemainder n / (n : ℝ)) atTop (𝓝 0) := by
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hstirling : Tendsto (fun n : ℕ => Real.log (Stirling.stirlingSeq n) / (n : ℝ)) atTop (𝓝 0) :=
    (Stirling.tendsto_stirlingSeq_sqrt_pi.log (by positivity)).div_atTop hnat
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq] using
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hnat
  have hsum : Tendsto
      (fun n : ℕ => Real.log (Stirling.stirlingSeq n) / (n : ℝ) +
        (1 / 2 : ℝ) * (Real.log 2 / (n : ℝ) + Real.log (n : ℝ) / (n : ℝ))) atTop (𝓝 0) := by
    simpa using hstirling.add (((tendsto_const_nhds.div_atTop hnat).add hlog).const_mul (1 / 2 : ℝ))
  apply hsum.congr'
  filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have h := Stirling.log_stirlingSeq_formula (m + 1)
  rw [Real.log_div (by positivity) (Real.exp_ne_zero _), Real.log_exp] at h
  have hrem : factorialLogRemainder (m + 1) =
      Real.log (Stirling.stirlingSeq (m + 1)) + (1 / 2 : ℝ) * Real.log (2 * (m + 1 : ℕ)) := by
    unfold factorialLogRemainder; linarith
  rw [hrem, Real.log_mul (by norm_num) (Nat.cast_ne_zero.mpr hn)]
  ring

theorem tendsto_factorialLogRemainder_mul_div (c : ℕ) :
    Tendsto (fun t : ℕ => factorialLogRemainder (t * c) / (t : ℝ)) atTop (𝓝 0) := by
  by_cases hc : c = 0
  · subst c; simp
  have hscaled : Tendsto
      (fun t : ℕ => factorialLogRemainder (t * c) / (t * c : ℕ) * (c : ℝ)) atTop (𝓝 0) := by
    simpa using (tendsto_factorialLogRemainder_div.comp
      (tendsto_id.atTop_mul_const' (Nat.pos_of_ne_zero hc))).mul_const (c : ℝ)
  refine hscaled.congr fun t => ?_
  by_cases ht : t = 0
  · simp [ht]
  rw [Nat.cast_mul]
  field_simp [Nat.cast_ne_zero.mpr hc, Nat.cast_ne_zero.mpr ht]

theorem mul_log_mul (x y : ℝ) :
    (x * y) * Real.log (x * y) = (x * Real.log x) * y + x * (y * Real.log y) := by
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0; · simp [hy]
  rw [Real.log_mul hx hy]; ring

theorem tendsto_log_exactWords_card_mul (counts : A → ℕ)
    (hD : 0 < ∑ a, counts a) :
    Tendsto
      (fun t : ℕ => Real.log (Fintype.card (ExactWords (fun a => t * counts a)) : ℝ) /
        ((t : ℝ) * (∑ a, counts a : ℕ)))
      atTop
      (𝓝 (finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)))) := by
  simp only [exactWords_card]
  have hD' : ((∑ a, counts a : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
  have hsum : Tendsto (fun t : ℕ => ∑ a, factorialLogRemainder (t * counts a) / (t : ℝ))
      atTop (𝓝 0) := by
    simpa using tendsto_finsetSum Finset.univ fun a _ => tendsto_factorialLogRemainder_mul_div (counts a)
  have herror : Tendsto
      (fun t : ℕ =>
        (factorialLogRemainder (t * ∑ a, counts a) / (t : ℝ) -
          ∑ a, factorialLogRemainder (t * counts a) / (t : ℝ)) / (∑ a, counts a : ℕ)) atTop (𝓝 0) := by
    simpa using ((tendsto_factorialLogRemainder_mul_div (∑ a, counts a)).sub hsum).div_const (∑ a, counts a : ℕ)
  have hlimit : Tendsto
      (fun t : ℕ =>
        finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) +
          (factorialLogRemainder (t * ∑ a, counts a) / (t : ℝ) -
            ∑ a, factorialLogRemainder (t * counts a) / (t : ℝ)) / (∑ a, counts a : ℕ))
      atTop (𝓝 (finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)))) := by
    simpa only [add_zero] using tendsto_const_nhds.add herror
  apply hlimit.congr'
  filter_upwards [eventually_ne_atTop (0 : ℕ)] with t ht
  have ht' : (t : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ht
  have hdiv_scalar (x y : ℝ) : entropyTerm (x / y) = entropyTerm x / y + (x / y) * Real.log y := by
    by_cases hx : x = 0; · simp [hx]
    by_cases hy : y = 0; · simp [hy]
    rw [entropyTerm, Real.log_div hx hy, entropyTerm]; ring
  have hnorm : finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) =
      Real.log (∑ a, counts a : ℕ) -
        (∑ a, (counts a : ℝ) * Real.log (counts a : ℝ)) / (∑ a, counts a : ℕ) := by
    unfold finiteEntropy
    simp only [hdiv_scalar]
    simp only [entropyTerm, neg_mul,
      Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_mul, Finset.sum_neg_distrib]
    rw [← Nat.cast_sum, div_self hD']; ring
  have hmult (c : A → ℕ) : Real.log (Nat.multinomial Finset.univ c : ℝ) =
      (∑ a, c a : ℕ) * Real.log (∑ a, c a : ℕ) - (∑ a, (c a : ℝ) * Real.log (c a : ℝ)) +
        factorialLogRemainder (∑ a, c a) - ∑ a, factorialLogRemainder (c a) := by
    have hspec : (∏ a, (Nat.factorial (c a) : ℝ)) * (Nat.multinomial Finset.univ c : ℝ) =
        (Nat.factorial (∑ a, c a) : ℝ) := by exact_mod_cast Nat.multinomial_spec Finset.univ c
    have hlog := congrArg Real.log hspec
    rw [Real.log_mul (Finset.prod_ne_zero_iff.mpr fun a _ => by positivity)
        (by exact_mod_cast (Nat.ne_of_gt (Nat.multinomial_pos Finset.univ c))),
      Real.log_prod (fun a _ => by positivity)] at hlog
    unfold factorialLogRemainder
    simp only [Finset.sum_sub_distrib, ← Nat.cast_sum]
    linarith
  have hmuleq : Real.log (Nat.multinomial Finset.univ (fun a => t * counts a) : ℝ) =
      (t : ℝ) * ((∑ a, counts a : ℕ) * Real.log (∑ a, counts a : ℕ) -
        ∑ a, (counts a : ℝ) * Real.log (counts a : ℝ)) +
        factorialLogRemainder (t * ∑ a, counts a) -
        ∑ a, factorialLogRemainder (t * counts a) := by
    have htsum : (∑ a, t * counts a) = t * ∑ a, counts a := (Finset.mul_sum Finset.univ counts t).symm
    have hlogs : (∑ a, ((t : ℝ) * counts a) * Real.log ((t : ℝ) * counts a)) =
        ((t : ℝ) * Real.log t) * (∑ a, counts a : ℕ) +
          (t : ℝ) * ∑ a, (counts a : ℝ) * Real.log (counts a : ℝ) := by
      simp only [mul_log_mul, Finset.sum_add_distrib, ← Finset.mul_sum, ← Nat.cast_sum]
    rw [hmult, htsum]
    simp only [Nat.cast_mul]
    rw [mul_log_mul, hlogs]; ring
  rw [hmuleq, hnorm, ← Finset.sum_div]
  field_simp [ht', hD']; ring

end MatrixMultiplication.Foundation

namespace MatrixMultiplication.AuxiliarySeparation

def binaryLaw (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) : FiniteLaw (Fin 2) where
  mass i := if i = 0 then q else 1 - q
  nonneg i := by fin_cases i <;> [simpa using hq₀; simpa using sub_nonneg.mpr hq₁]
  total := by simp [Fin.sum_univ_two]

variable {K : Type*} [CommSemiring K]
variable {A : Type*} [Fintype A] [DecidableEq A]

theorem tag_of_integral_bounds
    (q : FiniteLaw A) (values : A → ℝ) (p source C : ℝ)
    (hvalues : ∀ a, 0 < values a) (hsource : 0 < source) (hC : 0 < C)
    (hfinite : ∀ counts : A → ℕ, 0 < ∑ a, counts a →
      (Fintype.card (ExactWords counts) : ℝ) ^ p * ∏ a, values a ^ counts a ≤
        C * source ^ (∑ a, counts a)) :
    Real.exp (p * finiteEntropy q.mass) * ∏ a, values a ^ q.mass a ≤ source := by
  have ⟨a₀⟩ : Nonempty A := by by_contra! h; have := q.total; simp at this
  let c (n : ℕ) (a : A) : ℕ := ⌊((n : ℝ) + 1) * q.mass a⌋₊ + 1
  have hcpos (n : ℕ) : 0 < ∑ a, c n a :=
    Finset.sum_pos' (fun a _ => Nat.zero_le _) ⟨a₀, Finset.mem_univ a₀, Nat.succ_pos _⟩
  have hc (a : A) : Tendsto (fun n : ℕ => (c n a : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 (q.mass a)) := by
    have h0 : Tendsto (fun n : ℕ => (c n a : ℝ) / ((n : ℝ) + 1) - q.mass a) atTop (𝓝 0) := by
      refine squeeze_zero (fun n => ?_) (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
      · rw [sub_nonneg, le_div_iff₀ (by positivity)]
        dsimp only [c]; push_cast
        linarith [Nat.lt_floor_add_one (((n : ℝ) + 1) * q.mass a)]
      · rw [div_sub' (by positivity), div_le_div_iff_of_pos_right (by positivity)]
        dsimp only [c]; push_cast
        linarith [Nat.floor_le (mul_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1) (q.nonneg a))]
    simpa only [sub_add_cancel, zero_add] using h0.add_const (q.mass a)
  have hsum : Tendsto (fun n : ℕ => (∑ b, c n b : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 1) := by
    simpa only [Finset.sum_div, q.total] using tendsto_finsetSum Finset.univ fun b _ => hc b
  have hfreq (a : A) :
      Tendsto (fun n : ℕ => (c n a : ℝ) / (∑ b, c n b : ℕ)) atTop (𝓝 (q.mass a)) := by
    have h := (hc a).div hsum one_ne_zero
    simp only [div_one] at h
    refine h.congr fun n => ?_
    push_cast
    exact div_div_div_cancel_right₀ (by positivity : ((n : ℝ) + 1) ≠ 0) _ _
  have hlimit := ((continuous_finiteEntropy.continuousAt.tendsto.comp (tendsto_pi_nhds.mpr hfreq)).const_mul p).add
    (tendsto_finsetSum Finset.univ fun a _ => (hfreq a).mul_const (Real.log (values a)))
  have hlog : p * finiteEntropy q.mass + ∑ a, q.mass a * Real.log (values a) ≤ Real.log source := by
    refine le_of_tendsto hlimit (Eventually.of_forall fun n => ?_)
    have hD := hcpos n
    let u (t : ℕ) : ℝ := (Fintype.card (ExactWords (fun a => t * c n a)) : ℝ) ^ p *
      ∏ a, values a ^ (t * c n a)
    have hpos (t : ℕ) : 0 < u t :=
      mul_pos (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (exactWords_card_pos _)) p)
        (Finset.prod_pos fun a _ => pow_pos (hvalues a) _)
    apply (Real.le_log_iff_exp_le hsource).2
    apply exp_le_of_tendsto_log_div hsource hC (tendsto_id.atTop_mul_const' hD) (Eventually.of_forall hpos)
    · have hlim := ((tendsto_log_exactWords_card_mul (c n) hD).const_mul p).add_const
        (∑ a, ((c n a : ℝ) / (∑ a, c n a : ℕ)) * Real.log (values a))
      simp only [Nat.cast_mul, id_eq]
      apply hlim.congr'
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with t ht
      dsimp only [u]
      rw [Real.log_mul (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (exactWords_card_pos _)) p).ne'
          (Finset.prod_pos fun a _ => pow_pos (hvalues a) _).ne',
        Real.log_rpow (Nat.cast_pos.mpr (exactWords_card_pos _)),
        Real.log_prod fun a _ => (pow_pos (hvalues a) _).ne']
      simp only [Real.log_pow, Nat.cast_mul, mul_assoc, ← Finset.mul_sum]
      have ht' : (t : ℝ) ≠ 0 := (Nat.cast_pos.mpr ht).ne'
      have hD' : (∑ a, c n a : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
      simp_rw [div_mul_eq_mul_div]
      rw [← Finset.sum_div]
      push_cast; field_simp
    · filter_upwards [eventually_gt_atTop (0 : ℕ)] with t ht
      have hsum' : (∑ a, t * c n a) = t * ∑ a, c n a := (Finset.mul_sum _ _ _).symm
      simpa only [u, hsum', id_eq] using hfinite (fun a => t * c n a) (hsum' ▸ Nat.mul_pos ht hD)
  have h := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log hsource, Real.exp_add, Real.exp_sum] at h
  convert h using 1
  congr 1
  exact Finset.prod_congr rfl fun a _ => by rw [Real.rpow_def_of_pos (hvalues a), mul_comm]

section Tag

variable {s : ℕ} {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]

theorem Character.value_sharedFirstTensor_eq_sum (χ : Character K)
    (B : Fin s → Tensor K X Y Z) (ly : Y → Fin s) (lz : Z → Fin s)
    (hsupport : ∀ i x y z, B i x y z ≠ 0 → ly y = i ∧ lz z = i) :
    χ.value (sharedFirstTensor B) = χ.value (∑ i, B i) := by
  have hs : ∀ x y z, sharedFirstTensor B x y z ≠ 0 →
      x ∈ Set.range (id : X → X) ∧
        y ∈ Set.range (fun y => (ly y, y)) ∧
        z ∈ Set.range (fun z => (lz z, z)) := by
    intro x y z h
    have hyz : y.1 = z.1 := by by_contra hne; exact h (by simp [sharedFirstTensor, hne])
    have hb : B y.1 x y.2 z.2 ≠ 0 := by simpa only [sharedFirstTensor, hyz, ↓reduceIte] using h
    obtain ⟨hy, hz⟩ := hsupport y.1 x y.2 z.2 hb
    exact ⟨⟨x, rfl⟩, ⟨y.2, Prod.ext hy rfl⟩, ⟨z.2, Prod.ext (hz.trans hyz) rfl⟩⟩
  have heq := χ.value_eq_pullback_of_support (sharedFirstTensor B) id
    (fun y => (ly y, y)) (fun z => (lz z, z)) Function.injective_id
    (fun _ _ h => congrArg Prod.snd h) (fun _ _ h => congrArg Prod.snd h) hs
  have hp : Tensor.pullback id (fun y => (ly y, y)) (fun z => (lz z, z))
      (sharedFirstTensor B) = ∑ i, B i := by
    funext x y z
    simp only [Finset.sum_apply]
    change (if ly y = lz z then B (ly y) x y z else 0) = ∑ i, B i x y z
    rw [Finset.sum_eq_single (ly y)
      (fun i _ hi => by by_contra h; exact hi (hsupport i x y z h).1.symm) (by simp)]
    split_ifs with h
    · rfl
    · symm; by_contra hb; exact h ((hsupport (ly y) x y z hb).2.symm)
  rwa [hp] at heq

def branchWordTensor (B : Fin s → Tensor K X Y Z) {n : ℕ} (w : Fin n → Fin s) :
    Tensor K (Fin n → X) (Fin n → Y) (Fin n → Z) :=
  fun x y z => ∏ i, B (w i) (x i) (y i) (z i)

theorem Character.value_branchWordTensor (χ : Character K)
    (B : Fin s → Tensor K X Y Z) {n : ℕ} (w : Fin n → Fin s) :
    χ.value (branchWordTensor B w) = ∏ i, χ.value (B (w i)) := by
  induction n with
  | zero =>
      have hzero : branchWordTensor B w = Tensor.pullback
          (Equiv.equivPUnit (Fin 0 → X))
          (Equiv.equivPUnit (Fin 0 → Y))
          (Equiv.equivPUnit (Fin 0 → Z)) (unitTensor (K := K)) := by
        funext x y z; simp [branchWordTensor, Tensor.pullback, unitTensor]
      rw [hzero, χ.value_reindex, χ.map_one]; simp
  | succ n ih =>
      have heq : branchWordTensor B w = Tensor.pullback
          (Fin.consEquiv (fun _ : Fin (n + 1) => X)).symm
          (Fin.consEquiv (fun _ : Fin (n + 1) => Y)).symm
          (Fin.consEquiv (fun _ : Fin (n + 1) => Z)).symm
          (Tensor.product (B (w 0)) (branchWordTensor B (Fin.tail w))) := by
        funext x y z
        simp [branchWordTensor, Tensor.pullback, Tensor.product, Fin.consEquiv,
          Fin.prod_univ_succ, Fin.tail]
      rw [heq, χ.value_reindex, χ.map_product, ih, Fin.prod_univ_succ]; rfl

def typeWordCoordinate (counts : Fin s → ℕ)
    (e : Fin (Fintype.card (ExactWords counts)) ≃ ExactWords counts)
    {U : Type} (y : Fin (Fintype.card (ExactWords counts)) ×
      (Fin (∑ a, counts a) → U)) : Fin (∑ a, counts a) → (Fin s × U) :=
  fun i => ((e y.1).val i, y.2 i)

theorem Character.sharedFirst_tag_of_separation_of_coefficient_one (χ : Character K)
    (hsep : ∀ {M : ℕ} {X' Y' Z' : Type} [Fintype X'] [Fintype Y'] [Fintype Z'],
      0 < M → ∀ B' : Fin M → Tensor K X' Y' Z',
        (∑ i, χ.value (B' i)) * (M : ℝ) ^ χ.pX ≤
          6 * (M : ℝ) * χ.value (sharedFirstTensor B'))
    (q : FiniteLaw (Fin s)) (B : Fin s → Tensor K X Y Z)
    (hB : ∀ a, ∃ x y z, B a x y z = 1) :
    Real.exp (χ.pX * finiteEntropy q.mass) *
        ∏ a, χ.value (B a) ^ q.mass a ≤ χ.value (sharedFirstTensor B) := by
  have hBpos (a : Fin s) : 0 < χ.value (B a) :=
    zero_lt_one.trans_le (χ.one_le_value_of_coefficient_one (hB a))
  have hs : 0 < s := by
    by_contra hn
    obtain rfl : s = 0 := Nat.eq_zero_of_not_pos hn
    have htotal := q.total; simp at htotal
  let a : Fin s := ⟨0, hs⟩
  have hbranch : Tensor.pullback id (fun y => (a, y)) (fun z => (a, z))
      (sharedFirstTensor B) = B a := by
    funext x y z; simp [Tensor.pullback, sharedFirstTensor]
  have hbnd := χ.value_pullback_le (sharedFirstTensor B) id (fun y => (a, y)) (fun z => (a, z))
  rw [hbranch] at hbnd
  refine tag_of_integral_bounds q (fun a => χ.value (B a)) χ.pX (χ.value (sharedFirstTensor B)) 6
    hBpos ((hBpos a).trans_le hbnd) (by norm_num) fun counts _ => ?_
  let M := Fintype.card (ExactWords counts)
  let e : Fin M ≃ ExactWords counts := (Fintype.equivFin _).symm
  let W : Fin M → Tensor K (Fin (∑ a, counts a) → X)
      (Fin (∑ a, counts a) → Y) (Fin (∑ a, counts a) → Z) :=
    fun h => branchWordTensor B (e h).val
  have hM : 0 < M := by
    simpa only [M, Fintype.card_eq_nat_card] using exactWords_card_pos counts
  have hWval (h : Fin M) : χ.value (W h) = ∏ a, χ.value (B a) ^ counts a := by
    rw [χ.value_branchWordTensor, ← Fintype.prod_fiberwise' (e h).val (fun a => χ.value (B a))]
    simp only [Finset.prod_const, Finset.card_univ]
    exact Finset.prod_congr rfl fun a _ => by
      rw [show Fintype.card {i // (e h).val i = a} = counts a from (e h).property a]
  have hfinite : ((M : ℝ) * ∏ a, χ.value (B a) ^ counts a) * (M : ℝ) ^ χ.pX ≤
      6 * (M : ℝ) * χ.value (sharedFirstTensor W) := by
    simpa only [hWval, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
      hsep hM W
  have hp : Tensor.pullback id (typeWordCoordinate counts e) (typeWordCoordinate counts e)
      (Tensor.power (sharedFirstTensor B) (∑ a, counts a)) = sharedFirstTensor W := by
    funext x y z
    by_cases h : y.1 = z.1
    · simp [Tensor.pullback, Tensor.power, typeWordCoordinate, sharedFirstTensor, W, branchWordTensor, h]
    · obtain ⟨i, hi⟩ := Function.ne_iff.mp fun heq : (e y.1).val = (e z.1).val =>
        h (e.injective (Subtype.ext heq))
      simp only [Tensor.pullback, Tensor.power, sharedFirstTensor, h, ↓reduceIte,
        typeWordCoordinate, id_eq]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
  have hsource : χ.value (sharedFirstTensor W) ≤
      χ.value (sharedFirstTensor B) ^ (∑ a, counts a) := by
    rw [← hp, ← χ.value_power]
    exact χ.value_pullback_le _ _ _ _
  have hcancel : (M : ℝ) *
      ((M : ℝ) ^ χ.pX * ∏ a, χ.value (B a) ^ counts a) ≤
        (M : ℝ) * (6 * χ.value (sharedFirstTensor B) ^ (∑ a, counts a)) := calc
    _ = ((M : ℝ) * ∏ a, χ.value (B a) ^ counts a) * (M : ℝ) ^ χ.pX := by ring
    _ ≤ 6 * (M : ℝ) * χ.value (sharedFirstTensor W) := hfinite
    _ ≤ 6 * (M : ℝ) * χ.value (sharedFirstTensor B) ^ (∑ a, counts a) :=
      mul_le_mul_of_nonneg_left hsource (by positivity)
    _ = _ := by ring
  have hbound := (mul_le_mul_iff_right₀ (Nat.cast_pos.mpr hM : (0 : ℝ) < M)).mp hcancel
  simpa only [M, Fintype.card_eq_nat_card] using hbound

end Tag

namespace DeterminantFiltration

variable {K : Type*} [CommRing K]

abbrev Index (e : ℕ) := Sum (Fin (e + 2)) (Fin e)

def adaptedTensor (d e : ℕ) : Tensor K (Fin (d + 1)) (Index e) (Index (d + e))
  | i, .inl j, .inl k => if i.val + j.val = k.val then 1 else 0
  | i, .inl j, .inr k =>
      if j.val = e + 1 ∧ i.val < d ∧ e + i.val = k.val then 1 else 0
  | _, .inr _, .inl _ => 0
  | i, .inr j, .inr k => if i.val + j.val = k.val then 1 else 0

def gradedTensor (d e : ℕ) : Tensor K (Fin (d + 1)) (Index e) (Index (d + e))
  | i, .inl j, .inl k => if i.val + j.val = k.val then 1 else 0
  | _, .inl _, .inr _ => 0
  | _, .inr _, .inl _ => 0
  | i, .inr j, .inr k => if i.val + j.val = k.val then 1 else 0

def inputScale (e : ℕ) : Index e → K[X]
  | .inl _ => X
  | .inr _ => 1

def outputScale (e : ℕ) : Index e → K[X]
  | .inl _ => 1
  | .inr _ => X

def diagonalMap {I : Type*} [DecidableEq I] (s : I → K[X]) : I → I → K[X] :=
  fun i j => if i = j then s i else 0

theorem restrict_diagonal {I J N : Type*}
    [Fintype I] [Fintype J] [Fintype N]
    [DecidableEq I] [DecidableEq J] [DecidableEq N]
    (a : I → K[X]) (b : J → K[X]) (c : N → K[X])
    (T : Tensor K[X] I J N) (i : I) (j : J) (k : N) :
    Tensor.restrict (diagonalMap (K := K) a) (diagonalMap (K := K) b) (diagonalMap (K := K) c) T i j k =
      a i * b j * c k * T i j k := by
  simp [Tensor.restrict, diagonalMap, ite_mul, mul_ite]

def degeneration [Nontrivial K] (d e : ℕ) :
    Tensor.PolynomialRestrictionDegeneration (adaptedTensor (K := K) d e)
      (gradedTensor (K := K) d e) 1 0 1 1 where
  leftMap := diagonalMap (K := K) (fun _ => 1)
  middleMap := diagonalMap (K := K) (inputScale (K := K) e)
  rightMap := diagonalMap (K := K) (outputScale (K := K) (d + e))
  left_degree i j := by simp only [diagonalMap]; split_ifs <;> simp
  middle_degree i j := by
    simp only [diagonalMap]; split_ifs
    · cases i <;> simp [inputScale]
    · simp
  right_degree i j := by
    simp only [diagonalMap]; split_ifs
    · cases i <;> simp [outputScale]
    · simp
  vanishes i j k n hn := by
    obtain rfl : n = 0 := by omega
    rw [restrict_diagonal]
    rcases j with j | j <;> rcases k with k | k
    all_goals simp only [inputScale, outputScale, adaptedTensor, one_mul]
    all_goals (try split_ifs) <;> simp [← pow_two]
  leading i j k := by
    rw [restrict_diagonal]
    rcases j with j | j <;> rcases k with k | k
    all_goals simp only [inputScale, outputScale, adaptedTensor, gradedTensor, one_mul]
    all_goals (try split_ifs) <;> simp [← pow_two]

def firstMap (d : ℕ) (i : Fin (d + 1)) (x : Fin (d + 1) × Unit) : K :=
  if x = (i, ()) then 1 else 0

def inputMap (e : ℕ) : Index e → Fin (e + 1) × Bool → K
  | .inl j, y =>
    if h : j.val < e + 1 then
      if y = (⟨j.val, h⟩, false) then 1 else 0
    else
      if y = (⟨e, Nat.lt_succ_self e⟩, true) then 1 else 0
  | .inr j, y =>
    (if y = (⟨j.val + 1, by omega⟩, false) then -1 else 0) +
      (if y = (⟨j.val, by omega⟩, true) then 1 else 0)

def outputMap (d e : ℕ) : Index (d + e) → Fin ((d + 1) + (e + 1) - 1) × Bool → K
  | .inl k, (m, false) => if m.val = k.val then 1 else 0
  | .inl k, (m, true) => if m.val + 1 = k.val then 1 else 0
  | .inr _, (_, false) => 0
  | .inr k, (m, true) => if m.val = k.val then 1 else 0

theorem restrict_product_eq_adaptedTensor (d e : ℕ) :
    Tensor.restrict (firstMap (K := K) d) (inputMap (K := K) e) (outputMap (K := K) d e)
      (Tensor.product (convolution (K := K) (d + 1) (e + 1))
        (Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (K := K) Bool)))) =
      adaptedTensor (K := K) d e := by
  funext i j k
  let P := Tensor.product (convolution (K := K) (d + 1) (e + 1))
    (Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (K := K) Bool)))
  have hP (y : Fin (e + 1) × Bool) (z : Fin ((d + 1) + (e + 1) - 1) × Bool) :
      P (i, ()) y z = if z = (⟨i.val + y.1.val, by omega⟩, y.2) then 1 else 0 := by
    rcases y with ⟨m₁, b₁⟩
    rcases z with ⟨m₂, b₂⟩
    simp only [P, Tensor.product, convolution, Tensor.cyclic, Tensor.dotPairing,
      Prod.ext_iff, Fin.ext_iff, eq_comm (a := b₁), mul_ite, mul_one, mul_zero, ite_and]
    split_ifs <;> simp_all
  have hsum (y : Fin (e + 1) × Bool) :
      (∑ z, inputMap (K := K) e j y * outputMap d e k z * P (i, ()) y z) =
        inputMap e j y * outputMap d e k (⟨i.val + y.1.val, by omega⟩, y.2) := by
    simp only [hP, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have hA : Tensor.restrict (firstMap (K := K) d) (inputMap (K := K) e) (outputMap (K := K) d e) P i j k =
      ∑ y, inputMap e j y * outputMap d e k (⟨i.val + y.1.val, by omega⟩, y.2) := by
    unfold Tensor.restrict
    rw [Finset.sum_eq_single (i, ())
      (fun x _ hx => Finset.sum_eq_zero fun y _ => Finset.sum_eq_zero fun z _ => by simp [firstMap, hx])
      (fun h => absurd (Finset.mem_univ _) h)]
    simp only [firstMap, ↓reduceIte, one_mul, hsum]
  rw [hA]
  rcases j with j | j
  · by_cases hj : j.val < e + 1
    · simp only [inputMap, hj, ↓reduceDIte, ite_mul, zero_mul, one_mul, Finset.sum_ite_eq',
        Finset.mem_univ, ↓reduceIte]
      rcases k with k | k <;> simp [outputMap, adaptedTensor, show j.val ≠ e + 1 by omega]
    · have hj' : j.val = e + 1 := by omega
      simp only [inputMap, hj, ↓reduceDIte, ite_mul, zero_mul, one_mul, Finset.sum_ite_eq',
        Finset.mem_univ, ↓reduceIte]
      rcases k with k | k
      · simp [outputMap, adaptedTensor, hj', Nat.add_assoc]
      · simp only [outputMap, adaptedTensor, hj', true_and]
        congr 1; exact propext ⟨fun h => ⟨by omega, by omega⟩, fun h => by omega⟩
  · simp only [inputMap, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, one_mul, neg_one_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    rcases k with k | k
    · simp only [outputMap, adaptedTensor, show i.val + (j.val + 1) = i.val + j.val + 1 by omega,
        neg_add_cancel]
    · simp [outputMap, adaptedTensor]

def branch (d e : ℕ) (n : Fin 2) :
    Tensor K (Fin (d + 1)) (Index e) (Index (d + e))
  | i, .inl j, .inl k => if n = 0 then if i.val + j.val = k.val then 1 else 0 else 0
  | i, .inr j, .inr k => if n = 1 then if i.val + j.val = k.val then 1 else 0 else 0
  | _, _, _ => 0

def branchLabel (e : ℕ) : Index e → Fin 2
  | .inl _ => 0
  | .inr _ => 1

end DeterminantFiltration

namespace Character

variable {K : Type*} [CommRing K]
open DeterminantFiltration
variable (χ : Character K)

theorem convolution_concavity_tag_of_separation [Nontrivial K]
    (hsep : ∀ {M : ℕ} {X' Y' Z' : Type} [Fintype X'] [Fintype Y'] [Fintype Z'],
      0 < M → ∀ B' : Fin M → Tensor K X' Y' Z',
        (∑ i, χ.value (B' i)) * (M : ℝ) ^ χ.pX ≤
          6 * (M : ℝ) * χ.value (sharedFirstTensor B'))
    (a b : ℕ) (ha : 0 < a) (hb : 2 ≤ b)
    (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    Real.exp (χ.pX * Real.binEntropy q) *
        χ.value ((convolution (K := K)) a (b + 1)) ^ q *
        χ.value ((convolution (K := K)) a (b - 1)) ^ (1 - q) ≤
      (2 : ℝ) ^ χ.pX * χ.value ((convolution (K := K)) a b) := by
  obtain ⟨d, rfl⟩ : ∃ d, a = d + 1 := ⟨a - 1, by omega⟩
  obtain ⟨e, rfl, he⟩ : ∃ e, b = e + 1 ∧ 0 < e := ⟨b - 1, by omega, by omega⟩
  have hcoeff (n : Fin 2) : ∃ i j k, branch (K := K) d e n i j k = 1 := by
    fin_cases n
    · exact ⟨⟨0, by omega⟩, .inl ⟨0, by omega⟩, .inl ⟨0, by omega⟩, by simp [branch]⟩
    · exact ⟨⟨0, by omega⟩, .inr ⟨0, he⟩, .inr ⟨0, by omega⟩, by simp [branch]⟩
  have hsupp (n : Fin 2) (i : Fin (d + 1)) (j : Index e) (k : Index (d + e))
      (h : branch (K := K) d e n i j k ≠ 0) : branchLabel e j = n ∧ branchLabel (d + e) k = n := by
    fin_cases n <;> rcases j with j | j <;> rcases k with k | k <;> simp_all [branch, branchLabel]
  have hsum : (∑ n, branch (K := K) d e n) = gradedTensor (K := K) d e := by
    funext i j k; rcases j with j | j <;> rcases k with k | k <;> simp [branch, gradedTensor]
  let fz0 : Fin ((d + 1) + (e + 2) - 1) → Index (d + e) := fun k => .inl (Fin.cast (by omega) k)
  have hb0 : χ.value (branch (K := K) d e 0) = χ.value ((convolution (K := K)) (d + 1) (e + 2)) := by
    rw [χ.value_eq_pullback_of_support _ id Sum.inl fz0 Function.injective_id Sum.inl_injective
      (Sum.inl_injective.comp (Fin.cast_injective _))]
    · rfl
    · rintro i (j | j) (k | k) h <;>
        [exact ⟨⟨i, rfl⟩, ⟨j, rfl⟩, ⟨Fin.cast (by omega) k, by simp [fz0]⟩⟩;
         simp [branch] at h; simp [branch] at h; simp [branch] at h]
  let fz1 : Fin ((d + 1) + e - 1) → Index (d + e) := fun k => .inr (Fin.cast (by omega) k)
  have hb1 : χ.value (branch (K := K) d e 1) = χ.value ((convolution (K := K)) (d + 1) e) := by
    rw [χ.value_eq_pullback_of_support _ id Sum.inr fz1 Function.injective_id Sum.inr_injective
      (Sum.inr_injective.comp (Fin.cast_injective _))]
    · rfl
    · rintro i (j | j) (k | k) h <;>
        [simp [branch] at h; simp [branch] at h; simp [branch] at h;
         exact ⟨⟨i, rfl⟩, ⟨j, rfl⟩, ⟨Fin.cast (by omega) k, by simp [fz1]⟩⟩]
  have hent : finiteEntropy (binaryLaw q hq₀ hq₁).mass = Real.binEntropy q := by
    simp [finiteEntropy, Fin.sum_univ_two, binaryLaw, entropyTerm,
      Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, Real.negMulLog_def]; ring
  have ht := χ.sharedFirst_tag_of_separation_of_coefficient_one hsep (binaryLaw q hq₀ hq₁)
    (branch (K := K) d e) hcoeff
  rw [χ.value_sharedFirstTensor_eq_sum (branch (K := K) d e) (branchLabel e) (branchLabel (d + e)) hsupp,
    hsum, hent] at ht
  simp only [Fin.prod_univ_two, binaryLaw, ↓reduceIte, Fin.one_eq_zero_iff, hb0, hb1] at ht
  have hv := χ.value_reindex
    (Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (K := K) Bool)))
    (Equiv.refl Unit) finTwoEquiv finTwoEquiv
  rw [show Tensor.pullback (Equiv.refl Unit) finTwoEquiv finTwoEquiv
      (Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (K := K) Bool))) =
        Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (K := K) (Fin 2))) by
    funext i j k; simp [Tensor.pullback, Tensor.cyclic, Tensor.dotPairing]] at hv
  have hbool : χ.value (Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (K := K) Bool))) =
      (2 : ℝ) ^ χ.pX := hv.symm.trans (χ.value_cyclic_cyclic_dotPairing (by decide))
  have hgrad : χ.value (gradedTensor (K := K) d e) ≤
      (2 : ℝ) ^ χ.pX * χ.value ((convolution (K := K)) (d + 1) (e + 1)) := calc
    χ.value (gradedTensor (K := K) d e) ≤ χ.value (adaptedTensor (K := K) d e) :=
      χ.value_polynomialRestrictionDegeneration_le_ring (degeneration (K := K) d e)
    _ ≤ χ.value (Tensor.product (convolution (K := K) (d + 1) (e + 1))
          (Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (K := K) Bool)))) := by
      rw [← restrict_product_eq_adaptedTensor]
      exact χ.monotone _ (firstMap d) (inputMap e) (outputMap d e)
    _ = (2 : ℝ) ^ χ.pX * χ.value ((convolution (K := K)) (d + 1) (e + 1)) := by
      rw [χ.map_product, hbool, mul_comm]
  rw [show e + 1 + 1 = e + 2 from rfl, Nat.add_sub_cancel, mul_assoc]
  exact ht.trans hgrad

end Character

namespace Sector

open DeterminantFiltration

variable {K : Type*} [CommRing K]

def sourceWidth (a h : ℕ) : ℕ := 3 * h + a - 1

def rightStart (a h : ℕ) : ℕ := 2 * h + a - 1

def MiddleY (a h j : ℕ) : Prop := ¬ j < h ∧ j < rightStart a h

def MiddleZ (a h k : ℕ) : Prop := ¬ k < h + a - 1 ∧ k < rightStart a h

instance (a h j : ℕ) : Decidable (MiddleY a h j) :=
  inferInstanceAs (Decidable (¬ j < h ∧ j < rightStart a h))

instance (a h k : ℕ) : Decidable (MiddleZ a h k) :=
  inferInstanceAs (Decidable (¬ k < h + a - 1 ∧ k < rightStart a h))

abbrev YIndex (a h : ℕ) := Fin (sourceWidth a h)
abbrev ZIndex (a h : ℕ) := Fin (a + sourceWidth a h - 1)

def source (a h : ℕ) : Tensor K (Fin a) (YIndex a h) (ZIndex a h) :=
  convolution (K := K) a (sourceWidth a h)

def yLabel (a h : ℕ) (j : YIndex a h) : Fin 3 :=
  if j.val < h then 0 else if j.val < rightStart a h then 1 else 2

def zLabel (a h : ℕ) (k : ZIndex a h) : Fin 3 :=
  if k.val < h + a - 1 then 0 else if k.val < rightStart a h then 1 else 2

def branchFamily (a h : ℕ) (b : Fin 3) :
    Tensor K (Fin a) (YIndex a h) (ZIndex a h) :=
  fun i j k => if yLabel a h j = b ∧ zLabel a h k = b then source (K := K) a h i j k else 0

def retained (a h : ℕ) : Tensor K (Fin a) (YIndex a h) (ZIndex a h) :=
  ∑ b : Fin 3, branchFamily (K := K) a h b

theorem branchFamily_labels (a h : ℕ) (b : Fin 3) (i : Fin a)
    (j : YIndex a h) (k : ZIndex a h) (hn : branchFamily (K := K) a h b i j k ≠ 0) :
    yLabel a h j = b ∧ zLabel a h k = b := by
  by_contra hne; exact hn (by simp [branchFamily, hne])

theorem retained_apply (a h : ℕ) (i : Fin a) (j : YIndex a h) (k : ZIndex a h) :
    retained (K := K) a h i j k =
      if yLabel a h j = zLabel a h k then source (K := K) a h i j k else 0 := by
  rw [retained, Fin.sum_univ_three]
  dsimp only [Pi.add_apply, branchFamily]
  generalize yLabel a h j = y, zLabel a h k = z
  fin_cases y <;> fin_cases z <;> simp

def restriction [Nontrivial K] (a h : ℕ) :
    Tensor.PolynomialRestrictionDegeneration (source (K := K) a h) (retained (K := K) a h) 1 0 1 1 where
  leftMap := diagonalMap (K := K) (fun _ => 1)
  middleMap := diagonalMap (K := K) (fun j => if MiddleY a h j.val then X else 1)
  rightMap := diagonalMap (K := K) (fun k => if MiddleZ a h k.val then 1 else X)
  left_degree i j := by simp only [diagonalMap]; split_ifs <;> simp
  middle_degree output input := by
    simp only [diagonalMap]; split_ifs <;> simp
  right_degree output input := by
    simp only [diagonalMap]; split_ifs <;> simp
  vanishes i j k n hn := by
    obtain rfl : n = 0 := by omega
    rw [restrict_diagonal, one_mul]
    by_cases hs : i.val + j.val = k.val
    · have hi := i.isLt
      have hmid : MiddleZ a h k.val → MiddleY a h j.val := by
        unfold MiddleY MiddleZ rightStart; omega
      by_cases hy : MiddleY a h j.val <;> by_cases hz : MiddleZ a h k.val
      · simp [hy, hz]
      · simp [hy, hz, mul_assoc]
      · exact False.elim (hy (hmid hz))
      · simp [hy, hz]
    · have h0 : source (K := K) a h i j k = 0 := by simp [source, convolution, hs]
      simp [h0]
  leading i j k := by
    rw [restrict_diagonal, one_mul, retained_apply]
    by_cases hs : i.val + j.val = k.val
    · have hi := i.isLt
      have h1 : source (K := K) a h i j k = 1 := by simp [source, convolution, hs]
      rw [h1]
      by_cases hj0 : j.val < h <;> by_cases hj1 : j.val < rightStart a h <;>
        by_cases hk0 : k.val < h + a - 1 <;> by_cases hk1 : k.val < rightStart a h <;>
        (try unfold rightStart at *; omega)
      all_goals
        simp [MiddleY, MiddleZ, yLabel, zLabel, hj0, hj1, hk0, hk1, ← sq, Polynomial.coeff_X_pow]
    · have h0 : source (K := K) a h i j k = 0 := by simp [source, convolution, hs]
      simp [h0]

def leftY (a h : ℕ) (r : Fin h) : YIndex a h :=
  ⟨r.val, by have := r.isLt; unfold sourceWidth; omega⟩

def leftZ (a h : ℕ) (s : Fin (a + h - 1)) : ZIndex a h :=
  ⟨s.val, by have := s.isLt; unfold sourceWidth; omega⟩

def middleY (a h : ℕ) (s : Fin (a + h - 1)) : YIndex a h :=
  ⟨h + s.val, by have := s.isLt; unfold sourceWidth; omega⟩

def middleZ (a h : ℕ) (r : Fin h) : ZIndex a h :=
  ⟨h + a - 1 + r.val, by have := r.isLt; unfold sourceWidth; omega⟩

def rightY (a h : ℕ) (r : Fin h) : YIndex a h :=
  ⟨rightStart a h + r.val, by have := r.isLt; unfold rightStart sourceWidth; omega⟩

def rightZ (a h : ℕ) (s : Fin (a + h - 1)) : ZIndex a h :=
  ⟨rightStart a h + s.val, by have := s.isLt; unfold rightStart sourceWidth; omega⟩

theorem leftTensor_pullback (a h : ℕ) :
    Tensor.pullback id (leftY a h) (leftZ a h) (branchFamily (K := K) a h 0) =
      convolution (K := K) a h := by
  funext i r s
  have hr := r.isLt
  have hs : s.val < h + a - 1 := by have := s.isLt; omega
  simp [Tensor.pullback, branchFamily, yLabel, zLabel, leftY, leftZ, source, convolution, hr, hs]
  rfl

theorem rightTensor_pullback (a h : ℕ) :
    Tensor.pullback id (rightY a h) (rightZ a h) (branchFamily (K := K) a h 2) =
      convolution (K := K) a h := by
  funext i r s
  have hy : yLabel a h (rightY a h r) = 2 := by
    have := i.isLt; unfold yLabel rightY rightStart; dsimp; split_ifs <;> omega
  have hz : zLabel a h (rightZ a h s) = 2 := by
    unfold zLabel rightZ rightStart; dsimp; split_ifs <;> omega
  dsimp only [Tensor.pullback, branchFamily, id_eq]
  rw [hy, hz]
  simp only [and_self, ↓reduceIte, source, convolution, rightY, rightZ]
  exact if_congr (by omega) rfl rfl

def exchangedConvolution (a h : ℕ) :
    Tensor K (Fin a) (Fin (a + h - 1)) (Fin h) :=
  fun i s r => convolution (K := K) a h i r s

theorem middleTensor_pullback (a h : ℕ) :
    Tensor.pullback Fin.rev (middleY a h) (middleZ a h) (branchFamily (K := K) a h 1) =
      exchangedConvolution (K := K) a h := by
  funext i s r
  have hy : yLabel a h (middleY a h s) = 1 := by
    have := s.isLt; unfold yLabel middleY rightStart; dsimp; split_ifs <;> omega
  have hz : zLabel a h (middleZ a h r) = 1 := by
    have := r.isLt; unfold zLabel middleZ rightStart; dsimp; split_ifs <;> omega
  dsimp only [Tensor.pullback, branchFamily]
  rw [hy, hz]
  simp only [and_self, ↓reduceIte, source, exchangedConvolution, convolution, middleY, middleZ, Fin.val_rev]
  exact if_congr (by have := i.isLt; omega) rfl rfl

theorem convolution_tripling_tag_of_separation [Nontrivial K] (χ : Character K)
    (hsep : ∀ {M : ℕ} {X' Y' Z' : Type} [Fintype X'] [Fintype Y'] [Fintype Z'],
      0 < M → ∀ B' : Fin M → Tensor K X' Y' Z',
        (∑ i, χ.value (B' i)) * (M : ℝ) ^ χ.pX ≤
          6 * (M : ℝ) * χ.value (sharedFirstTensor B'))
    (a h : ℕ)
    (ha : 0 < a) (hh : 0 < h) :
    (3 : ℝ) ^ χ.pX * χ.value ((convolution (K := K)) a h) ^ (2 / 3 : ℝ) *
      χ.value (fun i s r => (convolution (K := K)) a h i r s) ^ (1 / 3 : ℝ) ≤
        χ.value ((convolution (K := K)) a (3 * h + a - 1)) := by
  have hb0 : χ.value (branchFamily (K := K) a h 0) = χ.value (convolution (K := K) a h) := by
    rw [χ.value_eq_pullback_of_support _ id (leftY a h) (leftZ a h) Function.injective_id
      (fun _ _ heq => Fin.ext (congrArg (fun t : YIndex a h => t.val) heq))
      (fun _ _ heq => Fin.ext (congrArg (fun t : ZIndex a h => t.val) heq)), leftTensor_pullback]
    intro i j k hn
    have hl := branchFamily_labels a h 0 i j k hn
    have hsrc : i.val + j.val = k.val := by
      by_contra hs; exact hn (by simp [branchFamily, source, convolution, hs])
    have hj : j.val < h := by
      have h1 := hl.1; unfold yLabel at h1; split_ifs at h1 <;> simp_all
    exact ⟨⟨i, rfl⟩, ⟨⟨j.val, hj⟩, rfl⟩, ⟨⟨k.val, by have := i.isLt; omega⟩, rfl⟩⟩
  have hb2 : χ.value (branchFamily (K := K) a h 2) = χ.value (convolution (K := K) a h) := by
    rw [χ.value_eq_pullback_of_support _ id (rightY a h) (rightZ a h) Function.injective_id
      (fun _ _ heq => by apply Fin.ext; have hv := congrArg Fin.val heq; dsimp [rightY] at hv; omega)
      (fun _ _ heq => by apply Fin.ext; have hv := congrArg Fin.val heq; dsimp [rightZ] at hv; omega),
      rightTensor_pullback]
    intro i j k hn
    have hl := branchFamily_labels a h 2 i j k hn
    have hsrc : i.val + j.val = k.val := by
      by_contra hs; exact hn (by simp [branchFamily, source, convolution, hs])
    have hj : rightStart a h ≤ j.val := by
      have h1 := hl.1; unfold yLabel at h1; split_ifs at h1 <;> simp_all
    have hjlt := j.isLt
    unfold sourceWidth at hjlt
    exact ⟨⟨i, rfl⟩,
      ⟨⟨j.val - rightStart a h, by unfold rightStart at *; omega⟩, Fin.ext (by dsimp [rightY]; omega)⟩,
      ⟨⟨k.val - rightStart a h, by have := i.isLt; unfold rightStart at *; omega⟩,
        Fin.ext (by dsimp [rightZ]; omega)⟩⟩
  have hb1 : χ.value (branchFamily (K := K) a h 1) = χ.value (exchangedConvolution (K := K) a h) := by
    rw [χ.value_eq_pullback_of_support _ Fin.rev (middleY a h) (middleZ a h) Fin.rev_injective
      (fun _ _ heq => by apply Fin.ext; have hv := congrArg Fin.val heq; dsimp [middleY] at hv; omega)
      (fun _ _ heq => by apply Fin.ext; have hv := congrArg Fin.val heq; dsimp [middleZ] at hv; omega),
      middleTensor_pullback]
    intro i j k hn
    have hl := branchFamily_labels a h 1 i j k hn
    have hsrc : i.val + j.val = k.val := by
      by_contra hs; exact hn (by simp [branchFamily, source, convolution, hs])
    have hj : h ≤ j.val ∧ j.val < rightStart a h := by
      have h1 := hl.1; unfold yLabel at h1; split_ifs at h1 <;> simp_all
    have hk : h + a - 1 ≤ k.val ∧ k.val < rightStart a h := by
      have h2 := hl.2; unfold zLabel at h2; split_ifs at h2 <;> simp_all
    exact ⟨⟨i.rev, Fin.rev_rev i⟩,
      ⟨⟨j.val - h, by unfold rightStart at hj; omega⟩, Fin.ext (by dsimp [middleY]; omega)⟩,
      ⟨⟨k.val - (h + a - 1), by unfold rightStart at hk; omega⟩, Fin.ext (by dsimp [middleZ]; omega)⟩⟩
  have hcoeff (b : Fin 3) : ∃ i j k, branchFamily (K := K) a h b i j k = 1 := by
    let i : Fin a := ⟨0, ha⟩
    let r : Fin h := ⟨0, hh⟩
    let z := convolutionOutput i r
    have hc : convolution (K := K) a h i r z = 1 := convolution_at_output i r
    fin_cases b
    · exact ⟨i, leftY a h r, leftZ a h z,
        (congrFun (congrFun (congrFun (leftTensor_pullback (K := K) a h) i) r) z).trans hc⟩
    · exact ⟨i.rev, middleY a h z, middleZ a h r,
        (congrFun (congrFun (congrFun (middleTensor_pullback (K := K) a h) i) z) r).trans hc⟩
    · exact ⟨i, rightY a h r, rightZ a h z,
        (congrFun (congrFun (congrFun (rightTensor_pullback (K := K) a h) i) r) z).trans hc⟩
  have hent : Real.exp (χ.pX * finiteEntropy (FiniteLaw.uniform (Fin 3)).mass) = (3 : ℝ) ^ χ.pX := by
    simp only [FiniteLaw.uniform, finiteEntropy, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, entropyTerm, Real.log_inv]
    norm_num
    rw [Real.rpow_def_of_pos (by norm_num)]
    congr 1; ring
  have hc : 0 < χ.value ((convolution (K := K)) a h) :=
    lt_of_lt_of_le zero_lt_one (χ.one_le_value_of_coefficient_one
      ⟨⟨0, ha⟩, ⟨0, hh⟩, convolutionOutput ⟨0, ha⟩ ⟨0, hh⟩, convolution_at_output _ _⟩)
  have hprod : (∏ b, χ.value (branchFamily (K := K) a h b) ^ (FiniteLaw.uniform (Fin 3)).mass b) =
      χ.value ((convolution (K := K)) a h) ^ (2 / 3 : ℝ) *
        χ.value (exchangedConvolution (K := K) a h) ^ (1 / 3 : ℝ) := by
    simp only [Fin.prod_univ_three, FiniteLaw.uniform, Fintype.card_fin, hb0, hb1, hb2]
    calc
      χ.value ((convolution (K := K)) a h) ^ ((3 : ℝ)⁻¹) *
          χ.value (exchangedConvolution (K := K) a h) ^ ((3 : ℝ)⁻¹) *
          χ.value ((convolution (K := K)) a h) ^ ((3 : ℝ)⁻¹) =
        (χ.value ((convolution (K := K)) a h) ^ ((3 : ℝ)⁻¹) *
          χ.value ((convolution (K := K)) a h) ^ ((3 : ℝ)⁻¹)) *
            χ.value (exchangedConvolution (K := K) a h) ^ ((3 : ℝ)⁻¹) := by ring
      _ = _ := by rw [← Real.rpow_add hc]; norm_num
  have htag := χ.sharedFirst_tag_of_separation_of_coefficient_one hsep (FiniteLaw.uniform (Fin 3))
    (branchFamily (K := K) a h) hcoeff
  rw [hent, hprod, χ.value_sharedFirstTensor_eq_sum (branchFamily (K := K) a h)
    (yLabel a h) (zLabel a h) (branchFamily_labels (K := K) a h)] at htag
  have hresult := htag.trans
    (χ.value_polynomialRestrictionDegeneration_le_ring (restriction (K := K) a h))
  change (3 : ℝ) ^ χ.pX * (χ.value ((convolution (K := K)) a h) ^ (2 / 3 : ℝ) *
    χ.value (fun i s r => (convolution (K := K)) a h i r s) ^ (1 / 3 : ℝ)) ≤
      χ.value ((convolution (K := K)) a (3 * h + a - 1)) at hresult
  simpa only [mul_assoc] using hresult

end Sector

noncomputable def growthProduct : ℕ → ℝ
  | 0 => 1
  | n + 1 => growthProduct n * (1 + 1 / (3 * ((n : ℝ) + 1)))

theorem growthProduct_pos (n : ℕ) : 0 < growthProduct n := by
  induction n with
  | zero => norm_num [growthProduct]
  | succ n ih => exact mul_pos ih (by positivity)

theorem growthProduct_cube_lower (n : ℕ) :
    (n : ℝ) + 1 ≤ growthProduct n ^ 3 := by
  induction n with
  | zero => norm_num [growthProduct]
  | succ n ih =>
    have ha : 0 < (n : ℝ) + 1 := by positivity
    have hnonneg : 0 ≤ 1 / (3 * ((n : ℝ) + 1)) := by positivity
    have hfactor : 1 + 1 / ((n : ℝ) + 1) ≤ (1 + 1 / (3 * ((n : ℝ) + 1))) ^ 3 := by
      have hdiv : 1 / ((n : ℝ) + 1) = 3 * (1 / (3 * ((n : ℝ) + 1))) := by field_simp
      rw [hdiv]
      nlinarith [sq_nonneg (1 / (3 * ((n : ℝ) + 1))),
        mul_nonneg (sq_nonneg (1 / (3 * ((n : ℝ) + 1)))) hnonneg]
    have hfactor_nonneg : 0 ≤ (1 + 1 / (3 * ((n : ℝ) + 1))) ^ 3 := by positivity
    have hfirst := mul_le_mul_of_nonneg_right ih hfactor_nonneg
    have hsecond := mul_le_mul_of_nonneg_left hfactor ha.le
    have htel : ((n : ℝ) + 1) * (1 + 1 / ((n : ℝ) + 1)) = (n : ℝ) + 2 := by field_simp; ring
    dsimp only [growthProduct]
    rw [mul_pow]
    push_cast
    linarith

theorem binary_entropy_log_partition {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    Real.binEntropy (A / (A + B)) + Real.log A * (A / (A + B)) +
      Real.log B * (1 - A / (A + B)) = Real.log (A + B) := by
  have hsum : A + B ≠ 0 := ne_of_gt (add_pos hA hB)
  have hcomp : 1 - A / (A + B) = B / (A + B) := by field_simp; ring
  simp only [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, Real.negMulLog_def]
  rw [hcomp, Real.log_div hA.ne' hsum, Real.log_div hB.ne' hsum]
  field_simp; ring

theorem finite_product_concavity {ι : Type*} [Fintype ι]
    (A B C p : ι → ℝ) {s : ℝ} (hs : 0 < s) (hsum : ∑ i, p i = s)
    (hA : ∀ i, 0 < A i) (hB : ∀ i, 0 < B i) (hC : ∀ i, 0 < C i)
    (hbound : ∀ i q, 0 ≤ q → q ≤ 1 →
      Real.exp (p i * Real.binEntropy q) * (B i) ^ q * (C i) ^ (1 - q) ≤
        (2 : ℝ) ^ (p i) * A i) :
    (∏ i, B i) ^ (1 / s) + (∏ i, C i) ^ (1 / s) ≤
      2 * (∏ i, A i) ^ (1 / s) := by
  have hprodA : 0 < ∏ i, A i := Finset.prod_pos fun i _ => hA i
  have hprodB : 0 < ∏ i, B i := Finset.prod_pos fun i _ => hB i
  have hprodC : 0 < ∏ i, C i := Finset.prod_pos fun i _ => hC i
  let a : ℝ := (∏ i, A i) ^ (1 / s)
  let b : ℝ := (∏ i, B i) ^ (1 / s)
  let c : ℝ := (∏ i, C i) ^ (1 / s)
  have ha : 0 < a := Real.rpow_pos_of_pos hprodA _
  have hb : 0 < b := Real.rpow_pos_of_pos hprodB _
  have hc : 0 < c := Real.rpow_pos_of_pos hprodC _
  let q : ℝ := b / (b + c)
  have hq0 : 0 ≤ q := le_of_lt (div_pos hb (add_pos hb hc))
  have hq1 : q ≤ 1 := (div_le_one (add_pos hb hc)).mpr (le_of_lt (lt_add_of_pos_right b hc))
  have hlog (i : ι) : p i * Real.binEntropy q + q * Real.log (B i) +
      (1 - q) * Real.log (C i) ≤ p i * Real.log 2 + Real.log (A i) := by
    have hleft1 : 0 < Real.exp (p i * Real.binEntropy q) * (B i) ^ q :=
      mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (hB i) _)
    have h := Real.log_le_log (mul_pos hleft1 (Real.rpow_pos_of_pos (hC i) _)) (hbound i q hq0 hq1)
    rw [Real.log_mul hleft1.ne' (Real.rpow_pos_of_pos (hC i) _).ne',
      Real.log_mul (Real.exp_pos _).ne' (Real.rpow_pos_of_pos (hB i) _).ne',
      Real.log_exp, Real.log_rpow (hB i), Real.log_rpow (hC i),
      Real.log_mul (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).ne' (hA i).ne',
      Real.log_rpow (by norm_num : (0 : ℝ) < 2)] at h
    simpa only [mul_comm (Real.log 2) (p i)] using h
  have hlogs := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hlog i
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    hsum, ← Real.log_prod fun i _ => (hA i).ne',
    ← Real.log_prod fun i _ => (hB i).ne',
    ← Real.log_prod fun i _ => (hC i).ne'] at hlogs
  have hnormalized : Real.binEntropy q + Real.log b * q + Real.log c * (1 - q) ≤
      Real.log 2 + Real.log a := by
    dsimp only [a, b, c]
    rw [Real.log_rpow hprodA, Real.log_rpow hprodB, Real.log_rpow hprodC]
    convert div_le_div_of_nonneg_right hlogs hs.le using 1 <;> field_simp [hs.ne']
  change Real.binEntropy (b / (b + c)) + Real.log b * (b / (b + c)) +
      Real.log c * (1 - b / (b + c)) ≤ Real.log 2 + Real.log a at hnormalized
  rw [binary_entropy_log_partition hb hc, ← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) ha.ne'] at hnormalized
  exact (Real.log_le_log_iff (add_pos hb hc) (mul_pos (by norm_num) ha)).mp hnormalized

theorem finite_product_tripling {ι : Type*} [Fintype ι]
    (A B C p : ι → ℝ) {s : ℝ} (hs : 0 < s) (hsum : ∑ i, p i = s)
    (_hA : ∀ i, 0 < A i) (hB : ∀ i, 0 < B i) (hC : ∀ i, 0 < C i)
    (hbound : ∀ i, (3 : ℝ) ^ p i * B i ^ (2 / 3 : ℝ) * C i ^ (1 / 3 : ℝ) ≤ A i)
    (hprod_eq : ∏ i, C i = ∏ i, B i) :
    3 * (∏ i, B i) ^ (1 / s) ≤ (∏ i, A i) ^ (1 / s) := by
  have hBprod : 0 < ∏ i, B i := Finset.prod_pos fun i _ => hB i
  have hprod : (3 : ℝ) ^ s * (∏ i, B i) ≤ ∏ i, A i := by
    have hmul := Finset.prod_le_prod₀ (s := Finset.univ)
      (f := fun i => (3 : ℝ) ^ p i * B i ^ (2 / 3 : ℝ) * C i ^ (1 / 3 : ℝ)) (g := A)
      (fun i _ => mul_nonneg
        (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (hB i).le _))
        (Real.rpow_nonneg (hC i).le _))
      (fun i _ => hbound i)
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      ← Real.rpow_sum_of_pos (by norm_num : (0 : ℝ) < 3) p Finset.univ, hsum,
      Real.finsetProd_rpow Finset.univ B fun i _ => (hB i).le,
      Real.finsetProd_rpow Finset.univ C fun i _ => (hC i).le, hprod_eq,
      mul_assoc, ← Real.rpow_add hBprod] at hmul
    norm_num at hmul
    exact hmul
  have hmean := Real.rpow_le_rpow (by positivity) hprod (by positivity : (0 : ℝ) ≤ 1 / s)
  rwa [Real.mul_rpow (by positivity) hBprod.le,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3), mul_one_div_cancel hs.ne', Real.rpow_one] at hmean

namespace Character

variable {K : Type*} [CommRing K]
variable (χ : Character K)
variable {X Y Z X' Y' Z' : Type}
variable [Fintype X] [Fintype Y] [Fintype Z]
variable [Fintype X'] [Fintype Y'] [Fintype Z']

def sixfoldProduct (T : Tensor K X Y Z) : ℝ :=
  χ.value T *
    χ.value (fun y z x => T x y z) *
    χ.value (fun z x y => T x y z) *
    χ.value (fun x z y => T x y z) *
    χ.value (fun z y x => T x y z) *
    χ.value (fun y x z => T x y z)

theorem sixfoldProduct_swap12 (T : Tensor K X Y Z) :
    χ.sixfoldProduct (fun y x z => T x y z) = χ.sixfoldProduct T := by
  dsimp [sixfoldProduct]; ring

theorem sixfoldProduct_swap23 (T : Tensor K X Y Z) :
    χ.sixfoldProduct (fun x z y => T x y z) = χ.sixfoldProduct T := by
  dsimp [sixfoldProduct]; ring

theorem sixfoldProduct_reindex (T : Tensor K X Y Z)
    (ex : X' ≃ X) (ey : Y' ≃ Y) (ez : Z' ≃ Z) :
    χ.sixfoldProduct (Tensor.pullback ex ey ez T) = χ.sixfoldProduct T := by
  unfold sixfoldProduct
  rw [χ.value_reindex T ex ey ez,
    ← χ.value_reindex (fun y z x => T x y z) ey ez ex,
    ← χ.value_reindex (fun z x y => T x y z) ez ex ey,
    ← χ.value_reindex (fun x z y => T x y z) ex ez ey,
    ← χ.value_reindex (fun z y x => T x y z) ez ey ex,
    ← χ.value_reindex (fun y x z => T x y z) ey ex ez]
  rfl

theorem sixfoldProduct_convolution_comm (a b : ℕ) :
    χ.sixfoldProduct ((convolution (K := K)) a b) = χ.sixfoldProduct ((convolution (K := K)) b a) := by
  let e : Fin (a + b - 1) ≃ Fin (b + a - 1) := finCongr (by omega)
  have heq : Tensor.pullback (Equiv.refl (Fin b)) (Equiv.refl (Fin a)) e
      ((convolution (K := K)) b a) = fun j i k => (convolution (K := K)) a b i j k := by
    funext j i k; exact (convolution_comm a b i j k).symm
  have h := χ.sixfoldProduct_reindex ((convolution (K := K)) b a)
    (Equiv.refl (Fin b)) (Equiv.refl (Fin a)) e
  rw [heq, χ.sixfoldProduct_swap12] at h
  exact h

def swap23Character : Character K where
  value T := χ.value (fun x z y => T x y z)
  nonneg T := χ.nonneg (fun x z y => T x y z)
  map_zero := χ.map_zero
  map_one := χ.map_one
  map_directSum T := by
    have heq : (fun x z y => Tensor.directSum T x y z) =
        Tensor.directSum (fun i x z y => T i x y z) := by
      funext x z y; simp only [Tensor.directSum, and_comm]
    change χ.value (fun x z y => Tensor.directSum T x y z) = _
    rw [heq, χ.map_directSum]
  map_product T S := χ.map_product (fun x z y => T x y z) (fun x z y => S x y z)
  monotone T A B C := by
    have heq : (fun x z y => Tensor.restrict A B C T x y z) =
        Tensor.restrict A C B (fun x z y => T x y z) := by
      funext x z y
      simp only [Tensor.restrict]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
    change χ.value (fun x z y => Tensor.restrict A B C T x y z) ≤ _
    rw [heq]
    exact χ.monotone (fun x z y => T x y z) A C B

def permutedCharacter (i : Fin 6) : Character K :=
  ![χ, χ.cyclicCharacter, χ.cyclicCharacter.cyclicCharacter,
    χ.swap23Character, χ.swap23Character.cyclicCharacter,
    χ.swap23Character.cyclicCharacter.cyclicCharacter] i

theorem prod_permutedCharacter_value (T : Tensor K X Y Z) :
    (∏ i : Fin 6, (χ.permutedCharacter i).value T) = χ.sixfoldProduct T := by
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
  change χ.value T * (χ.value (fun y z x => T x y z) *
      (χ.value (fun z x y => T x y z) * (χ.value (fun x z y => T x y z) *
      (χ.value (fun y x z => T x y z) * χ.value (fun z y x => T x y z))))) = _
  unfold sixfoldProduct; ring

@[simp] theorem cyclicCharacter_pX : χ.cyclicCharacter.pX = χ.pZ := rfl
@[simp] theorem cyclicCharacter_pZ : χ.cyclicCharacter.pZ = χ.pY := rfl

@[simp] theorem swap23Character_pX : χ.swap23Character.pX = χ.pX := by
  unfold pX pZ; congr 2
  exact congrArg χ.value (by funext x y z; simp [Tensor.cyclic, Tensor.dotPairing, eq_comm])

@[simp] theorem swap23Character_pY : χ.swap23Character.pY = χ.pZ := by
  unfold pY pZ; congr 2
  exact congrArg χ.value (by funext x y z; simp [Tensor.cyclic, Tensor.dotPairing, eq_comm])

@[simp] theorem swap23Character_pZ : χ.swap23Character.pZ = χ.pY := by
  unfold pY pZ; congr 2
  exact congrArg χ.value (by funext x y z; simp [Tensor.cyclic, Tensor.dotPairing, eq_comm])

def meanExponent : ℝ := (χ.pX + χ.pY + χ.pZ) / 3

theorem sum_permutedCharacter_pX_mean :
    (∑ i : Fin 6, (χ.permutedCharacter i).pX) = 6 * χ.meanExponent := by
  simp [permutedCharacter, Fin.sum_univ_succ, meanExponent]; ring

def convolutionProfile (a b : ℕ) : ℝ :=
  χ.sixfoldProduct (convolution (K := K) a b) ^ (1 / (6 * χ.meanExponent))

theorem value_convolution_pos {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    0 < χ.value (convolution (K := K) a b) :=
  zero_lt_one.trans_le (χ.one_le_value_of_coefficient_one
    ⟨⟨0, ha⟩, ⟨0, hb⟩, convolutionOutput ⟨0, ha⟩ ⟨0, hb⟩, convolution_at_output _ _⟩)

theorem convolutionProfile_comm (a b : ℕ) :
    χ.convolutionProfile a b = χ.convolutionProfile b a :=
  congrArg (fun s : ℝ => s ^ (1 / (6 * χ.meanExponent))) (χ.sixfoldProduct_convolution_comm a b)

theorem convolutionProfile_pos {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    0 < χ.convolutionProfile a b := by
  unfold convolutionProfile
  rw [← χ.prod_permutedCharacter_value]
  exact Real.rpow_pos_of_pos (Finset.prod_pos fun i _ =>
    (χ.permutedCharacter i).value_convolution_pos ha hb) _

theorem value_convolution_one_left {b : ℕ} (hb : 0 < b) :
    χ.value (convolution (K := K) 1 b) = (b : ℝ) ^ χ.pX := by
  rw [← χ.value_reindex _ (Equiv.equivPUnit (Fin 1)).symm (Equiv.refl _)
      (finCongr (by omega) : Fin b ≃ Fin (1 + b - 1)),
    convolution_one_left_dotPairing, χ.value_cyclic_cyclic_dotPairing hb]

theorem convolutionProfile_one_left {b : ℕ} (ht : 0 < χ.meanExponent) (hb : 0 < b) :
    χ.convolutionProfile 1 b = b := by
  have hb' : 0 < (b : ℝ) := Nat.cast_pos.mpr hb
  unfold convolutionProfile
  rw [← χ.prod_permutedCharacter_value]
  simp only [value_convolution_one_left _ hb, ← Real.rpow_sum_of_pos hb',
    χ.sum_permutedCharacter_pX_mean, ← Real.rpow_mul hb'.le]
  rw [show (6 * χ.meanExponent) * (1 / (6 * χ.meanExponent)) = 1 by field_simp [ht.ne'],
    Real.rpow_one]

theorem convolutionProfile_le_of_character_value_bounds {a b : ℕ}
    (ht : 0 < χ.meanExponent)
    (h : ∀ ψ : Character K, ψ.value (convolution (K := K) a b) ≤ (a + b - 1 : ℕ)) :
    χ.convolutionProfile a b ≤ (a + b - 1 : ℕ) ^ (1 / χ.meanExponent) := by
  unfold convolutionProfile
  rw [← χ.prod_permutedCharacter_value]
  have hprod : (∏ i : Fin 6, (χ.permutedCharacter i).value (convolution (K := K) a b)) ≤
      ((a + b - 1 : ℕ) : ℝ) ^ 6 :=
    (Finset.prod_le_prod₀ (fun i _ => (χ.permutedCharacter i).nonneg _)
      (fun i _ => h (χ.permutedCharacter i))).trans_eq (by simp)
  calc
    _ ≤ (((a + b - 1 : ℕ) : ℝ) ^ 6) ^ (1 / (6 * χ.meanExponent)) :=
      Real.rpow_le_rpow (Finset.prod_nonneg fun i _ => (χ.permutedCharacter i).nonneg _)
        hprod (by positivity)
    _ = ((a + b - 1 : ℕ) : ℝ) ^ (1 / χ.meanExponent) := by
      rw [← Real.rpow_natCast _ 6, ← Real.rpow_mul (by positivity)]
      congr 1; field_simp; norm_num

theorem prod_permutedCharacter_swapped_convolution (a b : ℕ) :
    (∏ i : Fin 6, (χ.permutedCharacter i).value
      (fun x z y => (convolution (K := K)) a b x y z)) =
    ∏ i : Fin 6, (χ.permutedCharacter i).value ((convolution (K := K)) a b) := by
  rw [χ.prod_permutedCharacter_value, χ.prod_permutedCharacter_value]
  exact χ.sixfoldProduct_swap23 _

variable [Nontrivial K]

theorem convolutionProfile_concave_of_separation
    (hsep : ∀ ψ : Character K,
      ∀ {M : ℕ} {X' Y' Z' : Type} [Fintype X'] [Fintype Y'] [Fintype Z'],
        0 < M → ∀ B' : Fin M → Tensor K X' Y' Z',
          (∑ i, ψ.value (B' i)) * (M : ℝ) ^ ψ.pX ≤
            6 * (M : ℝ) * ψ.value (sharedFirstTensor B'))
    {a b : ℕ} (ht : 0 < χ.meanExponent)
    (ha : 0 < a) (hb : 2 ≤ b) :
    χ.convolutionProfile a (b - 1) + χ.convolutionProfile a (b + 1) ≤
      2 * χ.convolutionProfile a b := by
  have h := finite_product_concavity
    (fun i : Fin 6 => (χ.permutedCharacter i).value ((convolution (K := K)) a b))
    (fun i : Fin 6 => (χ.permutedCharacter i).value ((convolution (K := K)) a (b + 1)))
    (fun i : Fin 6 => (χ.permutedCharacter i).value ((convolution (K := K)) a (b - 1)))
    (fun i : Fin 6 => (χ.permutedCharacter i).pX)
    (mul_pos (by norm_num : (0 : ℝ) < 6) ht) χ.sum_permutedCharacter_pX_mean
    (fun i => (χ.permutedCharacter i).value_convolution_pos ha (by omega))
    (fun i => (χ.permutedCharacter i).value_convolution_pos ha (by omega))
    (fun i => (χ.permutedCharacter i).value_convolution_pos ha (by omega))
    (fun i q hq₀ hq₁ =>
      (χ.permutedCharacter i).convolution_concavity_tag_of_separation
        (hsep (χ.permutedCharacter i)) a b ha hb q hq₀ hq₁)
  simp only [χ.prod_permutedCharacter_value] at h
  change χ.convolutionProfile a (b + 1) + χ.convolutionProfile a (b - 1) ≤
    2 * χ.convolutionProfile a b at h
  simpa only [add_comm] using h

theorem convolutionProfile_tripling_of_separation
    (hsep : ∀ ψ : Character K,
      ∀ {M : ℕ} {X' Y' Z' : Type} [Fintype X'] [Fintype Y'] [Fintype Z'],
        0 < M → ∀ B' : Fin M → Tensor K X' Y' Z',
          (∑ i, ψ.value (B' i)) * (M : ℝ) ^ ψ.pX ≤
            6 * (M : ℝ) * ψ.value (sharedFirstTensor B'))
    {a h : ℕ} (ht : 0 < χ.meanExponent)
    (ha : 0 < a) (hh : 0 < h) :
    3 * χ.convolutionProfile a h ≤ χ.convolutionProfile a (3 * h + a - 1) := by
  have hsw : ∃ x z y, (fun i s r => convolution (K := K) a h i r s) x z y = 1 :=
    ⟨⟨0, ha⟩, convolutionOutput ⟨0, ha⟩ ⟨0, hh⟩, ⟨0, hh⟩, convolution_at_output _ _⟩
  have h := finite_product_tripling
    (fun i : Fin 6 => (χ.permutedCharacter i).value ((convolution (K := K)) a (3 * h + a - 1)))
    (fun i : Fin 6 => (χ.permutedCharacter i).value ((convolution (K := K)) a h))
    (fun i : Fin 6 => (χ.permutedCharacter i).value (fun x z y => (convolution (K := K)) a h x y z))
    (fun i : Fin 6 => (χ.permutedCharacter i).pX)
    (mul_pos (by norm_num : (0 : ℝ) < 6) ht) χ.sum_permutedCharacter_pX_mean
    (fun i => (χ.permutedCharacter i).value_convolution_pos ha (by omega))
    (fun i => (χ.permutedCharacter i).value_convolution_pos ha hh)
    (fun i => zero_lt_one.trans_le
      ((χ.permutedCharacter i).one_le_value_of_coefficient_one hsw))
    (fun i => Sector.convolution_tripling_tag_of_separation (χ.permutedCharacter i)
      (hsep (χ.permutedCharacter i)) a h ha hh)
    (χ.prod_permutedCharacter_swapped_convolution a h)
  simpa only [χ.prod_permutedCharacter_value, convolutionProfile] using h

theorem exponent_sum_le_nine_quarters_of_separation_and_convolution
    (hsep : ∀ ψ : Character K,
      ∀ {M : ℕ} {X' Y' Z' : Type} [Fintype X'] [Fintype Y'] [Fintype Z'],
        0 < M → ∀ B' : Fin M → Tensor K X' Y' Z',
          (∑ i, ψ.value (B' i)) * (M : ℝ) ^ ψ.pX ≤
            6 * (M : ℝ) * ψ.value (sharedFirstTensor B'))
    (hconv : ∀ ψ : Character K, ∀ a b : ℕ,
      ψ.value (convolution (K := K) a b) ≤ (a + b - 1 : ℕ)) :
    χ.pX + χ.pY + χ.pZ ≤ 9 / 4 := by
  have h : χ.meanExponent ≤ 3 / 4 := by
    by_cases ht : 0 < χ.meanExponent
    · apply diagonal_exponent_le_three_quarters (D := fun a => χ.convolutionProfile a a) ht
      · intro n hn; exact (χ.convolutionProfile_pos hn hn).le
      · intro n hn
        let P := χ.convolutionProfile
        have hrow (a : ℕ) (ha : 1 ≤ a) (k : ℕ) :
            P a (a + k) ≤ P a a + (k : ℝ) * (P a (a + 1) - P a a) := by
          induction k with
          | zero => simp
          | succ k ih =>
            have hstep : P a (a + k + 1) - P a (a + k) ≤ P a (a + 1) - P a a := by
              clear ih
              induction k with
              | zero => rfl
              | succ k ihk =>
                have hc := χ.convolutionProfile_concave_of_separation hsep ht ha (by omega : 2 ≤ a + k + 1)
                rw [show a + k + 1 - 1 = a + k by omega] at hc
                rw [show a + (k + 1) = a + k + 1 by omega]
                dsimp [P]; linarith
            push_cast
            rw [show a + (k + 1) = a + k + 1 by omega]
            linarith
        let g (a : ℕ) : ℝ := P a (a + 1) - P a a
        have hupper (a : ℕ) (ha : 1 ≤ a) : P a a ≤ ((3 * (a : ℝ) - 1) / 2) * g a := by
          have ht' := χ.convolutionProfile_tripling_of_separation hsep ht ha ha
          have hc := hrow a ha (3 * a - 1)
          rw [show a + (3 * a - 1) = 3 * a + a - 1 by omega,
            Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at hc
          dsimp [P, g] at *; linarith
        have hinc (a : ℕ) (ha : 1 ≤ a) :
            P a a + g a + g (a + 1) ≤ P (a + 1) (a + 1) := by
          have hc := χ.convolutionProfile_concave_of_separation hsep ht (by omega : 0 < a + 1) (by omega : 2 ≤ a + 1)
          have hs := χ.convolutionProfile_comm a (a + 1)
          rw [Nat.add_sub_cancel] at hc
          dsimp [P, g] at *; linarith
        have hind (m : ℕ) : growthProduct m ≤ g (m + 1) ∧
            ((3 * ((m : ℝ) + 1) - 1) / 2) * growthProduct m ≤ P (m + 1) (m + 1) := by
          induction m with
          | zero =>
            have h1 := χ.convolutionProfile_one_left ht (by omega : 0 < 1)
            have h2 := χ.convolutionProfile_one_left ht (by omega : 0 < 2)
            norm_num [growthProduct, g, P, h1, h2]
          | succ m ih =>
            let r : ℝ := (m : ℝ) + 1
            have hr0 : r ≠ 0 := by positivity
            have hr : 0 < 3 * r := by positivity
            have hu := hupper (m + 2) (by omega)
            have hi := hinc (m + 1) (by omega)
            rw [show ((m + 2 : ℕ) : ℝ) = r + 1 by dsimp [r]; push_cast; ring] at hu
            have hgnew : growthProduct (m + 1) ≤ g (m + 2) := by
              dsimp only [growthProduct]
              rw [show (m : ℝ) + 1 = r from rfl,
                show growthProduct m * (1 + 1 / (3 * r)) = ((3 * r + 1) * growthProduct m) / (3 * r)
                  by field_simp]
              exact (div_le_iff₀ hr).mpr (by nlinarith [ih.1, ih.2])
            refine ⟨hgnew, ?_⟩
            have hdiag : ((3 * (r + 1) - 1) / 2) * growthProduct (m + 1) =
                ((3 * r - 1) / 2) * growthProduct m + growthProduct m + growthProduct (m + 1) := by
              dsimp only [growthProduct]
              rw [show (m : ℝ) + 1 = r from rfl]
              field_simp; ring
            push_cast
            rw [show (m : ℝ) + 1 = r from rfl, hdiag]
            linarith [ih.1, ih.2]
        cases n with
        | zero => omega
        | succ m =>
          have hdiag := (hind m).2
          have hpos := growthProduct_pos m
          have hlin : ((m : ℝ) + 1) * growthProduct m ≤ P (m + 1) (m + 1) :=
            (mul_le_mul_of_nonneg_right (by linarith [Nat.cast_nonneg (α := ℝ) m]) hpos.le).trans hdiag
          simpa only [Nat.cast_add, Nat.cast_one] using calc
            ((m : ℝ) + 1) ^ 4 = ((m : ℝ) + 1) ^ 3 * ((m : ℝ) + 1) := by ring
            _ ≤ ((m : ℝ) + 1) ^ 3 * growthProduct m ^ 3 :=
              mul_le_mul_of_nonneg_left (growthProduct_cube_lower m) (by positivity)
            _ = (((m : ℝ) + 1) * growthProduct m) ^ 3 := by ring
            _ ≤ P (m + 1) (m + 1) ^ 3 := pow_le_pow_left₀ (by positivity) hlin 3
      · intro n hn
        have h := χ.convolutionProfile_le_of_character_value_bounds (a := n) (b := n) ht
          (fun ψ => hconv ψ n n)
        have hnn : 1 ≤ n + n := by omega
        simpa only [Nat.cast_sub hnn, Nat.cast_add, Nat.cast_one, two_mul] using h
    · linarith
  unfold meanExponent at h
  linarith

end Character
end MatrixMultiplication.AuxiliarySeparation

end

end OAI
