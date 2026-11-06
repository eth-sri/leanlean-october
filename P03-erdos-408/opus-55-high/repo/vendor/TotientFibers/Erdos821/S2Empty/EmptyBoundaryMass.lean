module

public import Erdos821.S2.AnalyticParametersTasks
public import Erdos821.S2Empty.FiniteProducts
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Tactic.Positivity.Finset

@[expose] public section

noncomputable section

namespace Erdos821.S2Empty

open Erdos821.Blueprint.Graph

theorem sum_zeroCoordinates {α : Type*} [DecidableEq α] [Fintype α]
    {β : α → Type*} [∀ a, Fintype (β a)] [∀ a, DecidableEq (β a)] [∀ a, Zero (β a)]
    (S : α → Prop) [DecidablePred S] :
    (∑ x : (a : α) → β a,
      if ∀ a, S a → x a = 0 then (1 : ℝ) else 0) =
      ∏ a : {a : α // ¬ S a}, (Fintype.card (β a.1) : ℝ) := by
  classical
  let C : ((a : α) → β a) → Prop := fun x => ∀ a, S a → x a = 0
  have hcard : (Finset.univ.filter C).card = Fintype.card {x : (a : α) → β a // C x} :=
    (Fintype.card_of_subtype (Finset.univ.filter C) (by simp)).symm
  calc
    _ = ((Finset.univ.filter C).card : ℝ) := by simp [C]
    _ = (Fintype.card {x : (a : α) → β a // C x} : ℝ) := by simp_all
    _ = (Fintype.card ((a : {a : α // ¬ S a}) → β a.1) : ℝ) := by
      exact_mod_cast Fintype.card_congr (zeroCoordinatesEquiv S)
    _ = _ := by simp

/-- Distinct selected primes impose independent zero-residue conditions. -/
theorem group_zeroAverage_eq (P : PrimeGroups) (g : P.Group) (M : ℕ)
    (a : Fin M → P.Prime g) (ha : Function.Injective a) :
    (Fintype.card ((p : P.Prime g) → ZMod p.val) : ℝ)⁻¹ *
      (∑ y : (p : P.Prime g) → ZMod p.val,
        if ∀ i, y (a i) = 0 then (1 : ℝ) else 0) =
      ∏ i : Fin M, ((a i).val : ℝ)⁻¹ := by
  classical
  let S : P.Prime g → Prop := fun p => ∃ i, a i = p
  have hcond (y : (p : P.Prime g) → ZMod p.val) :
      (∀ p, S p → y p = 0) ↔ ∀ i, y (a i) = 0 := by
    constructor
    · grind
    · grind
  have hcount := sum_zeroCoordinates (α := P.Prime g)
      (β := fun p => ZMod p.val) S
  have hcount' :
      (∑ y : (p : P.Prime g) → ZMod p.val,
        if ∀ i, y (a i) = 0 then (1 : ℝ) else 0) =
        ∏ p : {p : P.Prime g // ¬ S p},
          (Fintype.card (ZMod p.val) : ℝ) := by
    simpa only [hcond] using hcount
  let e : Fin M ≃ {p : P.Prime g // S p} :=
    { toFun := fun i => ⟨a i, by grind⟩
      invFun := fun p => Classical.choose p.property
      left_inv := by grind
      right_inv := fun p => by
        grind }
  have hsel :
      (∏ p : {p : P.Prime g // S p}, (p.val.val : ℝ)) =
        ∏ i : Fin M, ((a i).val : ℝ) := by
    symm
    exact Fintype.prod_equiv e _ _ (fun _ => rfl)
  have hsplit :
      (∏ p : {p : P.Prime g // S p}, (p.val.val : ℝ)) *
        ∏ p : {p : P.Prime g // ¬ S p}, (p.val.val : ℝ) =
          ∏ p : P.Prime g, (p.val : ℝ) := by
    have h := Fintype.prod_subtype_mul_prod_subtype S
      (fun p : P.Prime g => (Fintype.card (ZMod p.val) : ℝ))
    simpa using h
  have hcard :
      (Fintype.card ((p : P.Prime g) → ZMod p.val) : ℝ) =
        (∏ i : Fin M, ((a i).val : ℝ)) *
          ∏ p : {p : P.Prime g // ¬ S p}, (p.val.val : ℝ) := by
    calc
      _ = ∏ p : P.Prime g, (Fintype.card (ZMod p.val) : ℝ) := by simp
      _ = ∏ p : P.Prime g, (p.val : ℝ) := by simp
      _ = _ := by grind
  have hcomp : 0 < ∏ p : {p : P.Prime g // ¬ S p}, (p.val.val : ℝ) := by
    apply Finset.prod_pos
    intro p hp
    exact_mod_cast (P.prime g p.val.val p.val.property).pos
  have hlist : 0 < ∏ i : Fin M, ((a i).val : ℝ) := by
    apply Finset.prod_pos
    intro i hi
    exact_mod_cast (P.prime g (a i).val (by simp)).pos
  rw [hcount']
  rw [hcard]
  simp only [ZMod.card]
  rw [Finset.prod_inv_distrib]
  grind

/-- The physical small-label restriction has total normalized mass at most one. -/
theorem local_small_group_mass_le_one (P : PrimeGroups) (g : P.Group) (M : ℕ)
    (hV : 0 < P.V g) :
    (Fintype.card ((p : P.Prime g) → ZMod p.val) : ℝ)⁻¹ *
      (P.V g) ^ (-(M : ℤ)) *
        (∑ a : Fin M → P.Prime g, ∑ y : (p : P.Prime g) → ZMod p.val,
          if Function.Injective a ∧ (∀ i, y (a i) = 0) then (1 : ℝ) else 0) ≤ 1 := by
  classical
  let Y := (p : P.Prime g) → ZMod p.val
  let cardY : ℝ := (Fintype.card Y : ℝ)
  have hcardNat : 0 < Fintype.card Y :=
    by positivity
  have hcard : 0 < cardY := by simpa [cardY] using hcardNat
  have havg (a : Fin M → P.Prime g) (ha : Function.Injective a) :
      ∑ y : Y, (if (∀ i, y (a i) = 0) then (1 : ℝ) else 0) =
        cardY * ∏ i : Fin M, ((a i).val : ℝ)⁻¹ := by
    have h := group_zeroAverage_eq P g M a ha
    have h' : (Fintype.card Y : ℝ)⁻¹ *
        (∑ y : Y, if ∀ i, y (a i) = 0 then (1 : ℝ) else 0) =
          ∏ i : Fin M, ((a i).val : ℝ)⁻¹ := by
      simpa [Y] using h
    calc
      _ = (Fintype.card Y : ℝ) *
          ((Fintype.card Y : ℝ)⁻¹ *
            ∑ y : Y, (if (∀ i, y (a i) = 0) then (1 : ℝ) else 0)) := by
          simp
      _ = cardY * ∏ i : Fin M, ((a i).val : ℝ)⁻¹ := by
          grind
  have hsum :
      (∑ a : Fin M → P.Prime g, ∑ y : Y,
        if Function.Injective a ∧ (∀ i, y (a i) = 0) then (1 : ℝ) else 0) =
      cardY * ∑ a : Fin M → P.Prime g,
        if Function.Injective a then ∏ i : Fin M, ((a i).val : ℝ)⁻¹ else 0 := by
    calc
      _ = ∑ a : Fin M → P.Prime g,
          if ha : Function.Injective a then
            ∑ y : Y, if ∀ i, y (a i) = 0 then (1 : ℝ) else 0
          else 0 := by
        apply Finset.sum_congr rfl
        intro a _
        by_cases ha : Function.Injective a <;> simp [ha]
      _ = ∑ a : Fin M → P.Prime g,
          if ha : Function.Injective a then
            cardY * ∏ i : Fin M, ((a i).val : ℝ)⁻¹
          else 0 := by
        grind
      _ = cardY * ∑ a : Fin M → P.Prime g,
          if Function.Injective a then ∏ i : Fin M, ((a i).val : ℝ)⁻¹ else 0 := by
        rw [Finset.mul_sum]
        simp
  have hVeq : (∑ p : P.Prime g, (p.val : ℝ)⁻¹) = P.V g := by
    change (∑ p : P.primes g, (p : ℝ)⁻¹) = ∑ p ∈ P.primes g, (p : ℝ)⁻¹
    exact Finset.sum_coe_sort (P.primes g) (fun p : ℕ => (p : ℝ)⁻¹)
  have hlabels :
      (∑ a : Fin M → P.Prime g,
        if Function.Injective a then ∏ i : Fin M, ((a i).val : ℝ)⁻¹ else 0) ≤
        (P.V g) ^ M := by
    calc
      _ ≤ ∑ a : Fin M → P.Prime g, ∏ i : Fin M, ((a i).val : ℝ)⁻¹ := by
        apply Finset.sum_le_sum
        intro a _
        by_cases ha : Function.Injective a
        · grind
        · simp only [ite_eq_right ha]
          positivity
      _ = (P.V g) ^ M := by
        calc
          _ = ∏ i : Fin M, P.V g := by
            calc
              _ = ∏ i : Fin M, ∑ p : P.Prime g, (p.val : ℝ)⁻¹ :=
                sum_pi_prod (fun (_ : Fin M) (p : P.Prime g) => (p.val : ℝ)⁻¹)
              _ = ∏ i : Fin M, P.V g := by
                grind
          _ = _ := by simp
  have hpow : (P.V g) ^ (-(M : ℤ)) = ((P.V g) ^ M)⁻¹ := by
    rw [zpow_neg, zpow_natCast]
  calc
    _ = (P.V g) ^ (-(M : ℤ)) *
        (∑ a : Fin M → P.Prime g,
          if Function.Injective a then ∏ i : Fin M, ((a i).val : ℝ)⁻¹ else 0) := by
      grind
    _ ≤ (P.V g) ^ (-(M : ℤ)) * (P.V g) ^ M :=
      mul_le_mul_of_nonneg_left hlabels (by positivity)
    _ = 1 := by
      rw [hpow]
      exact inv_mul_cancel₀ (by positivity)


end Erdos821.S2Empty
