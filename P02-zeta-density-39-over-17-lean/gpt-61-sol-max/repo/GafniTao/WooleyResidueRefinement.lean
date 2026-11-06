module
import Mathlib
public import GafniTao.WooleyWeightedComplexHolder
public import GafniTao.WooleyWeightedMean

@[expose] public section

/-!
# Residue refinement for Wooley Lemma 6.2

This file proves the exact size of a fibre of the reduction map
`ZMod (p^b) -> ZMod (p^a)`.  It is the finite arithmetic fact denoted
`U_1 = p^(b-a)` in equation (6.11).
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

def wooleyResidueRefinementFiber (p a b : ℕ) [NeZero p] (hab : a ≤ b)
    (xi : ZMod (p ^ a)) : Finset (ZMod (p ^ b)) :=
  Finset.univ.filter fun z =>
    ZMod.castHom (pow_dvd_pow p hab) (ZMod (p ^ a)) z = xi

theorem wooleyResidueRefinementFiber_card
    {p a b : ℕ} [NeZero p] (hab : a ≤ b) (xi : ZMod (p ^ a)) :
    (wooleyResidueRefinementFiber p a b hab xi).card = p ^ (b - a) := by
  let f : ZMod (p ^ b) →+ ZMod (p ^ a) :=
    (ZMod.castHom (pow_dvd_pow p hab) (ZMod (p ^ a))).toAddMonoidHom
  have hf : Function.Surjective f :=
    ZMod.castHom_surjective (pow_dvd_pow p hab)
  have hfiber (y : ZMod (p ^ a)) :
      (Finset.univ.filter fun z : ZMod (p ^ b) => f z = y).card =
        (Finset.univ.filter fun z : ZMod (p ^ b) => f z = xi).card := by
    exact AddMonoidHom.card_fiber_eq_of_mem_range f (hf y) (hf xi)
  have htotal :
      ∑ y : ZMod (p ^ a),
          (Finset.univ.filter fun z : ZMod (p ^ b) => f z = y).card =
        p ^ b := by
    rw [← Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset (ZMod (p ^ b))))
      (t := (Finset.univ : Finset (ZMod (p ^ a))))
      (f := f) (by simp)]
    simp
  have hmul : p ^ a *
      (Finset.univ.filter fun z : ZMod (p ^ b) => f z = xi).card =
      p ^ b := by simp_all
  have hpPow : 0 < p ^ a := pow_pos (NeZero.pos p) a
  have hcanonical : p ^ a * p ^ (b - a) = p ^ b := by
    rw [Nat.mul_comm, Nat.pow_sub_mul_pow p hab]
  have hcard :
      (Finset.univ.filter fun z : ZMod (p ^ b) => f z = xi).card =
        p ^ (b - a) := by
    exact Nat.eq_of_mul_eq_mul_left (by omega) (hmul.trans hcanonical.symm)
  exact hcard

theorem wooley_sum_refined_residue_mass
    {Q p a b : ℕ} [NeZero p] (hab : a ≤ b)
    (gamma : Fin Q → ℂ) (xi : ZMod (p ^ a)) :
    ∑ z ∈ wooleyResidueRefinementFiber p a b hab xi,
        wooleyWeightedResidueMassSq gamma z =
      wooleyWeightedResidueMassSq gamma xi := by
  unfold wooleyWeightedResidueMassSq wooleyResidueClass
    wooleyResidueRefinementFiber
  simp_rw [Finset.sum_filter]
  have hdistribute (z : ZMod (p ^ b)) :
      (if ZMod.castHom (pow_dvd_pow p hab) (ZMod (p ^ a)) z = xi then
          ∑ n : Fin Q,
            if ((((n : ℕ) + 1 : ℕ) : ZMod (p ^ b))) = z then
              ‖gamma n‖ ^ 2 else 0
        else 0) =
        ∑ n : Fin Q,
          if ZMod.castHom (pow_dvd_pow p hab) (ZMod (p ^ a)) z = xi then
            (if ((((n : ℕ) + 1 : ℕ) : ZMod (p ^ b))) = z then
              ‖gamma n‖ ^ 2 else 0)
          else 0 := by simp_all
  simp_rw [hdistribute]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Fintype.sum_eq_single
    (((n : ℕ) + 1 : ℕ) : ZMod (p ^ b))]
  · have hcast :
        ZMod.castHom (pow_dvd_pow p hab) (ZMod (p ^ a))
            ((((n : ℕ) + 1 : ℕ) : ZMod (p ^ b))) =
          ((((n : ℕ) + 1 : ℕ) : ZMod (p ^ a))) :=
      ZMod.cast_natCast (pow_dvd_pow p hab) ((n : ℕ) + 1)
    rw [hcast]
    by_cases hxi : ((((n : ℕ) + 1 : ℕ) : ZMod (p ^ a))) = xi <;>
      simp [hxi]
  · intro z hzne
    by_cases hzxi : ZMod.castHom (pow_dvd_pow p hab)
        (ZMod (p ^ a)) z = xi
    · rw [ite_eq_left hzxi, ite_eq_right (Ne.symm hzne)]
    · rw [ite_eq_right hzxi]




