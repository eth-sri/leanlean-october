module

public import Mathlib
public import PottsDiscontinuity.TorusTopology.PlanarFiniteCompassFan

/-! Algebra of the signed turn of finite compass words. -/

@[expose] public section

namespace PottsDiscontinuity.TorusTopology
open Planar.Medial

/-- The sum of turns between successive directions of an open word. -/
def compassWordTurn : List (Fin 4) → ℤ
  | [] => 0
  | [_] => 0
  | a::b::l => primalCompassQuarterTurn a b + compassWordTurn (b::l)

variable (a b : Fin 4) (l : List (Fin 4))

include l in
/-- The cyclic signed turn, with the last direction joined to the first. -/
def compassWordCyclicTurn : ℤ :=
  (l.zipWith primalCompassQuarterTurn (l.rotate 1)).sum

@[simp] lemma compassQuarterTurn_self (a : Fin 4) : primalCompassQuarterTurn a a = 0 := by
  fin_cases a <;> decide

private lemma compassWord_zip_close :
    ((a::l).zipWith primalCompassQuarterTurn (l++[b])).sum =
      compassWordTurn (a::l) + primalCompassQuarterTurn ((a::l).getLast (by simp)) b := by
  induction l generalizing a with
  | nil => simp [compassWordTurn]
  | cons c l ih =>
    simp only [List.cons_append,List.zipWith_cons_cons,List.sum_cons,compassWordTurn]
    grind

lemma compassWordCyclicTurn_cons (a : Fin 4) (l : List (Fin 4)) :
    compassWordCyclicTurn (a::l) = compassWordTurn (a::l) +
      primalCompassQuarterTurn ((a::l).getLast (by simp)) a := by
  unfold compassWordCyclicTurn
  rw [List.rotate_cons_succ,List.rotate_zero]
  exact compassWord_zip_close a a l

end PottsDiscontinuity.TorusTopology
