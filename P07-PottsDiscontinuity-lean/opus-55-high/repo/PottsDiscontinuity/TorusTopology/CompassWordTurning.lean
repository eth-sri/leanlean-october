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

/-- The cyclic signed turn, with the last direction joined to the first. -/
def compassWordCyclicTurn (l : List (Fin 4)) : ℤ :=
  (l.zipWith primalCompassQuarterTurn (l.rotate 1)).sum

theorem compassQuarterTurn_abs_le_two (a b : Fin 4) :
    |primalCompassQuarterTurn a b| ≤ 2 := by
  fin_cases a <;> fin_cases b <;> decide

section
variable (a : Fin 4)
@[simp] theorem compassQuarterTurn_self  : primalCompassQuarterTurn a a = 0 := by
  fin_cases a <;> decide

theorem compassWordTurn_replicate (n : ℕ) :
    compassWordTurn (List.replicate n a) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases n with
    | zero => rfl
    | succ n => simpa [List.replicate_succ,compassWordTurn] using ih
end

theorem compassWord_zip_close (a b : Fin 4) (l : List (Fin 4)) :
    ((a::l).zipWith primalCompassQuarterTurn (l++[b])).sum =
      compassWordTurn (a::l) + primalCompassQuarterTurn ((a::l).getLast (by simp)) b := by
  induction l generalizing a with
  | nil => aesop
  | cons c l ih =>
    simp only [List.cons_append,List.zipWith_cons_cons,List.sum_cons,compassWordTurn]
    grind

theorem compassWordCyclicTurn_cons (a : Fin 4) (l : List (Fin 4)) :
    compassWordCyclicTurn (a::l) = compassWordTurn (a::l) +
      primalCompassQuarterTurn ((a::l).getLast (by simp)) a := by
  simp [compassWordCyclicTurn, compassWord_zip_close]

theorem compassWordTurn_append_nonempty (a b : Fin 4) (l r : List (Fin 4)) :
    compassWordTurn ((a::l)++b::r) = compassWordTurn (a::l) +
      primalCompassQuarterTurn ((a::l).getLast (by simp)) b + compassWordTurn (b::r) := by
  induction l generalizing a with
  | nil => simp [compassWordTurn]
  | cons c l ih =>
    simp only [List.cons_append,compassWordTurn]
    grind

end PottsDiscontinuity.TorusTopology
