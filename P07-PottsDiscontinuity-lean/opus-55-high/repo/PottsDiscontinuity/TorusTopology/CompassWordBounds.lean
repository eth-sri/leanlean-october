module

public import Mathlib
public import PottsDiscontinuity.TorusTopology.CompassWordTurning

/-! Uniform turn bounds for a return consisting of three straight segments. -/

public section

namespace PottsDiscontinuity.TorusTopology
open Planar.Medial

section
variable (l : List (Fin 4)) (hl : l ≠ [])
include hl
theorem compassWordCyclicTurn_append_replicate_bound (b : Fin 4) (n : ℕ) (hn : 0 < n) :
    |compassWordCyclicTurn (l++List.replicate n b)-compassWordCyclicTurn l| ≤ 6 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  cases l with
  | nil => simp_all
  | cons a l =>
    have hlast : ((a::l)++b::List.replicate k b).getLast (by simp) = b := by
      grind
    have hb : compassWordTurn (b::List.replicate k b) = 0 := by
      simpa only [List.replicate_succ] using compassWordTurn_replicate b (k+1)
    have hc := compassWordCyclicTurn_cons a (l++b::List.replicate k b)
    change compassWordCyclicTurn ((a::l)++b::List.replicate k b) =
      compassWordTurn ((a::l)++b::List.replicate k b) +
        primalCompassQuarterTurn (((a::l)++b::List.replicate k b).getLast (by simp)) a at hc
    rw [hlast,compassWordTurn_append_nonempty,hb] at hc
    have ho := compassWordCyclicTurn_cons a l
    have h₁ := abs_le.mp (compassQuarterTurn_abs_le_two ((a::l).getLast (by simp)) b)
    have h₂ := abs_le.mp (compassQuarterTurn_abs_le_two b a)
    have h₃ := abs_le.mp (compassQuarterTurn_abs_le_two ((a::l).getLast (by simp)) a)
    grind

theorem compassWordCyclicTurn_append_three_replicates_bound
    (a b c : Fin 4) (m n k : ℕ)
    (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) :
    |compassWordCyclicTurn
        (l++List.replicate m a++List.replicate n b++List.replicate k c)-
      compassWordCyclicTurn l| ≤ 18 := by
  have hl₁ : l++List.replicate m a ≠ [] := by
    simp_all
  have hl₂ : l++List.replicate m a++List.replicate n b ≠ [] := by
    simp_all
  have h₁ := abs_le.mp (compassWordCyclicTurn_append_replicate_bound l hl a m hm)
  have h₂ := abs_le.mp (compassWordCyclicTurn_append_replicate_bound _ hl₁ b n hn)
  have h₃ := abs_le.mp (compassWordCyclicTurn_append_replicate_bound _ hl₂ c k hk)
  grind
end

end PottsDiscontinuity.TorusTopology
