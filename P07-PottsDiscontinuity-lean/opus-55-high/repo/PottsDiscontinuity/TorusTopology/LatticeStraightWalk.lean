module

public import PottsDiscontinuity.TorusTopology.MidpointCyclicTurning

/-! Literal directed straight segments for closing long periodic lattice arcs. -/

@[expose] public section

namespace PottsDiscontinuity.TorusTopology
open SimpleGraph
open PottsDiscontinuity.SixVertex

section
variable (z : ℤ × ℤ) (p : Torus.Port)
/-- Position after n unit steps in the named cardinal direction. -/
def straightPosition (n : ℕ) : ℤ × ℤ :=
  z+n • portVector p

theorem straightPosition_succ (n : ℕ) :
    straightPosition z p (n+1) = straightPosition z p n+portVector p := by
  simp only [straightPosition,add_nsmul,one_nsmul]
  abel

theorem straightPosition_injective  :
    Function.Injective (straightPosition z p) := by
  intro a b h
  cases p
  all_goals
    have hx := congrArg Prod.fst h
    have hy := congrArg Prod.snd h
    simp [straightPosition,portVector] at hx hy
    omega

theorem straightPosition_adj (n : ℕ) :
    FK.squareLattice.Adj (straightPosition z p n) (straightPosition z p (n+1)) := by
  rw [straightPosition_succ]
  exact squareLattice_adj_portVector _ _
end

/-- The actual n-edge straight lattice walk, with its original start retained. -/
def straightWalk (z : ℤ × ℤ) (p : Torus.Port) :
    (n : ℕ) → FK.squareLattice.Walk z (straightPosition z p n)
  | 0 => (Walk.nil : FK.squareLattice.Walk z z).copy rfl (by simp [straightPosition])
  | n+1 => (straightWalk z p n).concat (straightPosition_adj z p n)


section
variable (z : ℤ × ℤ) (p : Torus.Port) (n : ℕ)
theorem straightWalk_support  :
    (straightWalk z p n).support = (List.range (n+1)).map (straightPosition z p) := by
  induction n with
  | zero =>
    simp only [straightWalk,Walk.support_copy,Walk.support_nil]
    simp [straightPosition]
  | succ n ih =>
    simp only [straightWalk,Walk.support_concat,ih,List.range_succ,
      List.map_append,List.map_singleton]

theorem straightWalk_isPath  :
    (straightWalk z p n).IsPath := by
  rw [Walk.isPath_def,straightWalk_support]
  exact List.nodup_range.map (straightPosition_injective z p)

theorem straightWalk_compassDirections  :
    squareWalkCompassDirections (straightWalk z p n) = List.replicate n (portCompass p) := by
  induction n with
  | zero => simp [straightWalk,squareWalkCompassDirections]
  | succ n ih =>
    simp only [straightWalk,squareWalkCompassDirections,Walk.darts_concat,
      List.concat_eq_append,List.map_append,List.map_singleton]
    change squareWalkCompassDirections (straightWalk z p n) ++ _ = _
    rw [ih,List.replicate_succ']
    congr 1
    exact congrArg (fun d => [d])
      (squareDartCompass_eq_portCompass _ p (straightPosition_succ z p n))

theorem mem_straightWalk_support_iff (v : ℤ × ℤ) :
    v ∈ (straightWalk z p n).support ↔ ∃ k ≤ n, straightPosition z p k = v := by
  simp [straightWalk_support]
end

end PottsDiscontinuity.TorusTopology
