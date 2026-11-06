module
public import Mathlib

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.Duality.RayIndex
public import PottsDiscontinuity.FK.BoxExhaustion

/-! Finiteness of the nonzero-index region and the jump across a simple circuit. -/

@[expose] public section

namespace PottsDiscontinuity.Duality
open FK FK.Medial Filter
noncomputable section

section

variable (v : LatticeVertex) {u w : LatticeVertex} (p : squareLattice.Walk u w)
include v p

lemma rayIndex_left_telescope  (hleft : ∀ x ∈ p.support, v.1 ≤ x.1) :
    rayIndex v p = (if u.2 < v.2 then 1 else 0) -  if w.2 < v.2 then 1 else 0  := by
  induction p with
  | nil => simp [rayIndex]
  | @cons u z w h p ih =>
    grind [rayIndex, rayStep]

lemma rayIndex_zero_of_right  (hright : ∀ x ∈ p.support, x.1 < v.1) :
    rayIndex v p = 0 := by
  induction p with
  | nil => rfl
  | @cons u z w h p ih =>
    grind [rayIndex, rayStep]

lemma rayIndex_zero_of_level  (k : ℤ)
    (hk : ∀ x ∈ p.support, (if x.2 < v.2 then (1 : ℤ) else 0) = k) :
    rayIndex v p = 0 := by
  induction p with
  | nil => rfl
  | @cons u z w h p ih =>
    simp_all [rayIndex, rayStep]

end

section

variable {z : LatticeVertex} (p : squareLattice.Walk z z)


/-- The nonzero horizontal-ray index has finite support for every finite closed walk. -/
theorem finite_nonzero_rayIndex  :
    {v | rayIndex v p ≠ 0}.Finite := by
  have hevent (x : LatticeVertex) : ∀ᶠ n : ℕ in atTop, x ∈ latticeBox (0,0) n := by
    obtain ⟨N, hN⟩ := origin_latticeBox_exhaustive x
    exact eventually_atTop.2 ⟨N, fun n hn => latticeBox_mono _ hn hN⟩
  
  obtain ⟨N, hN⟩ := ((eventually_all_finset p.support.toFinset).2 fun x _ => hevent x).exists
  have hb (x : LatticeVertex) (hx : x ∈ p.support) :
      - N  ≤ x.1 ∧ x.1 ≤  N  ∧ - N  ≤ x.2 ∧ x.2 ≤  N  := by
    have h := (mem_latticeBox (0,0) x N).1 (hN x (by simpa using hx))
    
    omega
  apply (Finset.finite_toSet (latticeBox (0,0) (N+1))).subset
  intro v hv
  
  rw [Finset.mem_coe, mem_latticeBox]
  
  by_contra hn
  have hcases : v.1 ≤ - N  ∨  N  < v.1 ∨
      v.2 ≤ - N  ∨ (N ) < v.2 := by omega
  apply hv
  rcases hcases with hl | hr | hb' | ht
  · grind [rayIndex_left_telescope]
  · grind [rayIndex_zero_of_right]
  · apply rayIndex_zero_of_level v p 0
    grind
  · apply rayIndex_zero_of_level v p 1
    grind

/-- A nonzero index places the marked vertex in a finite component after only
those primal edges crossing the circuit have been removed. This is discrete separation. -/
theorem finite_avoidance_component_of_rayIndex_ne_zero  (v : LatticeVertex) (hv : rayIndex v p ≠ 0) :
    {w | (circuitAvoidanceGraph p).Reachable v w}.Finite := by
  apply (finite_nonzero_rayIndex p).subset
  intro w hw
  change rayIndex w p ≠ 0
  rw [← rayIndex_eq_of_avoidance_reachable p hw]
  exact hv

end

/-- A trail crosses its used vertical edge with a nonzero unit jump in the ray index. -/
theorem rayIndex_jump_of_vertical_edge (x y : ℤ) {u w : LatticeVertex}
    (p : squareLattice.Walk u w) (hp : p.IsTrail)
    (he : s((x,y-1),(x,y)) ∈ p.edges) :
    rayIndex (x,y) p ≠ rayIndex (x+1,y) p := by
  induction p with
  | nil => simp at he
  | @cons u z w h p ih =>
    by_cases hhead : s(u,z) = s((x,y-1),(x,y))
    · 
      have ht := rayIndex_horizontal_invariant x y p (by
                                                        simp_all)
      
      have hxx : ¬x+1 ≤ x := by omega
      rcases Sym2.eq_iff.1 hhead with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
        simp only [rayIndex, rayStep, ite_false, le_refl, ite_true, ite_eq_right hxx] <;> omega
    · 
      have hij := ih hp.of_cons (by
                                   simp_all <;> grind)
      have hs := rayStep_horizontal_invariant x y u z h hhead
      simp only [rayIndex]
      omega

end
end PottsDiscontinuity.Duality
