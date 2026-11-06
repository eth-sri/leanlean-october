module

public import PottsDiscontinuity.TorusTopology.LatticeStraightWalk

/-! A literal three-sided lattice return above two endpoints. -/

@[expose] public section

namespace PottsDiscontinuity.TorusTopology
open SimpleGraph Torus

/-- The upward segment from v to the named height. -/
def upperReturnNorth (v : ℤ × ℤ) (Y : ℤ) (hv : v.2 < Y) :
    FK.squareLattice.Walk v (v.1,Y) :=
  (straightWalk v .north (Y-v.2).toNat).copy rfl (by
    ext <;> simp [straightPosition,portVector,Int.toNat_of_nonneg (by omega : 0 ≤ Y-v.2)])

/-- The leftward segment at the named height. -/
def upperReturnWest (u v : ℤ × ℤ) (Y : ℤ) (h : u.1 < v.1) :
    FK.squareLattice.Walk (v.1,Y) (u.1,Y) :=
  (straightWalk (v.1,Y) .west (v.1-u.1).toNat).copy rfl (by
    ext <;> simp [straightPosition,portVector,Int.toNat_of_nonneg (by omega : 0 ≤ v.1-u.1)])

/-- The downward segment to u. -/
def upperReturnSouth (u : ℤ × ℤ) (Y : ℤ) (hu : u.2 < Y) :
    FK.squareLattice.Walk (u.1,Y) u :=
  (straightWalk (u.1,Y) .south (Y-u.2).toNat).copy rfl (by
    ext <;> simp [straightPosition,portVector,Int.toNat_of_nonneg (by omega : 0 ≤ Y-u.2)])

/-- The return from the right endpoint v to the left endpoint u via height Y. -/
def upperReturn (u v : ℤ × ℤ) (Y : ℤ) (h : u.1 < v.1)
    (hu : u.2 < Y) (hv : v.2 < Y) : FK.squareLattice.Walk v u :=
  ((upperReturnNorth v Y hv).append (upperReturnWest u v Y h)).append
    (upperReturnSouth u Y hu)

theorem upperReturnNorth_mem (v : ℤ × ℤ) (Y : ℤ) (hv : v.2 < Y) (z : ℤ × ℤ) :
    z ∈ (upperReturnNorth v Y hv).support ↔ z.1=v.1 ∧ v.2 ≤ z.2 ∧ z.2 ≤ Y := by
  rw [upperReturnNorth,Walk.support_copy,mem_straightWalk_support_iff]
  constructor
  · rintro ⟨k,hk,hz⟩
    have hx := congrArg Prod.fst hz
    have hy := congrArg Prod.snd hz
    simp [straightPosition,portVector] at hx hy
    omega
  · rintro ⟨hx,hlo,hhi⟩
    refine ⟨(z.2-v.2).toNat,by omega,?_⟩
    ext <;> simp [straightPosition,portVector,Int.toNat_of_nonneg (by omega : 0 ≤ z.2-v.2)]; omega

theorem upperReturnWest_mem (u v : ℤ × ℤ) (Y : ℤ) (h : u.1 < v.1) (z : ℤ × ℤ) :
    z ∈ (upperReturnWest u v Y h).support ↔ z.2=Y ∧ u.1 ≤ z.1 ∧ z.1 ≤ v.1 := by
  rw [upperReturnWest,Walk.support_copy,mem_straightWalk_support_iff]
  constructor
  · rintro ⟨k,hk,hz⟩
    have hx := congrArg Prod.fst hz
    have hy := congrArg Prod.snd hz
    simp [straightPosition,portVector] at hx hy
    omega
  · rintro ⟨hy,hlo,hhi⟩
    refine ⟨(v.1-z.1).toNat,by omega,?_⟩
    ext <;> simp [straightPosition,portVector,Int.toNat_of_nonneg (by omega : 0 ≤ v.1-z.1)]; omega

theorem upperReturnSouth_mem (u : ℤ × ℤ) (Y : ℤ) (hu : u.2 < Y) (z : ℤ × ℤ) :
    z ∈ (upperReturnSouth u Y hu).support ↔ z.1=u.1 ∧ u.2 ≤ z.2 ∧ z.2 ≤ Y := by
  rw [upperReturnSouth,Walk.support_copy,mem_straightWalk_support_iff]
  constructor
  · rintro ⟨k,hk,hz⟩
    have hx := congrArg Prod.fst hz
    have hy := congrArg Prod.snd hz
    simp [straightPosition,portVector] at hx hy
    omega
  · rintro ⟨hx,hlo,hhi⟩
    refine ⟨(Y-z.2).toNat,by omega,?_⟩
    ext <;> simp [straightPosition,portVector,Int.toNat_of_nonneg (by omega : 0 ≤ Y-z.2)]; omega

theorem path_tail_mem_iff {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (hp : p.IsPath) (z : V) :
    z ∈ p.support.tail ↔ z ∈ p.support ∧ z ≠ u := by
  have hh := hp.support_nodup
  rw [← p.cons_tail_support] at hh
  rw [← p.cons_tail_support,List.mem_cons]
  grind

theorem upperReturn_isPath (u v : ℤ × ℤ) (Y : ℤ) (h : u.1 < v.1)
    (hu : u.2 < Y) (hv : v.2 < Y) : (upperReturn u v Y h hu hv).IsPath := by
  have hn : (upperReturnNorth v Y hv).IsPath := by
    simp only [upperReturnNorth,Walk.isPath_copy]; exact straightWalk_isPath _ _ _
  have hw : (upperReturnWest u v Y h).IsPath := by
    simp only [upperReturnWest,Walk.isPath_copy]; exact straightWalk_isPath _ _ _
  have hs : (upperReturnSouth u Y hu).IsPath := by
    simp only [upperReturnSouth,Walk.isPath_copy]; exact straightWalk_isPath _ _ _
  rw [Walk.isPath_def,upperReturn,Walk.support_append,Walk.support_append]
  apply List.Nodup.append
  · apply List.Nodup.append hn.support_nodup hw.support_nodup.tail
    rw [List.disjoint_left]
    simp_all [upperReturnWest_mem, path_tail_mem_iff, upperReturnNorth_mem]
  · exact hs.support_nodup.tail
  · rw [List.disjoint_left]
    grind [upperReturnSouth_mem, path_tail_mem_iff, upperReturnNorth_mem, upperReturnWest_mem]

end PottsDiscontinuity.TorusTopology
