module

public import PottsDiscontinuity.TorusTopology.LatticeUpperReturn

/-! A supporting-line return for a simple periodic lattice arc. -/

public section

namespace PottsDiscontinuity.TorusTopology
open SimpleGraph Torus

/-- Integer linear height normal to the deck direction D. -/
def deckNormalHeight (D z : ℤ × ℤ) : ℤ := D.1*z.2-D.2*z.1

theorem deckNormalHeight_add_deck (D z : ℤ × ℤ) (k : ℕ) :
    deckNormalHeight D (z+k • D) = deckNormalHeight D z := by
  change D.1*(z.2+k • D.2)-D.2*(z.1+k • D.1) = _
  grind [deckNormalHeight]

theorem upperReturn_compassDirections (u v : ℤ × ℤ) (Y : ℤ) (h : u.1 < v.1)
    (hu : u.2 < Y) (hv : v.2 < Y) :
    squareWalkCompassDirections (upperReturn u v Y h hu hv) =
      List.replicate (Y-v.2).toNat 1 ++ List.replicate (v.1-u.1).toNat 2 ++
        List.replicate (Y-u.2).toNat 3 := by
  simp only [upperReturn,squareWalkCompassDirections,Walk.darts_append,List.map_append]
  simp only [upperReturnNorth,upperReturnWest,upperReturnSouth,Walk.darts_copy]
  change squareWalkCompassDirections (straightWalk v .north _) ++
    squareWalkCompassDirections (straightWalk (v.1,Y) .west _) ++
    squareWalkCompassDirections (straightWalk (u.1,Y) .south _) = _
  simp only [straightWalk_compassDirections,portCompass]

section
variable (D u v : ℤ × ℤ) (hDx : 0 < D.1) (heq : deckNormalHeight D u = deckNormalHeight D v)
include hDx heq
/-- Apart from its two endpoints the upper return lies strictly above the
supporting line normal to D. -/
theorem upperReturn_support_above (Y : ℤ) (h : u.1 < v.1) (hu : u.2 < Y) (hv : v.2 < Y)
    (z : ℤ × ℤ) (hz : z ∈ (upperReturn u v Y h hu hv).support) :
    z=u ∨ z=v ∨ deckNormalHeight D u < deckNormalHeight D z := by
  simp only [upperReturn,Walk.support_append,List.mem_append] at hz
  rcases hz with (hzn | hzw) | hzs
  · have hn := (upperReturnNorth_mem v Y hv z).mp hzn
    by_cases hzz : z=v
    · simp_all
    · have hzy : v.2 < z.2 := by
        grind
      simp_all [deckNormalHeight]
  · have hw := (upperReturnWest_mem u v Y h z).mp (List.mem_of_mem_tail hzw)
    right; right
    dsimp [deckNormalHeight] at heq ⊢
    rcases le_total 0 D.2 with hDy | hDy <;> nlinarith
  · have hs := (upperReturnSouth_mem u Y hu z).mp (List.mem_of_mem_tail hzs)
    by_cases hzz : z=u
    · simp_all
    · have hzy : u.2 < z.2 := by
        grind
      have hh := mul_pos hDx (sub_pos.mpr hzy)
      grind [deckNormalHeight]

/-- A simple arc lying below a supporting line closes to a genuine simple
lattice cycle by the literal upper return. -/
theorem isCycle_append_upperReturn (p : FK.squareLattice.Walk u v) (hp : p.IsPath)
    (hbelow : ∀ z ∈ p.support, deckNormalHeight D z ≤ deckNormalHeight D u)
    (Y : ℤ) (h : u.1 < v.1) (hu : u.2 < Y) (hv : v.2 < Y)
    (hlen : 1 < p.length) :
    (p.append (upperReturn u v Y h hu hv)).IsCycle := by
  have hret := upperReturn_isPath u v Y h hu hv
  apply hp.isCycle_append hret _ (Or.inl hlen)
  intro z hz hpz
  have hpn := hp.support_nodup
  rw [← p.cons_tail_support,List.nodup_cons] at hpn
  have hrn := hret.support_nodup
  rw [← (upperReturn u v Y h hu hv).cons_tail_support,List.nodup_cons] at hrn
  rcases (upperReturn_support_above D u v hDx heq Y h hu hv z (List.mem_of_mem_tail hpz)) with he | he | hh
  · simp_all
  · simp_all
  · exact (not_lt_of_ge (hbelow z (List.mem_of_mem_tail hz))) hh
end

end PottsDiscontinuity.TorusTopology
