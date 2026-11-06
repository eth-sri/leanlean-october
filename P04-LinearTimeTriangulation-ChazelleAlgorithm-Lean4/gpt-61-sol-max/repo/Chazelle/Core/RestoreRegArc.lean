module

public import Chazelle.Core.DownPhaseHostSimple
public import Chazelle.Core.RestoreFind

/-!
# WP-E, the search: every region of a nonempty normal form has an arc

A region is faced at a non-cut walk position (`exists_faces_nc`); the non-cut key lies inside an
arc of the region it faces (`arc_around`, `faces_unique`), and the arc records list it.
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Chazelle.Chain (sideInArc)

/-- **Every region of a nonempty valid normal form has an arc record.** -/
theorem region_arc {M : Model} {Q : Polygon} {N : NF} {reg : ℕ → Set Point}
    (hM : WalkAx M) (hN : IsNF M Q N) (hregs : NFRegs M Q N reg)
    (hne : (N.F M Q).Nonempty) {r : ℕ} (hr : r < N.nRegions) :
    0 < (N.region r).arcs.length ∧ (N.region r).arcs.getD 0 0 < N.arcs.length ∧
      (N.arc ((N.region r).arcs.getD 0 0)).reg = r := by
  have hF : N.F M Q ⊆ M.Adm := hN.1.2.1
  have hfin : (N.F M Q).Finite := hN.1.1
  have hR := hregs.1.1 r hr
  obtain ⟨p, t, hp, ht0, ht1, hnc, hf⟩ := DownHost.exists_faces_nc hM hF hfin hR
  obtain ⟨X, hX, l, r', harc, hin⟩ := hM.arc_around hF hfin hne hnc
  have hfX : M.Faces p t X := harc.2.2.2.2.2.2 p t hp ht0 ht1 hin
  have hXR : X = reg r := WalkAx.faces_unique hX hR hfX hf
  rw [hXR] at harc
  obtain ⟨j, hj, hjr, -, -⟩ := hregs.2.2.1.2.2.1 r hr l r' harc
  have hmem : j ∈ (N.region r).arcs := ((hregs.2.2.1.2.2.2 r hr j).2 ⟨hj, hjr⟩)
  have hlen : 0 < (N.region r).arcs.length := List.length_pos_of_mem hmem
  have h0 : (N.region r).arcs.getD 0 0 ∈ (N.region r).arcs := by
    simp_all
  obtain ⟨a, b⟩ := (hregs.2.2.1.2.2.2 r hr _).1 h0
  omega

end

end Restore

end Chazelle.Core
