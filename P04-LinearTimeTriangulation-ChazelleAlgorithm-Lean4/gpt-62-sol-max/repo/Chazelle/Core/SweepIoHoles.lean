module

public import Chazelle.Core.RestoreTHoles
public import Chazelle.Core.NFBuildRen

/-! The sweep uses the same hole computation as restoration, with its own register band. -/

namespace Chazelle.Core.SweepIo
open Machine BuildRam

@[expose] public section

/-- Swap the two descriptor/scratch bands and the two hole output blocks. -/
def holeRen (r : ℕ) : ℕ :=
  if 83000 ≤ r ∧ r < 83200 then r + 160000
  else if 243000 ≤ r ∧ r < 243200 then r - 160000
  else if 84000 ≤ r ∧ r < 84016 then r + 157300
  else if 241300 ≤ r ∧ r < 241316 then r - 157300
  else r

theorem holeRen_invol (r : ℕ) : holeRen (holeRen r) = r := by
  unfold holeRen; split_ifs <;> omega

/-- The chain-hole code in the sweep's registers. -/
def chainH : Stmt := Stmt.ren holeRen Restore.chainH

/-- The scratch registers of `chainH`. -/
def chainHL : List ℕ := [243090, 243095, 243096, 243097, 243098, 243099, 243100, 243101, 243102, 243103,
  243104, 243105, 243106, 243107, 243108, 243109, 243110, 243111, 243112, 243113, 243114, 241309, 241310,
  241311, 241312, 241313, 241314, 241315]

theorem holeList_one (c : Config) (h : c.nreg 241309 = 1) :
    ShotList.holeList c 241300 = [ShotList.holeAt c 241300 0] := by
  simp [ShotList.holeList, h]

abbrev HoleOut := Restore.HoleOutAt 241300

/-- The scratch registers of the hole routine. -/
def holeL : List ℕ := chainHL ++ [243092, 243093]

open Restore (Out)

private theorem holeOut_ren {M : Model} {Q : Polygon} {d : Config} {z : Point}
    (h : Restore.HoleOut M Q d z) : HoleOut M Q (cfgRen holeRen d) z := by
  obtain ⟨h3, he, hc, hn⟩ := h
  have a (j : ℕ) (hj : j < 3) : holeRen (241300 + 10 + 2*j) = 84000 + 10 + 2*j := by
    unfold holeRen; split_ifs <;> omega
  have b (j : ℕ) (hj : j < 3) : holeRen (241300 + 11 + 2*j) = 84000 + 11 + 2*j := by
    unfold holeRen; split_ifs <;> omega
  change d.nreg 84009 ≤ 3 at h3
  have hl : ShotList.holeList (cfgRen holeRen d) 241300 = ShotList.holeList d 84000 := by
    unfold ShotList.holeList
    change (List.range (min (d.nreg 84009) 3)).map _ = _
    apply List.map_congr_left
    intro j hj
    have hj' := List.mem_range.mp hj
    unfold ShotList.holeAt cfgRen
    simp only [a j (by omega), b j (by omega)]
  refine ⟨h3, fun j hj => ?_, hl ▸ hc, hl ▸ hn⟩
  change j < d.nreg 84009 at hj
  simpa only [cfgRen, a j (by omega), b j (by omega)] using he j hj

private theorem out_ren {c d : Config} (h : Out (cfgRen holeRen c) d Restore.holeL) :
    Out c (cfgRen holeRen d) holeL := by
  refine ⟨fun r hr => ?_, ?_, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  · change r ∉ Restore.holeL.map holeRen at hr
    have hnr := h.1 (holeRen r) (fun hmem => hr (List.mem_map.mpr ⟨_, hmem, holeRen_invol r⟩))
    simpa only [cfgRen, holeRen_invol] using hnr
  · have hh := congrFun h.2.1
    funext r
    simpa only [cfgRen, holeRen_invol] using hh (holeRen r)

variable {P : Polygon} {W : ℕ}

/-- **The holes of a position in a chain model** (`chainH`): pairs of distinct walk vertices
covering its point, near it; only the scratch registers `holeL` change.  The position
`x = (243005, 243006)` is normalised (height code `0` exactly at a walk vertex) and its point lies
on the chain; `243020` holds the address of the chain descriptor, `243022 = 0`, `243023 = 1`. -/
theorem chainH_exec {c : Config} (hw : WordsBounded W c) {H : Host} {C : Chain}
    (hC : ChainDescAt c.nmem (c.nreg 243020) (Qof P) H C)
    (hwf : c.nreg 243020 + 5 ≤ c.nreg ALLOC) (hsimp : C.P.Simple) (hWm : 2 * C.m + 7 ≤ W)
    (h22 : c.nreg 243022 = 0) (h23 : c.nreg 243023 = 1)
    (hxp : ProperPos (chainModel C) (Qof P) P.n ⟨c.nreg 243005, c.nreg 243006⟩)
    (hxe : c.nreg 243005 < (chainModel C).W.n)
    (hxc : c.nreg 243006 = 0 ∨ 0 < (chainModel C).param (Qof P) ⟨c.nreg 243005, c.nreg 243006⟩)
    (hxC : (chainModel C).pos (Qof P) ⟨c.nreg 243005, c.nreg 243006⟩ ∈ C.set) :
    ∃ c' k, Exec P W chainH c c' k ∧ k ≤ 100 ∧ HoleOut (chainModel C) (Qof P) c'
      ((chainModel C).pos (Qof P) ⟨c.nreg 243005, c.nreg 243006⟩) ∧ Out c c' holeL := by
  obtain ⟨d, k, e, hk, ho, hf⟩ := Restore.chainH_exec
    (c := cfgRen holeRen c) ((wordsBounded_ren holeRen_invol c).2 hw)
    hC hwf hsimp hWm h22 h23 hxp hxe hxc hxC
  exact ⟨cfgRen holeRen d, k, exec_of_ren holeRen_invol e, by omega, holeOut_ren ho, out_ren hf⟩

end
end Chazelle.Core.SweepIo
