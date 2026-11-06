import Mathlib.Tactic

import RequestProject.SurfaceLabel
import RequestProject.SurfaceFilling
import RequestProject.AttCycleLoop

/-!
# The boundary of the polygon reads the word

The marking of `RequestProject/SurfaceLabel.lean` sends the boundary of the polygon onto the
subdivided rose of the model of the presentation complex.  This file computes what is read:
crossing the two boundary edges of the letter `k` of the word `w j₀` gives, up to two
backtrackings which cancel, exactly the loop `letterLoop w (w j₀)[k]` of that letter.

* `FiniteChains.Davis.att_V`, `att_E`, `att_VE`, `att_V1E` — the values of the attaching map on
  the chains of the boundary;
* `FiniteChains.Davis.mapPath_letter_eq` — the image of the two boundary edges of a letter,
  computed as an explicit list of eight edges of the model;
* `FiniteChains.Davis.htpy_mapPath_letter` — after cancelling the two backtrackings, that image
  is the loop of the letter.
-/



namespace FiniteChains.Davis


open RACG Mirror Comb PresModel Cell


section

variable {α J : Type u} {w : J → List (α × Bool)} {j₀ : J}
  {κ ι : Type u} {M : ℕ} [NeZero M] [DecidableEq κ] [DecidableEq ι]
  {vc : Fin M → κ} {ec : Fin M → ι}
  {vlab : κ → Rose α} {elb : ι → Rose α}
  (hM : M = 2 * (w j₀).length)
  (hvlab : ∀ p : Fin M, vlab (vc p) = vertLab (w j₀) p.val)
  (helb : ∀ p : Fin M, elb (ec p) = edgeLab (w j₀) p.val)
  (hc : Compat vc ec)

/-- The loop of a letter, written out; the universe-polymorphic form of
`FiniteChains.Davis.letterLoop_eq`. -/
theorem letterLoop_eq' (q : α × Bool) :
    letterLoop w q =
      [ordPos ((iRose_monotone w) (Rose.base_le_edg q.1 (!q.2))),
       ordNeg ((iRose_monotone w) (Rose.mid_le_edg q.1 (!q.2))),
       ordPos ((iRose_monotone w) (Rose.mid_le_edg q.1 q.2)),
       ordNeg ((iRose_monotone w) (Rose.base_le_edg q.1 q.2))] := by
  obtain ⟨i, b⟩ := q
  cases b <;> rfl

include hM hvlab helb

/-! ### The values of the attaching map on the boundary -/

variable (p : Fin M)
theorem att_V  :
    surfAtt hM hvlab helb hc (spx1 (cV hc p)) = iRose w (vertLab (w j₀) p.val) := by
  rw [surfAtt, nerveAtt_spx1]
  show iRose w (vlab (vc p)) = _
  rw [hvlab p]

theorem att_E  :
    surfAtt hM hvlab helb hc (spx1 (cE hc p)) = iRose w (edgeLab (w j₀) p.val) := by
  rw [surfAtt, nerveAtt_spx1]
  show iRose w (elb (ec p)) = _
  rw [helb p]

theorem att_VE  :
    surfAtt hM hvlab helb hc (spx2 (cV_le_cE hc p)) = iRose w (edgeLab (w j₀) p.val) := by
  rw [surfAtt, nerveAtt_spx2]
  show iRose w (elb (ec p)) = _
  rw [helb p]

theorem att_V1E  :
    surfAtt hM hvlab helb hc (spx2 (cV1_le_cE hc p)) = iRose w (edgeLab (w j₀) p.val) := by
  rw [surfAtt, nerveAtt_spx2]
  show iRose w (elb (ec p)) = _
  rw [helb p]

/-! ### The image of one boundary edge -/

/-- The image of the two-edge crossing of the boundary edge at `p`. -/
theorem mapPath_bdEdge 
    (h1 : iRose w (vertLab (w j₀) p.val) ≤ iRose w (edgeLab (w j₀) p.val))
    (h0 : iRose w (edgeLab (w j₀) p.val) ≤ iRose w (edgeLab (w j₀) p.val))
    (h2 : iRose w (vertLab (w j₀) (p + 1).val) ≤ iRose w (edgeLab (w j₀) p.val)) :
    mapPath (orderCxMap (surfAtt hM hvlab helb hc) (surfAtt hM hvlab helb hc).monotone)
        (bdEdge hc p)
      = [ordPos h1, ordNeg h0, ordPos h0, ordNeg h2] := by
  have e1 := att_V hM hvlab helb hc p
  have e2 := att_VE hM hvlab helb hc p
  have e3 := att_E hM hvlab helb hc p
  have e4 := att_V hM hvlab helb hc (p + 1)
  have e5 := att_V1E hM hvlab helb hc p
  have c1 := ordPos_congr e1 e2
    ((surfAtt hM hvlab helb hc).monotone (spx1_le_spx2_left (cV_le_cE hc p))) h1
  have c2 := ordNeg_congr e3 e2
    ((surfAtt hM hvlab helb hc).monotone (spx1_le_spx2_right (cV_le_cE hc p))) h0
  have c3 := ordPos_congr e3 e5
    ((surfAtt hM hvlab helb hc).monotone (spx1_le_spx2_right (cV1_le_cE hc p))) h0
  have c4 := ordNeg_congr e4 e5
    ((surfAtt hM hvlab helb hc).monotone (spx1_le_spx2_left (cV1_le_cE hc p))) h2
  exact congrArg₂ List.cons c1 (congrArg₂ List.cons c2 (congrArg₂ List.cons c3
    (congrArg₂ List.cons c4 rfl)))

/-- The two backtrackings in the image of a boundary edge cancel. -/
theorem htpy_mapPath_bdEdge  (rv rv' re : Rose α)
    (hv : vertLab (w j₀) p.val = rv) (hv' : vertLab (w j₀) (p + 1).val = rv')
    (he : edgeLab (w j₀) p.val = re)
    (h1 : iRose w rv ≤ iRose w re) (h2 : iRose w rv' ≤ iRose w re) :
    Htpy (orderCx (PresPos w)) (iRose w rv) (iRose w rv')
      (mapPath (orderCxMap (surfAtt hM hvlab helb hc) (surfAtt hM hvlab helb hc).monotone)
        (bdEdge hc p))
      [ordPos h1, ordNeg h2] := by
  subst hv
  subst hv'
  subst he
  rw [mapPath_bdEdge hM hvlab helb hc p h1 (le_refl _) h2]
  have hcancel := htpy_ordNeg_ordPos (le_refl (iRose w (edgeLab (w j₀) p.val)))
  have hh := hcancel.congr_append (r := [ordPos h1]) (s := [ordNeg h2])
    (isPath_ordPos h1) (isPath_ordNeg h2)
  simpa using hh

/-! ### The letter read along the boundary -/

/-- **The boundary of the polygon reads the word**: crossing the two boundary edges of the
letter `k` gives the loop of that letter in the model of the presentation complex. -/
theorem htpy_mapPath_letter (k : ℕ) (hk : k < (w j₀).length) :
    Htpy (orderCx (PresPos w)) (ptBase w) (ptBase w)
      (mapPath (orderCxMap (surfAtt hM hvlab helb hc) (surfAtt hM hvlab helb hc).monotone)
        (bdEdge hc (cyc M (2 * k)) ++ bdEdge hc (cyc M (2 * k + 1))))
      (letterLoop w ((w j₀)[k]'hk)) := by
  classical
  set q : α × Bool := (w j₀)[k]'hk with hqdef
  
  have hq  := List.getElem?_eq_getElem hk
  -- the two positions of the letter
  have h2k : 2 * k < M := by omega
  have h2k1 : 2 * k + 1 < M := by omega
  have hv0 : (cyc M (2 * k)).val = 2 * k := Nat.mod_eq_of_lt h2k
  have hv1 : (cyc M (2 * k + 1)).val = 2 * k + 1 := Nat.mod_eq_of_lt h2k1
  have hsucc : cyc M (2 * k) + 1 = cyc M (2 * k + 1) := (cyc_succ (2 * k)).symm
  -- the labels
  have hq0 : (w j₀)[(2 * k) / 2]? = some q := by
    rw [show (2 * k) / 2 = k by omega]; exact hq
  have hq1 : (w j₀)[(2 * k + 1) / 2]? = some q := by
    rw [show (2 * k + 1) / 2 = k by omega]; exact hq
  have hvert0 : vertLab (w j₀) (cyc M (2 * k)).val = Rose.base := by
    rw [hv0]; exact vertLab_of_even (by omega)
  have hedge0 : edgeLab (w j₀) (cyc M (2 * k)).val = Rose.edg q.1 (!q.2) := by
    rw [hv0, edgeLab_eq hq0, if_pos (by omega)]
  have hvert1 : vertLab (w j₀) (cyc M (2 * k) + 1).val = Rose.mid q.1 := by
    simp_all [FiniteChains.Davis.vertLab_of_odd]
  have hvert1' : vertLab (w j₀) (cyc M (2 * k + 1)).val = Rose.mid q.1 := by
    rw [hv1]; exact vertLab_of_odd (by omega) hq1
  have hedge1 : edgeLab (w j₀) (cyc M (2 * k + 1)).val = Rose.edg q.1 q.2 := by
    rw [hv1, edgeLab_eq hq1, if_neg (by omega)]
  have hvert2 : vertLab (w j₀) (cyc M (2 * k + 1) + 1).val = Rose.base := by
    have hval : (cyc M (2 * k + 1) + 1).val = (2 * k + 2) % M := by
      rw [fin_succ_val, hv1]
    aesop
  -- the two halves of the letter
  have hA := htpy_mapPath_bdEdge hM hvlab helb hc (cyc M (2 * k)) Rose.base (Rose.mid q.1)
    (Rose.edg q.1 (!q.2)) hvert0 hvert1 hedge0
    ((iRose_monotone w) (Rose.base_le_edg q.1 (!q.2)))
    ((iRose_monotone w) (Rose.mid_le_edg q.1 (!q.2)))
  have hB := htpy_mapPath_bdEdge hM hvlab helb hc (cyc M (2 * k + 1)) (Rose.mid q.1) Rose.base
    (Rose.edg q.1 q.2) hvert1' hvert2 hedge1
    ((iRose_monotone w) (Rose.mid_le_edg q.1 q.2))
    ((iRose_monotone w) (Rose.base_le_edg q.1 q.2))
  have hcomb := Htpy.append_congr (hA.symm.isPath ⟨rfl, rfl, rfl⟩)
    (hB.symm.isPath ⟨rfl, rfl, rfl⟩) hA hB
  simp_all [FiniteChains.Comb.Htpy, letterLoop_eq', PresModel.ptBase, PresModel.iRose]

end

end FiniteChains.Davis

