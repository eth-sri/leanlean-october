module

public import RequestProject.SurfaceLabel
public import RequestProject.SurfaceFilling
public import RequestProject.AttCycle

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Davis

open RACG Mirror Comb PresModel Cell

universe u

variable {α J : Type u} {w : J → List (α × Bool)} {j₀ : J}
  {κ ι : Type u} {M : ℕ} [NeZero M] [DecidableEq κ] [DecidableEq ι]
  {vc : Fin M → κ} {ec : Fin M → ι}
  {vlab : κ → Rose α} {elb : ι → Rose α}
  (hM : M = 2 * (w j₀).length)
  (hvlab : ∀ p : Fin M, vlab (vc p) = vertLab (w j₀) p.val)
  (helb : ∀ p : Fin M, elb (ec p) = edgeLab (w j₀) p.val)
  (hc : Compat vc ec)

include hM hvlab helb

theorem att_V (p : Fin M) :
    surfAtt hM hvlab helb hc (spx1 (cV hc p)) = iRose w (vertLab (w j₀) p.val) := by
  rw [surfAtt, nerveAtt_spx1]; exact congrArg (iRose w) (hvlab p)

theorem htpy_mapPath_bdEdge (p : Fin M) (rv rv' re : Rose α)
    (hv : vertLab (w j₀) p.val = rv) (hv' : vertLab (w j₀) (p + 1).val = rv')
    (he : edgeLab (w j₀) p.val = re)
    (h1 : iRose w rv ≤ iRose w re) (h2 : iRose w rv' ≤ iRose w re) :
    IsPath (orderCx (PresPos w)).src (orderCx (PresPos w)).tgt
      (mapPath (orderCxMap (surfAtt hM hvlab helb hc) (surfAtt hM hvlab helb hc).monotone)
        (bdEdge hc p)) (iRose w rv) (iRose w rv') ∧
    Htpy (orderCx (PresPos w)) (iRose w rv) (iRose w rv')
      (mapPath (orderCxMap (surfAtt hM hvlab helb hc) (surfAtt hM hvlab helb hc).monotone)
        (bdEdge hc p))
      [ordPos h1, ordNeg h2] := by
  subst hv hv' he
  have hE : surfAtt hM hvlab helb hc (spx1 (cE hc p)) = iRose w (edgeLab (w j₀) p.val) := by
    rw [surfAtt, nerveAtt_spx1]; exact congrArg (iRose w) (helb p)
  have hVE : surfAtt hM hvlab helb hc (spx2 (cV_le_cE hc p)) = iRose w (edgeLab (w j₀) p.val) := by
    rw [surfAtt, nerveAtt_spx2]; exact congrArg (iRose w) (helb p)
  have hV1E : surfAtt hM hvlab helb hc (spx2 (cV1_le_cE hc p)) = iRose w (edgeLab (w j₀) p.val) := by
    rw [surfAtt, nerveAtt_spx2]; exact congrArg (iRose w) (helb p)
  have h0 : iRose w (edgeLab (w j₀) p.val) ≤ iRose w (edgeLab (w j₀) p.val) := le_rfl
  have hmap : mapPath (orderCxMap (surfAtt hM hvlab helb hc) (surfAtt hM hvlab helb hc).monotone)
      (bdEdge hc p) = [ordPos h1, ordNeg h0, ordPos h0, ordNeg h2] :=
    congrArg₂ List.cons
      (ordPos_congr (att_V hM hvlab helb hc p) hVE
        ((surfAtt hM hvlab helb hc).monotone (spx1_le_spx2_left (cV_le_cE hc p))) h1)
      (congrArg₂ List.cons
        (ordNeg_congr hE hVE
          ((surfAtt hM hvlab helb hc).monotone (spx1_le_spx2_right (cV_le_cE hc p))) h0)
        (congrArg₂ List.cons
          (ordPos_congr hE hV1E
            ((surfAtt hM hvlab helb hc).monotone (spx1_le_spx2_right (cV1_le_cE hc p))) h0)
          (congrArg₂ List.cons
            (ordNeg_congr (att_V hM hvlab helb hc (p + 1)) hV1E
              ((surfAtt hM hvlab helb hc).monotone (spx1_le_spx2_left (cV1_le_cE hc p))) h2)
            rfl)))
  rw [hmap]
  exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, by
    simpa using (htpy_ordNeg_ordPos h0).congr_append (r := [ordPos h1]) (s := [ordNeg h2])
      (isPath_ordPos h1) (isPath_ordNeg h2)⟩

theorem htpy_mapPath_letter (k : ℕ) (hk : k < (w j₀).length) :
    Htpy (orderCx (PresPos w)) (ptBase w) (ptBase w)
      (mapPath (orderCxMap (surfAtt hM hvlab helb hc) (surfAtt hM hvlab helb hc).monotone)
        (bdEdge hc (cyc M (2 * k)) ++ bdEdge hc (cyc M (2 * k + 1))))
      (letterLoop w ((w j₀)[k]'hk)) := by
  classical
  set q : α × Bool := (w j₀)[k]'hk
  have hq : (w j₀)[k]? = some q := List.getElem?_eq_getElem hk
  have hv0 : (cyc M (2 * k)).val = 2 * k := Nat.mod_eq_of_lt (by omega)
  have hv1 : (cyc M (2 * k + 1)).val = 2 * k + 1 := Nat.mod_eq_of_lt (by omega)
  have hq0 : (w j₀)[(2 * k) / 2]? = some q := by rwa [show (2 * k) / 2 = k by omega]
  have hq1 : (w j₀)[(2 * k + 1) / 2]? = some q := by rwa [show (2 * k + 1) / 2 = k by omega]
  have hvert1' : vertLab (w j₀) (cyc M (2 * k + 1)).val = Rose.mid q.1 := by
    rw [hv1]; exact vertLab_of_odd (by omega) hq1
  have hA := htpy_mapPath_bdEdge hM hvlab helb hc (cyc M (2 * k)) Rose.base (Rose.mid q.1)
    (Rose.edg q.1 (!q.2))
    (by rw [hv0]; exact vertLab_of_even (by omega))
    (by rw [← cyc_succ (2 * k), hvert1'])
    (by rw [hv0, edgeLab_eq hq0, if_pos (by omega)])
    ((iRose_monotone w) (Rose.base_le_edg q.1 (!q.2)))
    ((iRose_monotone w) (Rose.mid_le_edg q.1 (!q.2)))
  have hB := htpy_mapPath_bdEdge hM hvlab helb hc (cyc M (2 * k + 1)) (Rose.mid q.1) Rose.base
    (Rose.edg q.1 q.2) hvert1'
    (by
      rw [fin_succ_val, hv1]
      refine vertLab_of_even ?_
      rcases Nat.lt_or_ge (2 * k + 2) M with hlt | hge
      · rw [Nat.mod_eq_of_lt hlt]; omega
      · rw [show 2 * k + 2 = M by omega, Nat.mod_self])
    (by rw [hv1, edgeLab_eq hq1, if_neg (by omega)])
    ((iRose_monotone w) (Rose.mid_le_edg q.1 q.2))
    ((iRose_monotone w) (Rose.base_le_edg q.1 q.2))
  have hloop : letterLoop w q =
      [ordPos ((iRose_monotone w) (Rose.base_le_edg q.1 (!q.2))),
       ordNeg ((iRose_monotone w) (Rose.mid_le_edg q.1 (!q.2))),
       ordPos ((iRose_monotone w) (Rose.mid_le_edg q.1 q.2)),
       ordNeg ((iRose_monotone w) (Rose.base_le_edg q.1 q.2))] := by
    rcases q with ⟨_, _ | _⟩ <;> rfl
  rw [mapPath_append, hloop]
  simpa [PresModel.ptBase, PresModel.iRose] using Htpy.append_congr hA.1 hB.1 hA.2 hB.2
