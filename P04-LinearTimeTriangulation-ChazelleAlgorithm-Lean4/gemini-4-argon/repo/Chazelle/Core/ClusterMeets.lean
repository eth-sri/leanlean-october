module

public import Chazelle.Core.ClusterMain

/-!
# WP-I, part 73: the specification of the cluster decomposition

`clusters : ClusterSpec`.
-/

namespace Chazelle.Core

open Machine Machine.Stmt Programs Chazelle.Separator Chazelle.Separator.CombMap
open Chazelle.Core.Cluster

@[expose] public section

set_option maxHeartbeats 16000000 in
open Classical in
/-- **The cluster decomposition meets its specification.** -/
theorem clusterProg_meets : Meets clusterProg {bCluster}
    (fun P W c => P.n + 3 ≤ W ∧ 1 ≤ rd c bCluster 3 ∧ rd c bCluster 1 ≤ rd c bCluster 3 ^ 3 ∧
      Robust (c.nreg ALLOC) c.nmem
        (fun m => PlanarMapAt m (rd c bCluster 0) (rd c bCluster 1) (rd c bCluster 2)))
    (fun _ c c' =>
      c.nreg ALLOC ≤ rd c' bCluster 4 ∧ c.nreg ALLOC ≤ rd c' bCluster 5 ∧
      rd c' bCluster 4 + rd c bCluster 1 ≤ c'.nreg ALLOC ∧
      rd c' bCluster 5 + rd c bCluster 1 ≤ c'.nreg ALLOC ∧
      (Finset.univ.filter (fun v : Fin (rd c bCluster 1) =>
        c'.nmem (rd c' bCluster 4 + v) = 1)).card ≤ 7 * rd c bCluster 3 ^ 2 ∧
      (∀ u v (w : (memGraph c.nmem (rd c bCluster 0) (rd c bCluster 1) (rd c bCluster 2)).Walk u v),
        (∀ x ∈ w.support, c'.nmem (rd c' bCluster 4 + x) ≠ 1) →
          c'.nmem (rd c' bCluster 5 + u) = c'.nmem (rd c' bCluster 5 + v)) ∧
      (∀ l, (Finset.univ.filter (fun v : Fin (rd c bCluster 1) =>
        c'.nmem (rd c' bCluster 4 + v) ≠ 1 ∧ c'.nmem (rd c' bCluster 5 + v) = l)).card ≤
          rd c bCluster 3 ^ 2))
    (fun _ c => clusterK * ((rd c bCluster 1 + rd c bCluster 2) *
      (Nat.clog 2 (rd c bCluster 1 + rd c bCluster 2) + 1) + 1)) := by
  intro P W c hw ⟨hPn, hk, hμk, hrob⟩ hbud
  beta_reduce at hbud
  have e0 : rd c bCluster 0 = c.nreg 130000 := rfl
  have e1 : rd c bCluster 1 = (gOf c).μ := rfl
  have e3 : rd c bCluster 3 = (gOf c).k := rfl
  have eA : c.nreg ALLOC = (gOf c).A0 := rfl
  obtain ⟨F, iF, dF, M, hpl, hmap, hμ, hE, hμN, hB2, hO, hR, hV⟩ := inputFacts hrob
  rw [e1, e3] at hμk; rw [e3] at hk
  have hcost := totalCost_le (gOf c) hμ hE hk hμk
  set g := gOf c
  have hcb : c.nreg ALLOC + totalCost g ≤ W := by
    have : clusterK * ((rd c bCluster 1 + rd c bCluster 2) *
      (Nat.clog 2 (rd c bCluster 1 + rd c bCluster 2) + 1) + 1) =
      clusterK * ((g.μ + g.E) * (Nat.clog 2 (g.μ + g.E) + 1) + 1) := rfl
    omega
  have hEND : g.END ≤ W := by
    have h1 : g.END - g.A0 ≤ totalCost g := by unfold totalCost; omega
    have h2 : g.A0 ≤ g.END := by have := g.END_eq; omega
    omega
  have hU := g.U_ge; have hEe := g.END_eq
  -- phase 1
  obtain ⟨c1, k1, x1, hk1, hw1, hG1, hr1, hrr1, hrm1, ho1, hm1, T, a, ha, C, R, first, preE, slot,
    ρ, hD1⟩ := phase1_exec (P := P) hw (g := g) rfl (M := M) hpl hmap hμ hμN
      (by rw [← e0]; omega) hO hR hV hk hEND
  -- phase 2a
  obtain ⟨c2, k2, x2, hk2, hw2, hG2, hr2, hrr2, hrm2, ho2, hm2, hcard2, H, D, fin, nsp,
    ⟨act, hI2⟩, hflag2⟩ := phase2a_exec (P := P) hw1 hG1 hD1 hk hμ hμk hEND
  have hO' : g.bO + g.N ≤ g.A0 := hO
  have hR' : g.bR + g.N ≤ g.A0 := hR
  have hV' : g.bV + g.N ≤ g.A0 := hV
  have b2 := g.base_eq 2; have b6 := g.base_eq 6; have b48 := g.base_eq 48
  have b43 := g.base_eq 43; have b49 := g.base_eq 49; have b0 := g.base_eq 0
  have b1 := g.base_eq 1
  have hm12 : ∀ x, x < g.A0 → c2.nmem x = c.nmem x := fun x hx => by
    rw [hm2 x (by omega), hm1 x hx]
  have hmap2 : MapArrays c2.nmem g.bO g.bR g.bV g.μ g.N M := fun d => by
    have := d.2
    rw [hm2 _ (by omega), hm2 _ (by omega), hm2 _ (by omega)]; exact hD1.map d
  have hF2 : ∀ u, u < g.μ → c2.nmem (g.base 0 + u) < g.N ∧
      c2.nmem (g.bV + c2.nmem (g.base 0 + u)) = u := fun u hu => by
    have h := hD1.firstF u hu
    rwa [hm2 (g.base 0 + u) (by omega), hm2 (g.bV + c1.nmem (g.base 0 + u)) (by omega)]
  have hz2 : ∀ d, d < g.N → c2.nmem (g.base 1 + d) = 0 := fun d hd => by
    rw [hm2 _ (by omega)]; exact hD1.zero d hd
  -- the labels
  obtain ⟨c3, k3, x3, hk3, hw3, hr3, hrr3, hrm3, ho3, hm3, hlab3⟩ := labS_exec (P := P) hw2 hG2
    (M := M) hmap2 hF2 hz2 hμN hO hR hV hEND
  have hG3 : GR g c3 := hG2.frame (fun r hr => hr3 r (by unfold GRReg at hr; unfold LabRG; omega))
  -- the outputs
  obtain ⟨c4, k4, x4, hk4, hw4, h04, h05, hr4, hm4, hrr4, hrm4, ho4⟩ : ∃ c4 k4, Exec P W outS c3 c4 k4 ∧
      k4 = 2 ∧ WordsBounded W c4 ∧ c4.nreg 130004 = g.base 48 ∧ c4.nreg 130005 = g.base 2 ∧
      (∀ r, r ≠ 130004 → r ≠ 130005 → c4.nreg r = c3.nreg r) ∧ c4.nmem = c3.nmem ∧
      c4.rreg = c3.rreg ∧ c4.rmem = c3.rmem ∧ c4.output = c3.output := by
    unfold outS
    exec_block
    refine ⟨rfl, ‹_›, by config_simp; exact hG3.rbase 48 (by omega),
      by config_simp; exact hG3.rbase 2 (by omega), fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
    simp only
    rw [Machine.upd_other _ _ _ h2, Machine.upd_other _ _ _ h1]
  have hAl : ALLOC = 9999 := rfl
  have hA4 : c4.nreg ALLOC = c.nreg ALLOC := by
    rw [hr4 _ (by rw [hAl]; omega) (by rw [hAl]; omega), hr3 _ (by unfold LabRG; rw [hAl]; omega),
      hr2 _ (by rw [hAl]; omega), hr1 _ (by rw [hAl]; omega)]
  -- the allocator
  obtain ⟨c5, k5, x5, hk5, hA5, hA5k, hr5, hm5, hrr5, hrm5, ho5⟩ := bumpS_exec (P := P) hw4
    (E := g.END) (by rw [hr4 _ (by omega) (by omega)]; exact hG3.one)
    (by rw [hr4 _ (by omega) (by omega)]; exact hG3.rEND)
    (by rw [hA4, eA]; omega) hEND
  have hA4' : c4.nreg ALLOC = g.A0 := by rw [hA4]; rfl
  have r4 : c5.nreg 130004 = g.base 48 := by rw [hr5 _ (by rw [hAl]; omega)]; exact h04
  have r5 : c5.nreg 130005 = g.base 2 := by rw [hr5 _ (by rw [hAl]; omega)]; exact h05
  have hrd4 : rd c5 bCluster 4 = g.base 48 := r4
  have hrd5 : rd c5 bCluster 5 = g.base 2 := r5
  have hDF : ∀ v, v < g.μ → c5.nmem (g.base 48 + v) = c2.nmem (g.base 48 + v) := fun v hv => by
    rw [hm5, hm4, hm3 _ (by omega)]
  have hLAB : ∀ v, c5.nmem (g.base 2 + v) = c3.nmem (g.base 2 + v) := fun v => by rw [hm5, hm4]
  have hstep : ∀ u w, (primalEnv c2.nmem g.bO g.bR g.bV (g.base 0) (g.base 1) (g.base 48) g.μ
      g.N).Step u w → AdjN M u w ∧ u ∉ H ∧ u ∉ D ∧ w ∉ H ∧ w ∉ D := by
    rintro u w ⟨d, hd, -, hv, hh, hu, hw'⟩
    replace hd : d < g.N := hd
    have ho : c2.nmem (g.bO + d) < g.N := by rw [(hmap2 ⟨d, hd⟩).1]; exact (M.opp ⟨d, hd⟩).2
    simp only [primalEnv] at hv
    rw [view_lt hd] at hv
    simp only [Env.head, primalEnv] at hh
    rw [view_lt hd, view_lt ho] at hh
    rw [(hmap2 ⟨d, hd⟩).2.2] at hv
    rw [(hmap2 ⟨d, hd⟩).1] at hh
    replace hh : (M.vert (M.opp ⟨d, hd⟩) : ℕ) = w := (hmap2 (M.opp ⟨d, hd⟩)).2.2.symm.trans hh
    have huμ : u < g.μ := by rw [← hv]; exact (M.vert _).2
    have hwμ : w < g.μ := by rw [← hh]; exact (M.vert _).2
    simp only [primalEnv] at hu hw'
    rw [view_lt huμ] at hu
    rw [view_lt hwμ] at hw'
    have hu' := (hflag2 u huμ).not.mp hu
    have hw'' := (hflag2 w hwμ).not.mp hw'
    push Not at hu' hw''
    exact ⟨⟨⟨d, hd⟩, hv, hh⟩, hu'.2, hu'.1, hw''.2, hw''.1⟩
  refine ⟨c5, k1 + (k2 + (k3 + (k4 + k5))),
    .seq x1 (.seq x2 (.seq x3 (.seq x4 x5))), ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · -- cost
    have : k5 ≤ 3 * (g.END - g.A0) + 2 := by rwa [hA4'] at hk5
    have hT : k1 + (k2 + (k3 + (k4 + k5))) ≤ totalCost g := by unfold totalCost; omega
    exact le_trans hT hcost
  · rw [hrd4, eA]; omega
  · rw [hrd5, eA]; omega
  · rw [hrd4, hA5, e1]; omega
  · rw [hrd5, hA5, e1]; omega
  · rw [e1, e3, hrd4, card_fin_filter (p := fun v => c5.nmem (g.base 48 + v) = 1)]
    rw [Finset.filter_congr (fun v hv => by rw [hDF v (Finset.mem_range.mp hv)])]
    exact hcard2
  · intro u v w hw'
    rw [hrd4] at hw'
    rw [hrd5, hLAB, hLAB]
    have hBl : rd c bCluster 0 + 2 < g.A0 := hB2
    have hgraph : memGraph c.nmem (rd c bCluster 0) (rd c bCluster 1) (rd c bCluster 2) =
        memGraph c2.nmem (rd c bCluster 0) (rd c bCluster 1) (rd c bCluster 2) :=
      (memGraph_congr (A := g.A0) hm12 hB2 hO hV (fun d hd => by
        rw [(hmap ⟨d, hd⟩).1]; exact (M.opp ⟨d, hd⟩).2)).symm
    have hreach := reach_of_walk (m := c2.nmem) (bF := g.base 0) (bDB := g.base 1)
      (bVB := g.base 48) hmap2 (fun d hd => by rw [hz2 d hd]; omega)
      (B := rd c bCluster 0) (E := rd c bCluster 2) (by rw [hm12 _ (by omega)]; rfl)
      (by rw [hm12 _ (by omega)]; rfl) rfl (w.mapLe (le_of_eq hgraph)) (fun x hx => by
        have hx' : x ∈ w.support := by
          have e := SimpleGraph.Walk.support_mapLe_eq_support (h := le_of_eq hgraph) (p := w)
          exact cast (congrArg (x ∈ ·) e) hx
        rw [← hDF x x.2]; exact hw' x hx')
    exact (hlab3 u v u.2 v.2 (by rw [← hDF u u.2]; exact hw' u w.start_mem_support)
      (by rw [← hDF v v.2]; exact hw' v w.end_mem_support)).mpr hreach
  · intro l
    rw [e1, e3, hrd4, hrd5,
      card_fin_filter (p := fun v => c5.nmem (g.base 48 + v) ≠ 1 ∧ c5.nmem (g.base 2 + v) = l)]
    have heq : (Finset.range g.μ).filter (fun v => c5.nmem (g.base 48 + v) ≠ 1 ∧
        c5.nmem (g.base 2 + v) = l) = ((Finset.range g.μ).filter
        (fun v => c2.nmem (g.base 48 + v) ≠ 1)).filter (fun v => c3.nmem (g.base 2 + v) = l) := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨hv, h1, h2⟩; exact ⟨⟨hv, by rwa [← hDF v hv]⟩, by rwa [← hLAB]⟩
      · rintro ⟨⟨hv, h1⟩, h2⟩; exact ⟨hv, by rwa [hDF v hv], by rwa [hLAB]⟩
    rw [heq]
    have hc := class_card hI2 hstep (lab := fun v => c3.nmem (g.base 2 + v))
      (X := (Finset.range g.μ).filter (fun v => c2.nmem (g.base 48 + v) ≠ 1))
      (fun v hv => by
        simp only [Finset.mem_filter, Finset.mem_range] at hv
        have := (hflag2 v hv.1).not.mp hv.2; push Not at this
        exact ⟨hv.1, this.2, this.1⟩)
      (fun x hx y hy h => by
        simp only [Finset.mem_filter, Finset.mem_range] at hx hy
        exact (hlab3 x y hx.1 hy.1 hx.2 hy.2).mp h) l
    exact le_trans hc (s_le_sq rfl rfl)
  · -- the frame
    refine ⟨fun r hr hra => ?_, fun r _ => by rw [hrr5, hrr4, hrr3, hrr2, hrr1],
      fun x hx => ?_, fun x _ => by rw [hrm5, hrm4, hrm3, hrm2, hrm1],
      by rw [ho5, ho4, ho3, ho2, ho1], by rw [hA5, eA]; omega, by rw [hA5]; omega⟩
    · have : r < 130000 ∨ 140000 ≤ r := by
        simp only [Finset.mem_singleton, bandOf, bCluster] at hr; omega
      rw [hr5 r hra, hr4 r (by omega) (by omega), hr3 r (by unfold LabRG; omega),
        hr2 r (by omega), hr1 r (by omega)]
    · rw [hm5, hm4, hm3 _ (by rw [eA] at hx; omega)]; exact hm12 x hx

end

end Chazelle.Core
