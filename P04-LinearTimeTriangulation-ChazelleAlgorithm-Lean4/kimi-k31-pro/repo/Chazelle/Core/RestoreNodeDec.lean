module

public import Chazelle.Core.RestoreFNode
public import Chazelle.Core.RestoreNodeGend
public import Chazelle.Core.RestoreNodeArr
public import Chazelle.Core.RestoreNodeChild
public import Chazelle.Core.RestoreDescGeo
public import Chazelle.Core.GranNF
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.SimpTactics

/-!
# WP-E, the search: the decision at a node of the descent

`DescGood`: the facts of a stretch of a kind-1 piece that the descent's completeness reads (the
region and its arcs `A_i ∋` stretch, `A_j`, the good vertex `X` at offset `dX` with its good
chord, the target region `T` of the piece's normal form faced just after `X`).
`end_info`: what a node end test that did not succeed tells (in offsets).
`node_dec`: after a node run that did not succeed, the chosen child is above `T`.
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Set Filter Topology
open Chazelle.Chain (sidePt SideAttach sideLeft sideInArc)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Geometry (lerp)
open WalkEmbed (off off_nonneg off_lt off_key off_key')

/-- A vertex of the side walk of a chain inside the open box is a point of the chain. -/
theorem walk_vtx_box (C : Chain) (β : Bool) {e : ℕ} (he : e < (C.sideWalk β).n)
    (hb : |((C.sideWalk β).vtx e).2| < C.radius) : (C.sideWalk β).vtx e ∈ C.set := by
  rw [Chain.sideWalk_n] at he
  have hr := C.radius_pos
  by_cases h6 : 6 ≤ e
  · obtain ⟨i, rfl⟩ : ∃ i, e = i + 6 := ⟨e - 6, by omega⟩
    rw [C.sideWalk_vtx_tour β (by omega)]
    exact C.vertex_mem_set (C.sideIdx_le β i)
  · exfalso
    replace hb : True ∧ |((C.sideWalk β).vtx e).2| < C.radius := ⟨trivial, hb⟩
    interval_cases e
    · rw [C.sideWalk_vtx_zero] at hb
      have := hb.2; simp only [Chain.slitTop] at this; rwli [abs_of_pos hr] at this
    · rw [C.sideWalk_vtx_one] at hb
      have := hb.2; rwli [abs_of_pos hr] at this
    · rw [C.sideWalk_vtx_two] at hb
      have := hb.2; rwli [abs_neg, abs_of_pos hr] at this
    · rw [C.sideWalk_vtx_three] at hb
      have := hb.2; rwli [abs_neg, abs_of_pos hr] at this
    · rw [C.sideWalk_vtx_four] at hb
      have := hb.2; rwli [abs_of_pos hr] at this
    · rw [C.sideWalk_vtx_five] at hb
      have := hb.2; simp only [Chain.slitTop] at this; rwli [abs_of_pos hr] at this

variable {E : FEnv} {c₀ : Config} {Cα : Chain} {g g' L : ℕ}

/-- **A far point inside the box is in the vertex range** (or not a vertex). -/
theorem far_range (hE : FGood E c₀) {far : WPos} (hfe : far.edge < E.M.W.n)
    (hb : ∀ C : Chain, E.M = chainModel C → |(E.M.pos (Qof E.P) far).2| < C.radius) :
    0 < far.hgt ∨ c₀.nreg 81021 ≤ far.edge := by
  rcases Nat.eq_zero_or_pos far.hgt with h0 | h0
  · right
    refine (hE.hvc _ hfe (fun C hC => ?_)).1
    have e : far = ⟨far.edge, 0⟩ := by rw [← h0]
    have hb' := hb C hC
    rw [e] at hb'
    have hv : ∀ M' : Model, M'.pos (Qof E.P) ⟨far.edge, 0⟩ = M'.W.vtx far.edge := fun M' => by
      rw [pos_eq_sidePt]; show sidePt M'.W far.edge 0 = _
      unfold sidePt; rw [Chazelle.Geometry.lerp_zero]
    rw [hv] at hb' ⊢
    revert hb' hfe
    rw [hC]
    intro hfe hb'
    exact walk_vtx_box C _ hfe hb'
  · left; exact h0

/-- The host parameter and point of a node chord end's candidate. -/
theorem end_param (hS : Stretch E.M Cα g g' L) {d h : ℕ} (hd : d < L)
    (hpe : PosOK Cα (Qof E.P) E.P.n ⟨g' + d, h + 1⟩) :
    E.M.param (Qof E.P) ⟨(g + d) % E.M.W.n, endCode Cα (Qof E.P) (g' + d) (h + 1)⟩ =
      (chainModel Cα).param (Qof E.P) ⟨g' + d, h + 1⟩ ∧
    E.M.pos (Qof E.P) ⟨(g + d) % E.M.W.n, endCode Cα (Qof E.P) (g' + d) (h + 1)⟩ =
      (chainModel Cα).pos (Qof E.P) ⟨g' + d, h + 1⟩ := by
  set t := (chainModel Cα).param (Qof E.P) ⟨g' + d, h + 1⟩ with ht
  obtain ⟨-, ⟨ht0, -, -⟩, -⟩ := hpe
  rw [endM_param hS hd, endM_pos hS hd]
  unfold endCode
  split_ifs with hk
  · exact ⟨rfl, rfl⟩
  · have h0 : t = 0 := by
      rw [key_pz] at hk; push Not at hk; exact le_antisymm hk ht0
    have e : (chainModel Cα).param (Qof E.P) ⟨g' + d, 0⟩ =
        (chainModel Cα).param (Qof E.P) ⟨g' + d, h + 1⟩ := by
      rwr [← ht, h0]
    exact ⟨by rw [e], pos_of_param e⟩

/-- The code of an end is `0` iff its parameter is `0`. -/
theorem endCode_zero {p h : ℕ} :
    endCode Cα (Qof E.P) p (h + 1) = 0 ↔ ¬ 0 < (chainModel Cα).param (Qof E.P) ⟨p, h + 1⟩ := by
  unfold endCode
  split_ifs with hk
  · rw [key_pz] at hk; simp [hk]
  · rw [key_pz] at hk; simp [hk]

theorem nat_add_frac {a b : ℕ} {t t' : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (ht0' : 0 ≤ t')
    (ht1' : t' < 1) (h : (a : ℝ) + t = b + t') : a = b ∧ t = t' := by
  have h1 : (a : ℝ) < b + 1 := by linarith
  have h2 : (b : ℝ) < a + 1 := by linarith
  have h1' : a < b + 1 := by exact_mod_cast h1
  have h2' : b < a + 1 := by exact_mod_cast h2
  obtain rfl : a = b := by omega
  exact ⟨rfl, by linarith⟩

/-- **The facts of a stretch of a kind-1 piece** that the completeness of the descent reads:
the region `reg E.r` with the arc `A_i = (ai, bi)` containing the open stretch and the target arc
`A_j = (aj, bj)`, the good vertex `X` at the offset `dX` with its good chord, and the region `T`
of the piece's normal form faced just after `X`. -/
structure DescGood (E : FEnv) (c₀ : Config) (Cα : Chain) (Nα : NF) (g g' L : ℕ)
    (reg : ℕ → Set Point) (ai bi aj bj : ℝ) (dX : ℕ) (regα : ℕ → Set Point) (T : ℕ) : Prop where
  hregs : NFRegs E.M (Qof E.P) E.N reg
  hch : (E.N.region E.r).chords ≠ []
  hAi : E.M.IsArc (E.N.F E.M (Qof E.P)) (reg E.r) ai bi
  hAj : E.M.IsArc (E.N.F E.M (Qof E.P)) (reg E.r) aj bj
  hij : ai ≠ aj
  hAin : ∀ d, d < L → ∀ t : ℝ, 0 ≤ t → t < 1 → 0 < (d : ℝ) + t →
    sideInArc ai bi ((((g + d) % E.M.W.n : ℕ) : ℝ) + t)
  hcnt : ∀ d, d < L → InRange c₀ ((g + d) % E.M.W.n)
  hsetD : ∀ x ∈ Cα.set, x ∉ E.M.D
  hinB : ∀ C : Chain, E.M = chainModel C → Cα.set ⊆ C.set
  hX0 : 0 < dX
  hXL : dX < L
  hgX : ∃ σb, σb ≤ 1 ∧ GoodAt E reg ((g + dX) % E.M.W.n) σb
  hXc : ∃ (ex : Set Point) (px' : ℕ) (tx' : ℝ), ex ∈ E.M.Adm ∧
    SideAttach E.M.W ex ((g + dX) % E.M.W.n) 0 ∧ SideAttach E.M.W ex px' tx' ∧
    sidePt E.M.W ((g + dX) % E.M.W.n) 0 ≠ sidePt E.M.W px' tx' ∧
    ClosedArc ai bi ((((g + dX) % E.M.W.n : ℕ) : ℝ) + 0) ∧ ClosedArc aj bj (px' + tx') ∧
    CountOK E.M (E.N.F E.M (Qof E.P)) (reg E.r) ((((g + dX) % E.M.W.n : ℕ) : ℝ) + 0)
      (px' + tx')
  hregsα : NFRegs (chainModel Cα) (Qof E.P) Nα regα
  hRT : ∃ D, Dec.RecTree Nα D
  hT : T < Nα.nRegions
  hfT : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (chainModel Cα).Faces (g' + dX) ε (regα T)

/-- **What a node end test that did not succeed tells**, in offsets of the stretch (`dE`: the
offset of the end in `Cα`'s walk). -/
theorem end_info (hE : FGood E c₀) (hS : Stretch E.M Cα g g' L) (hGα : GoodModel (chainModel Cα))
    {Nα : NF} {reg : ℕ → Set Point} {ai bi aj bj : ℝ} {dX : ℕ} {regα : ℕ → Set Point} {T : ℕ}
    (hD : DescGood E c₀ Cα Nα g g' L reg ai bi aj bj dX regα T)
    {cs c' : Config} {s p σ : ℕ} (hR : EndRes E c₀ Cα s p σ cs c')
    (h30 : cs.nreg 81130 = g) (h31 : cs.nreg 81131 = g') (h35 : cs.nreg 81135 = g' + L)
    {pE h : ℕ} (hp : cs.nreg p = pE) (h55 : cs.nreg 81155 = h + 1)
    (hpe : PosOK Cα (Qof E.P) E.P.n ⟨pE, h + 1⟩)
    {tE : ℝ} (htE : tE = (chainModel Cα).param (Qof E.P) ⟨pE, h + 1⟩)
    {c : Set Point} (hcA : c ∈ (chainModel Cα).Adm)
    (hAE : SideAttach (chainModel Cα).W c pE tE)
    {pO : ℕ} {tO : ℝ} (hAO : SideAttach (chainModel Cα).W c pO tO)
    {L₀ : ℝ} (hL₀ : 0 < L₀)
    (hceq : c = Chazelle.segment (sidePt (chainModel Cα).W pE tE)
      (rayPt (sidePt (chainModel Cα).W pE tE) (dirOf σ) L₀))
    (hoO : rayPt (sidePt (chainModel Cα).W pE tE) (dirOf σ) L₀ = sidePt (chainModel Cα).W pO tO)
    (hkopen : ∀ s ∈ Ioo (0 : ℝ) 1, lerp (sidePt (chainModel Cα).W pE tE)
      (rayPt (sidePt (chainModel Cα).W pE tE) (dirOf σ) L₀) s ∈ Cα.dom)
    (hJ : aj = E.M.key (Qof E.P) ⟨cs.nreg 81140, cs.nreg 81141⟩)
    (hJr : 0 < cs.nreg 81141 ∨ c₀.nreg 81021 ≤ cs.nreg 81140)
    (hf0 : cs.nreg 81007 = 0) (hf1 : c'.nreg 81007 ≠ 1) :
    (c'.nreg s = 1 ↔ (0 < off (chainModel Cα).W.n g' (pE + tE) ∧
      off (chainModel Cα).W.n g' (pE + tE) < L)) ∧
    off (chainModel Cα).W.n g' (pE + tE) ≠ dX ∧
    (0 < off (chainModel Cα).W.n g' (pE + tE) → off (chainModel Cα).W.n g' (pE + tE) < L →
      g' ≤ pE ∧ c'.nreg (s + 5) = 1 ∧ c'.nreg (s + 1) = (g + (pE - g')) % E.M.W.n ∧
      SweepPrim.BitIs c' (s + 7) (0 < tE) ∧
      ∃ α : ℝ, 0 ≤ α ∧ (0 < α → α < L → α = off (chainModel Cα).W.n g' (pO + tO)) ∧
        (off (chainModel Cα).W.n g' (pO + tO) ≠ dX →
          GEnd L (off (chainModel Cα).W.n g' (pE + tE)) α (c'.nreg (s + 6) = 1) dX ∧
          ∀ u, u < L → (sideInArc (E.M.key (Qof E.P) ⟨c'.nreg (s + 1), c'.nreg (s + 2)⟩)
            (E.M.key (Qof E.P) ⟨c'.nreg (s + 3), c'.nreg (s + 4)⟩)
            (((g + u) % E.M.W.n : ℕ) : ℝ) ↔
            sideInArc (off (chainModel Cα).W.n g' (pE + tE)) α u))) := by
  have hn : 0 < E.M.W.n := by have := hS.hg; omega
  have hM := walkAx_of_goodModel hE.hGM
  have hMα := walkAx_of_goodModel hGα
  have hσ' := dirOf_pm σ
  have hpe' := hpe
  obtain ⟨hpn, ⟨ht0, ht1, -⟩, -⟩ := hpe'
  replace hpn : pE < (chainModel Cα).W.n := hpn
  rw [← htE] at ht0 ht1
  obtain ⟨Rb, Rp, R3, R4, R5, R6, -⟩ := hR
  rw [h31, hp, h35, h55, key_pz, ← htE] at Rb
  have hin : c'.nreg s = 1 ↔ (0 < off (chainModel Cα).W.n g' (pE + tE) ∧
      off (chainModel Cα).W.n g' (pE + tE) < L) := by
    rw [Rb.2]; exact inE_iff hS hpn ht0 ht1
  -- the end in the stretch
  have hst : 0 < off (chainModel Cα).W.n g' (pE + tE) → off (chainModel Cα).W.n g' (pE + tE) < L →
      ∃ d, pE = g' + d ∧ d < L ∧ (tE = 0 → 1 ≤ d) ∧ off (chainModel Cα).W.n g' (pE + tE) = d + tE ∧
        c'.nreg s = 1 ∧ eMof E cs p = (g + d) % E.M.W.n := by
    intro a b
    obtain ⟨i1, i2, i3⟩ := (inE_iff hS hpn ht0 ht1).2 ⟨a, b⟩
    refine ⟨pE - g', by omega, by omega, fun h0 => by rw [h0] at i3; sio at i3, ?_,
      hin.2 ⟨a, b⟩, by unfold eMof; rw [h30, h31, hp]⟩
    have e := endα_off hS (d := pE - g') (by omega) ht0 ht1
    rw [show g' + (pE - g') = pE by omega] at e
    exact e
  -- the end is not the good vertex
  have hcode : ∀ d, pE = g' + d → tE = 0 → endCode Cα (Qof E.P) (cs.nreg p) (cs.nreg 81155) = 0 :=
    fun d hd h0 => by
      rw [hp, h55]; exact endCode_zero.2 (by rw [← htE, h0]; exact lt_irrefl 0)
  have hne : off (chainModel Cα).W.n g' (pE + tE) ≠ dX := by
    intro hx
    have hX0 : (0 : ℝ) < dX := by exact_mod_cast hD.hX0
    have hXL : (dX : ℝ) < L := by exact_mod_cast hD.hXL
    obtain ⟨d, rfl, hd, -, ho, hs1, heM⟩ := hst (by rwx [hx]) (by rwx [hx])
    rw [ho] at hx
    obtain ⟨rfl, h0⟩ := nat_add_frac (a := d) (b := dX) ht0 ht1 le_rfl one_pos (by rw [hx, add_zero])
    obtain ⟨σb, hσb, hg⟩ := hD.hgX
    exact hf1 (R3 hs1 (by rw [heM]; exact hD.hcnt d hd) reg hD.hregs hD.hch (hcode d rfl h0) σb hσb
      (by rwx [heM]))
  refine ⟨hin, hne, fun a b => ?_⟩
  obtain ⟨d, rfl, hd, htd, ho, hs1, heM⟩ := hst a b
  have hdn : d < E.M.W.n := by have := hS.hLn; omega
  have hdt : (0 : ℝ) < d + tE := by
    rcases ht0.eq_or_lt with h0 | h0
    · have h1 : (1 : ℝ) ≤ d := by exact_mod_cast htd h0.symm
      linarith
    · have : (0 : ℝ) ≤ d := Nat.cast_nonneg _
      linarith
  obtain ⟨ct, ct', hTO, i60, i61, i63, e3, e4, ev, efl⟩ := R4 hs1 (by rw [heM]; exact hD.hcnt d hd) hf0
  rw [heM] at i60
  rw [hp, h55] at i61
  have hpar := end_param hS hd (h := h) hpe
  rw [← htE] at hpar
  have hx : (⟨ct.nreg 81060, ct.nreg 81061⟩ : WPos) =
      ⟨(g + d) % E.M.W.n, endCode Cα (Qof E.P) (g' + d) (h + 1)⟩ := by rw [i60, i61]
  obtain ⟨-, -, hcl⟩ := hTO
  obtain ⟨-, hex, hcomp⟩ := hcl reg hD.hregs
  rw [hx, i63] at hex hcomp
  have hz : E.M.pos (Qof E.P) ⟨(g + d) % E.M.W.n, endCode Cα (Qof E.P) (g' + d) (h + 1)⟩ =
      sidePt E.M.W ((g + d) % E.M.W.n) tE := by
    show sidePt E.M.W ((g + d) % E.M.W.n) (E.M.param (Qof E.P) _) = _
    rw [hpar.1]
  have hkx : E.M.key (Qof E.P) ⟨(g + d) % E.M.W.n, endCode Cα (Qof E.P) (g' + d) (h + 1)⟩ =
      (((g + d) % E.M.W.n : ℕ) : ℝ) + tE := by
    show _ + _ = _
    rw [hpar.1]
  rw [hz, hpar.1] at hex hcomp
  have hza : sidePt E.M.W ((g + d) % E.M.W.n) tE = sidePt (chainModel Cα).W (g' + d) tE := by
    rw [hS.hA.sidePt_eq hd tE, hS.mod' hd.le]
  rw [← hza] at hceq hoO hkopen
  have haC : sidePt E.M.W ((g + d) % E.M.W.n) tE ∈ Cα.set := hS.memM hd ht0 ht1
  have hAM : SideAttach E.M.W c ((g + d) % E.M.W.n) tE :=
    (hS.hA.sideAttach_iff hn (by rwo [Stretch.nα]) hd htd c).2
      (by rwx [hS.mod' hd.le])
  have hsec := attach_ray_left hAM hσ' hL₀ hceq
  obtain ⟨T', hT', hdom', hout', hadm', hnS', hsub'⟩ := inner_exit hE.hGM hE.hNF.1
    (hD.hregs.1.1 _ hE.hr) hD.hAi (Nat.mod_lt _ hn) ht0 ht1 (hD.hAin d hd tE ht0 ht1 hdt) hσ' hsec
    (fun C hC => C.snd_le_top_of_mem_set (hD.hinB C hC haC))
  obtain ⟨h10, h11⟩ := hcomp hsec hD.hch T' hT' hdom' hout' hadm' hnS' hsub'
  obtain ⟨T'', hT'', hstr, hposf, hfe, hfp, hadm'', hA1, hA2, hiff⟩ := hex h10 h11
  have hdomM : ∀ t, 0 < t → t < T'' →
      rayPt (sidePt E.M.W ((g + d) % E.M.W.n) tE) (dirOf σ) t ∈ E.M.D :=
    fun t h0 h1 => (Chazelle.Chain.regionsIn_subset (hD.hregs.1.1 _ hE.hr) (hstr t h0 h1)).1
  -- valid
  have hrange := far_range hE (far := ⟨ct'.nreg 83012, ct'.nreg 83013⟩) hfe (fun C hC => by
    rw [hposf, rayPt_snd]; exact (C.set_subset_box (hD.hinB C hC haC)).2)
  have hv : c'.nreg (s + 5) = 1 := ev.2 ⟨h10, h11, hrange⟩
  have hbad : ¬ CountOK E.M (E.N.F E.M (Qof E.P)) (reg E.r)
      ((((g + d) % E.M.W.n : ℕ) : ℝ) + tE)
      ((ct'.nreg 83012 : ℝ) + E.M.param (Qof E.P) ⟨ct'.nreg 83012, ct'.nreg 83013⟩) :=
    fun hc => hf1 (efl (hiff.2 (by rwx [hkx])))
  obtain ⟨α0, αarr⟩ := arrival_off hS (walkAx_of_goodModel hGα) hcA hAO haC hσ' hL₀ hceq hoO hkopen
    hD.hsetD hT'' hdomM hposf hA2
  obtain ⟨Rp1, Rp2, Rp7⟩ := Rp hs1
  rw [heM] at Rp1
  rw [hp, h55] at Rp2
  rw [hp, h55, key_pz, ← htE] at Rp7
  refine ⟨by omega, hv, by rw [Rp1, show g' + d - g' = d by omega], Rp7, off E.M.W.n g ((ct'.nreg 83012 : ℝ) +
    E.M.param (Qof E.P) ⟨ct'.nreg 83012, ct'.nreg 83013⟩), α0, αarr,
    fun hOX => ?_⟩
  obtain ⟨ex, px', tx', hex', hX, hX', hXX', hkxa, hkx', hgood⟩ := hD.hXc
  have hXn : dX < E.M.W.n := by have := hD.hXL; have := hS.hLn; omega
  have hxa : ((((g + dX) % E.M.W.n : ℕ) : ℝ) + 0) ≠ (((g + d) % E.M.W.n : ℕ) : ℝ) + tE := by
    intro he
    obtain ⟨e1, e2⟩ := nat_add_frac le_rfl one_pos ht0 ht1 he
    have := WalkEmbed.add_mod_inj hXn hdn e1
    subst this
    exact hne (by rw [ho, ← e2, add_zero])
  have hxa' : ((((g + dX) % E.M.W.n : ℕ) : ℝ) + 0) ≠
      (ct'.nreg 83012 : ℝ) + E.M.param (Qof E.P) ⟨ct'.nreg 83012, ct'.nreg 83013⟩ := by
    intro he
    obtain ⟨e1, e2⟩ := nat_add_frac le_rfl one_pos hfp.1 hfp.2.1 he
    have hα : off E.M.W.n g ((ct'.nreg 83012 : ℝ) +
        E.M.param (Qof E.P) ⟨ct'.nreg 83012, ct'.nreg 83013⟩) = dX := by
      rw [← he, off_key hS.hg hXn le_rfl one_pos, add_zero]
    have hX0 : (0 : ℝ) < dX := by exact_mod_cast hD.hX0
    have hXL : (dX : ℝ) < L := by exact_mod_cast hD.hXL
    exact hOX ((αarr (by rwx [hα]) (by rwx [hα])).symm.trans hα)
  obtain ⟨-, -, hside, hrot⟩ := end_gend hS (walkAx_of_goodModel hGα) hM hE.hNF.1.2.1 hE.hNF.1.1
    (family_ne hE.hNF hE.hr hD.hch) hD.hAi hD.hAj hD.hij hcA hAO hd ht0 ht1 hdt hσ' hL₀ hceq hoO
    hkopen hD.hsetD hT'' hdomM hposf hadm'' hA1 hA2 (hD.hAin d hd tE ht0 ht1 hdt) hbad hex'
    hD.hXL hX hX' hXX' hkxa hkx' hgood hxa hxa'
  rw [e3, e4, heM, hp, h55, ← hJ, hkx] at R6
  refine ⟨fun _ => by rw [ho]; exact hside.trans (R6 hv hJr).symm, fun u hu => ?_⟩
  rw [Rp1, Rp2, hkx, e3, e4, ho]
  exact hrot u hu

theorem dirOf1 : dirOf 1 = 1 := by simp [dirOf]
theorem dirOf0 : dirOf 0 = -1 := by simp [dirOf]

/-- **The decision at a node**: after a node run at chord `k` that set no success, the chosen
child is above the target region `T` (which is below the node). -/
theorem node_dec (hE : FGood E c₀) {Hα : Host} {Nα : NF} {Dα Bα : ℕ}
    (hP : PCtx E c₀ Cα Hα Nα g g' L Dα Bα) {c c' : Config} (hR : SRegs c g g' L Dα Bα)
    {reg : ℕ → Set Point} {ai bi aj bj : ℝ} {dX : ℕ} {regα : ℕ → Set Point} {T : ℕ}
    (hD : DescGood E c₀ Cα Nα g g' L reg ai bi aj bj dX regα T)
    (hJ : aj = E.M.key (Qof E.P) ⟨c.nreg 81140, c.nreg 81141⟩)
    (hJr : 0 < c.nreg 81141 ∨ c₀.nreg 81021 ≤ c.nreg 81140) (hw : FWin E c)
    {k : ℕ} (hk : k < Nα.nChords) (hb : Nα.Below (2 * k) T)
    (hraw : NodeRaw E c₀ Cα Nα k c c') (hf : c'.nreg 81007 = 0) :
    Nα.Below (c'.nreg 81150) T := by
  obtain ⟨c₁, c₂, c₃, c₄, ⟨u52, u53, u54, u55, F1⟩, fl₁, R₂, f₂, m₂, hw₂, R₃, f₃, m₃, x81, xC, xAll,
    fl₄, hch, fl'⟩ := hraw
  obtain ⟨r30, r31, r32, r33, r34, r35⟩ := hR
  have hS := hP.hS
  have hn : 0 < E.M.W.n := by have := hS.hg; omega
  have hnα := Stretch.nα Cα
  have hgL := hS.hgL
  have hsimp : Cα.P.Simple := by rw [hP.hQ]; exact (shearInvariance (epsOf E.P) E.P).1 hE.hG.1
  have hGα : GoodModel (chainModel Cα) := Or.inl ⟨Cα, hsimp, rfl⟩
  have hMα := walkAx_of_goodModel hGα
  obtain ⟨hpA, hpB⟩ := chord_posOK hsimp hP.hNα hk
  have hat := hP.hNα.2.2.1 k hk
  -- flags
  have f4 : c₄.nreg 81007 = 0 := by rwx [← fl']
  have f3 : c₃.nreg 81007 = 0 := by rwx [← fl₄]
  have f2 : c₂.nreg 81007 = 0 := by
    have := hw₂.1
    by_contra h
    have := m₃ (by omega); omega
  have f1 : c₁.nreg 81007 = 0 := by
    have := hw.1
    by_contra h
    have := m₂ (by rwo [fl₁] at h ⊢); omega
  -- registers
  have g2 : ∀ q, 81100 ≤ q → q ≤ 81159 → c₂.nreg q = c₁.nreg q :=
    fun q a b => f₂ q (by omega) (by omega) (by ufo EndW KeyW VertW)
  have g3 : ∀ q, 81100 ≤ q → q ≤ 81169 → c₃.nreg q = c₂.nreg q :=
    fun q a b => f₃ q (by omega) (by omega) (by ufo EndW KeyW VertW)
  have a30 : c₁.nreg 81130 = g := by rw [F1 _ (by norm_num) (by norm_num), r30]
  have a31 : c₁.nreg 81131 = g' := by rw [F1 _ (by norm_num) (by norm_num), r31]
  have a32 : c₁.nreg 81132 = L := by rw [F1 _ (by norm_num) (by norm_num), r32]
  have a35 : c₁.nreg 81135 = g' + L := by rw [F1 _ (by norm_num) (by norm_num), r35]
  have a40 : c₁.nreg 81140 = c.nreg 81140 := F1 _ (by norm_num) (by norm_num)
  have a41 : c₁.nreg 81141 = c.nreg 81141 := F1 _ (by norm_num) (by norm_num)
  have b30 : c₂.nreg 81130 = g := by rw [g2 _ (by norm_num) (by norm_num), a30]
  have b31 : c₂.nreg 81131 = g' := by rw [g2 _ (by norm_num) (by norm_num), a31]
  have b32 : c₂.nreg 81132 = L := by rw [g2 _ (by norm_num) (by norm_num), a32]
  have b35 : c₂.nreg 81135 = g' + L := by rw [g2 _ (by norm_num) (by norm_num), a35]
  have b40 : c₂.nreg 81140 = c.nreg 81140 := by rw [g2 _ (by norm_num) (by norm_num), a40]
  have b41 : c₂.nreg 81141 = c.nreg 81141 := by rw [g2 _ (by norm_num) (by norm_num), a41]
  have b53 : c₂.nreg 81153 = (Nα.chord k).lp := by rw [g2 _ (by norm_num) (by norm_num), u53]
  have b54 : c₂.nreg 81154 = (Nα.chord k).rp := by rw [g2 _ (by norm_num) (by norm_num), u54]
  have b55 : c₂.nreg 81155 = (Nα.chord k).h + 1 := by rw [g2 _ (by norm_num) (by norm_num), u55]
  have d30 : c₃.nreg 81130 = g := by rw [g3 _ (by norm_num) (by norm_num), b30]
  have d31 : c₃.nreg 81131 = g' := by rw [g3 _ (by norm_num) (by norm_num), b31]
  have d32 : c₃.nreg 81132 = L := by rw [g3 _ (by norm_num) (by norm_num), b32]
  have d53 : c₃.nreg 81153 = (Nα.chord k).lp := by rw [g3 _ (by norm_num) (by norm_num), b53]
  have d54 : c₃.nreg 81154 = (Nα.chord k).rp := by rw [g3 _ (by norm_num) (by norm_num), b54]
  -- the chord
  have hcF : (Nα.chord k).toSet (chainModel Cα) (Qof E.P) ∈ Nα.F (chainModel Cα) (Qof E.P) :=
    ⟨_, Dec.chord_mem hk, rfl⟩
  have hcA := hP.hNα.1.2.1 hcF
  have hne := Gran.lpt_ne_rpt hP.hNα hMα hk
  obtain ⟨hseg, hy, hopen, -, -⟩ := hMα.attach_seg hcA hat.1 hat.2 hne
  set A := sidePt (chainModel Cα).W (Nα.chord k).lp
    ((chainModel Cα).param (Qof E.P) (Nα.chord k).lpos) with hAdef
  set B := sidePt (chainModel Cα).W (Nα.chord k).rp
    ((chainModel Cα).param (Qof E.P) (Nα.chord k).rpos) with hBdef
  have hAB1 : A.1 < B.1 := by
    have hm : B ∈ (Nα.chord k).toSet (chainModel Cα) (Qof E.P) := hat.2.2.2.2.1
    have h1 : A.1 ≤ B.1 := hm.2.1
    rcases h1.lt_or_eq with h | h
    · exact h
    · exact absurd (Prod.ext h hy) hne
  have hL₀ : 0 < B.1 - A.1 := by linarith
  have hrA : rayPt A (dirOf 1) (B.1 - A.1) = B := by
    have := eq_rayPt (w := A) (x := B) (σ := 1) (Or.inl rfl) hy.symm
    rw [one_mul] at this; rw [dirOf1]; exact this.symm
  have hrB : rayPt B (dirOf 0) (B.1 - A.1) = A := by
    have := eq_rayPt (w := B) (x := A) (σ := -1) (Or.inr rfl) hy
    rw [show -1 * (A.1 - B.1) = B.1 - A.1 by ring] at this; rw [dirOf0]; exact this.symm
  have hJ1 : aj = E.M.key (Qof E.P) ⟨c₁.nreg 81140, c₁.nreg 81141⟩ := by rwx [a40, a41]
  have hJ2 : aj = E.M.key (Qof E.P) ⟨c₂.nreg 81140, c₂.nreg 81141⟩ := by rwx [b40, b41]
  have EA := end_info hE hS hGα hD (s := 81160) (p := 81153) (σ := 1) R₂ a30 a31 a35 u53 u55 hpA
    rfl hcA hat.1 hat.2 hL₀
    (by show _ = Chazelle.segment A (rayPt A (dirOf 1) (B.1 - A.1)); rwx [hrA]) hrA
    (by show ∀ s ∈ Ioo (0 : ℝ) 1, lerp A (rayPt A (dirOf 1) (B.1 - A.1)) s ∈ Cα.dom
        rwx [hrA]) hJ1
    (by rwx [a40, a41]) f1 (by rwn [f2])
  have EB := end_info hE hS hGα hD (s := 81170) (p := 81154) (σ := 0) R₃ b30 b31 b35 b54 b55 hpB
    rfl hcA hat.2 hat.1 hL₀
    (by show _ = Chazelle.segment B (rayPt B (dirOf 0) (B.1 - A.1))
        rwx [hrB, Chazelle.Geometry.segment_comm]) hrB
    (by show ∀ s ∈ Ioo (0 : ℝ) 1, lerp B (rayPt B (dirOf 0) (B.1 - A.1)) s ∈ Cα.dom
        rw [hrB]; exact WalkAx.open_rev hopen) hJ2 (by rwx [b40, b41]) f2
    (by rwn [f3])
  simp only [Nat.reduceAdd] at EA EB
  have tA0 : 0 ≤ (chainModel Cα).param (Qof E.P) (Nα.chord k).lpos := hpA.2.1.1
  have tA1 : (chainModel Cα).param (Qof E.P) (Nα.chord k).lpos < 1 := hpA.2.1.2.1
  have tB0 : 0 ≤ (chainModel Cα).param (Qof E.P) (Nα.chord k).rpos := hpB.2.1.1
  have tB1 : (chainModel Cα).param (Qof E.P) (Nα.chord k).rpos < 1 := hpB.2.1.2.1
  have hpAn : (Nα.chord k).lp < (chainModel Cα).W.n := hpA.1
  have hpBn : (Nα.chord k).rp < (chainModel Cα).W.n := hpB.1
  set tA : ℝ := (chainModel Cα).param (Qof E.P) ⟨(Nα.chord k).lp, (Nα.chord k).h + 1⟩ with htA
  set tB : ℝ := (chainModel Cα).param (Qof E.P) ⟨(Nα.chord k).rp, (Nα.chord k).h + 1⟩ with htB
  replace tA0 : 0 ≤ tA := tA0
  replace tA1 : tA < 1 := tA1
  replace tB0 : 0 ≤ tB := tB0
  replace tB1 : tB < 1 := tB1
  set da : ℝ := off (chainModel Cα).W.n g' ((Nα.chord k).lp + tA) with hda
  set db : ℝ := off (chainModel Cα).W.n g' ((Nα.chord k).rp + tB) with hdb
  obtain ⟨inA, neA, stA⟩ := EA
  obtain ⟨inB, neB, stB⟩ := EB
  have hX0 : (0 : ℝ) < dX := by exact_mod_cast hD.hX0
  have hXL : (dX : ℝ) < L := by exact_mod_cast hD.hXL
  -- the offsets of the ends
  have offE : ∀ (p : ℕ) (t : ℝ), p < (chainModel Cα).W.n → 0 ≤ t → t < 1 →
      0 < off (chainModel Cα).W.n g' (p + t) → off (chainModel Cα).W.n g' (p + t) < L →
      g' ≤ p ∧ p - g' < L ∧ off (chainModel Cα).W.n g' (p + t) = ((p - g' : ℕ) : ℝ) + t := by
    intro p t hp t0 t1 a b
    obtain ⟨i1, i2, -⟩ := (inE_iff hS hp t0 t1).2 ⟨a, b⟩
    refine ⟨i1, by omega, ?_⟩
    have e := endα_off hS (d := p - g') (by omega) t0 t1
    rwa [show g' + (p - g') = p by omega] at e
  have offU : ∀ u : ℕ, u < L → off (chainModel Cα).W.n g' (((g' + u : ℕ) : ℝ)) = u := by
    intro u hu
    have e := endα_off hS (d := u) hu le_rfl one_pos
    rwa [add_zero, add_zero] at e
  -- the end data
  obtain ⟨αa, ha0, haa, hgA, rotA⟩ : ∃ αa : ℝ, 0 ≤ αa ∧ (0 < αa → αa < L → αa = db) ∧
      GEnd L da αa (c₂.nreg 81166 = 1) dX ∧
      (0 < da → da < L → ∀ u, u < L →
        (sideInArc (E.M.key (Qof E.P) ⟨c₂.nreg 81161, c₂.nreg 81162⟩)
          (E.M.key (Qof E.P) ⟨c₂.nreg 81163, c₂.nreg 81164⟩) (((g + u) % E.M.W.n : ℕ) : ℝ) ↔
          sideInArc da αa u)) := by
    by_cases hi : 0 < da ∧ da < L
    · obtain ⟨-, -, -, -, α, h0, h1, h2⟩ := stA hi.1 hi.2
      obtain ⟨h3, h4⟩ := h2 neB
      exact ⟨α, h0, h1, h3, fun _ _ => h4⟩
    · exact ⟨0, le_rfl, fun h => absurd h (lt_irrefl 0), fun h => absurd h hi,
        fun a b => absurd ⟨a, b⟩ hi⟩
  obtain ⟨αb, hb0, hbb, hgB, rotB⟩ : ∃ αb : ℝ, 0 ≤ αb ∧ (0 < αb → αb < L → αb = da) ∧
      GEnd L db αb (c₃.nreg 81176 = 1) dX ∧
      (0 < db → db < L → ∀ u, u < L →
        (sideInArc (E.M.key (Qof E.P) ⟨c₃.nreg 81171, c₃.nreg 81172⟩)
          (E.M.key (Qof E.P) ⟨c₃.nreg 81173, c₃.nreg 81174⟩) (((g + u) % E.M.W.n : ℕ) : ℝ) ↔
          sideInArc db αb u)) := by
    by_cases hi : 0 < db ∧ db < L
    · obtain ⟨-, -, -, -, α, h0, h1, h2⟩ := stB hi.1 hi.2
      obtain ⟨h3, h4⟩ := h2 neA
      exact ⟨α, h0, h1, h3, fun _ _ => h4⟩
    · exact ⟨0, le_rfl, fun h => absurd h (lt_irrefl 0), fun h => absurd h hi,
        fun a b => absurd ⟨a, b⟩ hi⟩
  have hg0 : (0 : ℝ) ≤ g' := Nat.cast_nonneg _
  have hgn : (g' : ℝ) < (chainModel Cα).W.n := by
    rw [hnα]; have := hS.hgL; have := hS.hL0; exact_mod_cast (by omega : g' < 2 * Cα.m + 7)
  have hkA0 : (0 : ℝ) ≤ (Nα.chord k).lp + tA := by positivity
  have hkB0 : (0 : ℝ) ≤ (Nα.chord k).rp + tB := by positivity
  have hkAn : ((Nα.chord k).lp : ℝ) + tA < (chainModel Cα).W.n := by
    have : ((Nα.chord k).lp : ℝ) + 1 ≤ (chainModel Cα).W.n := by exact_mod_cast hpAn
    linarith
  have hkBn : ((Nα.chord k).rp : ℝ) + tB < (chainModel Cα).W.n := by
    have : ((Nα.chord k).rp : ℝ) + 1 ≤ (chainModel Cα).W.n := by exact_mod_cast hpBn
    linarith
  have hda0 : 0 ≤ da := off_nonneg hkA0 hgn
  have hdb0 : 0 ≤ db := off_nonneg hkB0 hgn
  have hdab : da ≠ db := by
    intro h
    obtain ⟨e1, e2⟩ := nat_add_frac tA0 tA1 tB0 tB1 (off_inj hg0 hgn hkA0 hkAn hkB0 hkBn h)
    apply hne
    show sidePt _ (Nα.chord k).lp tA = sidePt _ (Nα.chord k).rp tB
    rw [e1, e2]
  have hWX : WOK L da db αa αb (c₂.nreg 81166 = 1) (c₃.nreg 81176 = 1) (dX : ℕ) :=
    ⟨hX0, hXL, fun h => neA h.symm, fun h => neB h.symm, hgA, hgB⟩
  -- the registers of the left end at `c₃`
  have q60 : c₃.nreg 81160 = c₂.nreg 81160 := g3 _ (by norm_num) (by norm_num)
  have q61 : c₃.nreg 81161 = c₂.nreg 81161 := g3 _ (by norm_num) (by norm_num)
  have q62 : c₃.nreg 81162 = c₂.nreg 81162 := g3 _ (by norm_num) (by norm_num)
  have q63 : c₃.nreg 81163 = c₂.nreg 81163 := g3 _ (by norm_num) (by norm_num)
  have q64 : c₃.nreg 81164 = c₂.nreg 81164 := g3 _ (by norm_num) (by norm_num)
  have q65 : c₃.nreg 81165 = c₂.nreg 81165 := g3 _ (by norm_num) (by norm_num)
  have q66 : c₃.nreg 81166 = c₂.nreg 81166 := g3 _ (by norm_num) (by norm_num)
  have q67 : c₃.nreg 81167 = c₂.nreg 81167 := g3 _ (by norm_num) (by norm_num)
  -- passing the tests ↔ the candidate condition
  have toW : ∀ u : ℕ, WOK L da db αa αb (c₂.nreg 81166 = 1) (c₃.nreg 81176 = 1) (u : ℝ) →
      WCand E c₀ c₃ u := by
    rintro u ⟨w0, wL, wa, wb, wga, wgb⟩
    have hu : u < L := by exact_mod_cast wL
    unfold WCand GAt
    simp only [Nat.reduceAdd]
    rw [d30, d31, d32, d53, d54, q60, q61, q62, q63, q64, q65, q66, q67, key_vtx]
    refine ⟨hu, (hD.hcnt u hu).1, ?_, ?_, fun h1 h5 => ?_, fun h1 h5 => ?_⟩
    · rintro ⟨h1, h2, h3⟩
      obtain ⟨a, b⟩ := inA.1 h1
      obtain ⟨-, -, -, bit7, -⟩ := stA a b
      have t0 : tA = 0 := by
        have := bit7.2; rw [h3] at this; sil at this
      apply wa
      have e : off (chainModel Cα).W.n g' (((Nα.chord k).lp : ℝ) + tA) = u := by
        rw [← h2, t0, add_zero, offU u hu]
      exact e.symm
    · rintro ⟨h1, h2, h3⟩
      obtain ⟨a, b⟩ := inB.1 h1
      obtain ⟨-, -, -, bit7, -⟩ := stB a b
      have t0 : tB = 0 := by
        have := bit7.2; rw [h3] at this; sil at this
      apply wb
      have e : off (chainModel Cα).W.n g' (((Nα.chord k).rp : ℝ) + tB) = u := by
        rw [← h2, t0, add_zero, offU u hu]
      exact e.symm
    · obtain ⟨a, b⟩ := inA.1 h1
      rw [rotA a b u hu]; exact wga ⟨a, b⟩
    · obtain ⟨a, b⟩ := inB.1 h1
      rw [rotB a b u hu]; exact wgb ⟨a, b⟩
  have fromW : ∀ u : ℕ, 1 ≤ u → WCand E c₀ c₃ u →
      WOK L da db αa αb (c₂.nreg 81166 = 1) (c₃.nreg 81176 = 1) (u : ℝ) := by
    intro u hu1 hW
    unfold WCand GAt at hW
    simp only [Nat.reduceAdd] at hW
    rw [d30, d31, d32, d53, d54, q60, q61, q62, q63, q64, q65, q66, q67, key_vtx] at hW
    obtain ⟨hu, -, nA, nB, gA, gB⟩ := hW
    have hu0 : (0 : ℝ) < u := by exact_mod_cast hu1
    have huL : (u : ℝ) < L := by exact_mod_cast hu
    refine ⟨hu0, huL, fun h => ?_, fun h => ?_, fun ⟨a, b⟩ => ?_, fun ⟨a, b⟩ => ?_⟩
    · have a : 0 < da := h ▸ hu0
      have b : da < L := h ▸ huL
      obtain ⟨i1, -, i3⟩ := offE _ _ hpAn tA0 tA1 a b
      have h' := h.trans i3
      obtain ⟨e1, e2⟩ := nat_add_frac le_rfl one_pos tA0 tA1 (by rwx [add_zero])
      obtain ⟨-, -, -, bit7, -⟩ := stA a b
      exact nA ⟨inA.2 ⟨a, b⟩, by omega, by
        have := bit7.1; have h7 := bit7.2; rw [← e2] at h7; sio at h7⟩
    · have a : 0 < db := h ▸ hu0
      have b : db < L := h ▸ huL
      obtain ⟨i1, -, i3⟩ := offE _ _ hpBn tB0 tB1 a b
      have h' := h.trans i3
      obtain ⟨e1, e2⟩ := nat_add_frac le_rfl one_pos tB0 tB1 (by rwx [add_zero])
      obtain ⟨-, -, -, bit7, -⟩ := stB a b
      exact nB ⟨inB.2 ⟨a, b⟩, by omega, by
        have := bit7.1; have h7 := bit7.2; rw [← e2] at h7; sio at h7⟩
    · obtain ⟨-, v5, -⟩ := stA a b
      have := gA (inA.2 ⟨a, b⟩) v5
      rw [rotA a b u hu] at this; exact this
    · obtain ⟨-, v5, -⟩ := stB a b
      have := gB (inB.2 ⟨a, b⟩) v5
      rw [rotB a b u hu] at this; exact this
  -- the child
  obtain ⟨dd, hDec⟩ := hP.hDec
  obtain ⟨Dd, hRT⟩ := hD.hRT
  have hneα : (Nα.F (chainModel Cα) (Qof E.P)).Nonempty := ⟨_, hcF⟩
  have hdn : (Nα.chord k).dn < Nα.nRegions := (hRT.ends_lt k hk).2
  obtain ⟨-, hj, hjr⟩ := region_arc hMα hP.hNα hD.hregsα hneα hdn
  have hXn : g' + dX < (chainModel Cα).W.n := by rw [hnα]; have := hD.hXL; omega
  have offX : off (chainModel Cα).W.n g' (((g' + dX : ℕ) : ℝ)) = dX := offU dX hD.hXL
  have hpa : (((g' + dX : ℕ) : ℝ)) ≠ (Nα.chord k).lp + tA := by
    intro h; apply neA
    show off (chainModel Cα).W.n g' (((Nα.chord k).lp : ℝ) + tA) = dX
    rw [← h]; exact offX
  have hpb : (((g' + dX : ℕ) : ℝ)) ≠ (Nα.chord k).rp + tB := by
    intro h; apply neB
    show off (chainModel Cα).W.n g' (((Nα.chord k).rp : ℝ) + tB) = dX
    rw [← h]; exact offX
  have CS := child_side hGα hP.hNα hRT hD.hregsα hk hat.1 hat.2 hne hD.hT hXn hD.hfT hpa hpb hj hjr
  by_cases hw1 : c₄.nreg 81181 = 1
  · obtain ⟨hU, xe, hu1⟩ := xC hw1
    have hu := fromW _ hu1 hU
    have huL : c₄.nreg 81180 < L := by have := hU.1; rw [d32] at this; exact this
    have hside := witness_side_ok ha0 haa hb0 hbb hda0 hdb0 hdab hu hWX
    have hkU : (chainModel Cα).key (Qof E.P) ⟨c₄.nreg 81183, 0⟩ =
        (((g' + c₄.nreg 81180 : ℕ)) : ℝ) := by rw [key_vtx, xe, d31]
    have hUn : (((g' + c₄.nreg 81180 : ℕ)) : ℝ) < (chainModel Cα).W.n := by
      have : g' + c₄.nreg 81180 < (chainModel Cα).W.n := by rwo [hnα]
      exact_mod_cast this
    have hiff : sideInArc ((chainModel Cα).key (Qof E.P) (Nα.chord k).lpos)
        ((chainModel Cα).key (Qof E.P) (Nα.chord k).rpos)
        ((chainModel Cα).key (Qof E.P) ⟨c₄.nreg 81183, 0⟩) ↔
        sideInArc ((chainModel Cα).key (Qof E.P) (Nα.chord k).lpos)
        ((chainModel Cα).key (Qof E.P) (Nα.chord k).rpos) (((g' + dX : ℕ)) : ℝ) := by
      rw [hkU]
      show sideInArc (((Nα.chord k).lp : ℝ) + tA) ((Nα.chord k).rp + tB) _ ↔
        sideInArc (((Nα.chord k).lp : ℝ) + tA) ((Nα.chord k).rp + tB) _
      rw [sideInArc_rot hg0 hgn hkA0 hkAn hkB0 hkBn (Nat.cast_nonneg _) hUn,
        sideInArc_rot hg0 hgn hkA0 hkAn hkB0 hkBn (Nat.cast_nonneg _) (by exact_mod_cast hXn),
        offU _ huL, offX]
      exact hside
    obtain ⟨hlo, hhi⟩ := hch hw1
    by_cases hc : (sideInArc ((chainModel Cα).key (Qof E.P) (Nα.chord k).lpos)
        ((chainModel Cα).key (Qof E.P) (Nα.chord k).rpos) (((g' + dX : ℕ)) : ℝ) ↔
      ((chainModel Cα).key (Qof E.P) (Nα.arc ((Nα.region (Nα.chord k).dn).arcs.getD 0 0)).s =
          (chainModel Cα).key (Qof E.P) (Nα.chord k).lpos ∨
        sideInArc ((chainModel Cα).key (Qof E.P) (Nα.chord k).lpos)
          ((chainModel Cα).key (Qof E.P) (Nα.chord k).rpos)
          ((chainModel Cα).key (Qof E.P) (Nα.arc ((Nα.region (Nα.chord k).dn).arcs.getD 0 0)).s)))
    · rw [hlo (hiff.trans hc)]; exact below_lo hDec hk hb (CS.1 hc)
    · rw [hhi (fun h => hc (hiff.symm.trans h))]; exact below_hi hDec hk hb (CS.2 hc)
  · exfalso
    rcases witness_exists ha0 haa hb0 hbb hda0 hdb0 hWX with h | ⟨a, b, h⟩ | ⟨a, b, h⟩
    · exact hw1 (xAll (Or.inl (toW 1 (by rwx [Nat.cast_one]))))
    · obtain ⟨-, -, i3⟩ := offE _ _ hpAn tA0 tA1 a b
      have fl : ⌊da⌋₊ = (Nα.chord k).lp - g' := by
        show ⌊off (chainModel Cα).W.n g' (((Nα.chord k).lp : ℝ) + tA)⌋₊ = _
        rw [i3, Nat.floor_eq_iff (by positivity)]
        constructor <;> linarith
      exact hw1 (xAll (Or.inr (Or.inl ⟨by rw [q60]; exact inA.2 ⟨a, b⟩,
        by rw [d53, d31, ← fl]; exact toW _ h⟩)))
    · obtain ⟨-, -, i3⟩ := offE _ _ hpBn tB0 tB1 a b
      have fl : ⌊db⌋₊ = (Nα.chord k).rp - g' := by
        show ⌊off (chainModel Cα).W.n g' (((Nα.chord k).rp : ℝ) + tB)⌋₊ = _
        rw [i3, Nat.floor_eq_iff (by positivity)]
        constructor <;> linarith
      exact hw1 (xAll (Or.inr (Or.inr ⟨inB.2 ⟨a, b⟩,
        by rw [d54, d31, ← fl]; exact toW _ h⟩)))

end

end Restore

end Chazelle.Core
