module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SweepIoLHit
public import Chazelle.Core.RestoreTShot

/-!
# The sweep RAM (WP-D), answers: the local hit, part 2 (arcs, holes, shot)

The facts the shot wrapper needs: the gathered arcs are pieces of weight at most `γ`
(`nArc_piece`), the holes at a position on a vertical box side (`boxHole`), the shot block.
-/

namespace Chazelle.Core

namespace SweepIo

open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (sidePt sideLeft sideInArc)
open OracleQ (sj sk ek succP predP)

@[expose] public section

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-! ## Heights of walk positions -/

/-- **A position with a positive parameter off the horizontal box edges** lies strictly inside the
height band of the box. -/
theorem pos_abs_lt (C : Chain) (Q : Polygon) {n : ℕ} {x : WPos}
    (he : x.edge < (chainModel C).W.n) (hp : ProperPos (chainModel C) Q n x)
    (h0 : 0 < (chainModel C).param Q x) (hb : x.edge ≠ 0 ∧ x.edge ≠ 2 ∧ x.edge ≠ 4) :
    |((chainModel C).pos Q x).2| < C.radius := by
  have hn : (chainModel C).W.n = 2 * C.m + 7 := C.sideWalk_n _
  have hpos : (chainModel C).pos Q x = sidePt (C.sideWalk C.sideBeta) x.edge
      ((chainModel C).param Q x) := rfl
  set t := (chainModel C).param Q x
  have hR := C.radius_pos
  have ht1 := hp.2.1
  have hT := C.top_snd_lt_radius
  have hT' : -C.radius < C.top.2 := by
    have := lt_of_le_of_lt (C.abs_le_coordBound_of_mem_set C.top_mem_set).2 C.coordBound_lt_radius
    grind
  obtain ⟨-, b1, -, b3, -, b5, b6⟩ := C.sidePt_box C.sideBeta t
  rcases (by omega : x.edge = 1 ∨ x.edge = 3 ∨ x.edge = 5 ∨ (6 ≤ x.edge ∧ x.edge < 2 * C.m + 6) ∨
    x.edge = 2 * C.m + 6) with h | h | h | ⟨h1, h2⟩ | h
  · rw [hpos, h, b1]; simp only; rw [abs_lt]; constructor <;> nlinarith
  · rw [hpos, h, b3]; simp only; rw [abs_lt]; constructor <;> nlinarith
  · rw [hpos, h, b5]; simp only; rw [abs_lt]; constructor <;> nlinarith
  · have hmem : (chainModel C).pos Q x ∈ C.set := by
      rw [hpos, show x.edge = (x.edge - 6) + 6 by omega]
      exact C.sideWalk_tour_pt_mem C.sideBeta (by omega) (fun h' => by omega) hp.1 ht1
    exact lt_of_le_of_lt (C.abs_le_coordBound_of_mem_set hmem).2 C.coordBound_lt_radius
  · rw [hpos, h, b6]; simp only; rw [abs_lt]; constructor <;> nlinarith

/-! ## The gathered arcs are pieces -/

/-- **The normalised arc of a valid normal form** is a piece of the shot of weight at most `γ`. -/
theorem nArc_piece {C : Chain} (hP : C.P.Simple) {N : NF} (hNF : IsNF (chainModel C) (Qof P) N)
    {γ : ℕ} (hsg : (chainModel C).Semigranular (N.F (chainModel C) (Qof P)) γ) {a : ℕ}
    (ha : a < N.arcs.length) :
    ShotList.PieceOK (chainModel C) (Qof P) P.n (nArc (chainModel C) (Qof P) N a) ∧
      (chainModel C).arcWt ((chainModel C).key (Qof P) (nArc (chainModel C) (Qof P) N a).1)
        ((chainModel C).key (Qof P) (nArc (chainModel C) (Qof P) N a).2) ≤ γ := by
  obtain ⟨⟨hps, hse, -⟩, ⟨hpe, hee, -⟩⟩ := arc_end_facts hP hNF ha
  have hNF' := hNF
  obtain ⟨-, -, -, reg, hRC, -, hArcs, -, -, -, -⟩ := hNF'
  obtain ⟨hreg, harc⟩ := hArcs.1 a ha
  have hU := hRC.1 _ hreg
  have endok : ∀ u : WPos, ProperPos (chainModel C) (Qof P) P.n u →
      u.edge < (chainModel C).W.n →
      ShotList.NormPos (chainModel C) (Qof P) P.n (Restore.normOf (chainModel C) (Qof P) u) ∧
        (Restore.normOf (chainModel C) (Qof P) u).edge < (chainModel C).W.n ∧
        ((Restore.normOf (chainModel C) (Qof P) u).hgt = 0 ∨
          (chainModel C).InnerPt ((chainModel C).pos (Qof P)
            (Restore.normOf (chainModel C) (Qof P) u))) := by
    intro u hu hue
    obtain ⟨hN, he', hpos', -, hcase⟩ := Restore.normOf_facts hu
    refine ⟨hN, by omega, ?_⟩
    rcases hcase with h | h
    · omega
    · right
      set v := Restore.normOf (chainModel C) (Qof P) u
      have hve : v.edge < (chainModel C).W.n := by omega
      have hb : v.edge ≠ 0 ∧ v.edge ≠ 2 ∧ v.edge ≠ 4 := by
        refine ⟨fun h0 => ?_, fun h0 => ?_, fun h0 => ?_⟩ <;>
        · have := Model.param_horizontal (M := chainModel C) (Q := Qof P) (x := v)
            (ShootCut.box_horizontal (C := C) (by omega))
          linarith
      exact Restore.innerPt_chain_walk C (Qof P) hve hN.1.1 hN.1.2.1.le
        (pos_abs_lt C (Qof P) hve hN.1 h hb)
  obtain ⟨n1, n2, n3⟩ := endok _ hps hse
  obtain ⟨m1, m2, m3⟩ := endok _ hpe hee
  refine ⟨⟨n1, m1, n2, m2, n3, m3⟩, ?_⟩
  unfold nArc
  rw [(Restore.normOf_facts hps).2.2.2.1, (Restore.normOf_facts hpe).2.2.2.1]
  exact (arcWt_le_weight _ harc).trans (hsg _ hU)

/-! ## The hole at a position on a vertical side of the box -/

/-- **The edge of a position inside a vertical side of the box** is a hole covering it, near it. -/
theorem boxHole_ok (C : Chain) (hP : C.P.Simple) (Q : Polygon) {e h : ℕ} (he : e = 1 ∨ e = 3)
    (h0 : 0 < (chainModel C).param Q ⟨e, h⟩) (h1 : (chainModel C).param Q ⟨e, h⟩ < 1) :
    Restore.Cover (chainModel C) Q [(⟨e, 0⟩, ⟨e + 1, 0⟩)] ((chainModel C).pos Q ⟨e, h⟩) ∧
      Restore.Near (chainModel C) Q [(⟨e, 0⟩, ⟨e + 1, 0⟩)] ((chainModel C).pos Q ⟨e, h⟩) := by
  have hn : (chainModel C).W.n = 2 * C.m + 7 := C.sideWalk_n _
  have hm := C.one_le
  have hen : e + 1 < (chainModel C).W.n := by omega
  have kv : ∀ q : ℕ, (chainModel C).key Q ⟨q, 0⟩ = q := fun q => by
    simp_all
  have k0 : (chainModel C).key Q ⟨e, 0⟩ = e := kv e
  have k1 : (chainModel C).key Q ⟨e + 1, 0⟩ = ((e + 1 : ℕ) : ℝ) := kv (e + 1)
  refine ⟨fun p t hp ht0 ht1 hz => ?_, fun g hg p τ hp hτ0 hτ1 hc => ?_⟩
  · obtain ⟨rfl, rfl⟩ := SweepPrim.wall_unique C hP he h0 h1 hp ht0 ht1 hz
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    simp_all [sideInArc]
  · simp only [List.mem_singleton] at hg
    subst hg
    simp only at hc
    rw [k0, k1] at hc
    obtain ⟨t₂, h20, h21, h2⟩ := Restore.edge_keys (chainModel C).W (e := e) (by omega) hp hτ0 hτ1
      (by rw [Nat.mod_eq_of_lt hen]; exact hc)
    exact ⟨e, by omega, ⟨_, h0.le, h1.le, rfl⟩, t₂, h20, h21, h2⟩

/-! ## The shot as a run step -/

/-- The shot block of the answers. -/
def RS : ℕ := 241300

theorem regsOK_RS : ShotList.RegsOK RS := by
  omega_nf

/-- **The shot** as a run step: the post `ShotPost`, writing only the oracle bands and the shot
block `RS … RS + 299`. -/
theorem shot_irs {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx}
    {Ok : Polygon → Model → Prop} (hsh : ShooterOK sh Bs F X Ok) (hBs : Bs ⊆ oracleBands)
    (hXl : X.CapLocal) (hI : IInv W c₀ c) (pre : ShotList.ShotPre X Ok RS P W c)
    (hroom : c.nreg ALLOC + ShotList.shotCost (F (c.nreg (RS + 7))) (c.nreg (RS + 2)) ≤ W) :
    IRS P W c₀ (ShotList.shotList sh RS) c (ShotList.shotCost (F (c.nreg (RS + 7))) (c.nreg (RS + 2)))
      (fun c' => ShotList.ShotPost RS P c c' ∧
        (∀ r, bandOf r ∉ oracleBands → r ≠ ALLOC → ¬ (RS ≤ r ∧ r < RS + 300) →
          c'.nreg r = c.nreg r) ∧
        c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a)) := by
  obtain ⟨c', k, ex, hk, hpost, hfr⟩ := ShotList.shotList_execR hsh hBs hXl regsOK_RS c hI.hw pre hroom
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hfr
  have hio : ∀ r, bandOf r ∉ ioBands → bandOf r ∉ oracleBands ∧ ¬ (RS ≤ r ∧ r < RS + 300) :=
    fun r hr => ⟨fun h => hr (oracle_sub h), fun h => hr (by
      rw [band_sw (by omega_nf) (by omega_nf)]; exact bSweep_mem)⟩
  refine ⟨c', k, ex, hk, ⟨ex.wb_right, fun q hq => ?_, le_trans hI.hA f6,
    fun a ha => (f3 a (lt_of_lt_of_le ha hI.hA)).trans (hI.hm a ha),
    fun a ha => (f4 a (lt_of_lt_of_le ha hI.hA)).trans (hI.hrm a ha)⟩,
    ⟨fun r hr hra => f1 r (hio r hr).1 hra (hio r hr).2, fun r hr => f2 r (hio r hr).1 (hio r hr).2,
      f5, f6, f7⟩, hpost, fun r hr hra hw => f1 r hr hra hw, f6, f3⟩
  unfold IFix at hq
  rw [f1 q (not_oracle_sw (by omega) (by omega)) (by omega_nf)
    (by omega_nf)]
  exact hI.hin q hq

/-! ## Transport of the context -/

/-- **The local-hit context survives** a step keeping its registers, the memory below the
allocator, and not lowering the allocator. -/
theorem LCtx.transport {C : Chain} {N : NF} {E : ℕ} {c c' : Config} (h : LCtx P W C N E c)
    (hr : ∀ r, r = lMD ∨ r = lCD ∨ r = lNF ∨ r = TBR ∨ r = TLR → c'.nreg r = c.nreg r)
    (hm : ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) (hA : c.nreg ALLOC ≤ c'.nreg ALLOC) :
    LCtx P W C N E c' := by
  obtain ⟨hG, hWh, hctx, hcd, hmd, hmwf, hm0, hP, hNW, hE, hNF, htab, hbig, hTB, hTW⟩ := h
  have rMD := hr lMD (Or.inl rfl)
  have rCD := hr lCD (Or.inr (Or.inl rfl))
  have rNF := hr lNF (Or.inr (Or.inr (Or.inl rfl)))
  have rTB := hr TBR (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have rTL := hr TLR (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  rcases hmd with ⟨-, H, C', hC', hMC⟩ | ⟨h1, -⟩
  swap
  · omega
  obtain ⟨w1, w2, w3⟩ := ShotList.modelDesc_keep hmwf hm0 hC' hm hA
  refine ⟨hG, hWh, hctx.transport rCD hm hA, by omega, ?_, by simp_all,
    by simp_all, hP, by rw [rNF]; exact hNW.transport (fun a ha => hm a (by omega)),
    by omega, hNF, fun j hj => ?_, by simp_all, by omega,
    by omega⟩
  all_goals (grind [Chazelle.Core.ModelDescAt])

/-! ## The gather of the three regions -/

/-- The gather of the list at `lL` (three regions). -/
def lhGather : Stmt := .seq (block [.copyN gNF lNF, .copyN gL lL, .copyN gC K3]) (gather lCD)

/-- The registers of the gather call. -/
def GCall (r : ℕ) : Prop := sw 1000 ≤ r ∧ r ≤ sw 1021

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **The gather of the three regions** of the local hit. -/
theorem lhGather_irs {C : Chain} {N : NF} {E : ℕ} {rs : List ℕ} (hI : IInv W c₀ c)
    (hK : Consts c₀) (hL : LCtx P W C N E c) (hrs3 : rs.length = 3)
    (hrs : ∀ r ∈ rs, r < N.nRegions)
    (hlist : ∀ i, i < 3 → c.nmem (c.nreg lL + i) = rs.getD i 0)
    (hLA : c.nreg lL + 3 ≤ c.nreg ALLOC)
    (hroom : c.nreg ALLOC + (3 + gatherK N rs) ≤ W) :
    IRS P W c₀ lhGather c (3 + gatherK N rs) (fun c' =>
      c'.nreg gBase = c.nreg ALLOC ∧ c'.nreg gK = (regArcs N rs).length ∧
      c'.nreg ALLOC = c.nreg ALLOC + 4 * (regArcs N rs).length ∧
      (∀ k, k < (regArcs N rs).length → ShotList.arcAt c'.nmem (c.nreg ALLOC) k =
        nArc (chainModel C) (Qof P) N ((regArcs N rs).getD k 0)) ∧
      (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) ∧
      (∀ r, bandOf r ∉ oracleBands → ¬ GCall r → r ≠ ALLOC → c'.nreg r = c.nreg r)) := by
  have hK₀ := hK.fix hI
  have hok : okB W c.nmem [.copyN gNF lNF, .copyN gL lL, .copyN gC K3] c.nreg :=
    ⟨iscr_sw (by omega_nf) (by omega_nf),
      iscr_sw (by omega_nf) (by omega_nf),
      iscr_sw (by omega_nf) (by omega_nf), trivial⟩
  refine IRS.seq (K₂ := gatherK N rs) (IRS.block _ hI hok) ?_ |>.mono (by simp) (fun _ h => h)
  rintro c₁ hI₁ - - hc1
  have v1 : c₁.nreg gNF = c.nreg lNF ∧ c₁.nreg gL = c.nreg lL ∧ c₁.nreg gC = 3 := by
    rw [hc1]
    refine ⟨?_, ?_, ?_⟩
    · simp_all [regB, regI, upd, gNF, gL, gC, lNF, lL, K3, sw]
    · simp_all [regB, regI, upd, gNF, gL, gC, lNF, lL, K3, sw]
    simp_all [regB, regI, upd, gNF, gL, gC, lNF, lL, K3, sw] <;> omega_nf
  have k1 : ∀ r, r ≠ gNF → r ≠ gL → r ≠ gC → c₁.nreg r = c.nreg r := by
    intro r h1 h2 h3; rw [hc1]
    exact regB_other _ _ _ (fun i hi => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      grind [dstI])
  have hm1 : c₁.nmem = c.nmem := by rw [hc1]
  have hA1 : c₁.nreg ALLOC = c.nreg ALLOC := k1 _ (by omega_nf)
    (by omega_nf) (by omega_nf)
  have hL1 : LCtx P W C N E c₁ := hL.transport (fun r hr => k1 r
    (by omega_nf)
    (by omega_nf)
    (by omega_nf))
    (fun a _ => by rw [hm1]) hA1.ge
  refine (gather_irs (rs := rs) hI₁ hK hL1.hctx ⟨by omega_nf, by omega_nf,
    fun h => by omega_nf⟩ hL1.hP hL1.hNF (B := c₁.nreg lNF) hL1.hNW
    (by grind [lNF, gNF, sw, gL, gC]) hL1.hE hrs
    (fun j hj => by simp_all)
    (by omega) (by omega)
    (by omega)).mono le_rfl ?_
  grind [Chazelle.Core.SweepIo.GW, Chazelle.Core.SweepIo.ChainCtx, Chazelle.Core.SweepIo.GCall, Chazelle.Core.SweepIo.IInv, Chazelle.Core.SweepIo.Consts, Chazelle.Core.SweepIo.LCtx, Chazelle.Core.SweepIo.okB, GSet, sw, GCall, gNF, gL, gC]

/-! ## The holes -/

def lO : ℕ := sw 1120

/-- The hole of a position on a vertical box side: its edge. -/
def boxL : List Instr := [.constN 241309 1, .copyN 241310 lE, .addN 241311 lE K1]

/-- The holes at `x`: the edge on a vertical box side, else `chainH`. -/
def lhHoles : Stmt :=
  .ifLtN lE K6 (block boxL)
    (.seq (block [.copyN 243005 lE, .copyN 243006 lH]) (.seq (normS lCD 243005 243006 lO)
      (.seq (block [.copyN 243020 lCD, .constN 243022 0, .constN 243023 1]) chainH)))

/-- The registers the holes write (outside the oracle bands). -/
def HSet (r : ℕ) : Prop := (241309 ≤ r ∧ r ≤ 241315) ∨ (243000 ≤ r ∧ r < 243200) ∨ r = lO ∨
  r = lO + 1

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **The holes** at the position `x = (lE, lH)`. -/
theorem lhHoles_irs {C : Chain} (hI : IInv W c₀ c) (hK : Consts c₀) (hctx : ChainCtx P W c lCD C)
    (he : c.nreg lE < (chainModel C).W.n)
    (hpp : ProperPos (chainModel C) (Qof P) P.n ⟨c.nreg lE, c.nreg lH⟩)
    (hy : |((chainModel C).pos (Qof P) ⟨c.nreg lE, c.nreg lH⟩).2| < C.radius)
    (hloc : (c.nreg lE = 1 ∨ c.nreg lE = 3) ∨
      (6 ≤ c.nreg lE ∧ (chainModel C).pos (Qof P) ⟨c.nreg lE, c.nreg lH⟩ ∈ C.set))
    (hroom : c.nreg ALLOC + 11200 ≤ W) :
    IRS P W c₀ lhHoles c 11200 (fun c' =>
      HoleOut (chainModel C) (Qof P) c' ((chainModel C).pos (Qof P) ⟨c.nreg lE, c.nreg lH⟩) ∧
      (∀ r, bandOf r ∉ oracleBands → ¬ HSet r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.nreg ALLOC = c.nreg ALLOC ∧ c'.nmem = c.nmem) := by
  have hK₀ := hK.fix hI
  obtain ⟨k0, k1, k6, k4, k5, k2, k3⟩ := hK₀
  set x : WPos := ⟨c.nreg lE, c.nreg lH⟩ with hx
  have hn : (chainModel C).W.n = 2 * C.m + 7 := C.sideWalk_n _
  have hm1 := C.one_le
  have hnW : 2 * C.m + 7 ≤ W := hctx.2.2.2.2.2
  unfold lhHoles
  by_cases hbox : c.nreg lE < c.nreg K6
  · rw [k6] at hbox
    have hb : c.nreg lE = 1 ∨ c.nreg lE = 3 := by
      omega
    have hpar0 : 0 < (chainModel C).param (Qof P) x := ShootCut.box_param_pos' C (Qof P) hbox hpp.1 hy
    have hok : okB W c.nmem boxL c.nreg := by
      simp only [boxL, okB, okI, regI, upd, lE, K1, sw]
      ram_grind
    refine (IRS.ifT (by omega) (IRS.block _ hI hok)).mono (by simp [boxL]) ?_
    rintro c' rfl
    have e1 : c.nreg 240611 = 1 := k1
    have v9 : regB c.nmem boxL c.nreg 241309 = 1 := by
      simp_all [boxL, regB, regI, upd, lE, K1, sw]
    have v10 : regB c.nmem boxL c.nreg 241310 = c.nreg lE := by
      simp_all [boxL, regB, regI, upd, lE, K1, sw]
    have v11 : regB c.nmem boxL c.nreg 241311 = c.nreg lE + 1 := by
      simp_all [boxL, regB, regI, upd, lE, K1, sw]
    have vo : ∀ r, r ≠ 241309 → r ≠ 241310 → r ≠ 241311 → regB c.nmem boxL c.nreg r = c.nreg r :=
      fun r h1 h2 h3 => regB_other _ _ _ (fun i hi => by
        simp only [boxL, List.mem_cons, List.not_mem_nil, or_false] at hi
        grind [dstI])
    set c' : Config := { c with nreg := regB c.nmem boxL c.nreg } with hc'
    have hl : ShotList.holeList c' 241300 = [(⟨c.nreg lE, 0⟩, ⟨c.nreg lE + 1, 0⟩)] := by
      rw [holeList_one _ v9]
      grind [ShotList.holeAt]
    obtain ⟨hcov, hnear⟩ := boxHole_ok C hctx.2.2.2.2.1 (Qof P) hb hpar0 hpp.2.1
    ram_grind
  · -- a point of the chain: `chainH`
    rw [k6] at hbox
    
    have hxC : (chainModel C).pos (Qof P) x ∈ C.set := by
      grind
    refine (IRS.ifF (by omega) ?_).mono (K := 11198) (by omega) (fun _ h => h)
    -- copy the position
    have hok1 : okB W c.nmem [.copyN 243005 lE, .copyN 243006 lH] c.nreg :=
      ⟨iscr_sw (by norm_num) (by norm_num), iscr_sw (by norm_num) (by norm_num), trivial⟩
    refine IRS.seq (IRS.block _ hI hok1) ?_ |>.mono (K := 2 + (11015 + (3 + 100))) (by omega)
      (fun _ h => h)
    rintro c₁ hI₁ - - hc1
    have v15 : c₁.nreg 243005 = c.nreg lE := by
      simp_all [regB, regI, upd, lE, lH, sw]
    have v16 : c₁.nreg 243006 = c.nreg lH := by
      simp_all [regB, regI, upd, lE, lH, sw]
    have k1o : ∀ r, r ≠ 243005 → r ≠ 243006 → c₁.nreg r = c.nreg r := by
      intro r h1 h2; rw [hc1]
      exact regB_other _ _ _ (fun i hi => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        grind [dstI])
    have hm1 : c₁.nmem = c.nmem := by rw [hc1]
    have hA1 : c₁.nreg ALLOC = c.nreg ALLOC := k1o _ (by omega_nf) (by omega_nf)
    have hctx1 : ChainCtx P W c₁ lCD C := hctx.transport (k1o _ (by omega_nf)
      (by omega_nf)) (fun a _ => by rw [hm1]) hA1.ge
    -- normalise it
    have hpp1 : ProperPos (chainModel C) (Qof P) P.n ⟨c₁.nreg 243005, c₁.nreg 243006⟩ := by
      simp_all
    refine IRS.seq (normS_exact (normS_irs (dsc := lCD) (pe := 243005) (ph := 243006) (o := lO) hI₁
      (hK.fix hI₁) hctx1 ⟨by omega_nf, by omega_nf, by norm_num,
        by norm_num, by norm_num, by norm_num⟩
      ⟨by omega_nf, by omega_nf, by omega_nf,
        by omega_nf, by omega_nf, by omega_nf, by norm_num⟩
      (by omega) hpp1 (fun h' => by omega)
      (by omega)) ⟨by norm_num, by omega_nf⟩) ?_
    rintro c₂ hI₂ - - ⟨⟨n25, n26, k2, -, -⟩, hA2, hm2⟩
    obtain ⟨hNP, hne, hnpos, -, hncase⟩ := Restore.normOf_facts hpp
    have hu2 : (⟨c₂.nreg 243005, c₂.nreg 243006⟩ : WPos) = Restore.normOf (chainModel C) (Qof P) x := by
      rw [n25, n26, v15, v16]; unfold nhgt
      rcases hn' : Restore.normOf (chainModel C) (Qof P) x with ⟨e', h'⟩
      grind
    
    have k2o : ∀ r, bandOf r ∉ oracleBands → r ≠ 243006 → r ≠ lO → r ≠ lO + 1 → r ≠ ALLOC →
        c₂.nreg r = c₁.nreg r := k2
    have hctx2 : ChainCtx P W c₂ lCD C := hctx1.transport
      (k2o _ (not_oracle_sw (by omega_nf) (by omega_nf))
        (by omega_nf) (by omega_nf) (by omega_nf)
        (by omega_nf)) (fun a _ => by rw [hm2]) hA2.ge
    -- the descriptor and the constants
    have hok3 : okB W c₂.nmem [.copyN 243020 lCD, .constN 243022 0, .constN 243023 1] c₂.nreg :=
      ⟨iscr_sw (by norm_num) (by norm_num), ⟨iscr_sw (by norm_num) (by norm_num), Nat.zero_le _⟩,
        ⟨iscr_sw (by norm_num) (by norm_num), by omega⟩, trivial⟩
    refine IRS.seq (IRS.block _ hI₂ hok3) ?_
    rintro c₃ hI₃ - - hc3
    have v20 : c₃.nreg 243020 = c₂.nreg lCD := by
      rw [hc3]; show regB c₂.nmem [.copyN 243020 lCD, .constN 243022 0, .constN 243023 1] c₂.nreg 243020 = _
      simp only [regB, regI, upd, lCD, sw]; simp
    have v22 : c₃.nreg 243022 = 0 := by
      rw [hc3]; show regB c₂.nmem [.copyN 243020 lCD, .constN 243022 0, .constN 243023 1] c₂.nreg 243022 = _
      simp only [regB, regI, upd, lCD, sw]; simp
    have v23 : c₃.nreg 243023 = 1 := by
      rw [hc3]; show regB c₂.nmem [.copyN 243020 lCD, .constN 243022 0, .constN 243023 1] c₂.nreg 243023 = _
      simp only [regB, regI, upd, lCD, sw]; simp
    have k3o : ∀ r, r ≠ 243020 → r ≠ 243022 → r ≠ 243023 → c₃.nreg r = c₂.nreg r := by
      intro r h1 h2 h3; rw [hc3]
      exact regB_other _ _ _ (fun i hi => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        grind [dstI])
    have hm3 : c₃.nmem = c₂.nmem := by rw [hc3]
    have hA3 : c₃.nreg ALLOC = c₂.nreg ALLOC := k3o _ (by omega_nf) (by omega_nf)
      (by omega_nf)
    have h35 : c₃.nreg 243005 = c₂.nreg 243005 := k3o _ (by norm_num) (by norm_num) (by norm_num)
    have h36 : c₃.nreg 243006 = c₂.nreg 243006 := k3o _ (by norm_num) (by norm_num) (by norm_num)
    obtain ⟨-, -, hwf, ⟨H, hCD, -⟩, hP, hWm⟩ := hctx2
    -- the holes
    obtain ⟨c', k, ex, hk, hout, hOut⟩ := chainH_exec (P := P) (W := W) (c := c₃) hI₃.hw (H := H) (C := C)
      (by grind) (by rw [v20, hA3]; exact hwf.1) hP hWm v22 v23
      (by ram_grind) (by omega)
      (by grind) (by grind)
    have hHL : ∀ r, r ∈ holeL → HSet r := by
      intro r hr
      simp only [holeL, chainHL, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      unfold HSet; omega
    refine IRS.ofExec hI₃ ex (by omega) (fun r hr hra => hOut.1 r (fun h => hr (by
      grind [Chazelle.Core.SweepIo.IScr, HSet, lO, sw]))) hOut.2.1
      (fun a _ => by rw [hOut.2.2.1]) hOut.2.2.2.1 hOut.2.2.2.2
      (by rw [hOut.1 ALLOC (fun h => by grind [HSet, ALLOC, lO, sw])])
      (by rw [hOut.1 ALLOC (fun h => by grind [HSet, ALLOC, lO, sw])];
          omega) ⟨?_, fun r hr hh hra => ?_, ?_, ?_⟩
    · grind
    · rw [hOut.1 r (fun h => hh (hHL r h)), k3o r (fun h => hh (by omega_nf))
        (fun h => hh (by omega_nf)) (fun h => hh (by omega_nf)),
        k2o r hr (fun h => hh (by omega_nf)) (fun h => hh (Or.inr (Or.inr (Or.inl h))))
          (fun h => hh (Or.inr (Or.inr (Or.inr h)))) hra,
        k1o r (fun h => hh (by omega_nf)) (fun h => hh (by omega_nf))]
    · rw [hOut.1 ALLOC (fun h => by grind [HSet, ALLOC, lO, sw]), hA3, hA2,
        hA1]
    · rw [hOut.2.2.1, hm3, hm2, hm1]

/-! ## The shot and its hit -/

/-- The hit of a shot at a set off the domain containing the exit point is the exit point. -/
theorem firstHit_exit (C : Chain) {A : Set Point} {z : Point} {σ t : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hzt : z.2 ≤ C.top.2) (hf : Merge.FreeAt C z σ) (hA : A ⊆ C.domᶜ) (hF : FirstHit A z σ t)
    (hT : rayPt z σ (C.hitParam z σ) ∈ A) : t = C.hitParam z σ := by
  obtain ⟨hT0, -, hdom⟩ := Merge.hit_of_freeAt C hzt hσ hf
  obtain ⟨ht0, htA, hbefore⟩ := hF
  grind

/-- The shot block preparation. -/
def shPrepL : List Instr :=
  [.copyN 241300 lMD, .copyN 241301 gBase, .copyN 241302 gK, .constN 241303 2, .copyN 241304 lE,
    .copyN 241305 lH, .copyN 241306 lD, .copyN 241307 (sw 5), .copyN 241308 (sw 10)]

/-- Offer the hit of the shot. -/
def lhOffer : Stmt := .ifLtN K0 241320 (offerF accA lCD 241321 241322 lT lD lN lO) .skip

/-- The shot of the local hit and the offer of its hit. -/
def lhShotOffer (sh : Stmt) : Stmt :=
  .seq (block shPrepL) (.seq (ShotList.shotList sh RS) lhOffer)

theorem shPrepL_val (m f : ℕ → ℕ) :
    regB m shPrepL f 241300 = f lMD ∧ regB m shPrepL f 241301 = f gBase ∧
    regB m shPrepL f 241302 = f gK ∧ regB m shPrepL f 241303 = 2 ∧
    regB m shPrepL f 241304 = f lE ∧ regB m shPrepL f 241305 = f lH ∧
    regB m shPrepL f 241306 = f lD ∧ regB m shPrepL f 241307 = f (sw 5) ∧
    regB m shPrepL f 241308 = f (sw 10) ∧
    (∀ q, (q < 241300 ∨ 241308 < q) → regB m shPrepL f q = f q) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q hq => regB_other _ _ _ (fun i hi => by
    simp only [shPrepL, List.mem_cons, List.not_mem_nil, or_false] at hi
    core_grind)⟩ <;>
  aesop

/-- The cost of the shot and its offer. -/
def shotOfferK (Fg K : ℕ) : ℕ := 9 + (ShotList.shotCost Fg K + (offerFK + 2))

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- **The shot of the local hit** and the offer of its hit (filtered). -/
theorem lhShotOffer_irs {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx}
    {Ok : Polygon → Model → Prop} (hsh : ShooterOK sh Bs F X Ok) (hBs : Bs ⊆ oracleBands)
    (hXl : X.CapLocal) {C : Chain} {N : NF} {E : ℕ} {rs : List ℕ} {Mod : ℕ → Chain} {R₀ : ℝ}
    {L : Set ℝ} (hI : IInv W c₀ c) (hK : Consts c₀) (hL : LCtx P W C N E c)
    (hX : X.holds P c₀.nmem (c₀.nreg (sw 10)) (c₀.nreg ALLOC))
    (hcap : c₀.nreg (sw 5) ≤ X.cap P c₀.nmem (c₀.nreg (sw 10)))
    (hOk : Ok P (chainModel C))
    (hsg : (chainModel C).Semigranular (N.F (chainModel C) (Qof P)) (c₀.nreg (sw 5)))
    (he : c.nreg lE < (chainModel C).W.n)
    (hpp : ProperPos (chainModel C) (Qof P) P.n ⟨c.nreg lE, c.nreg lH⟩)
    (hy : |((chainModel C).pos (Qof P) ⟨c.nreg lE, c.nreg lH⟩).2| < C.radius)
    (hrs : ∀ a ∈ regArcs N rs, a < N.arcs.length)
    (hgK : c.nreg gK = (regArcs N rs).length)
    (hAB : c.nreg gBase + 4 * (regArcs N rs).length ≤ c.nreg ALLOC)
    (harcs : ∀ k, k < (regArcs N rs).length → ShotList.arcAt c.nmem (c.nreg gBase) k =
      nArc (chainModel C) (Qof P) N ((regArcs N rs).getD k 0))
    (hho : HoleOut (chainModel C) (Qof P) c ((chainModel C).pos (Qof P) ⟨c.nreg lE, c.nreg lH⟩))
    (hacc : AccOK P accA Mod R₀ ((chainModel C).pos (Qof P) ⟨c.nreg lE, c.nreg lH⟩)
      (dirOf (c.nreg lD)) L c)
    (htag : c.nreg lT ≤ 2) (hMod : Mod (c.nreg lT) = C) (hR : C.radius = R₀)
    (hn : c.nreg lN = 2 * C.m + 7)
    (hroom : c.nreg ALLOC + shotOfferK (F (c₀.nreg (sw 5))) (regArcs N rs).length ≤ W) :
    IRS P W c₀ (lhShotOffer sh) c (shotOfferK (F (c₀.nreg (sw 5))) (regArcs N rs).length)
      (fun c' => ∃ L', AccOK P accA Mod R₀ ((chainModel C).pos (Qof P) ⟨c.nreg lE, c.nreg lH⟩)
          (dirOf (c.nreg lD)) L' c' ∧
        (L' = L ∨ ∃ τ, L' = insert τ L ∧ 0 < τ ∧
          OnCB C (rayPt ((chainModel C).pos (Qof P) ⟨c.nreg lE, c.nreg lH⟩) (dirOf (c.nreg lD)) τ)) ∧
        (Merge.FreeAt C ((chainModel C).pos (Qof P) ⟨c.nreg lE, c.nreg lH⟩) (dirOf (c.nreg lD)) →
          ((chainModel C).pos (Qof P) ⟨c.nreg lE, c.nreg lH⟩).2 ≤ C.top.2 →
          rayPt ((chainModel C).pos (Qof P) ⟨c.nreg lE, c.nreg lH⟩) (dirOf (c.nreg lD))
              (C.hitParam ((chainModel C).pos (Qof P) ⟨c.nreg lE, c.nreg lH⟩) (dirOf (c.nreg lD))) ∈
            ShotList.loSet (chainModel C) (Qof P) c.nmem (c.nreg gBase) (regArcs N rs).length
              (ShotList.holeList c RS) →
          C.hitParam ((chainModel C).pos (Qof P) ⟨c.nreg lE, c.nreg lH⟩) (dirOf (c.nreg lD)) ∈ L') ∧
        (∀ r, bandOf r ∉ oracleBands → ¬ (RS ≤ r ∧ r < RS + 300) → (r < accA ∨ accA + 12 < r) →
          r ≠ lO → r ≠ lO + 1 → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
        c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a)) := by
  
  set x : WPos := ⟨c.nreg lE, c.nreg lH⟩ with hx
  set z := (chainModel C).pos (Qof P) x with hz
  set σ := dirOf (c.nreg lD) with hσ
  set K := (regArcs N rs).length with hKd
  have hσ' : σ = 1 ∨ σ = -1 := by grind [dirOf]
  have hWh := hL.hWh
  have hW2 : 2 ≤ W := by grind [hostWords]
  -- 1. prepare the shot block
  have hok : okB W c.nmem shPrepL c.nreg := by
    simp only [shPrepL, okB, okI]
    exact ⟨iscr_sw (by norm_num) (by norm_num), iscr_sw (by norm_num) (by norm_num),
      iscr_sw (by norm_num) (by norm_num), ⟨iscr_sw (by norm_num) (by norm_num), hW2⟩,
      iscr_sw (by norm_num) (by norm_num), iscr_sw (by norm_num) (by norm_num),
      iscr_sw (by norm_num) (by norm_num), iscr_sw (by norm_num) (by norm_num),
      iscr_sw (by norm_num) (by norm_num), trivial⟩
  refine IRS.seq (K₂ := ShotList.shotCost (F (c₀.nreg (sw 5))) K + (offerFK + 2))
    (IRS.block shPrepL hI hok) ?_ |>.mono (by simp [shPrepL, shotOfferK]) (fun _ h => h)
  rintro c₁ hI₁ - - hc1
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, po⟩ := shPrepL_val c.nmem c.nreg
  have hm1 : c₁.nmem = c.nmem := by rw [hc1]
  have q1 : ∀ q, (q < 241300 ∨ 241308 < q) → c₁.nreg q = c.nreg q := fun q hq => by
    simp_all
  have hA1 : c₁.nreg ALLOC = c.nreg ALLOC := q1 _ (by omega_nf)
  have c0 : c₁.nreg RS = c.nreg lMD := by rw [hc1]; exact p0
  have c1' : c₁.nreg (RS + 1) = c.nreg gBase := by rw [hc1]; exact p1
  have c2' : c₁.nreg (RS + 2) = K := by rw [hc1]; show regB _ _ _ 241302 = _; rw [p2, hgK]
  have c7 : c₁.nreg (RS + 7) = c₀.nreg (sw 5) := by
    rw [hc1]; show regB _ _ _ 241307 = _; rw [p7]; exact hI.hin _ (by omega_nf)
  have c8 : c₁.nreg (RS + 8) = c₀.nreg (sw 10) := by
    rw [hc1]; show regB _ _ _ 241308 = _; rw [p8]; exact hI.hin _ (by omega_nf)
  have hhl : ShotList.holeList c₁ RS = ShotList.holeList c RS := by
    unfold ShotList.holeList ShotList.holeAt
    rw [q1 (RS + 9) (by omega_nf)]
    congr 1
    funext j
    grind [RS]
  have hori : OriginIn c₁ (RS + 3) (.walk x) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hc1]; exact p3
    · rw [hc1]; exact p4
    · rw [hc1]; exact p5
  -- 2. the precondition of the shot
  have hL1 : LCtx P W C N E c₁ := hL.transport (fun r hr => q1 r (by
      grind [lMD, lCD, lNF, TBR, TLR, sw]))
    (fun a _ => by rw [hm1]) hA1.ge
  have hlow : ∀ a, a < c₀.nreg ALLOC → c₁.nmem a = c₀.nmem a := hI₁.hm
  have hX1 : X.holds P c₁.nmem (c₁.nreg (RS + 8)) (c₁.nreg ALLOC) := by
    rw [c8]
    exact X.mono _ _ _ _ _ hI₁.hA (X.local_ _ _ _ _ _ (fun a ha => (hlow a ha).symm) hX)
  have hcap1 : c₁.nreg (RS + 7) ≤ X.cap P c₁.nmem (c₁.nreg (RS + 8)) := by
    rw [c7, c8, hXl P c₀.nmem c₁.nmem _ _ (fun a ha => hlow a ha) hX]; exact hcap
  have hmd := hL1.hmd
  have hm0 := hL1.hm0
  have hmwf := hL1.hmwf
  have hreg := hL1.hctx.hostReg
  obtain ⟨-, -, hwfC, ⟨H, hCD, -⟩, hP, hWm⟩ := hL1.hctx
  have hcd1 := hL1.hcd
  obtain ⟨ho3, ho2, hcov, hnear⟩ := hho
  have h9 : c₁.nreg (RS + 9) = c.nreg 241309 := q1 _ (by omega_nf)
  have hRS1 : c₁.nreg RS + 1 = c₁.nreg lCD := by rw [hcd1, c0, q1 lMD (by omega_nf)]
  have pre : ShotList.ShotPre X Ok RS P W c₁ := by
    refine ⟨hL.hG, hWh, hX1, hcap1, by grind,
      by grind,
      by omega, by omega, H, C, by grind,
      by grind, hOk, hWm, fun j hj => ?_, fun j hj => ?_, .walk x, hori,
      ⟨he, hpp.2.2⟩, Or.inr ⟨Restore.innerPt_chain_walk C (Qof P) he hpp.1 hpp.2.1.le hy,
        fun x' hx' => by grind⟩, hy, ?_⟩
    · rw [c2'] at hj
      rw [c1', hm1, harcs j hj, c7]
      have hmem : (regArcs N rs).getD j 0 ∈ regArcs N rs := getD_mem_of_lt hj
      exact nArc_piece hP hL.hNF hsg (hrs _ hmem)
    · rw [h9] at hj
      rw [q1 (RS + 10 + 2 * j) (by omega_nf), q1 (RS + 11 + 2 * j) (by omega_nf)]
      exact ho2 j hj
    · rw [hhl, c1', c2', hm1]
      refine Restore.avoid_of_cover hcov (fun g hg => ?_) _ _ _
      unfold ShotList.holeList at hg
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hg
      rw [List.mem_range] at hj
      have hj' : j < c.nreg 241309 := by
        have e9 : c.nreg (241300 + 9) = c.nreg 241309 := rfl
        omega
      exact ⟨rfl, (ho2 j hj').1⟩
  -- 3. the shot
  refine IRS.seq (shot_irs hsh hBs hXl hI₁ pre (by grind [shotOfferK])) ?_
    |>.mono (by rw [c7, c2']) (fun _ h => h)
  rintro c₂ hI₂ - hAb ⟨hpost, k2, hA2, hm2⟩
  have hmdC : ModelDescAt c₁.nmem (c₁.nreg RS) (Qof P) (chainModel C) := by
    grind
  obtain ⟨hfl, A, hlo, hhi, hyes, hno⟩ := hpost (chainModel C) (.walk x) hmdC hori
  have hσ6 : dirOf (c₁.nreg (RS + 6)) = σ := by
    rw [hσ]; congr 1; rw [hc1]; exact p6
  rw [hσ6] at hyes hno
  have hev : Origin.eval (chainModel C) (Qof P) (Origin.walk x) = z := rfl
  rw [hev] at hyes hno
  rw [c1', c2', hhl, hm1] at hlo
  rw [c1', c2', hm1] at hhi
  have hAoff : A ⊆ C.domᶜ := by
    intro w hw
    have := hhi hw
    unfold ShotList.hiSet at this
    simp only [Set.mem_iUnion] at this
    obtain ⟨j, -, hj⟩ := this
    exact Sweep.arcSet_subset_compl_dom C hP _ _ hj
  -- registers after the shot
  have keep2 : ∀ r, 240000 ≤ r → r < 250000 → ¬ (RS ≤ r ∧ r < RS + 300) → c₂.nreg r = c₁.nreg r :=
    fun r h1 h2 h3 => k2 r (not_oracle_sw h1 h2) (by omega_nf) h3
  have keepc : ∀ r, 240000 ≤ r → r < 250000 → (r < RS ∨ RS + 299 < r) → c₂.nreg r = c.nreg r :=
    fun r h1 h2 h3 => (keep2 r h1 h2 (by omega)).trans (q1 r (by unfold RS at h3; omega))
  have t2 : c₂.nreg lT = c.nreg lT := keepc _ (by omega_nf) (by omega_nf)
    (by omega_nf)
  have d2 : c₂.nreg lD = c.nreg lD := keepc _ (by omega_nf) (by omega_nf)
    (by omega_nf)
  have n2 : c₂.nreg lN = c.nreg lN := keepc _ (by omega_nf) (by omega_nf)
    (by omega_nf)
  have cd2 : c₂.nreg lCD = c.nreg lCD := keepc _ (by omega_nf) (by omega_nf)
    (by omega_nf)
  have a2 : ∀ j, j ≤ 12 → c₂.nreg (accA + j) = c.nreg (accA + j) := fun j hj =>
    keepc _ (by omega_nf) (by omega_nf) (by omega_nf)
  have hacc2 : AccOK P accA Mod R₀ z σ L c₂ := hacc.transport a2
  have hA2' : c.nreg ALLOC ≤ c₂.nreg ALLOC := hA1 ▸ hA2
  have hm2' : ∀ a, a < c.nreg ALLOC → c₂.nmem a = c.nmem a := fun a ha => by
    rw [hm2 a (by omega), hm1]
  have hctx2 : ChainCtx P W c₂ lCD C := by
    have := hL.hctx
    exact this.transport cd2 hm2' hA2'
  have k0₂ : c₂.nreg K0 = 0 := (hK.fix hI₂).1
  -- the completeness of the shot
  have complete : Merge.FreeAt C z σ → z.2 ≤ C.top.2 →
      rayPt z σ (C.hitParam z σ) ∈
        ShotList.loSet (chainModel C) (Qof P) c.nmem (c.nreg gBase) K (ShotList.holeList c RS) →
      c₂.nreg 241320 = 1 ∧ ∀ t, FirstHit A z σ t → t = C.hitParam z σ := by
    intro hf hzt hlo'
    have hTA := hlo hlo'
    refine ⟨?_, fun t ht => firstHit_exit C hσ' hzt hf hAoff ht hTA⟩
    by_contra hne
    obtain ⟨hT0, -, -⟩ := Merge.hit_of_freeAt C hzt hσ' hf
    exact hno hne _ hT0 hTA
  unfold lhOffer
  have hfl' : c₂.nreg 241320 ≤ 1 := hfl
  by_cases hflag : c₂.nreg K0 < c₂.nreg 241320
  · rw [k0₂] at hflag
    have h1 : c₂.nreg 241320 = 1 := by omega
    obtain ⟨t, hFH, hpp2, he2, hpos2⟩ := hyes h1
    have hroom2 : c₂.nreg ALLOC + offerFK ≤ W := by
      rw [c7, c2', hA1] at hAb; unfold shotOfferK at hroom; omega
    refine (IRS.ifT (by omega) (offerF_irs (L := L) (τ := t) (Mod := Mod) hI₂ hK hL.hG
      (by unfold hostWords at hWh; omega)
      ⟨by omega_nf, by omega_nf⟩
      ⟨by omega_nf, by omega_nf, by norm_num, by norm_num, by norm_num,
        by norm_num, by omega_nf, by omega_nf, by omega_nf,
        by omega_nf, by omega_nf, by omega_nf,
        by omega_nf, by omega_nf⟩
      ⟨by norm_num, by omega_nf, by omega_nf, by omega_nf,
        by omega_nf, by omega_nf, by omega_nf,
        by omega_nf, by omega_nf, by omega_nf,
        by omega_nf, by omega_nf, by omega_nf,
        by omega_nf, by omega_nf, by omega_nf,
        by omega_nf⟩
      ⟨by omega_nf, by omega_nf, by omega_nf,
        by omega_nf, by omega_nf, by omega_nf⟩
      (by rw [d2]; exact hacc2) (by omega) (by grind [Chazelle.Core.SweepIo.ChainCtx])
      (by rw [t2, hMod]; exact hR) (by rw [n2, hn, t2, hMod]) (by rw [t2, hMod]; exact he2)
      (by rw [t2, hMod]; exact hpp2) (by rw [t2, hMod, d2]; exact hpos2) (by grind)
      hroom2)).mono (by omega) ?_
    rintro c' ⟨⟨L', hacc', hL', hcomp⟩, k3, hA3, hm3⟩
    simp only [d2, t2, hMod] at hacc' hL' hcomp
    refine ⟨L', hacc', ?_, fun hf hzt hlo' => ?_, fun r hr hrs hra hro hro1 hrA => ?_,
      hA2'.trans hA3, fun a ha => by rw [hm3 a (by omega)]; exact hm2' a ha⟩
    · rcases hL' with h | ⟨h, hg⟩
      · exact Or.inl h
      · exact Or.inr ⟨t, h, hFH.1, hg⟩
    · obtain ⟨-, ht⟩ := complete hf hzt hlo'
      rw [hcomp hzt, ← ht t hFH]
      exact Set.mem_insert _ _
    · rw [k3 r hr hra (fun h => hrs (by subst h; omega_nf)) hro hro1 hrA,
        k2 r hr hrA hrs]
      exact q1 r (by unfold RS at hrs; omega)
  · refine (IRS.ifF hflag (IRS.skip (K := offerFK) hI₂ ⟨L, hacc2, Or.inl rfl, fun hf hzt hlo' => ?_,
      fun r hr hrs hra hro hro1 hrA => ?_, hA2', hm2'⟩)).mono (by omega) (fun _ h => h)
    · rw [k0₂] at hflag
      grind
    · rw [k2 r hr hrA hrs]
      exact q1 r (by unfold RS at hrs; omega)

end

end SweepIo

end Chazelle.Core
