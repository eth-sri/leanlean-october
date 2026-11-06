module

public import Chazelle.Core.SweepIoPrim
public import Chazelle.Core.OracleRamLoc
public import Chazelle.Core.Facts2
public import Chazelle.Core.ShootCutShPt
public import Chazelle.Core.RestoreTNorm
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.ChainTactics
set_option maxRecDepth 20000

/-!
# The sweep RAM (WP-D), answers: building blocks of the local hit

* `normS`: normalising a walk position in place (height code `0` exactly at parameter `0`), by a
  key comparison of `(e, 0)` and `(e, h)` (`offCmp`); positions on the box edges need no test.
* `locJ`: double identification with the spine position (`OracleR.myLoc`, with the table of
  powers of the answer stage).
-/

namespace Chazelle.Core

namespace SweepIo

open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed
open Chazelle.Chain (sidePt sideLeft sideInArc)

@[expose] public section

/-! ## Constants of the answer stage -/

/-- The constant registers of the answer stage (set by its initialisation). -/
def K0 : ℕ := sw 610
def K1 : ℕ := sw 611
def K6 : ℕ := sw 612
def K4 : ℕ := sw 613
def K5 : ℕ := sw 614
def K2 : ℕ := sw 615
def K3 : ℕ := sw 616

/-- The constants hold their values. -/
def Consts (c : Config) : Prop :=
  c.nreg K0 = 0 ∧ c.nreg K1 = 1 ∧ c.nreg K6 = 6 ∧ c.nreg K4 = 4 ∧ c.nreg K5 = 5 ∧
    c.nreg K2 = 2 ∧ c.nreg K3 = 3

theorem Consts.fix {c₀ c : Config} {W : ℕ} (h : Consts c₀) (hI : IInv W c₀ c) : Consts c := by
  have k : ∀ i, 610 ≤ i → i ≤ 616 → c.nreg (sw i) = c₀.nreg (sw i) := fun i h1 h2 =>
    hI.hin _ (by ufo IFix sw)
  obtain ⟨a, b, d, e, f, g, i⟩ := h
  exact ⟨(k 610 le_rfl (by norm_num)).trans a, (k 611 (by norm_num) (by norm_num)).trans b,
    (k 612 (by norm_num) (by norm_num)).trans d, (k 613 (by norm_num) (by norm_num)).trans e,
    (k 614 (by norm_num) (by norm_num)).trans f, (k 615 (by norm_num) (by norm_num)).trans g,
    (k 616 (by norm_num) le_rfl).trans i⟩

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-! ## Normalising a position -/

/-- The box rule: on the horizontal box edges `0, 2, 4` the height code becomes `0`. -/
def normBox (pe ph : ℕ) : Stmt :=
  .ifLtN pe K1 (.instr (.constN ph 0))
    (.ifLtN pe K2 .skip
      (.ifLtN pe K3 (.instr (.constN ph 0))
        (.ifLtN pe K4 .skip
          (.ifLtN pe K5 (.instr (.constN ph 0)) .skip))))

/-- **Normalise the position `(pe, ph)` in place**: on a walk edge `≥ 6`, compare the keys of
`(pe, 0)` and `(pe, ph)` (bits at `o`, `o + 1`) and set `ph := 0` unless the parameter is
positive; on the box edges apply `normBox`. -/
def normS (dsc pe ph o : ℕ) : Stmt :=
  .ifLtN pe K6 (normBox pe ph)
    (.seq (callOff dsc pe K0 pe ph K0 o) (.ifLtN K0 o .skip (.instr (.constN ph 0))))

/-- The normalised height code of a position. -/
noncomputable def nhgt (M : Model) (Q : Polygon) (u : WPos) : ℕ := (Restore.normOf M Q u).hgt

theorem normS_irs {dsc pe ph o : ℕ} {C : Chain} (hI : IInv W c₀ c) (hK : Consts c)
    (hctx : ChainCtx P W c dsc C)
    (hr : 240000 ≤ dsc ∧ dsc < 250000 ∧ 240700 ≤ pe ∧ pe < 250000 ∧ 240700 ≤ ph ∧ ph < 250000)
    (ho : 240700 ≤ o ∧ o + 1 < 250000 ∧ o ≠ pe ∧ o ≠ ph ∧ o + 1 ≠ pe ∧ o + 1 ≠ ph ∧ pe ≠ ph)
    (he : c.nreg pe < (chainModel C).W.n)
    (hpp : ProperPos (chainModel C) (Qof P) P.n ⟨c.nreg pe, c.nreg ph⟩)
    (hy : c.nreg pe < 6 → c.nreg pe ≠ 0 → c.nreg pe ≠ 2 → c.nreg pe ≠ 4 →
      |((chainModel C).pos (Qof P) ⟨c.nreg pe, c.nreg ph⟩).2| < C.radius)
    (hroom : c.nreg ALLOC + 11015 ≤ W) :
    IRS P W c₀ (normS dsc pe ph o) c 11015
      (fun c' => c'.nreg pe = c.nreg pe ∧
        c'.nreg ph = nhgt (chainModel C) (Qof P) ⟨c.nreg pe, c.nreg ph⟩ ∧
        (∀ r, bandOf r ∉ oracleBands → r ≠ ph → r ≠ o → r ≠ o + 1 → r ≠ ALLOC →
          c'.nreg r = c.nreg r) ∧
        c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a)) := by
  obtain ⟨k0, k1, k6, k4, k5, k2, k3⟩ := hK
  have hK0 : K0 = 240610 := rfl
  have hK6 : K6 = 240612 := rfl
  set u : WPos := ⟨c.nreg pe, c.nreg ph⟩ with hu
  unfold normS
  by_cases hbox : c.nreg pe < c.nreg K6
  · refine (IRS.ifT hbox ?_).mono (K := 11013) (by omega) (fun _ => id)
    rw [k6] at hbox
    -- the horizontal box edges: the code becomes `0`
    have hzero : (c.nreg pe = 0 ∨ c.nreg pe = 2 ∨ c.nreg pe = 4) →
        IRS P W c₀ (.instr (.constN ph 0)) c 1 (fun c' => c'.nreg pe = c.nreg pe ∧
          c'.nreg ph = nhgt (chainModel C) (Qof P) ⟨c.nreg pe, c.nreg ph⟩ ∧
          (∀ r, bandOf r ∉ oracleBands → r ≠ ph → r ≠ o → r ≠ o + 1 → r ≠ ALLOC →
            c'.nreg r = c.nreg r) ∧
          c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a)) := by
      intro he0
      have hpar : (chainModel C).param (Qof P) u = 0 :=
        Model.param_horizontal (ShootCut.box_horizontal (C := C) he0)
      refine (IRS.reg hI (iscr_sw hr.2.2.2.2.1 hr.2.2.2.2.2)
        (Exec.constN hI.hw ph 0 (Nat.zero_le _))).mono le_rfl ?_
      rintro c' rfl
      simp only
      refine ⟨by rw [upd_other _ _ _ ho.2.2.2.2.2.2], by
        rw [upd_same]; unfold nhgt Restore.normOf; rw [ite_eq_left hpar], fun r hr1 hr2 hr3 hr4 hr5 => ?_,
        by rw [upd_other _ _ _ (by ufo ALLOC)], fun _ _ => by simp⟩
      rw [upd_other _ _ _ hr2]
    -- the other box edges: the code is kept
    have hkeep : (c.nreg pe = 1 ∨ c.nreg pe = 3 ∨ c.nreg pe = 5) →
        IRS P W c₀ .skip c 0 (fun c' => c'.nreg pe = c.nreg pe ∧
          c'.nreg ph = nhgt (chainModel C) (Qof P) ⟨c.nreg pe, c.nreg ph⟩ ∧
          (∀ r, bandOf r ∉ oracleBands → r ≠ ph → r ≠ o → r ≠ o + 1 → r ≠ ALLOC →
            c'.nreg r = c.nreg r) ∧
          c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a)) := by
      intro he1
      refine IRS.skip hI ⟨rfl, ?_, fun _ _ _ _ _ _ => rfl, le_rfl, fun _ _ => rfl⟩
      have hpos := ShootCut.box_param_pos' C (Qof P) hbox hpp.1
        (hy hbox (by omega) (by omega) (by omega))
      unfold nhgt Restore.normOf
      rw [ite_eq_right hpos.ne']
    unfold normBox
    rcases (by omega : c.nreg pe = 0 ∨ c.nreg pe = 1 ∨ c.nreg pe = 2 ∨ c.nreg pe = 3 ∨
      c.nreg pe = 4 ∨ c.nreg pe = 5) with h | h | h | h | h | h
    · exact (IRS.ifT (by rwn [k1, h]) (hzero (Or.inl h))).mono (by omega) (fun _ => id)
    · exact (IRS.ifF (by rwn [k1, h]) (IRS.ifT (by rwn [k2, h])
        (hkeep (Or.inl h)))).mono (by omega) (fun _ => id)
    · exact (IRS.ifF (by rwn [k1, h]) (IRS.ifF (by rwn [k2, h])
        (IRS.ifT (by rwn [k3, h]) (hzero (Or.inr (Or.inl h)))))).mono (by omega)
        (fun _ => id)
    · exact (IRS.ifF (by rwn [k1, h]) (IRS.ifF (by rwn [k2, h])
        (IRS.ifF (by rwn [k3, h]) (IRS.ifT (by rwn [k4, h])
          (hkeep (Or.inr (Or.inl h))))))).mono (by omega) (fun _ => id)
    · exact (IRS.ifF (by rwn [k1, h]) (IRS.ifF (by rwn [k2, h])
        (IRS.ifF (by rwn [k3, h]) (IRS.ifF (by rwn [k4, h])
          (IRS.ifT (by rwn [k5, h]) (hzero (Or.inr (Or.inr h)))))))).mono (by omega)
        (fun _ => id)
    · exact (IRS.ifF (by rwn [k1, h]) (IRS.ifF (by rwn [k2, h])
        (IRS.ifF (by rwn [k3, h]) (IRS.ifF (by rwn [k4, h])
          (IRS.ifF (by rwn [k5, h]) (hkeep (Or.inr (Or.inr h)))))))).mono (by omega)
        (fun _ => id)
  · refine IRS.mono (K := 11013) (IRS.ifF hbox ?_) (by omega) (fun _ => id)
    rw [k6] at hbox
    have hn6 : 6 ≤ c.nreg pe := by omega
    have hn0 : 0 < (chainModel C).W.n := by omega
    refine IRS.seq (K₂ := 3) (callOff_irs (dsc := dsc) (ex := pe) (hx := K0) (ey := pe) (hy := ph)
      (g := K0) (o := o) hI hctx ⟨hr.1, hr.2.1, by omega, hr.2.2.2.1, by rwn [hK0],
      by rwn [hK0], by omega, hr.2.2.2.1, by omega, hr.2.2.2.2.2, by rwn [hK0],
      by rwn [hK0]⟩
      ⟨ho.1, ho.2.1⟩ he he (by rwx [k0]) ?_ hpp (fun _ => hn6)
      (fun h0 => hn6) (by omega)) ?_
    · rw [k0]; exact ⟨le_rfl, by norm_num, Nat.zero_le _⟩
    rintro c₁ hI₁ hA₁ hA₁' ⟨b0, -, hk1, -, hm1⟩
    rw [k0] at b0
    have hlt := (off_lt_iff (chainModel C) (Qof P) (g := 0) hn0 (x := (⟨c.nreg pe, 0⟩ : WPos)) (y := u)
      he le_rfl (by norm_num) he hpp.1 hpp.2.1)
    simp only at hlt
    have h10 : c₁.nreg K0 = 0 := by
      rw [hk1 _ (not_oracle_sw (by rwn [hK0]) (by rwn [hK0])) (by rwo [hK0])
        (by rwo [hK0]) (by ruo [hK0] ALLOC), k0]
    have hpe1 : c₁.nreg pe = c.nreg pe := hk1 _ (not_oracle_sw (by omega) (by omega)) (by omega)
      (by omega) (by ufo ALLOC)
    have hph1 : c₁.nreg ph = c.nreg ph := hk1 _ (not_oracle_sw (by omega) (by omega)) (by omega)
      (by omega) (by ufo ALLOC)
    by_cases hb : c₁.nreg K0 < c₁.nreg o
    · refine (IRS.ifT hb (IRS.skip (K := 1) hI₁ ?_)).mono (by omega) (fun _ => id)
      rw [h10] at hb
      have hbit : c₁.nreg o = 1 := by have := b0.1; omega
      have hp := (b0.2.1 hbit)
      rw [hlt] at hp
      have hpar : 0 < (chainModel C).param (Qof P) u := by
        rcases hp with hp | ⟨-, hp⟩
        · exact absurd hp (lt_irrefl _)
        · exact hp
      refine ⟨hpe1, ?_, fun r hr1 hr2 hr3 hr4 hr5 => hk1 r hr1 hr3 hr4 hr5, hA₁, hm1⟩
      rw [hph1]; unfold nhgt Restore.normOf; rw [ite_eq_right hpar.ne']
    · refine IRS.mono (K := 1 + 2) (IRS.ifF hb ?_) (by omega) (fun _ => id)
      rw [h10] at hb
      have hbit : c₁.nreg o ≠ 1 := by omega
      have hpar : (chainModel C).param (Qof P) u = 0 := by
        by_contra hne
        exact hbit ((b0.2).2 ((hlt).2 (Or.inr ⟨rfl, lt_of_le_of_ne hpp.1 (Ne.symm hne)⟩)))
      refine (IRS.reg hI₁ (iscr_sw hr.2.2.2.2.1 hr.2.2.2.2.2)
        (Exec.constN hI₁.hw ph 0 (Nat.zero_le _))).mono le_rfl ?_
      rintro c' rfl
      simp only
      refine ⟨by rwx [upd_other _ _ _ ho.2.2.2.2.2.2], by
        rw [upd_same]; unfold nhgt Restore.normOf; rw [ite_eq_left hpar], fun r hr1 hr2 hr3 hr4 hr5 => ?_,
        by rwx [upd_other _ _ _ (by ufo ALLOC)], hm1⟩
      rw [upd_other _ _ _ hr2]; exact hk1 r hr1 hr3 hr4 hr5
/-! ## Double identification with the spine position -/

/-- The table of powers of two of the answer stage (base and length). -/
def TBR : ℕ := sw 600
def TLR : ℕ := sw 601

theorem band12_oracle {r : ℕ} (h1 : 120000 ≤ r) (h2 : r < 130000) : bandOf r ∈ oracleBands := by
  have : bandOf r = bOQuery := by ufo bandOf bOQuery
  rwd [this]

theorem band1_oracle {r : ℕ} (h1 : 10000 ≤ r) (h2 : r < 20000) : bandOf r ∈ oracleBands := by
  have : bandOf r = bSign := by ufo bandOf bSign
  rwd [this]

theorem bl_oracle {r : ℕ} (h : OracleR.BL r = true) : bandOf r ∈ oracleBands := by
  simp only [OracleR.BL, NFLoc.Bdir, NFLoc.Bloc, WalkKey.Bcmp, WalkKey.Bk, Bool.or_eq_true,
    decide_eq_true_eq] at h
  by_cases h1 : r < 20000
  · exact band1_oracle (by omega) h1
  by_cases h5 : r < 60000
  · exact band5_oracle (by omega) h5
  · exact band12_oracle (by omega) (by omega)

/-- **An oracle-framed run** as an answer-stage step: it writes only oracle registers, keeps the
memory and emits nothing. -/
theorem IRS.ofFrameB {s : Stmt} {B : ℕ → Bool} {c' : Config} {k K : ℕ} {Q : Config → Prop}
    (hI : IInv W c₀ c) (ex : Exec P W s c c' k) (hk : k ≤ K) (fr : SignK.FrameB B c c')
    (hB : ∀ r, B r = true → bandOf r ∈ oracleBands) (hq : Q c') : IRS P W c₀ s c K Q := by
  have hf : ∀ r, bandOf r ∉ oracleBands → B r = false := fun r hr => by
    cases h : B r
    · rfl
    · exact absurd (hB r h) hr
  have hA : c'.nreg ALLOC = c.nreg ALLOC := fr.1 _ (hf _ (by decide))
  refine ⟨c', k, ex, hk, ⟨ex.wb_right, fun q hq' => ?_, by rw [hA]; exact hI.hA,
    fun a ha => by rw [fr.2.2.1]; exact hI.hm a ha,
    fun a ha => by rw [fr.2.2.2.1]; exact hI.hrm a ha⟩,
    ⟨fun r hr _ => fr.1 r (hf r (fun h => hr (oracle_sub h))),
      fun r hr => fr.2.1 r (hf r (fun h => hr (oracle_sub h))), fr.2.2.2.2, by rw [hA],
      by rwo [hA]⟩, hq⟩
  rw [fr.1 q (hf q (fun h => fix_not_scr hq' (Or.inr h)))]
  exact hI.hin q hq'

/-- **Double identification** of the position `(pe, ph)` in the normal form at `nf` of the model
of the descriptor at `md`, leaving the spine position in `o`. -/
def locJ (md nf pe ph o : ℕ) : Stmt :=
  .seq (block (cps [(50000, md), (50001, nf), (50002, pe), (50003, ph), (120041, TBR),
      (120042, TLR)] ++ [.constN 120012 0, .constN 120011 1]))
    (.seq OracleR.myLoc (.instr (.copyN o 120170)))

theorem locJ_irs {md nf pe ph o : ℕ} {C : Chain} {N : NF} (hI : IInv W c₀ c)
    (hG : GoodEnv P) (hWh : hostWords P.n ≤ W)
    (hr : 240000 ≤ md ∧ md < 250000 ∧ 240000 ≤ nf ∧ nf < 250000 ∧ 240000 ≤ pe ∧ pe < 250000 ∧
      240000 ≤ ph ∧ ph < 250000) (ho : 240700 ≤ o ∧ o < 250000)
    (hmd : ModelDescAt c.nmem (c.nreg md) (Qof P) (chainModel C))
    (hmwf : ModelDescWF P (c.nreg ALLOC) c.nmem (c.nreg md)) (hP : C.P.Simple)
    (hN : NFAt c.nmem (c.nreg nf) N) (hNF : IsNF (chainModel C) (Qof P) N)
    (he : c.nreg pe < (chainModel C).W.n)
    (hpp : ProperPos (chainModel C) (Qof P) P.n ⟨c.nreg pe, c.nreg ph⟩)
    (htab : ∀ j, j < c.nreg TLR → c.nmem (c.nreg TBR + j) = 2 ^ j)
    (hbig : N.arcs.length < 2 ^ c.nreg TLR) (hB : c.nreg nf + 7 ≤ c.nreg TBR)
    (hAB : c.nmem (c.nreg nf + 4) + 5 * N.arcs.length ≤ c.nreg TBR)
    (hSB : c.nmem (c.nreg nf + 6) + N.arcs.length ≤ c.nreg TBR)
    (hTW : c.nreg TBR + c.nreg TLR ≤ W)
    (_hroom : c.nreg ALLOC + (5500 * (c.nreg TLR + 1) + 9) ≤ W) :
    IRS P W c₀ (locJ md nf pe ph o) c (5500 * (c.nreg TLR + 1) + 9)
      (fun c' => c'.nreg o < N.arcs.length ∧
        (¬ (chainModel C).IsCut (N.F (chainModel C) (Qof P))
            ((chainModel C).key (Qof P) ⟨c.nreg pe, c.nreg ph⟩) →
          N.F (chainModel C) (Qof P) = ∅ ∨
            sideInArc (OracleQ.sk (chainModel C) (Qof P) N (c'.nreg o))
              (OracleQ.ek (chainModel C) (Qof P) N (c'.nreg o))
              ((chainModel C).key (Qof P) ⟨c.nreg pe, c.nreg ph⟩)) ∧
        ((chainModel C).IsCut (N.F (chainModel C) (Qof P))
            ((chainModel C).key (Qof P) ⟨c.nreg pe, c.nreg ph⟩) →
          OracleQ.sk (chainModel C) (Qof P) N (c'.nreg o) =
              (chainModel C).key (Qof P) ⟨c.nreg pe, c.nreg ph⟩ ∨
            OracleQ.ek (chainModel C) (Qof P) N (c'.nreg o) =
              (chainModel C).key (Qof P) ⟨c.nreg pe, c.nreg ph⟩) ∧
        (∀ r, bandOf r ∉ oracleBands → r ≠ o → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
        c'.nreg ALLOC = c.nreg ALLOC ∧ c'.nmem = c.nmem) := by
  have hTB : TBR = 240600 := rfl
  have hTL : TLR = 240601 := rfl
  unfold locJ
  set ins := [(50000, md), (50001, nf), (50002, pe), (50003, ph), (120041, TBR), (120042, TLR)]
    with hins
  have hnd : (ins.map Prod.fst).Nodup := by simp [hins]
  have hsrc : ∀ p ∈ ins, ∀ q ∈ ins, p.2 ≠ q.1 := by
    simp only [hins, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      hTB, hTL]; omega
  -- the setup block
  have hTBv : c.nreg TBR = c.nreg 240600 := rfl
  have hTLv : c.nreg TLR = c.nreg 240601 := rfl
  set l : List Instr := cps ins ++ [.constN 120012 0, .constN 120011 1] with hl
  have hok : okB W c.nmem l c.nreg := by
    simp only [hl, hins, cps, List.map, List.cons_append, List.nil_append, okB, okI]
    refine ⟨Or.inr (band5_oracle (by norm_num) (by norm_num)),
      Or.inr (band5_oracle (by norm_num) (by norm_num)),
      Or.inr (band5_oracle (by norm_num) (by norm_num)),
      Or.inr (band5_oracle (by norm_num) (by norm_num)),
      Or.inr (band12_oracle (by norm_num) (by norm_num)),
      Or.inr (band12_oracle (by norm_num) (by norm_num)),
      ⟨Or.inr (band12_oracle (by norm_num) (by norm_num)), Nat.zero_le _⟩,
      ⟨Or.inr (band12_oracle (by norm_num) (by norm_num)), ?_⟩, trivial⟩
    have := hWh; ufo hostWords at this
  have hlen : l.length = 8 := by simp [hl, hins, cps]
  refine IRS.mono (K := l.length + (5500 * (c.nreg TLR + 1) + 1))
    (IRS.seq (IRS.block l hI hok) ?_) (by rwo [hlen]) (fun _ => id)
  rintro c₁ hI₁ hA₁ hA₁' rfl
  set c₁ : Config := { c with nreg := regB c.nmem l c.nreg } with hc₁
  have hreg : ∀ r, c₁.nreg r = (if r = 120011 then 1 else if r = 120012 then 0 else
      if r = 120042 then c.nreg TLR else if r = 120041 then c.nreg TBR else
      if r = 50003 then c.nreg ph else if r = 50002 then c.nreg pe else
      if r = 50001 then c.nreg nf else if r = 50000 then c.nreg md else c.nreg r) := by
    intro r
    show regB c.nmem l c.nreg r = _
    simp only [hl, hins, cps, List.map, List.cons_append, List.nil_append, regB, regI]
    simp only [upd]
    have h1 : md ≠ 50000 := by omega
    have h2 : nf ≠ 50000 ∧ nf ≠ 50001 := by omega
    have h3 : pe ≠ 50000 ∧ pe ≠ 50001 ∧ pe ≠ 50002 := by omega
    have h4 : ph ≠ 50000 ∧ ph ≠ 50001 ∧ ph ≠ 50002 ∧ ph ≠ 50003 := by omega
    have h5 : (240600 : ℕ) ≠ 50000 ∧ (240600 : ℕ) ≠ 50001 ∧ (240600 : ℕ) ≠ 50002 ∧
      (240600 : ℕ) ≠ 50003 := by omega
    have h6 : (240601 : ℕ) ≠ 50000 ∧ (240601 : ℕ) ≠ 50001 ∧ (240601 : ℕ) ≠ 50002 ∧
      (240601 : ℕ) ≠ 50003 ∧ (240601 : ℕ) ≠ 120041 := by omega
    simp only [TBR, TLR, sw, ite_eq_right h2.1, ite_eq_right h3.1, ite_eq_right h3.2.1,
      ite_eq_right h4.1, ite_eq_right h4.2.1, ite_eq_right h4.2.2.1]
    split_ifs <;> first | rfl | omega
  have r00 : c₁.nreg 50000 = c.nreg md := by rws [hreg]
  have r01 : c₁.nreg 50001 = c.nreg nf := by rws [hreg]
  have r02 : c₁.nreg 50002 = c.nreg pe := by rws [hreg]
  have r03 : c₁.nreg 50003 = c.nreg ph := by rws [hreg]
  have r41 : c₁.nreg 120041 = c.nreg TBR := by rws [hreg]
  have r42 : c₁.nreg 120042 = c.nreg TLR := by rws [hreg]
  have r12 : c₁.nreg 120012 = 0 := by rws [hreg]
  have r11 : c₁.nreg 120011 = 1 := by rws [hreg]
  have rother : ∀ r, bandOf r ∉ oracleBands → c₁.nreg r = c.nreg r := by
    intro r hr
    rw [hreg]
    have h5 : r < 50000 ∨ 60000 ≤ r := by
      by_contra h'; push Not at h'; exact hr (band5_oracle h'.1 h'.2)
    have h12 : r < 120000 ∨ 130000 ≤ r := by
      by_contra h'; push Not at h'; exact hr (band12_oracle h'.1 h'.2)
    have : r ≠ 120011 ∧ r ≠ 120012 ∧ r ≠ 120042 ∧ r ≠ 120041 ∧ r ≠ 50003 ∧ r ≠ 50002 ∧
        r ≠ 50001 ∧ r ≠ 50000 := by omega
    simp [this.1, this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2.1, this.2.2.2.2.2.1,
      this.2.2.2.2.2.2.1, this.2.2.2.2.2.2.2]
  have hm₁ : c₁.nmem = c.nmem := rfl
  have hA1 : c₁.nreg ALLOC = c.nreg ALLOC := rother ALLOC (by decide)
  clear_value c₁
  clear hreg hc₁
  -- the locate call
  have hW3 : P.n + 3 ≤ W := by ufo hostWords at hWh
  obtain ⟨hD6, hLW⟩ := NFLoc.locChainWF_of hmwf (by have := hI.hw.1 ALLOC; omega) hWh
  have hD : NFLoc.LocDPre P W c₁ := ⟨hG, hW3, by rwx [r00],
    by rwx [r00, hm₁], chainModel C, by rwx [r00, hm₁], by rwx [r02]⟩
  have hst : ∀ j, j < N.arcs.length → ProperPos (chainModel C) (Qof P) P.n (N.arc j).s := by
    intro j hj
    obtain ⟨_, -, -, -, -, -, -, hpr⟩ := hNF.2.2.2
    have := (hpr j hj).1
    rwa [show (Qof P).n = P.n from shear_n _ _] at this
  obtain ⟨c₂, k₂, e₂, hk₂, fr₂, hj₂, hl1, hl2⟩ := OracleR.myLoc_exec arcCover (P := P) (W := W)
    (c := c₁) hI₁.hw hD hG hW3 (M := chainModel C) (N := N) (by rwx [r00, hm₁])
    (Or.inl ⟨C, hP, rfl⟩) (by rwx [r01, hm₁]) hNF (by rwx [r02, r03]) hst
    r41 r42 r12 r11 (fun j hj => by rw [hm₁]; exact htab j hj) hbig
    (by rwx [r01]) (by rwx [r01, hm₁]) (by rwx [r01, hm₁]) hTW
  have hfo : ∀ r, bandOf r ∉ oracleBands → c₂.nreg r = c₁.nreg r := fun r hr => fr₂.1 r (by
    cases h : OracleR.BL r
    · rfl
    · exact absurd (bl_oracle h) hr)
  refine IRS.seq (K₁ := 5500 * (c.nreg TLR + 1)) (IRS.ofFrameB hI₁ e₂ hk₂
    fr₂ (fun r h => bl_oracle h) (Q := fun c' => c' = c₂) rfl) ?_ |>.mono le_rfl (fun _ => id)
  rintro c₃ hI₃ - - rfl
  refine IRS.mono (IRS.reg (r := o) hI₃ (iscr_sw ho.1 ho.2)
    (Exec.copyN hI₃.hw o 120170)) le_rfl ?_
  rintro c' rfl
  simp only [upd]
  rw [r02, r03] at hl1 hl2
  refine ⟨hj₂, fun h => ?_, fun h => ?_, fun r hr hro hra => ?_, ?_, fr₂.2.2.1.trans hm₁⟩
  · exact hl1 h
  · exact hl2 h
  · rw [ite_eq_right hro, hfo r hr, rother r hr]
  · rw [ite_eq_right (show ALLOC ≠ o from fun h => absurd ho.1 (by rwd [← h])),
      hfo ALLOC (by decide), hA1]

end

end SweepIo

end Chazelle.Core
