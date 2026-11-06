module

public import Chazelle.MacT
public import Chazelle.Core.DownPhaseOracleCuR1
public import Chazelle.Core.RestoreTHoleChain
public import Chazelle.Core.ShotListGLeaf
public import Chazelle.Core.SweepPrimJun
public import Chazelle.Core.DownPhaseOracleChR2
public import Chazelle.Core.ShootCutGrade
public import Chazelle.Core.DownPhaseOracleTop
public import Chazelle.Core.RestoreTPos
public import Chazelle.Mountain.PieceSteps

namespace Chazelle.Core
namespace SweepIo
@[expose] public section
open Machine Machine.Stmt Programs SweepPrim SignK
open Chazelle.Chain (sideE sidePt)
open Restore (Cover Near eHole vHole prevV cover_chain_vertex cover_chain_edge near_eHole
  near_vHole key_hole eHole_mem vHole_mem)
variable {P : Polygon} {W : ℕ}

/-- **Where the candidate of a chain model lies**: at a tour vertex, or inside a tour edge. -/
theorem chain_x_cases {C : Chain} {Q : Polygon} {n : ℕ} {x : WPos}
    (hx : ProperPos ztc Q n x) (he : x.edge < (chainModel C).W.n)
    (hxc : x.hgt = 0 ∨ 0 < (chainModel C).param Q x) (hz : (chainModel C).pos Q x ∈ C.set) :
    6 ≤ x.edge ∧
      (x.hgt = 0 → x.edge - 6 ≤ 2 * C.m ∧
        (chainModel C).pos Q x = C.vertex ztyop) ∧
      (0 < x.hgt → x.edge - 6 < 2 * C.m ∧ 0 < (chainModel C).param Q x ∧
        (chainModel C).param Q x < 1) := by
  zucn
  have hpos : (chainModel C).pos Q x = sidePt ztcs x.edge
      _ := rfl
  zubmb

  · zufsc
  refine ztxzi
  · have hp0 : ztmrc := by
      zudei
    zuedg

  · grind
  grind

/-! ## The holes as a list -/
theorem holeList_one (c : Config) (h : c.nreg 241309 = 1) :
    ShotList.holeList c 241300 = [ShotList.holeAt c 241300 0] := by
  simp [ShotList.holeList, h]

/-! ## The contract -/

/-- **The holes in the registers** `241309 … 241315` are proper and cover the point `z`. -/
def HoleOut (M : Model) (Q : Polygon) (c : Config) (z : Point) : Prop :=
  c.nreg 241309 ≤ 3 ∧
    (∀ j < c.nreg 241309, c.nreg ztgyt < M.W.n ∧
      c.nreg ztgyu < M.W.n ∧ c.nreg ztgyt ≠ c.nreg ztgyu) ∧
    Cover M Q zttcz z ∧ Near M Q zttcz z

/-- The scratch registers of `holeS`. -/
def holeL : List ℕ := chainHL ++ [243092, 243093]
theorem holeAt_eq (c : Config) (j : ℕ) :
    ShotList.holeAt c 241300 j = (⟨c.nreg ztgyt, 0⟩, ⟨c.nreg ztgyu, 0⟩) :=
  rfl

/-! ## Hole arithmetic -/
variable {c : Config}
theorem hole_mem {j : ℕ} (hj : j < c.nreg 241309) (h3 : c.nreg 241309 ≤ 3) :
    ShotList.holeAt c 241300 j ∈ ShotList.holeList c 241300 :=
  List.mem_map.2 by_grind
theorem vHole_six {n c : ℕ} (h : c + 6 < n) : vHole n ztthh = ztyga := by
  zucah
theorem vtx_hole_ne {m c : ℕ} (hc : c ≤ 2 * m) : c + 5 ≠ ztfqb % ztfk := by
  zuidu
  · zuczo
  · zudap
theorem sOf_sideS {C : Chain} {b : ℕ} (hb : b = 1 ↔ C.sideBeta = true) :
    sOf C.m C.topIdx b = C.sideS C.sideBeta := by
  zumuk
set_option maxHeartbeats 1600000 in
/-- **The holes of a position in a chain model** (`chainH`): pairs of distinct walk vertices
covering its point, near it; only the scratch registers `holeL` change.  The position
`x = (243005, 243006)` is normalised (height code `0` exactly at a walk vertex) and its point lies
on the chain; `243020` holds the address of the chain descriptor, `243022 = 0`, `243023 = 1`. -/
theorem chainH_exec (hw : WordsBounded W c) {H : Host} {C : Chain}
    (hC : ChainDescAt c.nmem (c.nreg 243020) zta H C)
    (hwf : c.nreg 243020 + 5 ≤ c.nreg ALLOC) (hsimp : C.P.Simple) (hWm : 2 * C.m + 7 ≤ W)
    (h22 : c.nreg 243022 = 0) (h23 : c.nreg 243023 = 1)
    (hxp : ProperPos ztc zta P.n ztgom)
    (hxe : c.nreg 243005 < (chainModel C).W.n)
    (hxc : c.nreg 243006 = 0 ∨ 0 < (chainModel C).param zta ztgom)
    (hxC : (chainModel C).pos zta ztgom ∈ C.set) :
    ∃ c' k, Exec P W chainH c c' k ∧ k ≤ 100 ∧ HoleOut ztc zta c'
      ((chainModel C).pos zta ztgom) ∧ Out c c' holeL := by
  set c₀ := c with hc₀
  have h05 : c.nreg 243005 = c₀.nreg 243005 := rfl
  have h06 : c.nreg 243006 = c₀.nreg 243006 := rfl
  zubb
  zuet
  -- the candidate
  set x : WPos := ⟨c₀.nreg 243005, c₀.nreg 243006⟩ with hxdef
  obtain ⟨he6, hvtx, hedge⟩ := chain_x_cases hxp hxe hxc hxC
  have hxe' : c₀.nreg 243005 < 2 * C.m + 7 := by_omega
  -- the descriptor words
  set B := c.nreg 243020 with hBdef
  zudqo
  have hBW : ztsam := by
    have := hw.1 ALLOC; omega
  obtain ⟨c₁, k₁, hk₁, e₁, v97, v98, v99, v100, v101, v90, v96, v103, v104, o₁⟩ :=
    chainPre_exec (P := P) hw (B := B) rfl h23 hs2 hs3 rfl hBW hWm
  obtain ⟨c₂, k₂, hk₂, e₂, v102, o₂⟩ := sS_exec (P := P) e₁.wb_right v99 v100 v98
    (by zuonf; omega)
  have hS : sOf C.m C.topIdx ztggy = C.sideS C.sideBeta := sOf_sideS hs4
  zugdk

  zubad
  have hi : c₀.nreg 243005 - 6 ≤ 2 * C.m := by_omega
  obtain ⟨c₃, k₃, hk₃, e₃, v106, o₃⟩ := jS_exec (P := P) e₂.wb_right (m := C.m) (i := c₀.nreg 243005 - 6) by_omega v102
    ztjqf ztlig hSle hi
    by_omega
  set j := (S + (c₀.nreg 243005 - 6)) % ztbb with hjdef
  zudhq
  -- registers carried to the branch

  have r05 : c₃.nreg 243005 = c₀.nreg 243005 := by zuoau
  have r06 : c₃.nreg 243006 = c₀.nreg 243006 := by zuoav
  have r22 : ztusa := by rw [o₁₃.1 _ by_decide, h22]
  have r23 : ztusb := by rw [o₁₃.1 _ by_decide, h23]
  have r100 : c₃.nreg 243100 = 2 * C.m := by zunmu
  have r102 : c₃.nreg 243102 = S := by zuoaw
  have r103 : c₃.nreg 243103 = 6 := by zunmv
  have r97 : c₃.nreg 243097 = C.m := by zunmw
  have r98 : c₃.nreg 243098 = C.topIdx := by zunmx
  have r101 : c₃.nreg 243101 = 7 := by zunmy
  have r96 : c₃.nreg 243096 = 2 := by zunmz
  have r90 : c₃.nreg 243090 = 2 * C.m + 7 := by zunna
  have hL₁₃ : ∀ r ∈ chainHL ++ [243102] ++ [243105, 243106], r ∈ holeL := by
    decide
  have hpos : (chainModel C).pos _ x =
      Chazelle.Chain.sidePt (chainModel C).W x.edge ztwte := rfl
  by_cases hh : c₀.nreg 243006 = 0
  · -- a tour vertex
    have g06 : ¬ c₃.nreg 243022 < c₃.nreg 243006 := by_omega
    obtain ⟨c₄, k₄, hk₄, e₄, w9, w10, w11, w12, w13, wtop, o₄⟩ := vtxH_exec (P := P)
      e₃.wb_right r97 r98 r100 r101 r96 r90 r103 r102 by_omega r23 hSle hj hWm
    have ex : ztpjm :=
      .seq e₁ ztjds
    have ho : ztlxi := (o₁₃.trans o₄).mono (fun r hr => by
      simp only [holeL, chainHL, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr ⊢; omega)
    refine ztkkn
    zuxy

    have h9 : c₄.nreg 241309 = 2 ∨ c₄.nreg 241309 = 3 := by zupaw; split_ifs <;> simp
    have m0 : ztzqv :=
      hole_mem (j := 0) by_omega by_omega
    have m1 : ztzqw :=
      hole_mem (j := 1) by_omega by_omega
    have va : vHole (chainModel C).W.n ztczc =
        ztbqr := by
      zugee
    have vb : vHole (chainModel C).W.n ztwsn =
        ztbqs := by
      zugef
    zumkl
    · zuhj
      · show c₄.nreg 241310 < _ ∧ c₄.nreg 241311 < _ ∧ c₄.nreg 241310 ≠ c₄.nreg 241311
        zugve

      · show c₄.nreg 241312 < _ ∧ c₄.nreg 241313 < _ ∧ c₄.nreg 241312 ≠ c₄.nreg 241313
        zugvf

      · have ht : ztmwe := by
          grind
        zuvf
        show c₄.nreg 241314 < _ ∧ c₄.nreg 241315 < _ ∧ c₄.nreg 241314 ≠ c₄.nreg 241315
        omega
    · zugr

      refine cover_chain_vertex hsimp hk by_grind by_grind
        ztefc _
      zuvf
      have h93 : c₄.nreg 241309 = 3 := by_grind
      have m2 : ztinc ∈ ShotList.holeList c₄ 241300 :=
        hole_mem (j := 2) by_omega by_omega
      rw [hn, show 2 * C.m + 6 = 2 * C.m + 6 from rfl, vHole_six by_omega, t14, t15,
        Nat.mod_self] at *
      omega
    · zudif
      zukeb
      zugr

      zucn
      zuiur
      have za : ztykv := by
        zufnh
      have zb : ztbank := by
        zufni
      zues

      zubwm
      zuhj
      · have e : ShotList.holeAt c₄ 241300 0 =
            vHole (chainModel C).W.n ztczc := by rw [va]; rfl
        zurh
        zufsh
      · have e : ShotList.holeAt c₄ 241300 1 =
            vHole (chainModel C).W.n ztwsn := by rw [vb]; rfl
        zurh
        zufsi
      · have ht : ztmwe := by
          zuefj
        zuvf
        have e : ShotList.holeAt c₄ 241300 2 = vHole (chainModel C).W.n ztcc := by
          zuhlt
          show (ztinc : WPos × WPos) = _
          grind
        zurh
        have e2m : ztyxz := by
          zugtm
        zudhd

        have ztop : ztyku := by
          zudfw
        zufsj
  · -- inside a tour edge
    zulkd
    have g06 : c₃.nreg 243022 < c₃.nreg 243006 := by_omega
    zufyf
    have hi2' : c₀.nreg 243005 - 6 < 2 * C.m := hi2
    have he6' : 6 ≤ c₀.nreg 243005 := he6
    obtain ⟨c₄, k₄, hk₄, e₄, w9, w10, w11, w12, w13, o₄⟩ := edgeH_exec (P := P)
      e₃.wb_right r100 v106 r102 r103 r23 r05 hj hSle by_omega hWm
    have ex : ztpjm :=
      .seq e₁ ztjdt
    have ho : ztlxi := (o₁₃.trans o₄).mono (fun r hr => by
      simp only [holeL, chainHL, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr ⊢; omega)
    refine ztkkn
    zucms

    have m0 : ztzqv :=
      hole_mem (j := 0) by_omega by_omega
    have m1 : ztzqw :=
      hole_mem (j := 1) by_omega by_omega
    zumkl
    · zuow
      · grind
      grind
    · have e1 : eHole (chainModel C).W.n (c₀.nreg 243005 - 6 + 6) =
          ztbqr := by
        unfold eHole
        rw [hn, w10, w11, Nat.mod_eq_of_lt by_omega, show c₀.nreg 243005 - 6 + 6 =
          c₀.nreg 243005 by omega]
      have e2 : eHole (chainModel C).W.n ztddo =
          ztbqs := by
        zuuc

      have hcov := cover_chain_edge hsimp hi2 hτ hτ1 ztmdg
        by_grind zta
      grind
    · zuhgi
      zues

      have hq' : q < min (c₄.nreg 241309) 3 := hq
      zufwo
      zuow
      · have e : ShotList.holeAt c₄ 241300 0 = eHole (chainModel C).W.n ztqkc := by
          zujjr
          show (ztbqr : WPos × WPos) = _
          zugeg
        zurh
        exact near_eHole _ _ by_omega by_grind hp' h0 h1 hkk
      · have e2 : eHole (chainModel C).W.n ztddo =
            ztbqs := by
          zuuc

        have e : ShotList.holeAt c₄ 241300 1 =
            eHole (chainModel C).W.n ztddo := by
          zukvi
        zurh
        zufil
        rw [show c₀.nreg 243005 - 6 + 6 = c₀.nreg 243005 by omega] at a1 a2
        have zt : Chazelle.Chain.sidePt (chainModel C).W ztddo
            ztydj = (chainModel C).pos zta x := by
          show Geometry.lerp ztiez
            ztifa _ =
            Geometry.lerp ((chainModel C).wa ztqkc) ((chainModel C).wb ztqkc)
              _
          zukqa
          zudxm
        zugki
end
end SweepIo
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft sideKey_inj)
open Chazelle.Jordan (offset)
open Chazelle.Geometry (lerp)
open WalkEmbed
namespace Sweep
section Top
variable (J : Merge.Junction)

/-- **`RLabel` from the positions just before a vertex position of the stretch** (offset
`1 ≤ d ≤ rL1 + rL2`): the corresponding positions of the walk of `C₂` are those just before the
position following the counterpart of `d - 1`.  This covers the split vertex (`d = rL1`, case G)
and the end of the stretch (`d = rL1 + rL2`). -/
theorem rlabel_before0 (hP : J.P.Simple) {S₂ : Set ztf}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {d : ℕ} (hd1 : 1 ≤ d)
    (hd : d ≤ rL1 J + rL2 J) {G V : Set Point}
    (hW : BeforeFaces ztbm
      ztbn 0 G)
    (hW₂ : BeforeFaces ztj
      ztbalh 0 V) :
    RLabel J S₂ G V := by
  zuv
  zucbq

  zumef
  zudox
  zubdc
  zufpa
  have hPm : ztwoi := by
    zugdh
  have hPm₂ : ztwpj % (chainModel J.right).W.n =
      (ztwlf % (chainModel J.right).W.n +
        (chainModel J.right).W.n - 1) % (chainModel J.right).W.n := by
    zuilr

  obtain ⟨s, hnc, hs⟩ := ((eventually_not_cut_before hC.hM hC.hF hC.hfin
    ztcro).and
    (Ioo_mem_nhdsGT (show (0 : ℝ) < min ztkaw 1 from
      lt_min ztdvj one_pos))).exists
  have hs1 := lt_of_lt_of_le hs.2 ztwth
  have hs2 := lt_of_lt_of_le hs.2 ztwti
  have hs3 := lt_of_lt_of_le hs.2 ztgh
  refine ztfde
  · grind
  · zubii
  grind

/-- **The label of a faced side.**  If the region `G` is the faced side `ρ` of a chord going in
direction `dir` at a position of the right stretch, its label is the region of `S₂` faced on the
same side of the corresponding position of the walk of `C₂` (just after it if `ρ · dir = -1`,
just before it if `ρ · dir = 1`; at a vertex position, just before the position following the
counterpart of the predecessor). -/
theorem rlabel_of_faced (hP : J.P.Simple) {S₂ : Set ztf}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {d : ℕ}
    (hd : d < rL1 J + rL2 J) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {ρ dir : ℝ} {G : Set Point}
    (hfac : FacedSide ztbm
      ztbn t ρ dir G) :
    (ρ * dir = -1 → ∀ V, AfterFaces ztj
      ztwmz t V →
        RLabel J S₂ G V) ∧
    (ρ * dir = 1 → ∀ V,
      (0 < t → BeforeFaces ztj
        ztwmz t V →
          RLabel J S₂ G V) ∧
      (t = 0 → 1 ≤ d → BeforeFaces ztj
        ztbalh 0 V →
          RLabel J S₂ G V)) := by
  refine ⟨fun h V hV => rlabel_after J hP hS₂ hS₂f hd ht0 ht1 ztvvc hV,
    fun h V => ⟨fun htp hV => ?_, fun ht hd1 hV => ?_⟩⟩
  · exact rlabel_before J hP hS₂ hS₂f hd ht0 ht1 by_grind ztqqc hV
  · zucfb
    exact rlabel_before0 J hP hS₂ hS₂f hd1 hd.le ztqqc hV

/-- **The middle region of a tie leaving the stretch has no label.**  Let two distinct chords of
`F₂⁺` be attached at a vertex position inside the right stretch (not its base), with far
attachments off the stretch, and let `G` be on the same side `ρ` of both.  Then `G` has no
label. -/
theorem tie_unlabelled (hP : J.P.Simple) {Q : Polygon}
    {S₂ : Set ztf} (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    (_hF : (chainModel J.whole).ChordFamily Q ztbi) {e e' : Set Point}
    (he : e ∈ F₂plus J S₂) (he' : e' ∈ F₂plus J S₂) (hne : e' ≠ e) {d : ℕ}
    (hd0 : d ≠ 0) (hd : d < rL1 J + rL2 J)
    (heA : SideAttach (chainModel J.whole).W e
      ztbn 0)
    (heA' : SideAttach (chainModel J.whole).W e'
      ztbn 0)
    {pb pb' : ℕ} {tb tb' : ℝ} (hB : SideAttach (chainModel J.whole).W e pb tb)
    (hB' : SideAttach (chainModel J.whole).W e' pb' tb')
    (hBne : sidePt (chainModel J.whole).W pb tb ≠ sidePt (chainModel J.whole).W
      ztbn 0)
    (hBne' : sidePt (chainModel J.whole).W pb' tb' ≠ sidePt (chainModel J.whole).W
      ztbn 0)
    (hout : ¬ (0 < off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztbd ∧
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztbd <
        ((rL1 J + rL2 J : ℕ) : ℝ)))
    (hout' : ¬ (0 < off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zteun ∧
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zteun <
        ((rL1 J + rL2 J : ℕ) : ℝ)))
    {ρ : ℝ} (hρ : ρ = 1 ∨ ρ = -1) {G : Set Point}
    (hG : G ∈ (chainModel J.whole).regions ztbi)
    (hS : SideOf ztbm ρ e G) (hS' : SideOf ztbm ρ e' G) :
    ∀ V, ¬ RLabel J S₂ G V := by
  rintro V ⟨d'', hd'', t'', ht'', hnc, hfG, -⟩
  zucf
  zust
  zudnl
  zurn
  zugyp
  zuinq
  zueqz
  have hgn : (g : ℝ) < W.n := by exact_mod_cast hC.hg
  obtain ⟨-, hy, -⟩ := hM.attach_seg ztcik heA hB ztbsb
  obtain ⟨-, hy', -⟩ := hM.attach_seg ztmkq heA' hB' zthrn
  have h1 : ztdrh :=
    by grind
  have h1' : ztdri :=
    by grind
  have hopp := tie_opposite hM hFs he he' hne heA heA' hB.2.2.2.1 hB'.2.2.2.1 h1 h1'
  obtain ⟨θ, hθ, hori⟩ := exists_sign hρ ztzhf
  have hθρ : ztxfm := by
    zugl
  have hori' : ztxpm := by
    have e1 : -θ * ρ * ztbak =
        θ * ρ * ztix := by_ring
    zukd
    have hprod : 0 < ztrm *
        ztwvg := by
      have e2 : ztrm *
          ztwvg =
          ztxho * (-(ztdem *
            ztix)) := by_ring
      zubyo

    zugkj
  zuehl
  zuiys
  have hA0 : ztygk := by
    zueyd
    positivity
  have hAL : ztxbw := by
    zueyd
    zubfq
    linarith
  have hpre : ∀ {q : ℕ} {s : ℝ}, ¬ (0 < off W.n (g : ℝ) ztej ∧
      off W.n (g : ℝ) ztej < ((rL1 J + rL2 J : ℕ) : ℝ)) →
      ((rL1 J + rL2 J : ℕ) : ℝ) ≤ off W.n (g : ℝ) ztej ∨ off W.n (g : ℝ) ztej ≤ 0 := by
    grind
  have hb1 := chord_bound hM hFs he heA hB ztbsb hρ hG hS hθ hori hg0 hgn hA0 hAL
    by_grind
  have hb2 := chord_bound hM hFs he' heA' hB' zthrn hρ hG hS' hθ' hori' hg0 hgn hA0
    hAL by_grind
  zuiyr
  have hpos : 0 < off W.n (g : ℝ) ztgbg := by
    zuduj
  have hlt : off W.n (g : ℝ) ztgbg <
      ((rL1 J + rL2 J : ℕ) : ℝ) := by
    zudui

  zubwv

/-! ## The start of the sweep -/

/-! ## Detection -/

/-- **A virtual label** of a region `G` of `F₂⁺`: a region `V` of `S₂` on the side `ρ` of a chord
`c ∈ S₂` containing a chord of `F₂⁺` attached at a position of the right stretch (not the base or
the split vertex) with `G` on its side `ρ`.  This is what the sweep's label is after an event on
such a chord. -/
def VLabel (S₂ : Set ztf) (G V : Set Point) : Prop :=
  ∃ (e c : Set Point) (ρ : ℝ) (d : ℕ) (t : ℝ), e ∈ F₂plus J S₂ ∧ c ∈ S₂ ∧ e ⊆ c ∧
    ztbtc ∧ d < rL1 J + rL2 J ∧ 0 ≤ t ∧ t < 1 ∧ ztits ∧
    SideAttach (chainModel J.whole).W e
      ztbn t ∧
    SideOf ztbm ρ e G ∧ SideOf ztj ρ c V

/-- **A virtual label is the label** whenever the region has one (lemma (E)). -/
theorem label_of_vlabel (hP : J.P.Simple) {Q : Polygon}
    {S₂ : Set ztf} (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    (hF : (chainModel J.whole).ChordFamily Q ztbi) {G V V' : Set Point}
    (hG : G ∈ (chainModel J.whole).regions ztbi)
    (hV : V ∈ (chainModel J.right).regions S₂) (hV' : V' ∈ (chainModel J.right).regions S₂)
    (hVL : VLabel J S₂ G V) (hL : RLabel J S₂ G V') :
    V' = V ∨ ztfno := by
  zubax
  exact label_side_gen2 J hP hS₂ hF hd ht0 ht1 hsec he hc hec heA hρ hG hV hV' hGs hVs hL

/-- A region on a side of a chord of `S₂` touches it: the chord is an exit chord of the
region. -/
theorem touches_of_sideOf {S₂ : Set ztf} (hS₂ : S₂ ⊆ Merge.augChords J.right)
    {c V : Set Point} (hc : c ∈ S₂) {ρ : ℝ} (hVs : SideOf ztj ρ c V) :
    Chazelle.Chain.TouchesIn (chainModel J.right).D c V := by
  zucok
  zudoh
  have hz : (ztwsj : Point) ∈ c := by
    rw [hcdef]; exact ztgpk
  have hzD : (ztwsj : Point) ∈ (chainModel J.right).D :=
    hH.open_mem _ by_linarith by_linarith
  exact touches_of_side hz hzD (hVs _ hz hzD)

/-- **Detection in an unlabelled region** (the bracket lemma in terms of virtual labels): for a
region without a label with a virtual label `V`, and a non-cut position of the `C₁` part facing
it, the next chord of `F₂⁺` with an attachment inside the right stretch is a chord in a chord of
`S₂` with `V` on the side of the region, or ends at the shared vertex. -/
theorem detect_unlabelled (hP : J.P.Simple) {Q : Polygon}
    {S₂ : Set ztf} (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    (hF : (chainModel J.whole).ChordFamily Q ztbi) {G V : Set Point}
    (hG : G ∈ (chainModel J.whole).regions ztbi)
    (hV : V ∈ (chainModel J.right).regions S₂) (hU : ∀ V', ¬ RLabel J S₂ G V')
    (hVL : VLabel J S₂ G V) {p₀ : ℕ} {t₀ : ℝ} (hp₀ : p₀ < (chainModel J.whole).W.n)
    (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) (hnc₀ : ¬ (chainModel J.whole).IsCut ztbi zthw)
    (hfG₀ : (chainModel J.whole).Faces p₀ t₀ G)
    (ho₀ : ((rL1 J + rL2 J : ℕ) : ℝ) <
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zthw) :
    ∃ ρ : ℝ, ztbtc ∧ BracketConcl2 J S₂ ρ V
      ztwmg := by
  zubax
  exact ⟨ρ, hρ, bracket2 J hP hS₂ hF hρ hG hV hU he hc hec hd ht0 ht1 hsec heA hGs hVs hp₀ ht₀
    hnc₀ hfG₀ ho₀⟩

/-- **The bracket of a tie leaving the stretch** (the two top chords at the split vertex in
case G): for a tie at a position inside the right stretch whose two chords have their far
attachments off the stretch, with `G` on the same side of both (`fb` oriented by `-1`, `ff` by
`1`), and a non-cut position of the `C₁` part facing `G`: the far attachment of `ff` is after
that position (or at offset `0`), and no chord of `F₂⁺` with an attachment inside the stretch
(not at offset `0`) is attached between them. -/
theorem bracket_tie (hP : J.P.Simple) {Q : Polygon}
    {S₂ : Set ztf} (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    (hF : (chainModel J.whole).ChordFamily Q ztbi) {ρ : ℝ} (hρ : ρ = 1 ∨ ρ = -1)
    {G : Set Point} (hG : G ∈ (chainModel J.whole).regions ztbi)
    {fb ff : Set Point} (hfb : fb ∈ F₂plus J S₂) (hff : ff ∈ F₂plus J S₂) (hbf : fb ≠ ff)
    {pa : ℕ}
    (hAL : off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zteuk <
      ((rL1 J + rL2 J : ℕ) : ℝ))
    (hbA : SideAttach (chainModel J.whole).W fb pa 0)
    (hfA : SideAttach (chainModel J.whole).W ff pa 0) {pbb pff : ℕ} {tbb tff : ℝ}
    (hbB : SideAttach (chainModel J.whole).W fb pbb tbb)
    (hfF : SideAttach (chainModel J.whole).W ff pff tff)
    (hbne : sidePt (chainModel J.whole).W pa 0 ≠ sidePt (chainModel J.whole).W pbb tbb)
    (hfne : sidePt (chainModel J.whole).W pa 0 ≠ sidePt (chainModel J.whole).W pff tff)
    (hbS : SideOf ztbm ρ fb G) (hfS : SideOf ztbm ρ ff G)
    (hbo : 0 < -1 * ρ * ((sidePt (chainModel J.whole).W pa 0).1 -
      (sidePt (chainModel J.whole).W pbb tbb).1))
    (hfo : 0 < 1 * ρ * ((sidePt (chainModel J.whole).W pa 0).1 -
      (sidePt (chainModel J.whole).W pff tff).1))
    (hbout : ¬ (0 < off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztkcf ∧
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztkcf <
        ((rL1 J + rL2 J : ℕ) : ℝ)))
    (hfout : ¬ (0 < off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztdhx ∧
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztdhx <
        ((rL1 J + rL2 J : ℕ) : ℝ)))
    {p₀ : ℕ} {t₀ : ℝ} (hp₀ : p₀ < (chainModel J.whole).W.n) (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (hnc₀ : ¬ (chainModel J.whole).IsCut ztbi zthw)
    (hfG₀ : (chainModel J.whole).Faces p₀ t₀ G)
    (ho₀ : ((rL1 J + rL2 J : ℕ) : ℝ) <
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zthw) :
    (off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztdhx = 0 ∨
      (((rL1 J + rL2 J : ℕ) : ℝ) ≤
          off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztdhx ∧
        off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zthw <
          off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztdhx)) ∧
    ∀ e ∈ F₂plus J S₂, ∀ (pw : ℕ) (tw : ℝ) (pb : ℕ) (tb : ℝ),
      SideAttach (chainModel J.whole).W e pw tw → SideAttach (chainModel J.whole).W e pb tb →
      sidePt (chainModel J.whole).W pw tw ≠ sidePt (chainModel J.whole).W pb tb →
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zthw <
        off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztbjs →
      (off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztdhx = 0 ∨
        off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztbjs <
          off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztdhx) →
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztbd <
        ((rL1 J + rL2 J : ℕ) : ℝ) →
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztbd ≠ 0 → False := by
  zucf
  zust
  zudnl
  zued
  have hgn : ztcx := by
    zucfu
  zupz
  obtain ⟨hLb, hbo₀⟩ := back_end J hP hS₂ hρ hG hfb hbA hbB hbne hbS hbo hAL hbout hp₀ ht₀
    hnc₀ hfG₀ ho₀
  have hfe := fwd_end J hP hS₂ hρ hG hff hfA hfF hfne hfS hfo hAL hfout hp₀ ht₀ hnc₀ hfG₀
    ho₀
  refine ⟨hfe, fun e he pw tw pb tb hW hB hWB hoW hoZ hoB hB0 => ?_⟩
  zufyu
  zucoa
  have hA0 := off_nonneg kA0 hgn
  have heb : e ≠ fb := by
    zunq
    rcases key_of_two hM ztcik hbA hbB hbne hW with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> linarith
  have hef : e ≠ ff := by
    zunq
    rcases key_of_two hM ztcik hfA hfF hfne hW with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · linarith
    grind
  -- non-crossing with `fb`: the stretch attachment of `e` is before the tie
  have hBA : o ztbd < o zteuk := by
    have hle : o ztbd ≤ o zteuk := by
      zux

      have := no_cross_off hM hFs hF.1 hfb he (Ne.symm heb) hbA hbB hbne hB hW hg0 hgn
        by_linarith hc by_linarith
      grind
    zubug
    · zubh
    · zubvx

      rcases tie_third hM hFs hfb hff he hbf hbA hfA hB with h' | h'
      · grind
      grind
  zugrt
  · zuhwn
    have := no_cross_off hM hFs hF.1 hff he ztmbu hfF hfA (Ne.symm hfne) hB hW hg0 hgn
      by_grind by_grind hBA
    grind
  · zuklu
    · linarith
    · have := no_cross_off hM hFs hF.1 hff he ztmbu hfA hfF hfne hW hB hg0 hgn
        by_linarith by_linarith h
      grind

/-! ## Transparent brackets -/
end Top
end Sweep
end
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft sideKey_inj)
open WalkEmbed
namespace Sweep
variable {M : Model} {F : Set (Set Point)} {p : ℕ} {t : ℝ} {Q : Polygon}
/-- Every chord of a finite admissible family has a region on each side. -/
theorem side_region_exists (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) {c : Set Point} (hc : c ∈ F) {ρ : ℝ} (hρ : ρ = 1 ∨ ρ = -1) :
    ∃ U ∈ M.regions F, SideOf M ρ c U := by
  zucsh
  zuvm
  · exact ztkyg
  · exact ⟨Dn, hDn, fun z hz hzD => (hside z hz hzD).mono fun δ h => by
      simpa [sub_eq_add_neg] using h.2⟩

/-- Two regions faced just after the same position are equal. -/
theorem after_unique (ht1 : t < 1)
    {U U' : Set Point} (hU : U ∈ M.regions F) (hU' : U' ∈ M.regions F)
    (h : AfterFaces M p t U) (h' : AfterFaces M p t U') : U = U' := by
  obtain ⟨δ, hδ, h1⟩ := h
  obtain ⟨δ', hδ', h2⟩ := h'
  set s := min ztfth ztca / 2 with hs
  have hs0 : ztxx := by
    simp_all
  have hs1 : ztlbe := by
    grind
  have hs2 : ztslw := by
    grind
  have hs3 : ztmww := by_grind
  exact WalkAx.faces_unique hU hU' by_grind (h2 s hs0 hs2 hs3)

/-- Two regions faced just before the same position are equal. -/
theorem before_unique (ht0 : 0 ≤ t)
    {U U' : Set Point} (hU : U ∈ M.regions F) (hU' : U' ∈ M.regions F)
    (h : BeforeFaces M p t U) (h' : BeforeFaces M p t U') : U = U' := by
  obtain ⟨δ, hδ, h1a, h1b⟩ := h
  obtain ⟨δ', hδ', h2a, h2b⟩ := h'
  zukmk
  · set s := min ztfth t / 2 with hs
    have hs0 : ztxx := by
      simp_all
    have hs1 : ztlbe := by
      grind
    have hs2 : ztslw := by
      grind
    have hs3 : ztslv := by_grind
    exact WalkAx.faces_unique hU hU' by_grind (h2a htp s hs0 hs2 hs3)
  · subst ht00
    set s := min δ δ' / 2 with hs
    zucmn
    have hs1 : ztlbe := by_grind
    have hs2 : ztslw := by_grind
    exact WalkAx.faces_unique hU hU' by_grind (h2b rfl s hs0 hs2)

/-- **The region faced just after a uniquely attached chord** lies on its side `-dir` (item
(c)). -/
theorem after_side {F : Set ztf} (hGM : GoodModel M)
    (hFam : M.ChordFamily Q F) {e : Set Point} (he : e ∈ F) {p : ℕ} {t : ℝ}
    (hA : SideAttach M.W e p t) (huniq : ∀ e' ∈ F, SideAttach M.W e' p t → e' = e) {dir : ℝ}
    (hdir : ztcqu ∨
      ztcmz)
    {G : Set Point} (hG : G ∈ M.regions F) (hW : AfterFaces M p t G) : SideOf M (-dir) e G := by
  zubm
  have hρ : -dir = 1 ∨ -dir = -1 := by
    grind
  zubgx

  have hd2 : -dir * dir = -1 := by_grind
  rw [after_unique hA.2.2.1 hG hU hW (hfac.1 hd2)]
  exact hS

/-- **The region faced just before a uniquely attached chord** lies on its side `dir` (item
(c)). -/
theorem before_side {F : Set ztf} (hGM : GoodModel M)
    (hFam : M.ChordFamily Q F) {e : Set Point} (he : e ∈ F) {p : ℕ} {t : ℝ}
    (hA : SideAttach M.W e p t) (huniq : ∀ e' ∈ F, SideAttach M.W e' p t → e' = e) {dir : ℝ}
    (hdir : ztcqu ∨
      ztcmz)
    {G : Set Point} (hG : G ∈ M.regions F) (hW : BeforeFaces M p t G) : SideOf M dir e G := by
  zubm
  have hρ : dir = 1 ∨ dir = -1 := by
    grind
  zubgx

  have hd2 : dir * dir = 1 := by_grind
  rw [before_unique hA.2.1 hG hU hW (hfac.2 hd2)]
  exact hS

/-- **The regions faced around a tie** (item (c)): at a tie whose leaving edge goes down, the
region faced just after is below the east chord and the region faced just before is below the
west chord; when the edge goes up, the region faced just after is above the west chord and the
region faced just before is above the east chord. -/
theorem after_side_tie {F : Set ztf} (hGM : GoodModel M)
    (hFam : M.ChordFamily Q F) {ce cw : Set Point} (hce : ce ∈ F) (hcw : cw ∈ F)
    (hne : cw ≠ ce) {p : ℕ} {t : ℝ} (hAe : SideAttach M.W ce p t)
    (hAw : SideAttach M.W cw p t) (hE : ∀ z ∈ ce, (sidePt M.W p t).1 ≤ z.1)
    (hWd : ∀ z ∈ cw, z.1 ≤ (sidePt M.W p t).1) {G : Set Point} (hG : G ∈ M.regions F) :
    ((M.wb p).2 < (M.wa p).2 → AfterFaces M p t G → SideOf M (-1) ce G) ∧
    ((M.wb p).2 < (M.wa p).2 → BeforeFaces M p t G → SideOf M (-1) cw G) ∧
    ((M.wa p).2 < (M.wb p).2 → AfterFaces M p t G → SideOf M 1 cw G) ∧
    ((M.wa p).2 < (M.wb p).2 → BeforeFaces M p t G → SideOf M 1 ce G) := by
  zubm
  zubl

  obtain ⟨Ue, hUe, hSe⟩ := side_region_exists hM hF hfin hce (Or.inr rfl : (-1 : ℝ) = 1 ∨ _)
  obtain ⟨Uw, hUw, hSw⟩ := side_region_exists hM hF hfin hcw (Or.inr rfl : (-1 : ℝ) = 1 ∨ _)
  obtain ⟨Ue', hUe', hSe'⟩ := side_region_exists hM hF hfin hce (Or.inl rfl : (1 : ℝ) = 1 ∨ _)
  obtain ⟨Uw', hUw', hSw'⟩ := side_region_exists hM hF hfin hcw (Or.inl rfl : (1 : ℝ) = 1 ∨ _)
  have fe := fun {ρ U} (hρ : ρ = 1 ∨ ρ = -1) (hU : U ∈ M.regions F) (hS : SideOf M ρ ce U) =>
    (faced_or_middle hGM hFam hce hAe hρ hU hS ztbaev).2 cw hcw hne hAw
  have fw := fun {ρ U} (hρ : ρ = 1 ∨ ρ = -1) (hU : U ∈ M.regions F) (hS : SideOf M ρ cw U) =>
    (faced_or_middle hGM hFam hcw hAw hρ hU hS (Or.inr ⟨rfl, hWd⟩)).2 ce hce hne.symm hAe
  refine ⟨fun hdn hW => ?_, fun hdn hW => ?_, fun hup hW => ?_, fun hup hW => ?_⟩
  · obtain ⟨-, -, h, -⟩ := fe ztbt hUe hSe
    zuhew
    rw [after_unique hAe.2.2.1 hG hUe hW ztvvb]; omega
  · obtain ⟨-, -, h, -⟩ := fw ztbt hUw hSw
    zuhew
    rw [before_unique hAw.2.1 hG hUw hW ztvvd]; omega
  · obtain ⟨-, -, -, h⟩ := fw ztp hUw' hSw'
    zuhex
    rw [after_unique hAw.2.2.1 hG hUw' hW ztvvb]; omega
  · obtain ⟨-, -, -, h⟩ := fe ztp hUe' hSe'
    zuhex
    rw [before_unique hAe.2.1 hG hUe' hW ztvvd]; omega

/-! ## Transparent blocks (the stack rule) -/

/-! ## The invariant -/
section Inv
variable (J : Merge.Junction)

/-- **The middle region of a tie of top chords leaving the stretch** (case G, above the two top
chords at the split vertex): two distinct chords of `F₂⁺` through the top of `C₂` attached at a
vertex position inside the right stretch (not its base), with far attachments off the stretch,
and `G` on the same side of both. -/
def TieOut (S₂ : Set ztf) (G : Set Point) : Prop :=
  ∃ (e e' : Set Point) (d : ℕ) (pb pb' : ℕ) (tb tb' : ℝ) (ρ : ℝ),
    e ∈ F₂plus J S₂ ∧ e' ∈ F₂plus J S₂ ∧ e' ≠ e ∧ d ≠ 0 ∧ d < rL1 J + rL2 J ∧
    SideAttach (chainModel J.whole).W e ztbn 0 ∧
    SideAttach (chainModel J.whole).W e'
      ztbn 0 ∧
    SideAttach (chainModel J.whole).W e pb tb ∧ SideAttach (chainModel J.whole).W e' pb' tb' ∧
    sidePt (chainModel J.whole).W pb tb ≠ sidePt (chainModel J.whole).W
      ztbn 0 ∧
    sidePt (chainModel J.whole).W pb' tb' ≠ sidePt (chainModel J.whole).W
      ztbn 0 ∧
    ¬ (0 < off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztbd ∧
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztbd <
        ((rL1 J + rL2 J : ℕ) : ℝ)) ∧
    ¬ (0 < off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zteun ∧
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zteun <
        ((rL1 J + rL2 J : ℕ) : ℝ)) ∧
    ztbtc ∧ SideOf ztbm ρ e G ∧ SideOf ztbm ρ e' G ∧
    J.right.top ∈ e ∧ J.right.top ∈ e'

/-- **The invariant of the sweep's label** `λ` for the current region `G`: every label of `G` is
`λ`; if `G` has no label, `λ` is a virtual label of `G` or `G` is the middle region of a tie
leaving the stretch (the cases in which the next stretch-anchored cut is found). -/
def Valid (S₂ : Set ztf) (G L : Set Point) : Prop :=
  (∀ V ∈ (chainModel J.right).regions S₂, RLabel J S₂ G V → LabS J S₂ L V) ∧
    (ztlut → VLabel J S₂ G L ∨ TieOut J S₂ G)

/-- **Rule for fused chords, events after the stack pops of tie partners** (λ := the recorded side
of the chord of `S₂`): a virtual label is valid. -/
theorem valid_of_vlabel (hP : J.P.Simple) {Q : Polygon}
    {S₂ : Set ztf} (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    (hF : (chainModel J.whole).ChordFamily Q ztbi) {G L : Set Point}
    (hG : G ∈ (chainModel J.whole).regions ztbi)
    (hL : L ∈ (chainModel J.right).regions S₂) (hVL : VLabel J S₂ G L) : Valid J S₂ G L :=
  ⟨fun V hV hR => by
    rcases label_of_vlabel J hP hS₂ hF hG hL hV hVL hR with h | ⟨h, -⟩
    · tauto
    tauto, by_simp_all⟩

/-- **Rule for faced sides** (top chords, shared chords, the start; λ := the region located in
`N₂`): a label is valid. -/
theorem valid_of_rlabel (hP : J.P.Simple) {S₂ : Set ztf}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {G L : Set Point}
    (hG : G ∈ (chainModel J.whole).regions ztbi)
    (hL : L ∈ (chainModel J.right).regions S₂) (hR : RLabel J S₂ G L) : Valid J S₂ G L :=
  ⟨fun V hV hR' => by
    rcases label_right3 J hP hS₂ hS₂f hG hV hL hR' hR with h | ⟨h, -⟩
    · tauto
    tauto,
    by grind⟩

/-- **The middle region of a tie leaving the stretch** is valid for every `λ`. -/
theorem valid_of_tieOut (hP : J.P.Simple) {Q : Polygon}
    {S₂ : Set ztf} (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    (hF : (chainModel J.whole).ChordFamily Q ztbi) {G : Set Point}
    (hG : G ∈ (chainModel J.whole).regions ztbi) (hT : TieOut J S₂ G) (L : Set Point) :
    Valid J S₂ G L := by
  obtain ⟨e, e', d, pb, pb', tb, tb', ρ, he, he', hne, hd0, hd, hA, hA', hB, hB', hBne, hBne',
    hout, hout', hρ, hS, hS', ht, ht'⟩ := hT
  have hU := tie_unlabelled J hP hS₂ hF he he' hne hd0 hd hA hA' hB hB' hBne hBne' hout hout'
    hρ hG hS hS'
  exact ⟨by_simp_all, fun _ => Or.inr ⟨e, e', d, pb, pb', tb, tb', ρ, he, he',
    hne, hd0, hd, hA, hA', hB, hB', hBne, hBne', hout, hout', hρ, hS, hS', ht, ht'⟩⟩

/-- **Detection from a valid state.**  Let the sweep be at a non-cut position of the `C₁` part
facing `G` with a valid label `λ`.  Then:
* if `G` has a label, every fused chord `h ⊆ c'` attached at a stretch position (not the base or
  the split vertex) with `G` on its side has `c'` touching `λ` (so `h` is a candidate);
* if `G` has no label, either the bracket conclusion holds with `λ` (the next stretch-anchored
  cut is made by a chord of a chord of `S₂` touching `λ`, or at the shared vertex), or `G` is the
  middle of a tie leaving the stretch (the next stretch-anchored cut is made by one of its two
  chords, a top chord in the case of the top of `C₂`). -/
theorem detect_valid (hP : J.P.Simple) {Q : Polygon}
    {S₂ : Set ztf} (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    (hF : (chainModel J.whole).ChordFamily Q ztbi) {G L : Set Point}
    (hG : G ∈ (chainModel J.whole).regions ztbi)
    (hL : L ∈ (chainModel J.right).regions S₂) (hvalid : Valid J S₂ G L)
    {p₀ : ℕ} {t₀ : ℝ} (hp₀ : p₀ < (chainModel J.whole).W.n) (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (hnc₀ : ¬ (chainModel J.whole).IsCut ztbi zthw)
    (hfG₀ : (chainModel J.whole).Faces p₀ t₀ G)
    (ho₀ : ((rL1 J + rL2 J : ℕ) : ℝ) <
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zthw) :
    ((∃ V₀ ∈ (chainModel J.right).regions S₂, RLabel J S₂ G V₀) →
      ∀ (h c' V' : Set Point) (ρ' : ℝ) (d : ℕ) (t : ℝ), (ρ' = 1 ∨ ρ' = -1) →
        h ∈ F₂plus J S₂ → c' ∈ S₂ → h ⊆ c' → d < rL1 J + rL2 J → 0 ≤ t → t < 1 →
        ztits →
        SideAttach (chainModel J.whole).W h
          ztbn t →
        SideOf ztbm ρ' h G → V' ∈ (chainModel J.right).regions S₂ →
        SideOf ztj ρ' c' V' →
        LabS J S₂ L V' ∧ Chazelle.Chain.TouchesIn (chainModel J.right).D c' V') ∧
    (ztlut →
      (∃ ρ : ℝ, ztbtc ∧ BracketConcl2 J S₂ ρ L
        ztwmg) ∨
      TieOut J S₂ G) := by
  refine ⟨fun ⟨V₀, hV₀, hR⟩ h c' V' ρ' d t hρ' hh hc' hhc hd ht0 ht1 hsec hhA hGs hV' hVs => ?_,
    fun hU => ?_⟩
  · zuive
    have h2 := label_side_gen2 J hP hS₂ hF hd ht0 ht1 hsec hh hc' hhc hhA hρ' hG
      hV' hV₀ hGs hVs hR
    exact ⟨labS_trans J h1 h2, touches_of_sideOf J hS₂.2.1 hc' hVs⟩
  · rcases hvalid.2 hU with h1 | h1
    · exact Or.inl (detect_unlabelled J hP hS₂ hF hG hL hU h1 hp₀ ht₀ hnc₀ hfG₀ ho₀)
    simp_all

/-! ## Item (b): the partner at a tie of a shared-vertex chord -/

/-- **The kinds of chords of `F₂⁺`**: contained in a chord of `S₂`, horizontal through the shared
vertex (the shared chords), or horizontal through the top of `C₂` (the top chords). -/
theorem F₂plus_cases {S₂ : Set ztf} (hS₂ : S₂ ⊆ Merge.augChords J.right) {e : Set Point}
    (he : e ∈ F₂plus J S₂) :
    (∃ c ∈ S₂, e ⊆ c) ∨ (J.shared ∈ e ∧ ∀ z ∈ e, z.2 = J.shared.2) ∨
      (J.right.top ∈ e ∧ ∀ z ∈ e, z.2 = J.right.top.2) := by
  have hvert : ∀ (k : ℕ) (σ : ℝ), J.whole.vertex k ∈ J.whole.chordSet k σ ∧
      ∀ z ∈ J.whole.chordSet k σ, z.2 = (J.whole.vertex k).2 := by
    intro k σ
    refine ⟨Geometry.left_mem_segment _ _, fun z hz => ?_⟩
    zugbs
    exact hz.1
  rcases he with he | ⟨σ, -, -, rfl⟩
  · rcases J.fusion_subset_image ∅ S₂ he with (⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩) | hsh
    · zubjt

      obtain ⟨-, -, -, hrd⟩ := J.ends_right ztbac
      show Merge.shoot J.whole _ 1 ⊆ c
      rw [hl, hcdef]
      zvnel at hrd
      exact Merge.shoot_subset_pos J.whole hH.lt hrd
    · zubjt

      obtain ⟨-, hld, -, -⟩ := J.ends_right ztbac
      show Merge.shoot J.whole _ _ ⊆ c
      rw [hr, hcdef]
      zvnen at hld
      exact Merge.shoot_subset_neg J.whole hH.lt hld
    · zufle
      zuhl
      obtain ⟨h1, h2⟩ := hvert J.m₁ σ
      tauto
  · zulw
    obtain ⟨h1, h2⟩ := hvert ztrw σ
    have hv : ztxmm := by
      zubut
    grind
end Inv
end Sweep
end
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft sideKey_inj)
open WalkEmbed
namespace Sweep
theorem off_sub {n g k y s : ℝ} (hg0 : 0 ≤ g) (hgn : g < n) (_hk0 : 0 ≤ k) (_hkn : k < n)
    (hy : y = k - s ∨ y = k - s + n) (hy0 : 0 ≤ y) (hyn : y < n) (hs : 0 < s)
    (hso : s < off n g k) : off n g y = off n g k - s := by
  unfold off at *
  grind

/-- **The positions just before the next cut key face the current region**: if `x₀` (non-cut,
inside a walk edge) faces `G` and no cut lies strictly between `x₀` and the key `K` (in offsets
from `g`, `o(x₀) < o(K)`), then `G` is faced just before `K`. -/
theorem before_faces_of_gap {M : Model} (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) {g : ℝ} (hg0 : 0 ≤ g) (hgn : g < M.W.n) {G : Set Point}
    (hG : G ∈ M.regions F) {p₀ : ℕ} {t₀ : ℝ} (hp₀ : p₀ < M.W.n) (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (hnc₀ : ¬ M.IsCut F zthw) (hfG₀ : M.Faces p₀ t₀ G) {pK : ℕ} {tK : ℝ}
    (hpK : pK < M.W.n) (htK0 : 0 ≤ tK) (htK1 : tK < 1)
    (ho : off M.W.n g zthw < off M.W.n g ztkm)
    (hgap : ∀ x, M.IsCut F x → 0 ≤ x → x < M.W.n →
      ¬ (off M.W.n g zthw < off M.W.n g x ∧ off M.W.n g x < off M.W.n g ztkm)) :
    BeforeFaces M pK tK G := by
  zukzu
  set o := off (n : ℝ) g with hodef
  zuqi
  obtain ⟨x0, x1⟩ := Corr.key_mem hp₀ ht₀.1.le ht₀.2
  obtain ⟨k0, k1⟩ := Corr.key_mem hpK htK0 htK1
  have hx0o : 0 ≤ o _ := off_nonneg x0 hgn
  set δ := o ((pK : ℝ) + tK) - o ztmzm with hδ
  zukhq
  -- a position just before `K` faces `G`
  have key : ∀ (q : ℕ) (u s : ℝ), q < n → u ∈ Ioo (0 : ℝ) 1 → 0 < s → s < δ →
      ((q : ℝ) + u = (pK : ℝ) + tK - s ∨ (q : ℝ) + u = (pK : ℝ) + tK - s + n) →
      M.Faces q u G := by
    intro q u s hq hu hs0 hs1 hqu
    obtain ⟨y0, y1⟩ := Corr.key_mem hq hu.1.le hu.2
    have hoy : o _ = o _ - s :=
      off_sub hg0 hgn k0 k1 hqu y0 y1 hs0 by_linarith
    have hnc : ¬ M.IsCut F ztxy := by
      grind
    obtain ⟨U, hU, hfU⟩ := hM.exists_faces_of_not_cut hF hfin hq hu hnc
    have heq : G = U := by
      refine (hM.eq_iff_not_separates hF hfin hG hU hp₀ hq ht₀ hu hnc₀ hnc hfG₀ hfU).2
        fun c hc ⟨qa, qb, sa, sb, hQA, hQB, hQAB, hsep⟩ => ?_
      zucho

      have hxa := fun h => hnc₀ ztkjq
      have hxb := fun h => hnc₀ ztkjr
      have hya := fun h => hnc ztkjq
      have hyb := fun h => hnc ztkjr
      have hxy : (p₀ : ℝ) + t₀ ≠ q + u := by
        grind
      zubge

      have hnot : ∀ {r : ℕ} {v : ℝ}, SideAttach M.W c r v →
          ¬ Btw (o ztmzm) (o ztxy) (o ztmzo) := by
        zudqh

        have hcut : ztidq := ⟨c, hc, r, v, hR, rfl⟩
        zulto

      grind
    grind
  refine ⟨min δ 1, by_grind, fun htp s hs0 hs1 hs2 => ?_, fun ht s hs0 hs1 => ?_⟩
  · refine key pK _ s hpK by_grind hs0
      ztzwy by_grind
  · zucfb
    have hs1' := lt_of_lt_of_le hs1 ztgh
    refine key _ _ s zthp by_grind hs0
      ztzwy ?_
    rcases Nat.eq_zero_or_pos pK with h0 | h0
    · zubvi
      right
      rw [show (0 + n - 1) % n = n - 1 by zvmyc; omega,
        Nat.cast_sub by_omega]
      grind
    · left
      rw [show (pK + n - 1) % n = pK - 1 by
        rw [show pK + n - 1 = (pK - 1) + n by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt by_omega], Nat.cast_sub by_omega]
      simp
section Cand
variable (J : Merge.Junction)

/-- **The candidate chords** of the sweep for the label `λ`: pieces of chords of `S₂` touching `λ`
or a region at a side of the slit of `C₂` (the label triple, F2)
(the pieces seen from the endpoints of the exit chords of `λ`), the chords through the shared
vertex (the shared chords), and the chords through the top of `C₂` (the top chords). -/
def Cand (S₂ : Set ztf) (L : Set Point) : Set ztf :=
  {h | h ∈ F₂plus J S₂ ∧ ((∃ c ∈ S₂, h ⊆ c ∧ ∃ V, LabS J S₂ L V ∧
    Chazelle.Chain.TouchesIn (chainModel J.right).D c V) ∨ J.shared ∈ h ∨ J.right.top ∈ h)}

/-- The attachment at offset `0` of the stretch is the shared vertex. -/
theorem sidePt_off_zero (hP : J.P.Simple) {S₂ : Set ztf}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {p : ℕ} {t : ℝ}
    (hp : p < (chainModel J.whole).W.n) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (h0 : off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztk = 0) :
    sidePt (chainModel J.whole).W p t = J.shared := by
  zuv
  zued
  have hgn : ztcx := by
    zucfu
  zufyt
  have hk := off_inj hg0 hgn k0 k1 hg0 hgn (by rw [h0, off_self])
  obtain ⟨rfl, rfl⟩ := sideKey_inj ht0 ht1 le_rfl zero_lt_one
    (show (p : ℝ) + t = ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) + 0 by zvncl; exact hk)
  zudti
  have := hC.A1 0 ztbg
  rw [add_zero, add_zero, Nat.mod_eq_of_lt hC.hg, Nat.mod_eq_of_lt hC.hg'] at this
  zubk
  exact right_vtx0 J

/-- The split vertex (offset `rL1` inside the stretch, case G) is the top of `C₂`. -/
theorem sidePt_split (hP : J.P.Simple) {S₂ : Set ztf}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) (hlt : rL1 J < rL1 J + rL2 J) :
    sidePt (chainModel J.whole).W
      ztif 0 = J.right.top := by
  zuv
  have hδ : ztixu := by
    zuccr
    have := hC.hδ by_omega
    omega
  zudti
  have := hC.A2 0 ztbg
  zuigy
  rw [this, show 6 + tpos J.right 0 + rL1 J + rδ J = 6 + tpos J.right 0 + (rL1 J + rδ J) by ring]
  zulzp

/-- **A chord of `F₂⁺` bounding a labelled region, with an attachment in the stretch, is a
candidate**: if `G` has a label and is on the side `σ` of `h`, and `h` has an attachment at an
offset below the length of the stretch, then `h ∈ Cand λ` for a valid `λ`. -/
theorem cand_of_side (hP : J.P.Simple) {Q : Polygon}
    {S₂ : Set ztf} (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    (hF : (chainModel J.whole).ChordFamily Q ztbi) {G L : Set Point}
    (hG : G ∈ (chainModel J.whole).regions ztbi)
    (_hL : L ∈ (chainModel J.right).regions S₂) (hvalid : Valid J S₂ G L)
    (hlab : ∃ V₀ ∈ (chainModel J.right).regions S₂, RLabel J S₂ G V₀)
    {h : Set Point} (hh : h ∈ F₂plus J S₂) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hS : SideOf ztbm σ h G) {pB : ℕ} {tB : ℝ}
    (hB : SideAttach (chainModel J.whole).W h pB tB)
    (hBL : off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztdhv <
      ((rL1 J + rL2 J : ℕ) : ℝ)) : h ∈ Cand J S₂ L := by
  zucf
  zued
  have hgn : ztcx := by
    zucfu
  obtain ⟨k0, k1⟩ := Corr.key_mem hB.1 hB.2.1 hB.2.2.1
  have hBpt := hB.2.2.2.1
  rcases F₂plus_cases J hS₂.2.1 hh with ⟨c, hc, hhc⟩ | ⟨hv, -⟩ | ⟨ht, -⟩
  · rcases (off_nonneg k0 hgn).lt_or_eq with hpos | hzero
    · -- a proper position of the stretch, or the split vertex
      obtain ⟨hpd, hoff⟩ := hC.decomp hB.1 hB.2.1 hB.2.2.1
      set dB := dOf (chainModel J.whole).W.n _ pB with hdB
      rw [hoff] at hpos hBL
      have hdL : dB < rL1 J + rL2 J := by
        have : (dB : ℝ) < ((rL1 J + rL2 J : ℕ) : ℝ) := by zuntw
        zufc
      rw [← hpd] at hB hBpt
      by_cases hsplit : tB = 0 ∧ dB = rL1 J
      · obtain ⟨rfl, hdr⟩ := hsplit
        rw [hdr] at hB hBpt hdL
        refine ⟨hh, Or.inr ztgej⟩
        rw [← sidePt_split J hP hS₂.2.1 hS₂.1 hdL]
        omega
      · have hsec : tB = 0 → dB ≠ 0 ∧ dB ≠ rL1 J := by
          intro ht0
          refine ⟨fun h0 => ?_, by_simp_all⟩
          simp_all
        obtain ⟨V', hV', hVs'⟩ := side_region_exists hC.hM₂ hC.hS hC.hSfin hc hσ
        obtain ⟨V₀, hV₀, hR⟩ := hlab
        zuive
        have h2 := label_side_gen2 J hP hS₂ hF hdL hB.2.1 hB.2.2.1 hsec hh hc hhc hB
          hσ hG hV' hV₀ hS hVs' hR
        exact ⟨hh, Or.inl ⟨c, hc, hhc, V', labS_trans J h1 h2,
          touches_of_sideOf J hS₂.2.1 hc hVs'⟩⟩
    · refine ⟨hh, Or.inr ztenp⟩
      rw [← sidePt_off_zero J hP hS₂.2.1 hS₂.1 hB.1 hB.2.1 hB.2.2.1 hzero.symm]
      omega
  · exact ztuhp
  · exact ztuhp

/-- **A labelled region has a label among the regions of `S₂`.** -/
theorem rlabel_region (hP : J.P.Simple) {S₂ : Set ztf}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {G V : Set Point}
    (hR : RLabel J S₂ G V) : ∃ V' ∈ (chainModel J.right).regions S₂, RLabel J S₂ G V' := by
  zuv
  obtain ⟨d, hd, t, ht, hnc, hfG, -⟩ := hR
  set P₂ := ztfw % (chainModel J.right).W.n with hP₂
  have hP₂n : P₂ < (chainModel J.right).W.n := Nat.mod_lt _ hC.n₂_pos
  have hnc₂ : ¬ (chainModel J.right).IsCut S₂ ((P₂ : ℝ) + t) := by
    rintro ⟨c, hc, q, u, hA, hk⟩
    obtain ⟨rfl, rfl⟩ := sideKey_inj hA.2.1 hA.2.2.1 ht.1.le ht.2 hk.symm
    obtain ⟨e, he, -, -, heA⟩ := hC.transfer hd ht.1.le ht.2 ztpbo hc hA
    exact hnc ⟨e, he, _, _, heA, rfl⟩
  obtain ⟨V', hV', hf⟩ := hC.hM₂.exists_faces_of_not_cut hC.hS hC.hSfin hP₂n ht hnc₂
  exact ⟨V', hV', d, hd, t, ht, hnc, hfG, hf⟩

/-- **Detection of the next event** (the loop over the walk).  Let the sweep be at a non-cut
position `x₀` of the `C₁` part facing `G`, with a valid label `λ`, and let `K` be the next cut key
(no cut strictly between), at which no bracket chord is attached (every chord at `K` has an
attachment inside the stretch) and some chord has an attachment strictly inside the stretch at
positive offset.  Then a candidate chord of `λ` is attached at `K`: the sweep's lazy test finds
the event. -/
theorem next_event_detected (hP : J.P.Simple) {Q : Polygon}
    {S₂ : Set ztf} (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    (hF : (chainModel J.whole).ChordFamily Q ztbi) {G L : Set Point}
    (hG : G ∈ (chainModel J.whole).regions ztbi)
    (hL : L ∈ (chainModel J.right).regions S₂) (hvalid : Valid J S₂ G L)
    {p₀ : ℕ} {t₀ : ℝ} (hp₀ : p₀ < (chainModel J.whole).W.n) (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (hnc₀ : ¬ (chainModel J.whole).IsCut ztbi zthw)
    (hfG₀ : (chainModel J.whole).Faces p₀ t₀ G)
    (ho₀ : ((rL1 J + rL2 J : ℕ) : ℝ) <
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zthw)
    {pK : ℕ} {tK : ℝ} (hpK : pK < (chainModel J.whole).W.n) (htK0 : 0 ≤ tK) (htK1 : tK < 1)
    (hoK : off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zthw <
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztkm)
    (hgap : ∀ x, (chainModel J.whole).IsCut ztbi x → 0 ≤ x →
      x < (chainModel J.whole).W.n →
      ¬ (off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zthw <
          off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) x ∧
        off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) x <
          off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztkm))
    {e : Set Point} (he : e ∈ F₂plus J S₂) (heK : SideAttach (chainModel J.whole).W e pK tK)
    {pB : ℕ} {tB : ℝ} (heB : SideAttach (chainModel J.whole).W e pB tB)
    (heKB : sidePt (chainModel J.whole).W pK tK ≠ sidePt (chainModel J.whole).W pB tB)
    (hB0 : 0 < off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztdhv)
    (hBL : off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztdhv <
      ((rL1 J + rL2 J : ℕ) : ℝ))
    (hnobr : ∀ e' ∈ F₂plus J S₂, SideAttach (chainModel J.whole).W e' pK tK →
      ∃ (pb : ℕ) (tb : ℝ), SideAttach (chainModel J.whole).W e' pb tb ∧
        off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztbd <
          ((rL1 J + rL2 J : ℕ) : ℝ)) :
    ∃ h ∈ Cand J S₂ L, SideAttach (chainModel J.whole).W h pK tK := by
  zucf
  zust
  zudnl
  zuiwc
  zued
  have hgn : ztcx := by
    zucfu
  zupz
  obtain ⟨kK0, kK1⟩ := Corr.key_mem hpK htK0 htK1
  -- a chord of `F₂⁺` attached at a cut key of the `C₁` part after `x₀` is attached at `K`
  have hatK : ∀ {h : Set Point} {pz : ℕ} {tz : ℝ}, h ∈ F₂plus J S₂ →
      SideAttach (chainModel J.whole).W h pz tz → o zthw < o zthe →
      o zthe ≤ o ztkm → SideAttach (chainModel J.whole).W h pK tK := by
    intro h pz tz hh hZ h1 h2
    obtain ⟨z0, z1⟩ := Corr.key_mem hZ.1 hZ.2.1 hZ.2.2.1
    zudt
    · exact absurd by_grind (hgap _ ⟨h, hh, pz, tz, hZ, rfl⟩ z0 z1)
    · have hk := off_inj hg0 hgn z0 z1 kK0 kK1 h2
      obtain ⟨rfl, rfl⟩ := sideKey_inj hZ.2.1 hZ.2.2.1 htK0 htK1 hk
      exact hZ
  by_cases hlab : ∃ V₀ ∈ (chainModel J.right).regions S₂, RLabel J S₂ G V₀
  · -- a labelled region: the chord at `K` on the side of `G`
    have hW := before_faces_of_gap hM hFs hF.1 hg0 hgn hG hp₀ ht₀ hnc₀ hfG₀ hpK htK0 htK1 hoK
      hgap
    by_cases htie : ∃ e' ∈ F₂plus J S₂, e' ≠ e ∧ SideAttach (chainModel J.whole).W e' pK tK
    · zufiy
      have hside : ∃ h ∈ F₂plus J S₂, SideAttach (chainModel J.whole).W h pK tK ∧
          ∃ σ : ℝ, ztdd ∧ SideOf ztbm σ h G := by
        rcases hM.tie_pair hFs he he' ztnr heK hA' with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · obtain ⟨-, hhor, -⟩ := hM.tie_shape hFs he he' heK hA' h1 h2
          have hs := after_side_tie hGM hF he he' hne heK hA' h1 h2 hG
          grind
        · obtain ⟨-, hhor, -⟩ := hM.tie_shape hFs he' he hA' heK h2 h1
          have hs := after_side_tie hGM hF he' he ztnr hA' heK h2 h1 hG
          grind
      obtain ⟨h, hh, hhK, σ, hσ, hS⟩ := hside
      obtain ⟨pb, tb, hb, hbL⟩ := hnobr h hh hhK
      exact ⟨h, cand_of_side J hP hS₂ hF hG hL hvalid hlab hh hσ hS hb hbL, hhK⟩
    · zucyh
      have huniq : ∀ e' ∈ F₂plus J S₂, SideAttach (chainModel J.whole).W e' pK tK → e' = e := by
        grind
      have hS : ∃ σ : ℝ, ztdd ∧ SideOf ztbm σ e G := by
        rcases hM.attach_dir ztcik heK with hd | hd
        · exact ⟨1, Or.inl rfl, before_side hGM hF he heK huniq by_grind hG hW⟩
        · exact ⟨-1, Or.inr rfl, before_side hGM hF he heK huniq by_grind hG hW⟩
      obtain ⟨σ, hσ, hS⟩ := hS
      exact ⟨e, cand_of_side J hP hS₂ hF hG hL hvalid hlab he hσ hS heB hBL, heK⟩
  · -- an unlabelled region
    have hU : ∀ V, ¬ RLabel J S₂ G V := by
      intro V hR
      exact hlab (rlabel_region J hP hS₂.2.1 hS₂.1 hR)
    rcases (detect_valid J hP hS₂ hF hG hL hvalid hp₀ ht₀ hnc₀ hfG₀ ho₀).2 hU with
      ⟨ρ, -, hZ, hhZ, pz, tz, hZA, htrack, hzpos, hfinal⟩ | hT
    · have hnot : ztjax := fun h =>
        hfinal e he pK tK pB tB heK heB heKB hoK h hBL hB0.ne'
      zudrw
      zuicv
      rcases hzpos with h | ⟨-, hz⟩
      · grind
      have hZK := hatK hhZ hZA hz hzK
      refine ⟨hZ, ⟨hhZ, ?_⟩, hZK⟩
      rcases htrack with ⟨c, hc, hZc, V', -, hrel, hVs⟩ | hk | hk
      · refine Or.inl ⟨c, hc, hZc, V', ?_, touches_of_sideOf J hS₂.2.1 hc hVs⟩
        rcases hrel with rfl | ⟨-, h⟩
        · tauto
        tauto
      · grind
      grind
    · obtain ⟨e₁, e₂, d, pb, pb', tb, tb', ρ, he₁, he₂, hne, hd0, hd, hA₁, hA₂, hB₁, hB₂, hBne₁,
        hBne₂, hout₁, hout₂, hρ, hS₁, hS₂', ht₁, ht₂⟩ := hT
      zurn
      zuinr
      obtain ⟨-, hy₁, -⟩ := hM.attach_seg (hFs he₁) hA₁ hB₁ ztqav
      obtain ⟨-, hy₂, -⟩ := hM.attach_seg (hFs he₂) hA₂ hB₂ ztqaw
      have hx₁ : ztdrh :=
        by grind
      have hx₂ : ztdri :=
        by grind
      have hopp := tie_opposite hM hFs he₁ he₂ hne hA₁ hA₂ hB₁.2.2.2.1 hB₂.2.2.2.1 hx₁ hx₂
      obtain ⟨θ, hθ, hori⟩ := exists_sign hρ (sub_ne_zero.2 (Ne.symm hx₁))
      have hθρ : ztxfm := by
        zugl
      have hori' : ztxpm := by
        have e1 : -θ * ρ * ztbak =
            θ * ρ * ztix := by_ring
        zukd
        have hprod : 0 < ztrm *
            ztwvg := by
          have e2 : ztrm *
              ztwvg =
              ztxho * (-(ztdem *
                ztix)) := by_ring
          zubyo

        zugkj
      have hAL : o ztckh < ((rL1 J + rL2 J : ℕ) : ℝ) := by
        have hoA : o ztckh = d + 0 := hC.off_M hd le_rfl zero_lt_one
        zueyd
        zubfq
        linarith
      -- the forward chord of the tie and its far attachment
      obtain ⟨ff, hff, pf, tf, hfF, htf, hfe, hclear⟩ : ∃ ff ∈ F₂plus J S₂, ∃ (pf : ℕ) (tf : ℝ),
          SideAttach W ff pf tf ∧ J.right.top ∈ ff ∧
          (o ztbbc = 0 ∨ (((rL1 J + rL2 J : ℕ) : ℝ) ≤ o ztbbc ∧
            o _ < o ztbbc)) ∧
          ∀ e ∈ F₂plus J S₂, ∀ (pw : ℕ) (tw : ℝ) (pb : ℕ) (tb : ℝ),
            SideAttach W e pw tw → SideAttach W e pb tb → sidePt W pw tw ≠ sidePt W pb tb →
            o _ < o ztbjs → (o ztbbc = 0 ∨ o ztbjs < o ztbbc) →
            o ztbd < ((rL1 J + rL2 J : ℕ) : ℝ) → o ztbd ≠ 0 → False := by
        zugaf
        · obtain ⟨h1, h2⟩ := bracket_tie J hP hS₂ hF hρ hG he₂ he₁ hne hAL hA₂ hA₁ hB₂ hB₁
            ztqaw ztqav hS₂' hS₁ by_linarith hori hout₂ hout₁ hp₀ ht₀ hnc₀
            hfG₀ ho₀
          exact ⟨e₁, he₁, pb, tb, hB₁, ht₁, h1, h2⟩
        · obtain ⟨h1, h2⟩ := bracket_tie J hP hS₂ hF hρ hG he₁ he₂ ztnr hAL hA₁ hA₂
            hB₁ hB₂ ztqav ztqaw hS₁ hS₂' hori by_linarith hout₁ hout₂ hp₀
            ht₀ hnc₀ hfG₀ ho₀
          exact ⟨e₂, he₂, pb', tb', hB₂, ht₂, h1, h2⟩
      have hnot : ztjax := fun h =>
        hclear e he pK tK pB tB heK heB heKB hoK h hBL hB0.ne'
      zudrw
      zuicv
      rcases hfe with h | ⟨-, hz⟩
      · grind
      exact ⟨ff, ⟨hff, Or.inr (Or.inr htf)⟩, hatK hff hfF hz hzK⟩

/-! ## The loop invariant of the RAM -/
omit J in
/-- **No cut between two positions**: two non-cut positions inside walk edges with no cut strictly
between them (in offsets from `g`) face the same region. -/
theorem same_region_of_gap {M : Model} (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) {g : ℝ} (hg0 : 0 ≤ g) (hgn : g < M.W.n) {U U' : Set Point}
    (hU : U ∈ M.regions F) (hU' : U' ∈ M.regions F) {p p' : ℕ} {t t' : ℝ} (hp : p < M.W.n)
    (hp' : p' < M.W.n) (ht : t ∈ Ioo (0 : ℝ) 1) (ht' : t' ∈ Ioo (0 : ℝ) 1)
    (hc : ¬ M.IsCut F ztk) (hc' : ¬ M.IsCut F ztjg) (hf : M.Faces p t U)
    (hf' : M.Faces p' t' U') (hlt : off M.W.n g ztk < off M.W.n g ztjg)
    (hgap : ∀ x, M.IsCut F x → 0 ≤ x → x < M.W.n →
      ¬ (off M.W.n g ztk < off M.W.n g x ∧ off M.W.n g x < off M.W.n g ztjg)) :
    U = U' := by
  refine (hM.eq_iff_not_separates hF hfin hU hU' hp hp' ht ht' hc hc' hf hf').2
    fun c hcF ⟨qa, qb, sa, sb, hQA, hQB, hQAB, hsep⟩ => ?_
  zubhm
  zufzh
  zucho

  have hxa := fun h => hc ztkjt
  have hxb := fun h => hc ztkju
  have hya := fun h => hc' ztkjt
  have hyb := fun h => hc' ztkju
  have hxy : ztkzg := by
    grind
  zubge

  have hnot : ∀ {r : ℕ} {v : ℝ}, SideAttach M.W c r v →
      ¬ Btw (off M.W.n g ztdj) (off M.W.n g ztbiz) (off M.W.n g ztmzo) := by
    zudqh

    have hcut : ztidq := ⟨c, hcF, r, v, hR, rfl⟩
    zulto

  grind
end Cand
end Sweep
open Chazelle.Chain (freeIn regionsIn)
namespace Sweep
variable {n g : ℕ}
/-- Offsets along one walk edge. -/
theorem off_add_small (_hg : g < n) {p : ℕ} (_hp : p < n) {t s : ℝ} (ht : 0 ≤ t)
    (hs : 0 ≤ s) (hts : t + s < 1) :
    off n g ztwoq = off n g ztdj + s := by
  zumtr
  have hgp : (g : ℝ) ≤ p ∨ (p : ℝ) + 1 ≤ g := by
    rcases le_or_gt g p with h | h
    · simp_all
    · right; exact_mod_cast h
  grind

/-- A key whose offset is slightly above that of `(p, t)` (on the same edge) is the key
`p + t + u`. -/
theorem eq_of_off_small (hg : g < n) {p : ℕ} (hp : p < n) {t u x : ℝ} (ht : 0 ≤ t)
    (hu : 0 ≤ u) (htu : t + u < 1) (hx0 : 0 ≤ x) (hxn : x < n)
    (h : off n g x = off n g ztdj + u) : x = (p : ℝ) + t + u := by
  have hpn : ztcjz := by exact_mod_cast hp
  have hgn : ztcrg := by_simp_all
  zuhqx
variable {M : Model}

/-- **The region faced just after a key**, and a cut-free stretch after it. -/
theorem after_region_exists (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) {g : ℕ} (hg : g < M.W.n) {p : ℕ} (hp : p < M.W.n) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t < 1) :
    ∃ δ > (0 : ℝ), t + δ ≤ 1 ∧ (∀ s ∈ Ioo (0 : ℝ) δ, ¬ M.IsCut F ztwoq) ∧
      ∃ G ∈ M.regions F, AfterFaces M p t G := by
  obtain ⟨δ₀, hδ₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1
    ztzeq
  have hδ₀' : (0 : ℝ) < δ₀ := hδ₀
  set δ := min δ₀ ztca with hδ
  have hδ0 : ztcfy := lt_min hδ₀' by_linarith
  have hδ1 : δ ≤ δ₀ := min_le_left _ _
  have hδ2 : δ ≤ 1 - t := min_le_right _ _
  have hnc : ∀ s ∈ Ioo (0 : ℝ) δ, ¬ M.IsCut F ztwoq := by
    zugg
    have := hsub ⟨hs.1, lt_of_lt_of_le hs.2 hδ1⟩
    grind
  refine ⟨δ, hδ0, by_linarith, hnc, ?_⟩
  obtain ⟨U, hU, hfU⟩ := hM.exists_faces_of_not_cut hF hfin hp
    (t := t + δ / 2) ztbcx (hnc ztbfe ztbcx)
  refine ⟨U, hU, δ, hδ0, fun s hs0 hs1 hs2 => ?_⟩
  have hcs : ¬ M.IsCut F ztwoq := hnc s ztdxi
  obtain ⟨U', hU', hfU'⟩ := hM.exists_faces_of_not_cut hF hfin hp (t := t + s)
    ⟨by_linarith, hs2⟩ hcs
  suffices U' = U by zvnnr; exact hfU'
  zueqz
  have hgn : ztehn := by exact_mod_cast hg
  -- positions of the cut-free stretch face one region
  have key : ∀ a b : ℝ, 0 < a → a < b → b < δ → ∀ A B : Set Point, A ∈ M.regions F →
      B ∈ M.regions F → M.Faces p (t + a) A → M.Faces p (t + b) B → A = B := by
    intro a b ha hab hb A B hA hB hfA hfB
    refine same_region_of_gap hM hF hfin hg0 hgn hA hB hp hp ztbcx
      ⟨by_linarith, by_linarith⟩ (hnc a ⟨ha, by_linarith⟩)
      (hnc b ⟨by_linarith, hb⟩) hfA hfB ?_ ?_
    · rw [off_add_small hg hp ht0 ha.le by_linarith,
        off_add_small hg hp ht0 by_linarith by_linarith]
      linarith
    · intro x hx hx0 hxn ⟨h1, h2⟩
      rw [off_add_small hg hp ht0 ha.le by_linarith] at h1
      rw [off_add_small hg hp ht0 by_linarith by_linarith] at h2
      set u := off M.W.n g x - off M.W.n g ztdj with hu
      have hxe := eq_of_off_small hg hp ht0 (u := u) by_linarith by_linarith hx0 hxn
        by_grind
      exact hnc u ztbcx by_grind
  rcases lt_trichotomy s ztbfe with h | h | h
  · grind
  · subst h; exact WalkAx.faces_unique hU' hU hfU' hfU
  grind
end Sweep
end
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft freeIn regionsIn)
open WalkEmbed
namespace Sweep
section Machine
variable (J : Merge.Junction)

/-- `λ` is a valid label of every region of `F₂⁺` on the side `ρ` of the chord `e`. -/
def SideLabel (S₂ : Set ztf) (e : Set Point) (ρ : ℝ) (L : Set Point) : Prop :=
  ∀ G ∈ (chainModel J.whole).regions ztbi, SideOf ztbm ρ e G →
    Valid J S₂ G L

/-- **Rule for a fused chord**: `e ⊆ c ∈ S₂` attached at the stretch position `d` (not the base,
not the split vertex): the side labels of `e` are the regions of `S₂` on the same side of `c`. -/
theorem sideLabel_fused (hP : J.P.Simple) {Q : Polygon}
    {S₂ : Set ztf} (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    (hF : (chainModel J.whole).ChordFamily Q ztbi) {e c : Set Point}
    (he : e ∈ F₂plus J S₂) (hc : c ∈ S₂) (hec : e ⊆ c) {d : ℕ} (hd : d < rL1 J + rL2 J)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (hsec : t = 0 → d ≠ 0 ∧ d ≠ rL1 J)
    (hA : SideAttach (chainModel J.whole).W e
      ztbn t)
    {ρ : ℝ} (hρ : ρ = 1 ∨ ρ = -1) {V : Set Point} (hV : V ∈ (chainModel J.right).regions S₂)
    (hVs : SideOf ztj ρ c V) : SideLabel J S₂ e ρ V :=
  fun _G hG hS => valid_of_vlabel J hP hS₂ hF hG hV
    ⟨e, c, ρ, d, t, he, hc, hec, hρ, hd, ht0, ht1, hsec, hA, hS, hVs⟩
end Machine
end Sweep
end
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft freeIn regionsIn)
open WalkEmbed
namespace Sweep
section Machine
variable (J : Merge.Junction)

/-- **The regions of a pocket have no label**: a chord of `F₂⁺` attached at the base copy of the
shared vertex (offset `0`) and at a key `A` of the `C₁` part; every non-cut position after `A`
faces an unlabelled region. -/
theorem no_label_of_pocket (hP : J.P.Simple) {S₂ : Set ztf}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {G : Set Point}
    (hG : G ∈ (chainModel J.whole).regions ztbi) {e : Set Point}
    (he : e ∈ F₂plus J S₂) {pa pb : ℕ} {ta tb : ℝ}
    (hA : SideAttach (chainModel J.whole).W e pa ta) (hB : SideAttach (chainModel J.whole).W e pb tb)
    (hAB : sidePt (chainModel J.whole).W pa ta ≠ sidePt (chainModel J.whole).W pb tb)
    (hAo : ((rL1 J + rL2 J : ℕ) : ℝ) ≤
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztbf)
    (hBo : off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztbd = 0)
    {px : ℕ} {tx : ℝ} (hpx : px < (chainModel J.whole).W.n) (htx : tx ∈ Ioo (0 : ℝ) 1)
    (hcx : ¬ (chainModel J.whole).IsCut ztbi ztcat)
    (hfx : (chainModel J.whole).Faces px tx G)
    (hx : off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztbf <
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztcat) :
    ∀ V, ¬ RLabel J S₂ G V := by
  zudjo
  zuv
  zupo

  have hne := (hC.hM.eq_iff_not_separates hC.hF hC.hfin hG hG hpx zthp htx ht hcx
    hc hfx hf).1 rfl e he
  zudgo

  zucu

  zucii

  have hoy : ztbaol := off_key hg (by have := hC.hL; omega)
    ht.1.le ht.2
  have hyrl : ztfkl := by
    zubfq
    zujcc
  have hy0 : ztgti := by have := ht.1; positivity
  have hxy : ztxcz := by
    grind
  zuis

  rw [hoy, hBo]
  unfold Btw
  grind

/-- **The two attachments of a chord are its two ends**: the chord leaves them in opposite
directions. -/
theorem dir_opposite {M : Model} (hM : WalkAx M) {e : Set Point} (he : e ∈ M.Adm) {pa pb : ℕ}
    {ta tb : ℝ} (hA : SideAttach M.W e pa ta) (hB : SideAttach M.W e pb tb)
    (hAB : sidePt M.W pa ta ≠ sidePt M.W pb tb)
    (hdA : ∀ z ∈ e, (sidePt M.W pa ta).1 ≤ z.1) : ∀ z ∈ e, z.1 ≤ (sidePt M.W pb tb).1 := by
  obtain ⟨a, b, hab, hcab, hy, -, -, -⟩ := hM.ends e he
  obtain ⟨a', b', -, hcab', hend⟩ := end_of_not_mem hM he
  have hAe := hA.2.2.2.1
  have hBe := hB.2.2.2.1
  have hAD : sidePt M.W pa ta ∉ M.D := hM.trace pa hA.1 ta hA.2.1 hA.2.2.1.le
  have hBD : sidePt M.W pb tb ∉ M.D := hM.trace pb hB.1 tb hB.2.1 hB.2.2.1.le
  have hA' := hend _ hAe hAD
  have hB' := hend _ hBe hBD
  rw [hcab'] at hAe hBe ⊢
  zugh
  zuje
  have ha'e : a' ∈ e := by_grind
  have hb'e : b' ∈ e := by_grind
  have h1 := hdA a' ha'e
  have h2 := hdA b' hb'e
  zudlh
  rcases hA' with hA' | hA' <;> rcases hB' with hB' | hB'
  · simp_all
  · zuodu; rw [hA'] at h2; nlinarith
  · zuodu; rw [hA'] at h1; nlinarith
  simp_all

/-- **The initial label**: the region faced just before the start of the `C₁` part (the copy of the
shared vertex at offset `L`) has the label `λ₀` faced in the model of `C₂` just before the end of
the right stretch. -/
theorem valid_start (hP : J.P.Simple) {S₂ : Set ztf}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) (hL1 : 1 ≤ rL1 J + rL2 J)
    {G V : Set Point} (hG : G ∈ (chainModel J.whole).regions ztbi)
    (hV : V ∈ (chainModel J.right).regions S₂)
    (hW : BeforeFaces ztbm
      ((6 + tpos J.whole J.m₁ + ztqvg) % (chainModel J.whole).W.n) 0 G)
    (hW₂ : BeforeFaces ztj
      (ztwug %
        (chainModel J.right).W.n) 0 V) :
    Valid J S₂ G V :=
  valid_of_rlabel J hP hS₂ hS₂f hG hV
    (rlabel_before0 J hP hS₂ hS₂f hL1 le_rfl hW hW₂)
end Machine
end Sweep
end
end Chazelle.Core
section
set_option hygiene false
local macro "zqblk" : tactic => `(tactic| (have h1 := C.topIdx_min hT by_simp_all
                                           by_contra hne
                                           have h2 := C.vertex_snd_le_top hT
                                           unfold Chain.top at h2
                                           rw [ev T hT, ev _ C.topIdx_le] at h2))
local macro "zqbll" : tactic => `(tactic| all_goals exact r₄ _ by_decide by_decide by_decide by_decide)
set_option hygiene true

/-!
# Down-phase pieces (D4), part 4: the top and the orientation bit of a host chain

Mathematics: for a chain `C = ⟨H.poly Q, s, m⟩` of a host,

* `hchain_vertex`: its vertices are the evaluated host points `(s + k) mod N`;
* `hchain_topIdx`: the least offset of a highest point (`scanS`) is the top index;
* `hchain_topIdx_leaf`: on a leaf (the points are vertices of `Q`, distinct heights) every
  offset of a highest point (`gTop`) is the top index;
* `sideCcw_up'`, `sideBeta_iff'`: the orientation bit from six sign tests at the top, for any
  chain whose top is not its first vertex — the neighbour after the top may be at the same height
  (host chains have horizontal chord edges), which `Brute.sideCcw_up` excludes;
* `hchain_beta`: the same on the host points.

RAM: `betaS` (`betaS_exec`): `218014 := 0` if `T = 0`, else three host lookups (the points
before, at and after the top, the last one modulo `N`), the six sign tests of `IOrc.testsI`
into `170082 … 170088` and the decision tree `IOrc.logI`.
-/
namespace Chazelle.Core
namespace DrvP
open Machine Machine.Stmt Programs SignK WalkKey NFLoc SweepPrim
open Chazelle.Chain (sideCcw sideCross sideDot)
@[expose] public section
theorem sideCcw_up' {a v b : Point} {h : ℝ} (hh : 0 < h) (ha : a.2 < v.2) :
    sideCcw ztfd ztbdn ztgg ↔
      zthqo ∨ ztgrh ∨
      zthwi ∨ ztkvs := by
  zufqy
  swap
  · exact Brute.sideCcw_up hh ha hb
  zuhdt
  have hdet : det a v b = ztry * ztclz := by
    rw [← e1]; unfold sideCross; simp_all
  have e2 : ztyzc := by
    zule
  have e3 : ztyzb := by
    zule
  have e4 : sideDot ztfd ztbdn = 0 := by
    zumur
  have e5 : sideDot ztfd ztgg = ztry * ztcts := by
    zumur
  zufqe
  rw [e1, e2, e3, e4, e5, hdet, hb]
  rcases lt_trichotomy b.1 v.1 with h1 | h1 | h1
  · have p1 : 0 < ztry * ztclz := mul_pos_of_neg_of_neg by_linarith by_linarith
    have p2 : h * ztry < 0 := mul_neg_of_pos_of_neg hh by_linarith
    grind
  · simp_all
  · have p1 : ztry * ztclz < 0 := mul_neg_of_pos_of_neg by_linarith by_linarith
    simp_all

/-- **The orientation bit of a chain** whose top is not its first vertex (no distinct heights
needed). -/
theorem sideBeta_iff' (C : Chain) (h0 : 0 < C.topIdx) :
    C.sideBeta = true ↔ IOrc.BetaF ztxux C.top ztxuw := by
  zumlc
  have hsl : ztzon := by
    zulbb
  zumog
  zuwi
  have ha : ztxsv := by
    refine lt_of_le_of_ne (C.vertex_snd_le_top by_omega) ztdnv
    have := C.topIdx_min (j := C.topIdx - 1) by_omega (fun i hi => by
      zvmwe; exact C.vertex_snd_le_top hi)
    omega
  rw [sideCcw_up' ztqem ha]
  unfold IOrc.BetaF
  grind

/-! ## Host chains -/
section hostchain
variable {P : Polygon} {H : Host} {C : Chain}
theorem qof_n (P : Polygon) : (Qof P).n = P.n := shear_n _ _
theorem hchain_n (hC : C.P = H.poly zta) : C.P.n = (H.pts P.n).length := by
  rw [hC, DownMath.host_poly_n, qof_n]

/-- The vertices of a host chain are evaluated host points. -/
theorem hchain_vertex (hC : C.P = H.poly zta) (k : ℕ) :
    C.vertex k = (pt H P.n (zttw % (H.pts P.n).length)).eval zta := by
  have hn := hchain_n hC
  have hpos := C.n_pos
  show C.P.vtx ztbaay = _
  have hlt : zttw % (H.pts P.n).length < (H.pts (Qof P).n).length := by
    rw [qof_n]; exact Nat.mod_lt _ by_omega
  rw [hn, hC, DownMath.host_poly_vtx _ _ hlt, qof_n]
  rfl
theorem hchain_vertex_lt (hC : C.P = H.poly zta) {k : ℕ}
    (hk : C.s + k < (H.pts P.n).length) : C.vertex k = (pt H P.n zttw).eval zta := by
  rw [hchain_vertex hC, Nat.mod_eq_of_lt hk]

/-- **The top index of a host chain** is the least offset of a highest point. -/
theorem hchain_topIdx (hC : C.P = H.poly zta) (hsm : C.s + C.m < (H.pts P.n).length)
    {T : ℕ} (hT : T ≤ C.m) (hle : ∀ j, j ≤ C.m → Yh P H ztjhj ≤ Yh P H ztsvy)
    (hlt : ∀ j, j < T → Yh P H ztjhj < Yh P H ztsvy) : C.topIdx = T := by
  have ev : ∀ j, j ≤ C.m → (C.vertex j).2 = Yh P H _ := fun j hj => by
    rw [hchain_vertex_lt hC by_omega]; rfl
  zqblk
  have := hlt C.topIdx by_omega
  linarith

/-- **The top index of a leaf** (its points are the vertices `a, …, a + m` of `Q`, of distinct
heights) is every offset of a highest point. -/
theorem hchain_topIdx_leaf (hC : C.P = H.poly zta) (hsm : C.s + C.m < (H.pts P.n).length)
    (hD : DistinctHeights zta) {a : ℕ} (han : a + C.m < P.n)
    (hpt : ∀ k, k ≤ C.m → pt H P.n zttw = .vtx ztbzd) {T : ℕ} (hT : T ≤ C.m)
    (hle : ∀ j, j ≤ C.m → IOrc.Y P ztdgj ≤ IOrc.Y P (a + T)) : C.topIdx = T := by
  have ev : ∀ j, j ≤ C.m → (C.vertex j).2 = IOrc.Y P _ := fun j hj => by
    rw [hchain_vertex_lt hC by_omega, hpt j hj]; rfl
  zqblk
  have h3 := hle _ C.topIdx_le
  zubp
  exact hD _ _ by_omega by_omega
    by_omega zttrw

/-- **The orientation bit of a host chain** from the host points before, at and after the top. -/
theorem hchain_beta (hC : C.P = H.poly zta) (hT0 : 0 < C.topIdx)
    (hsT : C.s + C.topIdx < (H.pts P.n).length) :
    C.sideBeta = true ↔ IOrc.BetaF ((pt H P.n ztgdh).eval zta)
      ((pt H P.n ztwi).eval zta)
      ((pt H P.n ((C.s + C.topIdx + 1) % (H.pts P.n).length)).eval zta) := by
  rw [sideBeta_iff' C hT0, hchain_vertex_lt hC by_omega,
    show C.s + ztbap = C.s + C.topIdx - 1 by omega]
  zultq
  rw [hchain_vertex_lt hC hsT, hchain_vertex hC, ← Nat.add_assoc]
end hostchain

/-! ## The program -/

/-- The host point of index `src` into the slot `d`. -/
def lkTo (src d : ℕ) : Stmt := .seq (block [.copyN 50071 src])
  (.seq lookStmt ztxng)

/-- The indices of the points before, at and after the top. -/
def nbrS : Stmt :=
  .seq (block [.addN 218050 218001 218013, .subN 218051 218050 218021,
    .addN 218052 218050 218021])
    (.ifLtN 218052 218012 .skip (block [.constN 218052 0]))

/-- The six sign tests (the bits of `IOrc.logI`). -/
def testsS : Stmt :=
  .seq (kbit 218053 218056 218059 2 170082) (.seq (kbit 218053 218056 218059 3 170083)
  (.seq (kbit 218056 218059 218056 0 170085) (.seq (kbit 218053 218056 218053 0 170086)
  (.seq (kbit 218056 218059 218056 1 170087) (kbit 218059 218056 218059 1 170088)))))

/-- The orientation bit for a top that is not the first vertex. -/
def bitI : Stmt :=
  .seq nbrS (.seq (lkTo 218051 218053) (.seq (lkTo 218050 218056) (.seq (lkTo 218052 218059)
    (.seq testsS (.seq (block [.constN 170012 0]) (.seq IOrc.logI
      (block [.copyN 218014 170075])))))))

/-- **The orientation bit** into `218014`. -/
def betaS : Stmt := .ifLtN 218020 218013 bitI (block [.constN 218014 0])

/-- The registers `betaS` writes. -/
def Bbit (r : ℕ) : Bool :=
  decide ztgze || Bk r || decide ztgxw ||
    decide (r = 218014) || decide (218050 ≤ r ∧ r < 218062)
theorem wr_betaS : wr Bbit betaS = true := by
  rfl

/-! ## Execution -/
section exec
variable {P : Polygon} {W : ℕ}

/-- **A host point into a slot.** -/
theorem lkTo_exec {H : Host} {m₀ : ℕ → ℕ} {HB : ℕ} (E : ScE P W H m₀ HB) (c : Config)
    (hE : HostEnv W HB H.length m₀ c) {src d p : ℕ} (hsrc : c.nreg src = p)
    (hp : p < (H.pts P.n).length) (hd : 50080 ≤ d) :
    ∃ c' k, Exec P W zttsk c c' k ∧ k ≤ 1737 ∧ HostEnv W HB H.length m₀ c' ∧
      SymPtIn c' d ztlrv ∧
      (∀ r, Bhost r = false → r ≠ d → r ≠ d + 1 → r ≠ d + 2 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem := by
  zuyv
  obtain ⟨c₁, k₁, e₁, hk₁, v71, r₁, m₁⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 50071 src])
      c c₁ k₁ ∧ k₁ = 1 ∧ c₁.nreg 50071 = p ∧ ztedg ∧
      c₁.nmem = c.nmem := by
    exec_block
    simp_all
  have E₁ : zthof := ⟨e₁.wb_right, by zvmww; exact hE.h60,
    by zvmww; exact hE.h61, by zvmww; exact hE.h67,
    by zvmww; exact hE.h68, by zvmww; exact hE.h69,
    by zvmxn; exact hE.mem⟩
  obtain ⟨c₂, k₂, e₂, hk₂, F₂, E₂, s₂⟩ := look_pt E c₁ E₁ v71 hp
  zue
  obtain ⟨c₃, k₃, e₃, hk₃, s₃, r₃, m₃⟩ : ∃ c₃ k₃, Exec P W
      ztxng c₂ c₃ k₃ ∧ k₃ = 3 ∧
      SymPtIn c₃ d ztlrv ∧
      (∀ r, r ≠ d → r ≠ d + 1 → r ≠ d + 2 → c₃.nreg r = c₂.nreg r) ∧ c₃.nmem = c₂.nmem := by
    exec_block
    refine ⟨rfl, symPtIn_copy s₂ ?_ ?_ ?_, fun r h1 h2 h3 => ?_, rfl⟩
    · simp
    · zufx
    · zufx
    simp_all
  have ex : Exec P W zttsk c c₃ _ := .seq e₁ ztcr
  refine ⟨c₃, _, ex, by_omega, ⟨e₃.wb_right, ?_, ?_, ?_, ?_, ?_, by zumzp; exact E₂.mem⟩, s₃,
    fun r h0 h1 h2 h3 => ?_, by zunyf⟩
  all_goals try (rw [r₃ _ by_omega by_omega by_omega])
  · exact E₂.h60
  · exact E₂.h61
  · exact E₂.h67
  · exact E₂.h68
  · exact E₂.h69
  · rw [F₂.1 r h0, r₁ r (by rintro rfl; simp [Bhost] at h0)]

/-- The indices of the neighbours of the top. -/
theorem nbrS_exec (c : Config) (hw : WordsBounded W c) {s T N : ℕ} (h01 : c.nreg 218001 = s)
    (h13 : c.nreg 218013 = T) (h21 : c.nreg 218021 = 1) (h12 : c.nreg 218012 = N)
    (_hT : 1 ≤ T) (hsT : s + T < N) (hNW : N ≤ W) :
    ∃ c' k, Exec P W nbrS c c' k ∧ k ≤ 6 ∧ c'.nreg 218050 = s + T ∧
      c'.nreg 218051 = s + T - 1 ∧ c'.nreg 218052 = ztkeg % N ∧
      (∀ r, r ≠ 218050 → r ≠ 218051 → r ≠ 218052 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem := by
  obtain ⟨c₁, k₁, e₁, hk₁, v50, v51, v52, r₁, m₁⟩ : ∃ c₁ k₁, Exec P W
      (block [.addN 218050 218001 218013, .subN 218051 218050 218021, .addN 218052 218050 218021])
      c c₁ k₁ ∧ k₁ = 3 ∧ c₁.nreg 218050 = s + T ∧ c₁.nreg 218051 = s + T - 1 ∧
      c₁.nreg 218052 = s + T + 1 ∧
      (∀ r, r ≠ 218050 → r ≠ 218051 → r ≠ 218052 → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem := by
    exec_block
    · omega
    · config_simp; omega
    simp_all
  zud
  have n₁ : c₁.nreg 218012 = N := by_simp_all
  by_cases hc : c₁.nreg 218052 < c₁.nreg 218012
  · refine spec_seq ⟨c₁, k₁, e₁, spec_ifLtN_true hc (spec_skip w₁ ⟨by_omega, v50, v51, ?_, r₁, m₁⟩)⟩
    rw [v52, Nat.mod_eq_of_lt by_omega]
  · refine spec_seq ⟨c₁, k₁, e₁, spec_ifLtN_false hc ?_⟩
    exec_block
    · omega
    refine ⟨by_omega, by_simp_all, by_simp_all, ?_, fun r a b d => ?_,
      m₁⟩
    · config_simp
      rw [v52, n₁] at hc
      rw [show s + T + 1 = N by omega, Nat.mod_self]
    simp_all
theorem bkb_ne {r d : ℕ} (h : r < 10000 ∨ 10500 ≤ r) (hd : r ≠ d) : SweepPrim.Bkb d r = false := by
  simp only [SweepPrim.Bkb, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not,
    beq_eq_false_iff_ne]; omega

/-- One kernel bit into a register of band `17`, with its frame. -/
theorem kbit17 (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (c : Config) (hw : WordsBounded W c)
    {a b d op dst : ℕ} (ha : 218000 ≤ a) (hb : 218000 ≤ b) (hd : 218000 ≤ d)
    (hdst1 : 170000 ≤ dst) (hdst2 : dst < 170100) (hop : op ≤ 3) {sa sb sd : SymPt}
    (hla : sa.Lt P.n) (hlb : sb.Lt P.n) (hld : sd.Lt P.n) (hsa : SymPtIn c a sa)
    (hsb : SymPtIn c b sb) (hsd : SymPtIn c d sd) :
    ∃ c' k, Exec P W ztfib c c' k ∧ k ≤ 241 ∧
      BitIs c' dst (SignTest op ztxhi ztxoq ztbaiq) ∧
      (∀ r, ztcu → r ≠ dst → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem := by
  obtain ⟨c', k, e, hk, F, b1, b2⟩ := kbit_exec hG hW c hw (a := a) (b := b) (d := d) (op := op)
    (dst := dst) by_omega by_omega by_omega by_omega hop hla hlb hld hsa hsb hsd
  exact ⟨c', k, e, hk, ztomj, fun r h1 h2 => F.1 r (bkb_ne h1 h2), F.2.2.1⟩

/-- **The six sign tests** on the slots `218053` (`A`), `218056` (`V`), `218059` (`B`). -/
theorem testsS_exec (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (c : Config) (hw : WordsBounded W c)
    {A V B : SymPt} (hA : A.Lt P.n) (hV : V.Lt P.n) (hB : B.Lt P.n) (sA : SymPtIn c 218053 A)
    (sV : SymPtIn c 218056 V) (sB : SymPtIn c 218059 B) :
    ∃ c' k, Exec P W testsS c c' k ∧ k ≤ 1446 ∧
      BitIs c' 170082 (0 < det ztbadq ztbafm ztbadr) ∧
      BitIs c' 170083 (det ztbadq ztbafm ztbadr = 0) ∧
      BitIs c' 170085 ((V.eval zta).1 < (B.eval zta).1) ∧
      BitIs c' 170086 ((A.eval zta).1 < (V.eval zta).1) ∧
      BitIs c' 170087 ((V.eval zta).2 < (B.eval zta).2) ∧
      BitIs c' 170088 ((B.eval zta).2 < (V.eval zta).2) ∧
      (∀ r, ztcu → ztbqm → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem := by
  -- slots survive every kernel bit
  have keep : ∀ {d d' : Config} {x : ℕ} {sp : SymPt}, SymPtIn d x sp → 218000 ≤ x →
      (∀ r, ztcu → ztbqm → d'.nreg r = d.nreg r) →
      SymPtIn d' x sp := fun h hx hr => symPtIn_copy h by_grind
        by_grind by_grind
  obtain ⟨c₁, k₁, e₁, hk₁, b₁, r₁, m₁⟩ := kbit17 (op := 2) (dst := 170082) hG hW c hw
    by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num hA hV hB
    sA sV sB
  have f₁ : ∀ r, ztcu → ztbqm → c₁.nreg r = c.nreg r :=
    by grind
  obtain ⟨c₂, k₂, e₂, hk₂, b₂, r₂, m₂⟩ := kbit17 (op := 3) (dst := 170083) hG hW c₁ e₁.wb_right
    by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num hA hV hB
    (keep sA by_norm_num f₁) (keep sV by_norm_num f₁) (keep sB by_norm_num f₁)
  have f₂ : ∀ r, ztcu → ztbqm → c₂.nreg r = c.nreg r :=
    by grind
  obtain ⟨c₃, k₃, e₃, hk₃, b₃, r₃, m₃⟩ := kbit17 (op := 0) (dst := 170085) hG hW c₂ e₂.wb_right
    by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num hV hB hV
    ztrsr (keep sB by_norm_num f₂) ztrsr
  have f₃ : ∀ r, ztcu → ztbqm → c₃.nreg r = c.nreg r :=
    by grind
  obtain ⟨c₄, k₄, e₄, hk₄, b₄, r₄, m₄⟩ := kbit17 (op := 0) (dst := 170086) hG hW c₃ e₃.wb_right
    by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num hA hV hA
    ztrsp (keep sV by_norm_num f₃) ztrsp
  have f₄ : ∀ r, ztcu → ztbqm → c₄.nreg r = c.nreg r :=
    by grind
  obtain ⟨c₅, k₅, e₅, hk₅, b₅, r₅, m₅⟩ := kbit17 (op := 1) (dst := 170087) hG hW c₄ e₄.wb_right
    by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num hV hB hV
    ztrss (keep sB by_norm_num f₄) ztrss
  have f₅ : ∀ r, ztcu → ztbqm → c₅.nreg r = c.nreg r :=
    by grind
  obtain ⟨c₆, k₆, e₆, hk₆, b₆, r₆, m₆⟩ := kbit17 (op := 1) (dst := 170088) hG hW c₅ e₅.wb_right
    by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num hB hV hB
    ztrsq (keep sV by_norm_num f₅) ztrsq
  have ex : Exec P W testsS c c₆ _ :=
    .seq e₁ ztfv
  refine ⟨c₆, _, ex, by_omega, ?_, ?_, ?_, ?_, ?_, b₆, by_grind, by_grind⟩
  · refine b₁.of_eq ?_
    grind
  · refine b₂.of_eq ?_
    grind
  · refine b₃.of_eq ?_
    grind
  · refine b₄.of_eq ?_
    grind
  · refine b₅.of_eq ?_
    grind
set_option maxHeartbeats 2000000 in
/-- **The orientation bit**: `218014 := 1` iff the top offset `T` (`218013`) is positive and the
six sign tests at the host points `s + T - 1`, `s + T`, `(s + T + 1) mod N` give `BetaF`. -/
theorem betaS_exec {H : Host} {m₀ : ℕ → ℕ} {HB : ℕ} (E : ScE P W H m₀ HB) (c : Config)
    (hE : HostEnv W HB H.length m₀ c) (h12 : c.nreg 218012 = (H.pts P.n).length)
    (h20 : c.nreg 218020 = 0) (h21 : c.nreg 218021 = 1)
    (hsT : c.nreg 218001 + c.nreg 218013 < (H.pts P.n).length) :
    ∃ c' k, Exec P W betaS c c' k ∧ k ≤ 7000 ∧ FrameB Bbit c c' ∧ c'.nreg 218014 ≤ 1 ∧
      (c'.nreg 218014 = 1 ↔ 0 < c.nreg 218013 ∧
        IOrc.BetaF ((pt H P.n (c.nreg 218001 + c.nreg 218013 - 1)).eval zta)
          ((pt H P.n (c.nreg 218001 + c.nreg 218013)).eval zta)
          ((pt H P.n ((c.nreg 218001 + c.nreg 218013 + 1) % (H.pts P.n).length)).eval
            zta)) := by
  zuyv
  zumcu
  have hNW := E.hN
  obtain ⟨s, hs⟩ : ztjbv := by_simp_all
  obtain ⟨T, hT⟩ : ∃ T, c.nreg 218013 = T := by_simp_all
  obtain ⟨N, hN⟩ : ∃ N, (H.pts P.n).length = N := by_simp_all
  rw [hs, hT, hN] at hsT ⊢
  rw [hN] at h12 hNW
  unfold betaS
  by_cases hc : c.nreg 218020 < c.nreg 218013
  swap
  · have hT0 : T = 0 := by_omega
    refine spec_ifLtN_false hc ?_
    obtain ⟨c', k, e, hk, v⟩ : ∃ c' k, Exec P W (block [.constN 218014 0]) c c' k ∧ k = 1 ∧
        c'.nreg 218014 = 0 := by
      exec_block
      · omega
      simp
    exact ⟨c', k, e, by_omega, exec_frameB (Exec.ifLtN_false hc e) wr_betaS, by_omega,
      by omega⟩
  have hT1 : 1 ≤ T := by_omega
  zumju
  -- the indices
  obtain ⟨c₁, k₁, e₁, hk₁, v50, v51, v52, r₁, m₁⟩ := nbrS_exec (P := P) c hw hs hT h21 h12 hT1
    hsT hNW
  have E₁ : zthof := ⟨e₁.wb_right,
    by zunaa; exact hE.h60,
    by zunaa; exact hE.h61,
    by zunaa; exact hE.h67,
    by zunaa; exact hE.h68,
    by zunaa; exact hE.h69, by zvmxn; exact hE.mem⟩
  have hNpos : ztgab := by_omega
  -- the three points
  obtain ⟨c₂, k₂, e₂, hk₂, E₂, sA₂, r₂, m₂⟩ := lkTo_exec E c₁ E₁ v51 by_omega
    (d := 218053) by_norm_num
  obtain ⟨c₃, k₃, e₃, hk₃, E₃, sV₃, r₃, m₃⟩ := lkTo_exec E c₂ E₂ (src := 218050) (p := s + T)
    (by rw [r₂ _ by_decide by_decide by_decide by_decide]; omega)
    by_omega (d := 218056) by_norm_num
  obtain ⟨c₄, k₄, e₄, hk₄, E₄, sB₄, r₄, m₄⟩ := lkTo_exec E c₃ E₃ (src := 218052)
    (p := ztkeg % N)
    (by rw [r₃ _ by_decide by_decide by_decide by_decide,
      r₂ _ by_decide by_decide by_decide by_decide]; omega)
    ztktg (d := 218059) by_norm_num
  have sA₃ : SymPtIn c₃ 218053 ztkwu := by
    refine symPtIn_copy sA₂ ?_ ?_ ?_
    all_goals exact r₃ _ by_decide by_decide by_decide by_decide
  have sA₄ : SymPtIn c₄ 218053 ztkwu := by
    refine symPtIn_copy sA₃ ?_ ?_ ?_
    zqbll
  have sV₄ : SymPtIn c₄ 218056 (pt H P.n zttzf) := by
    refine symPtIn_copy sV₃ ?_ ?_ ?_
    zqbll
  have hA := pt_lt (i := s + T - 1) E.hwf E.npos by_omega
  have hV := pt_lt (i := s + T) E.hwf E.npos by_omega
  have hB := pt_lt (i := ztkeg % N) E.hwf E.npos
    ztktg
  -- the tests
  obtain ⟨c₅, k₅, e₅, hk₅, bpp, bp0, bbx, bax, bby, bby', r₅, m₅⟩ := testsS_exec E.good hWn c₄
    e₄.wb_right hA hV hB sA₄ sV₄ sB₄
  zuef
  obtain ⟨c₆, k₆, e₆, hk₆, v12, r₆⟩ : ∃ c₆ k₆, Exec P W (block [.constN 170012 0]) c₅ c₆ k₆ ∧
      k₆ = 1 ∧ c₆.nreg 170012 = 0 ∧ c₆ = { c₅ with nreg := upd c₅.nreg 170012 0 } := by
    exec_block
    · omega
    simp
  zujb
  have bit6 : ∀ {r : ℕ} {p : Prop}, BitIs c₅ r p → r ≠ 170012 → BitIs c₆ r p :=
    fun h hr => h.of_eq (by zunrz; simp only [upd, ite_eq_right hr])
  obtain ⟨c₇, k₇, e₇, hk₇, b, hb, rfl, hbit⟩ := IOrc.logI_exec (P := P) c₆ w₆ v12 by_omega
    (bit6 bpp by_decide) (bit6 bp0 by_decide) (bit6 bbx by_decide) (bit6 bax by_decide)
    (bit6 bby by_decide) (bit6 bby' by_decide) (fun h0 hp => by_grind)
  zubgp
  obtain ⟨c₈, k₈, e₈, hk₈, v14⟩ : ∃ c₈ k₈, Exec P W (block [.copyN 218014 170075])
      { c₆ with nreg := upd c₆.nreg 170075 b } c₈ k₈ ∧ k₈ = 1 ∧ c₈.nreg 218014 = b := by
    exec_block
    simp
  have ex : Exec P W bitI c c₈ _ :=
    .seq e₁ ztey
  refine ⟨c₈, _, ex, by_omega, exec_frameB (Exec.ifLtN_true hc ex) wr_betaS, by_omega, ?_⟩
  rw [v14, hbit]
  unfold IOrc.BetaF
  exact ⟨fun h => ⟨hT1, h⟩, fun h => h.2⟩
end exec
end
end DrvP
end Chazelle.Core
end
section
set_option hygiene false
local macro "zqbji" : tactic => `(tactic| (intro q hq; zvmxh at hq))
local macro "zqbjj" : tactic => `(tactic| (have i5 := hI.hin 83005 by_norm_num by_norm_num
                                           have i6 := hI.hin 83006 by_norm_num by_norm_num))
local macro "zqbjk" : tactic => `(tactic| simp only [List.mem_cons, List.not_mem_nil, or_false] at hq)
local macro "zqbjl" : tactic => `(tactic| (have hW1 : ztbla := by have := hI.hw.1 83023; rw [hI.h23] at this; omega))
local macro "zqbjm" : tactic => `(tactic| rw [t4 _ by_simp, t3 _ by_simp])
set_option hygiene true

/-!
# WP-E, the candidate test on the RAM, part 13: the count test

`countS kc` scans the exit chords of the region and counts those with an end strictly inside the
key interval `(key x, key f)` (`83053`) and inside `(key f, key x)` (`83054`), for the candidate
`x` (`83005`, `83006`) and the arrival position `f` (`83012`, `83013`); the success bit `83014`
is `1` iff both counts are at least `2` (`count_rs`: `83014 = 1` iff `CountOK`, by
`sideExits_ncard`).

Scratch registers: `83030 … 83032`, `83047 … 83049` (the chord), `83055` (the constant `2`),
`83056`, `83057` (`x < f`, `f < x`), `83060 … 83067` (the comparisons of the two ends with `x`
and `f`), `83068`, `83069` (the side flags of the chord).
-/
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Machine Machine.Stmt Programs SweepPrim
open Chazelle.Chain (sideInArc)
variable {P : Polygon} {W : ℕ} {M : Model} {N : NF} {c₀ c : Config}

/-- **Update of a side flag** `f`: set if the key `k` is strictly inside the arc `(a, b)` (bits
`bab`: `a < b`, `bak`: `a < k`, `bkb`: `k < b`). -/
def updArc (bab bak bkb f : ℕ) : Stmt :=
  .ifLtN bab 83023
    (.ifLtN bak 83023 ztmaa ztwdo)
    (.ifLtN bak 83023 .skip ztmaa)
theorem updArc_rs {bab bak bkb f : ℕ} {a b k : ℝ} (hf : Scr f) (hI : TInv W c₀ c)
    (h1 : BitIs c bab ztteo) (h2 : BitIs c bak (a < k)) (h3 : BitIs c bkb (k < b)) :
    RS P W c₀ (updArc bab bak bkb f) c 7 (fun c' => FlagUpd c c' f (sideInArc a b k)) := by
  have e1 := hI.h23
  rw [← sideInArc_bits]
  unfold updArc
  rcases bit01 h1 with ⟨q1, n1⟩ | ⟨q1, n1⟩ <;>
  rcases bit01 h2 with ⟨q2, n2⟩ | ⟨q2, n2⟩ <;>
  rcases bit01 h3 with ⟨q3, n3⟩ | ⟨q3, n3⟩
  · zuloe

  · refine RS.ifT by_omega (RS.ifT by_omega ztlfm)
    simp_all
  · refine RS.ifT by_omega (RS.ifF by_omega (leaf_set hI hf by_norm_num ?_))
    simp_all
  · grind
  · grind
  · refine RS.ifF by_omega ztclu
    simp_all
  · zulod

  · refine RS.ifF by_omega (RS.ifF by_omega ztlfm)
    simp_all

/-! ## Reading an exit chord -/

/-- Read the exit chord at place `83030`: `83047 := h + 1`, `83048 := lp`, `83049 := rp`. -/
def cRead : Stmt :=
  .seq ztuby (.seq ztigl
    (.seq ztthw (.seq ztnax
      (.seq ztthx (chF 2 83049)))))
theorem cRead_rs (hE : TGood P W M N c₀) (hI : TInv W c₀ c)
    (ht : c.nreg 83030 < (N.region ztco).chords.length)
    (hroom : c.nreg ALLOC + 70 ≤ W) :
    RS P W c₀ cRead c 70 (fun c' =>
      c'.nreg 83047 = (N.chord ztxdx).h + 1 ∧
      c'.nreg 83048 = (N.chord ztxdx).lp ∧
      c'.nreg 83049 = (N.chord ztxdx).rp ∧
      Agr c c' [83032, 83047, 83048, 83049]) := by
  zuhfa
  set i := chordAt N _ _ with hidef
  have h1 := tRegItem_exec (tr := 83030) ztbt by_trivial hE hI
    by_simp_all by_omega
  zujkf
  refine RS.mono (K := 20 + (1 + (14 + (1 + ztsrc)))) ?_ by_norm_num ztb
  refine RS.seq ztqck fun c₁ hI₁ hA₁ ⟨v₁, h8₁⟩ =>
    RS.seq (RS.copy hI₁ (r := 83032) (a := 50210) by_trivial)
    fun c₂ hI₂ hA₂ hc₂ => ?_
  have q2 : c₂.nreg 83032 = i := by zunie; rfl
  zuclq
  refine RS.seq (chF_rs (f := 0) (d := 83047) by_norm_num by_trivial hE hI₂
    by_omega by_omega) fun c₃ hI₃ hA₃ ⟨v₃, a₃⟩ => ?_
  have q3 : c₃.nreg 83032 = i := by zunea
  zugkx
  have hh : ztpgr := by
    zubtv
    have := hh _ hil
    zuic
  refine RS.seq (RS.add hI₃ by_trivial
    (by zuoal; have := hE.hW; unfold hostWords at this; zuosy; omega))
    fun c₄ hI₄ hA₄ h₄ => ?_
  have q4 : c₄.nreg 83032 = i := by_simp_all
  have v4 : c₄.nreg 83047 = (N.chord i).h + 1 := by zunmq; rfl
  refine RS.seq (chF_rs (f := 1) (d := 83048) by_norm_num by_trivial hE hI₄
    by_omega by_omega) fun c₅ hI₅ hA₅ ⟨v₅, a₅⟩ => ?_
  have q5 : c₅.nreg 83032 = i := by zuntn
  refine (chF_rs (f := 2) (d := 83049) by_norm_num by_trivial hE hI₅
    by_omega by_omega).mono le_rfl fun c₆ ⟨v₆, a₆⟩ => ?_
  refine ⟨?_, ?_, ?_, ((((a2.trans a₃).trans ztjgm).trans a₅).trans a₆).mono
    by_simp⟩
  · rw [a₆ _ by_norm_num by_norm_num by_simp, a₅ _ by_norm_num by_norm_num by_simp,
      v4]
  · zuelg
  · zuine

/-! ## The comparisons of the ends -/

/-- The four comparisons of the ends `L = (83048, 83047)`, `R = (83049, 83047)` of the chord
with `x` and `f`. -/
def cCmps (kc : ℕ → ℕ → ℕ → ℕ → Stmt) : Stmt :=
  .seq (.seq ztqsg (cp2 83060 83061))
    (.seq (.seq (kc 83048 83047 83012 83013) (cp2 83062 83063))
      (.seq (.seq (kc 83049 83047 83005 83006) (cp2 83064 83065))
        (.seq (kc 83049 83047 83012 83013) (cp2 83066 83067))))
variable {kc : ℕ → ℕ → ℕ → ℕ → Stmt} {Kk : ℕ}
theorem cCmps_rs (hK : KeyOK kc Kk)
    (hE : TGood P W M N c₀) (hI : TInv W c₀ c)
    (hL : PosG M zta P.n ⟨c.nreg 83048, c.nreg 83047⟩)
    (hR : PosG M zta P.n ⟨c.nreg 83049, c.nreg 83047⟩)
    (hf : PosG M zta P.n ztbfl)
    (hroom : c.nreg ALLOC + 4 * ztblz ≤ W) :
    RS P W c₀ ztvkt c (4 * ztblz) (fun c' =>
      BitIs c' 83060 (keyAt M P c 83048 83047 < keyAt M P c 83005 83006) ∧
      BitIs c' 83061 (keyAt M P c 83005 83006 < keyAt M P c 83048 83047) ∧
      BitIs c' 83062 (keyAt M P c 83048 83047 < keyAt M P c 83012 83013) ∧
      BitIs c' 83063 (keyAt M P c 83012 83013 < keyAt M P c 83048 83047) ∧
      BitIs c' 83064 (keyAt M P c 83049 83047 < keyAt M P c 83005 83006) ∧
      BitIs c' 83065 (keyAt M P c 83005 83006 < keyAt M P c 83049 83047) ∧
      BitIs c' 83066 (keyAt M P c 83049 83047 < keyAt M P c 83012 83013) ∧
      BitIs c' 83067 (keyAt M P c 83012 83013 < keyAt M P c 83049 83047) ∧
      Agr c c' [83060, 83061, 83062, 83063, 83064, 83065, 83066, 83067]) := by
  zqbjj
  have hx : ztyli := by
    zudkd
  unfold cCmps
  refine RS.mono (K := ztblz + (ztblz + ztzys)) ?_ by_omega
    ztb
  have g : ∀ {c₁ : Config} {S : List ℕ}, Agr c c₁ S → (∀ q ∈ [83005, 83006, 83012, 83013, 83047,
      83048, 83049], q ∉ S) → ∀ q ∈ [83005, 83006, 83012, 83013, 83047, 83048, 83049],
      c₁.nreg q = c.nreg q := fun ha hS q hq => by
    have := hS q hq
    zqbjk
    exact ha q by_omega by_omega this
  refine RS.seq (kcmp_rs hK by_trivial by_trivial by_trivial
    by_trivial by_trivial by_trivial by_omega hE hI hL hx
    by_omega) fun c₁ hI₁ hA₁ ⟨b60, b61, a₁⟩ => ?_
  have g1 := g a₁ by_simp
  refine RS.seq (kcmp_rs hK by_trivial by_trivial by_trivial
    by_trivial by_trivial by_trivial by_omega hE hI₁
    by_grind
    by_grind by_omega)
    fun c₂ hI₂ hA₂ ⟨b62, b63, a₂⟩ => ?_
  have g2 := g (a₁.trans a₂) by_simp
  refine RS.seq (kcmp_rs hK by_trivial by_trivial by_trivial
    by_trivial by_trivial by_trivial by_omega hE hI₂
    by_grind
    by_grind by_omega)
    fun c₃ hI₃ hA₃ ⟨b64, b65, a₃⟩ => ?_
  have g3 := g ((a₁.trans a₂).trans a₃) by_simp
  refine (kcmp_rs hK by_trivial by_trivial by_trivial
    by_trivial by_trivial by_trivial by_omega hE hI₃
    by_grind
    by_grind by_omega).mono le_rfl
    fun c₄ ⟨b66, b67, a₄⟩ => ?_
  unfold keyAt at *
  rw [g1 83048 by_simp, g1 83047 by_simp, g1 83012 by_simp, g1 83013 by_simp] at b62 b63
  rw [g2 83049 by_simp, g2 83047 by_simp, g2 83005 by_simp, g2 83006 by_simp] at b64 b65
  rw [g3 83049 by_simp, g3 83047 by_simp, g3 83012 by_simp, g3 83013 by_simp] at b66 b67
  have t4 : ∀ q ∈ [83060, 83061, 83062, 83063, 83064, 83065], c₄.nreg q = c₃.nreg q := by
    zqbji
    exact a₄ q by_omega by_omega by_grind
  have t3 : ∀ q ∈ [83060, 83061, 83062, 83063], c₃.nreg q = c₂.nreg q := by
    zqbji
    exact a₃ q by_omega by_omega ztbaw
  have t2 : ∀ q ∈ [83060, 83061], c₂.nreg q = c₁.nreg q := by
    zqbji
    exact a₂ q by_omega by_omega ztbaw
  refine ⟨b60.of_eq ?_, b61.of_eq ?_, b62.of_eq ?_, b63.of_eq ?_, b64.of_eq ?_, b65.of_eq ?_,
    b66, b67, (((a₁.trans a₂).trans a₃).trans a₄).mono by_simp⟩
  · grind
  · rw [t4 _ by_simp, t3 _ by_simp, t2 _ by_simp]
  · zqbjm
  · zqbjm
  · zukyr
  · zukyr

/-! ## The side flags -/

/-- The side flags `83068` (inside `(x, f)`) and `83069` (inside `(f, x)`) of the chord. -/
def cUpd : Stmt :=
  .seq (.instr (.constN 83068 0)) (.seq (.instr (.constN 83069 0))
    (.seq (updArc 83056 83061 83062 83068) (.seq (updArc 83056 83065 83066 83068)
      (.seq (updArc 83057 83063 83060 83069) (updArc 83057 83067 83064 83069)))))
theorem flag_val {c : Config} {r : ℕ} {p : Prop} (h1 : c.nreg r ≤ 1) (h2 : c.nreg r = 1 ↔ p) :
    c.nreg r = (open Classical in if p then 1 else 0) := by
  grind
theorem cUpd_rs {kx kf kL kR : ℝ} (hI : TInv W c₀ c) (b56 : BitIs c 83056 (kx < kf))
    (b57 : BitIs c 83057 (kf < kx)) (b60 : BitIs c 83060 (kL < kx))
    (b61 : BitIs c 83061 (kx < kL)) (b62 : BitIs c 83062 (kL < kf))
    (b63 : BitIs c 83063 (kf < kL)) (b64 : BitIs c 83064 (kR < kx))
    (b65 : BitIs c 83065 (kx < kR)) (b66 : BitIs c 83066 (kR < kf))
    (b67 : BitIs c 83067 (kf < kR)) :
    RS P W c₀ cUpd c 30 (fun c' =>
      c'.nreg 83068 ≤ 1 ∧ (c'.nreg 83068 = 1 ↔ sideInArc kx kf kL ∨ sideInArc kx kf kR) ∧
      c'.nreg 83069 ≤ 1 ∧ (c'.nreg 83069 = 1 ↔ sideInArc kf kx kL ∨ sideInArc kf kx kR) ∧
      Agr c c' [83068, 83069]) := by
  zqbjl
  unfold cUpd
  refine RS.mono (K := 1 + (1 + (7 + (7 + (7 + 7))))) ?_ by_norm_num ztb
  refine RS.seq (RS.const hI (r := 83068) (v := 0) by_trivial by_omega)
    fun c₁ hI₁ _ h₁ => ?_
  refine RS.seq (RS.const hI₁ (r := 83069) (v := 0) by_trivial by_omega)
    fun c₂ hI₂ _ h₂ => ?_
  have a2 : Agr c c₂ [83068, 83069] := ((Agr.of_upd h₁).trans ztpvt).mono by_simp
  have tr : ∀ {c' : Config} {S : List ℕ}, Agr c c' S → ∀ r ∈ [83056, 83057, 83060, 83061, 83062,
      83063, 83064, 83065, 83066, 83067], r ∉ S → c'.nreg r = c.nreg r := fun ha r hr hS => by
    zuvy
    exact ha r by_omega by_omega hS
  refine RS.seq (updArc_rs by_trivial hI₂ (b56.of_eq ztkfy)
    (b61.of_eq ztkfy) (b62.of_eq ztkfy))
    fun c₃ hI₃ _ ⟨u1, u2, a₃⟩ => ?_
  have a3 := a2.trans a₃
  refine RS.seq (updArc_rs by_trivial hI₃ (b56.of_eq ztkfz)
    (b65.of_eq ztkfz) (b66.of_eq ztkfz))
    fun c₄ hI₄ _ ⟨v1, v2, a₄⟩ => ?_
  have a4 := a3.trans a₄
  refine RS.seq (updArc_rs by_trivial hI₄ (b57.of_eq ztkga)
    (b63.of_eq ztkga) (b60.of_eq ztkga))
    fun c₅ hI₅ _ ⟨w1, w2, a₅⟩ => ?_
  have a5 := a4.trans a₅
  refine (updArc_rs by_trivial hI₅ (b57.of_eq ztkgb)
    (b67.of_eq ztkgb) (b64.of_eq ztkgb)).mono
    le_rfl fun c₆ ⟨z1, z2, a₆⟩ => ?_
  have e68 : c₂.nreg 83068 = 0 := by rw [h₂, upd_ne by_norm_num, h₁, upd_eq]
  have e69 : c₂.nreg 83069 = 0 := by rw [h₂, upd_eq]
  have f68 : c₆.nreg 83068 = c₄.nreg 83068 := by
    rw [a₆ _ by_norm_num by_norm_num by_simp, a₅ _ by_norm_num by_norm_num by_simp]
  have f69 : c₄.nreg 83069 = c₂.nreg 83069 := by
    rw [a₄ _ by_norm_num by_norm_num by_simp, a₃ _ by_norm_num by_norm_num by_simp]
  refine ⟨by_omega, ?_, by_omega, ?_,
    (((a2.trans a₃).trans a₄).trans a₅).trans a₆ |>.mono by_simp⟩
  · grind
  grind

/-! ## The count loop -/

/-- The additions of the count loop. -/
def cAdd : Stmt :=
  .seq (.instr (.addN 83053 83053 83068)) (.seq (.instr (.addN 83054 83054 83069))
    ztejr)

/-- The body of the count loop. -/
def countBody (kc : ℕ → ℕ → ℕ → ℕ → Stmt) : Stmt := .seq cRead (.seq ztvkt (.seq cUpd cAdd))

/-- The cost bound of the body of the count loop. -/
def countKB (Kk : ℕ) : ℕ := 70 + (4 * ztblz + (30 + (1 + ztcse)))

/-- The registers the count loop writes. -/
def countScr : List ℕ := [83030, 83032, 83047, 83048, 83049, 83053, 83054, 83060, 83061, 83062,
  83063, 83064, 83065, 83066, 83067, 83068, 83069]

/-- **The invariant of the count loop** for the arrival position `f` (started in `cS`). -/
def CountI (M : Model) (P : Polygon) (N : NF) (c₀ : Config) (f : WPos) (cS c : Config) : Prop :=
  c.nreg 83031 = (N.region ztco).chords.length ∧ c.nreg 83030 ≤ c.nreg 83031 ∧
    c.nreg 83053 = cntP (fun t => SideHit M P N ztwmu ztxke
      ztwne) (c.nreg 83030) ∧
    c.nreg 83054 = cntP (fun t => SideHit M P N ztxke ztwmu
      ztwne) (c.nreg 83030) ∧
    BitIs c 83056 (M.key zta ztfy < M.key zta f) ∧
    BitIs c 83057 (M.key zta f < M.key zta ztfy) ∧
    c.nreg 83012 = f.edge ∧ c.nreg 83013 = f.hgt ∧ Agr cS c countScr

/-- **One iteration of the count loop.** -/
theorem countBody_rs (hK : KeyOK kc Kk)
    (hE : TGood P W M N c₀) {f : WPos} (hf : PosG M zta P.n f) {cS : Config}
    (hI : TInv W c₀ c) (hA : CountI M P N c₀ f cS c) (ht : c.nreg 83030 < c.nreg 83031)
    (hroom : c.nreg ALLOC + countKB Kk ≤ W) :
    RS P W c₀ ztvlw c ztvlx (fun c' => CountI M P N c₀ f cS c' ∧
      c'.nreg 83030 = c.nreg 83030 + 1) := by
  obtain ⟨hL, htL, n53, n54, b56, b57, f12, f13, aS⟩ := hA
  zudpj

  have hpos := hE.chordPosG hil
  unfold countBody countKB
  refine RS.seq (cRead_rs hE hI ht' ztnvp)
    fun c₁ hI₁ hA₁ ⟨s1, s2, s3, a₁⟩ => ?_
  have g1 : ∀ q ∈ [83005, 83006, 83012, 83013, 83030, 83031, 83053, 83054, 83056, 83057],
      c₁.nreg q = c.nreg q := fun q hq => by
    zqbjk
    exact a₁ q by_omega by_omega ztbaw
  have hLp : ztzoz := by zumzh; tauto
  have hRp : PosG M zta P.n ⟨c₁.nreg 83049, c₁.nreg 83047⟩ := by zuond; tauto
  have hfp : PosG M zta P.n ztrbt := by
    zunix; exact hf
  refine RS.seq (cCmps_rs hK hE hI₁ hLp hRp hfp ztnvp)
    fun c₂ hI₂ hA₂ ⟨b60, b61, b62, b63, b64, b65, b66, b67, a₂⟩ => ?_
  zuehn

  set i := chordAt N ztco ztccu
  have kL : keyAt M P c₁ 83048 83047 = M.key zta (N.chord i).lpos := by
    unfold keyAt; zumzh; rfl
  have kR : keyAt M P c₁ 83049 83047 = M.key zta (N.chord i).rpos := by
    unfold keyAt; zuond; rfl
  have kx : keyAt M P c₁ 83005 83006 = M.key zta ztfy := by
    unfold keyAt; zuone; rfl
  have kf : keyAt M P c₁ 83012 83013 = M.key zta f := by
    unfold keyAt; zunix
  rw [kL, kx] at b60 b61
  rw [kL, kf] at b62 b63
  rw [kR, kx] at b64 b65
  rw [kR, kf] at b66 b67
  have a12 := a₁.trans a₂
  have b56' := b56.of_eq (a12 83056 by_norm_num by_norm_num by_simp)
  have b57' := b57.of_eq (a12 83057 by_norm_num by_norm_num by_simp)
  refine RS.seq (cUpd_rs hI₂ b56' b57' b60 b61 b62 b63 b64 b65 b66 b67)
    fun c₃ hI₃ hA₃ ⟨u1, u2, v1, v2, a₃⟩ => ?_
  have a13 := a12.trans a₃
  have g3 : ∀ q ∈ [83030, 83031, 83053, 83054, 83056, 83057, 83012, 83013],
      c₃.nreg q = c.nreg q := fun q hq => by
    zqbjk
    exact a13 q by_omega by_omega ztbaw
  zugkx
  have hcl : c.nreg 83053 ≤ c.nreg 83030 := by rw [n53]; exact cntP_le _ _
  have hcl' : c.nreg 83054 ≤ c.nreg 83030 := by rw [n54]; exact cntP_le _ _
  have hW31 := hI.hw.1 83031
  unfold cAdd
  refine RS.seq (RS.add hI₃ (r := 83053) (a := 83053) (b := 83068) by_trivial
    (by rw [g3 83053 by_simp]; omega)) fun c₄ hI₄ _ h₄ => ?_
  refine RS.seq (RS.add hI₄ (r := 83054) (a := 83054) (b := 83069) by_trivial
    (by rw [h₄, upd_ne by_norm_num, upd_ne by_norm_num, g3 83054 by_simp]; omega))
    fun c₅ hI₅ _ h₅ => ?_
  have e23' := hI₅.h23
  have e30 : c₅.nreg 83030 = c.nreg 83030 := by
    rw [h₅, upd_ne by_norm_num, h₄, upd_ne by_norm_num, g3 83030 by_simp]
  refine (RS.add hI₅ by_trivial
    by_omega).mono le_rfl fun c₆ h₆ => ?_
  have v53 : c₆.nreg 83053 = c.nreg 83053 + c₃.nreg 83068 := by
    rw [h₆, upd_ne by_norm_num, h₅, upd_ne by_norm_num, h₄, upd_eq, g3 83053 by_simp]
  have v54 : c₆.nreg 83054 = c.nreg 83054 + c₃.nreg 83069 := by
    rw [h₆, upd_ne by_norm_num, h₅, upd_eq, h₄, upd_ne by_norm_num, upd_ne by_norm_num,
      g3 83054 by_simp]
  have v30 : c₆.nreg 83030 = c.nreg 83030 + 1 := by rw [h₆, upd_eq, e30, e23']
  have a36 : Agr c₃ c₆ [83053, 83054, 83030] :=
    (((Agr.of_upd h₄).trans (Agr.of_upd h₅)).trans (Agr.of_upd h₆)).mono by_simp
  have a16 := a13.trans a36
  have g6 : ∀ q, 80000 ≤ q → q < 90000 → q ∉ countScr → c₆.nreg q = c.nreg q :=
    fun q h1 h2 hq => a16 q h1 h2 (fun h => hq (by simp [countScr] at h ⊢; omega))
  refine ⟨ztbfh, v30⟩
  · rw [g6 83031 by_norm_num by_norm_num by_decide]; exact hL
  · rw [v30, g6 83031 by_norm_num by_norm_num by_decide]; omega
  · rw [v53, v30, cntP_succ, ← n53, flag_val u1 u2]; rfl
  · rw [v54, v30, cntP_succ, ← n54, flag_val v1 v2]; rfl
  · exact b56.of_eq (g6 83056 by_norm_num by_norm_num by_decide)
  · exact b57.of_eq (g6 83057 by_norm_num by_norm_num by_decide)
  · rw [g6 83012 by_norm_num by_norm_num by_decide, f12]
  · rw [g6 83013 by_norm_num by_norm_num by_decide, f13]
  · zuetd
    rw [g6 q h1 h2 hq, aS q h1 h2 hq]

/-- The success bit: both counts at least `2`. -/
def succS : Stmt :=
  .seq ztoug (.ifLtN 83053 83055 .skip (.ifLtN 83054 83055 .skip (setF 83014)))

/-- **The count test.** -/
def countS (kc : ℕ → ℕ → ℕ → ℕ → Stmt) : Stmt :=
  .seq (.seq (kc 83005 83006 83012 83013) (cp2 83056 83057)) (.seq (.instr (.constN 83053 0))
    (.seq (.instr (.constN 83054 0)) (.seq (.instr (.constN 83055 2)) (.seq ztqxg
      (.seq ztfey (.seq ztfer
        (.seq (.whileLtN 83030 83031 ztvlw) succS)))))))

/-- The cost bound of the count test for a region with `D` exit chords. -/
def countK (Kk D : ℕ) : ℕ :=
  ztblz + (1 + (1 + (1 + (13 + (1 + (1 + ((ztlmj * D + 2) + ztjec)))))))

/-- The registers the count test writes. -/
def countW : List ℕ := [83014, 83030, 83031, 83032, 83047, 83048, 83049, 83053, 83054, 83055,
  83056, 83057, 83060, 83061, 83062, 83063, 83064, 83065, 83066, 83067, 83068, 83069]

/-- **Contract of the count test** for the arrival position `f` in `83012`, `83013`. -/
theorem count_rs (hK : KeyOK kc Kk)
    (hE : TGood P W M N c₀) {f : WPos} (hf : PosG M zta P.n f) (hI : TInv W c₀ c)
    (hf12 : c.nreg 83012 = f.edge) (hf13 : c.nreg 83013 = f.hgt)
    (hroom : c.nreg ALLOC + countK Kk (N.region ztco).chords.length ≤ W) :
    RS P W c₀ (countS kc) c (countK Kk (N.region ztco).chords.length) (fun c' =>
      c'.nreg 83014 ≤ 1 ∧
      (c'.nreg 83014 = 1 ↔
        2 ≤ cntP (fun t => SideHit M P N ztwmu ztxke
          ztwne) (N.region (c₀.nreg 83002)).chords.length ∧
        2 ≤ cntP (fun t => SideHit M P N ztxke ztwmu
          ztwne) (N.region (c₀.nreg 83002)).chords.length) ∧
      Agr c c' countW) := by
  zqbjl
  have hW2 : zteht := by have := hE.hW; unfold hostWords at this; omega
  zqbjj
  have hx : ztyli := by zuone; exact hE.xPosG
  have hfp : PosG M zta P.n ztbfl := by_simp_all
  unfold countS countK
  unfold countK at hroom
  refine RS.seq (kcmp_rs hK by_trivial by_trivial by_trivial
    by_trivial by_trivial by_trivial by_omega hE hI hx hfp
    by_omega) fun c₁ hI₁ hA₁ ⟨b56, b57, a₁⟩ => ?_
  have kx : M.key zta ztbcf = M.key zta ztfy := by
    zuikw
  have kf : M.key zta ztbfl = M.key zta f := by
    simp_all
  rw [kx, kf] at b56 b57
  refine RS.seq ztrke
    fun c₂ hI₂ hA₂ h₂ => ?_
  refine RS.seq ztrkf
    fun c₃ hI₃ hA₃ h₃ => ?_
  refine RS.seq (RS.const hI₃ by_trivial hW2)
    fun c₄ hI₄ hA₄ h₄ => ?_
  refine RS.seq (RS.op (tRegLen_exec (f := 2) ztbt hE hI₄ by_omega))
    fun c₅ hI₅ hA₅ ⟨v₅, h8₅⟩ => ?_
  refine RS.seq (RS.copy hI₅ by_trivial)
    fun c₆ hI₆ hA₆ h₆ => ?_
  refine RS.seq (RS.const hI₆ by_trivial by_omega)
    fun c₇ hI₇ hA₇ h₇ => ?_
  have a27 : Agr c₁ c₇ [83053, 83054, 83055, 83031, 83030] :=
    ((((((Agr.of_upd h₂).trans ztmai).trans ztjgm).trans
      (Agr.of_band h8₅ [])).trans (Agr.of_upd h₆)).trans (Agr.of_upd h₇)).mono by_simp
  have a17 := a₁.trans a27
  have e31 : c₇.nreg 83031 = (N.region ztco).chords.length := by
    rw [h₇, upd_ne by_norm_num, h₆, upd_eq, v₅]; rfl
  have e30 : c₇.nreg 83030 = 0 := by_simp_all
  have e53 : c₇.nreg 83053 = 0 := by
    simp_all
  have e54 : c₇.nreg 83054 = 0 := by
    simp_all
  have e55 : c₇.nreg 83055 = 2 := by
    simp_all
  have hI0 : CountI M P N c₀ f c₇ c₇ := by
    refine ⟨e31, by_omega, by rw [e53, e30, cntP_zero], by rw [e54, e30, cntP_zero],
      b56.of_eq by_simp_all,
      b57.of_eq by_simp_all, ?_, ?_, Agr.refl _ _⟩
    · rw [a17 _ by_norm_num by_norm_num by_simp, hf12]
    · rw [a17 _ by_norm_num by_norm_num by_simp, hf13]
  have hμ : ztlmj * (c₇.nreg 83031 - c₇.nreg 83030) =
      ztlmj * (N.region ztco).chords.length := by
    simp_all
  refine RS.seq ((RS.while (CountI M P N c₀ f c₇) ztgiv
    ztvlx (fun c hA ht => by_omega)
    (fun c hIc hA ht hr => (countBody_rs hK hE hf hIc hA ht hr).mono le_rfl
      fun c' ⟨hA', h30⟩ => ⟨hA', by zunqf; have := hA.1; omega⟩)
    hI₇ hI0 by_omega).mono (by zvnhc) (fun c h => h))
    fun c₈ hI₈ hA₈ ⟨⟨hL, htL, n53, n54, _, _, _, _, a₈⟩, hnt⟩ => ?_
  have hT : c₈.nreg 83030 = (N.region ztco).chords.length := by_omega
  zvncs at n53 n54
  have e55' : c₈.nreg 83055 = 2 := by
    rw [a₈ _ by_norm_num by_norm_num by_decide, e55]
  have a18 : Agr c c₈ countW := (a17.trans a₈).mono by_decide
  unfold succS
  refine RS.seq (RS.const hI₈ by_trivial by_omega)
    fun c₉ hI₉ hA₉ h₉ => ?_
  have q53 : c₉.nreg 83053 = c₈.nreg 83053 := by zuoga
  have q54 : c₉.nreg 83054 = c₈.nreg 83054 := by zuoga
  have q55 : c₉.nreg 83055 = 2 := by rw [h₉, upd_ne by_norm_num, e55']
  have q14 : c₉.nreg 83014 = 0 := by rw [h₉, upd_eq]
  have a19 : Agr c c₉ countW := (a18.trans (Agr.of_upd h₉)).mono by_decide
  by_cases t1 : c₉.nreg 83053 < c₉.nreg 83055
  · refine RS.ifT t1 ztlfo
    omega
  · by_cases t2 : c₉.nreg 83054 < c₉.nreg 83055
    · refine RS.ifF t1 (RS.ifT t2 ztlfo)
      omega
    · refine RS.ifF t1 (RS.ifF t2 ((RS.const hI₉ by_trivial
        hW1).mono by_norm_num fun c' h' => ⟨by zunqg, ?_,
          (a19.trans ztpvs).mono by_decide⟩))
      rw [h', upd_eq, ← n53, ← n54, ← q53, ← q54]; omega
end
end Restore
end Chazelle.Core
end
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Machine Machine.Stmt Programs SweepPrim SignK NFLoc ShotList ShotListG

/-! ## The program -/

/-- The output bits `hit` and `succ` start at `0`. -/
def tInit : Stmt := .seq (.instr (.constN 83011 0)) ztoug

/-- The chord triple: the height vertex, then the left and the right walk edge (the candidate's
edge first for a ray to the right). -/
def writeT : Stmt := .seq (.instr (.copyN 83015 83007))
  (.ifLtN 83022 83008 (.seq (.instr (.copyN 83016 83005)) (.instr (.copyN 83017 83012)))
    (.seq (.instr (.copyN 83016 83012)) (.instr (.copyN 83017 83005))))

/-- After a hit: the arrival position, the count test, the chord triple. -/
def postHit : Stmt := .seq tArr (.seq (countS gKey) (.ifLtN 83022 83014 writeT .skip))

/-- The hit bit and the arrival position of the wrapper. -/
def hitCp : Stmt := .seq (.instr (.copyN 83011 84020))
  (.seq (.instr (.copyN 83012 84021)) (.instr (.copyN 83013 84022)))

/-- The shot part of the test. -/
def shotA (sh : Stmt) : Stmt :=
  .seq arcBuild (.seq holeS (.seq shPrep (.seq ztqwg hitCp)))

/-- **The candidate test.** -/
def testS (sh : Stmt) : Stmt :=
  .seq tSetup (.seq tInit (.seq (validS gKey gLeft tTurnN tTurnP)
    (.ifLtN 83022 83010 (.seq ztwdv (.ifLtN 83022 83011 postHit .skip)) .skip)))
variable {P : Polygon} {W : ℕ} {M : Model} {N : NF} {c₀ c : Config}

/-! ## The chord triple -/
theorem scr_out {r : ℕ} (h1 : 83010 ≤ r) (h2 : r < 83020) : Scr r := by unfold Scr; omega

/-- **The chord triple.** -/
theorem writeT_rs (hE : TGood P W M N c₀) (hI : TInv W c₀ c) :
    RS P W c₀ writeT c 6 (fun c' => c'.nreg 83015 = c₀.nreg 83007 ∧
      (c₀.nreg 83008 = 1 → c'.nreg 83016 = c₀.nreg 83005 ∧ c'.nreg 83017 = c.nreg 83012) ∧
      (c₀.nreg 83008 ≠ 1 → c'.nreg 83016 = c.nreg 83012 ∧ c'.nreg 83017 = c₀.nreg 83005) ∧
      Agr c c' [83015, 83016, 83017]) := by
  have i05 : ztmup := hI.hin _ by_norm_num by_norm_num
  have i07 : c.nreg 83007 = c₀.nreg 83007 := hI.hin _ by_norm_num by_norm_num
  have i08 : ztsew := hI.hin _ by_norm_num by_norm_num
  zumff
  refine RS.seq (K₂ := 5) (RS.copy hI (r := 83015) (a := 83007)
    ztevi) (fun c₁ hI₁ _ h₁ => ?_)
  have a07 : c₁.nreg 83015 = c₀.nreg 83007 := by_simp_all
  have k₁ : ∀ r, r ≠ 83015 → c₁.nreg r = c.nreg r := by_simp_all
  by_cases hs : c₀.nreg 83008 = 1
  · have g : c₁.nreg 83022 < c₁.nreg 83008 := by
      rw [k₁ _ by_norm_num, k₁ _ by_norm_num, hI.h22, i08, hs]; omega
    refine (RS.ifT g (RS.seq (K₂ := 1) (RS.copy hI₁
      ztevi) (fun c₂ hI₂ _ h₂ => ?_))).mono by_norm_num
      ztb
    refine (RS.copy hI₂ ztevi).mono
      le_rfl ztcvh
    zukie
    refine ⟨by_simp_all, fun _ => ztcp,
      by omega, fun q _ _ hq => ?_⟩
    · simp_all
    · simp_all
    simp_all
  · have g : ¬ c₁.nreg 83022 < c₁.nreg 83008 := by
      grind
    refine (RS.ifF g (RS.seq (K₂ := 1) (RS.copy hI₁
      ztevi) (fun c₂ hI₂ _ h₂ => ?_))).mono by_norm_num
      ztb
    refine (RS.copy hI₂ ztevi).mono
      le_rfl ztcvh
    zukie
    refine ⟨by_simp_all, by_omega,
      fun _ => ztcp, fun q _ _ hq => ?_⟩
    · simp_all
    · simp_all
    simp_all

/-! ## After a hit -/

/-- The cost bound of the post-hit stage for a region with `D` exit chords. -/
def postHitK (D : ℕ) : ℕ := 35012 + (countK 11010 D + 8)

/-- **After a hit**: from the returned position of the far end, the arrival position (chain
models), the count test at it, and the chord triple on success.  Registers `83010`, `83011` are
unchanged. -/
theorem postHit_rs (hE : TGood P W M N c₀) (hI : TInv W c₀ c)
    (hp : ProperPos M zta P.n ztbfl) (he : c.nreg 83012 < M.W.n)
    (hy : ∀ C : Chain, M = chainModel C →
      |(M.pos (Qof P) ⟨c.nreg 83012, c.nreg 83013⟩).2| < C.radius)
    (hex : ∀ C : Chain, M = chainModel C → ∃ p t, Sweep.Arrival M.W
      ztxkh ztjs p t)
    (hroom : c.nreg ALLOC + postHitK (N.region ztco).chords.length ≤ W) :
    RS P W c₀ postHit c (postHitK (N.region ztco).chords.length) (fun c' =>
      ProperPos M zta P.n ztha ∧ c'.nreg 83012 < M.W.n ∧
      M.pos zta ztha = M.pos zta ztbfl ∧
      (∀ C : Chain, M = chainModel C → Sweep.Arrival M.W
        ztxkh ztjs ztfgi
        ztwzk) ∧
      ztxie ∧
      c'.nreg 83014 ≤ 1 ∧
      (c'.nreg 83014 = 1 ↔
        2 ≤ cntP (fun t => SideHit M P N ztwmu
          ztwtq ztwne)
          (N.region ztco).chords.length ∧
        2 ≤ cntP (fun t => SideHit M P N ztwtq
          ztwmu ztwne)
          (N.region ztco).chords.length) ∧
      (c'.nreg 83014 = 1 → c'.nreg 83015 = c₀.nreg 83007 ∧
        ztgrf ∧
        ztgrg) ∧
      c'.nreg 83010 = c.nreg 83010 ∧ c'.nreg 83011 = c.nreg 83011) := by
  unfold postHitK at hroom ⊢
  refine RS.seq (tArr_rs hE hI hp he hy hex by_omega) ztiy
  obtain ⟨p₁, e₁, q₁, arr₁, int₁, ag₁⟩ := h₁
  have hf : PosG M _ P.n ztrbt :=
    posG_of_band e₁ p₁ by_grind
  refine RS.seq (count_rs gKey_ok hE hf hI₁ rfl rfl by_omega) ztcne
  obtain ⟨b14, i14, ag₂⟩ := h₂
  have k₂ : ∀ r, r ∈ [83010, 83011, 83012, 83013] → c₂.nreg r = c₁.nreg r := fun r hr =>
    ag₂ r by_grind by_grind (by simp [countW] at hr ⊢; omega)
  have k₁ : ∀ r, r ∈ [83010, 83011] → c₁.nreg r = c.nreg r := fun r hr =>
    ag₁ r by_grind by_grind by_grind
  have r12 : c₂.nreg 83012 = c₁.nreg 83012 := by_grind
  have r13 : c₂.nreg 83013 = c₁.nreg 83013 := by_grind
  have r10 : c₂.nreg 83010 = c.nreg 83010 := by_grind
  have r11 : c₂.nreg 83011 = c.nreg 83011 := by_grind
  -- the facts of the far end at `c₂`
  have F : ∀ c' : Config, (∀ r, r ∈ [83010, 83011, 83012, 83013, 83014] → c'.nreg r = c₂.nreg r) →
      ProperPos M zta P.n ztha ∧ c'.nreg 83012 < M.W.n ∧
      M.pos zta ztha = M.pos zta ztbfl ∧
      (∀ C : Chain, M = chainModel C → Sweep.Arrival M.W
        ztxkh ztjs ztfgi
        ztwzk) ∧
      (M = interiorModel zta → c'.nreg 83012 = c.nreg 83012 ∧
        c'.nreg 83013 = c.nreg 83013) ∧
      c'.nreg 83014 ≤ 1 ∧
      (c'.nreg 83014 = 1 ↔
        2 ≤ cntP (fun t => SideHit M P N ztwmu
          ztwtq ztwne) (N.region (c₀.nreg 83002)).chords.length ∧
        2 ≤ cntP (fun t => SideHit M P N ztwtq
          ztwmu ztwne) (N.region (c₀.nreg 83002)).chords.length) ∧
      c'.nreg 83010 = c.nreg 83010 ∧ c'.nreg 83011 = c.nreg 83011 := by
    intro c' hc
    rw [hc 83012 by_simp, hc 83013 by_simp, hc 83014 by_simp, hc 83010 by_simp,
      hc 83011 by_simp, r12, r13, r10, r11]
    grind
  by_cases hs : c₂.nreg 83014 = 1
  · have g : c₂.nreg 83022 < c₂.nreg 83014 := by
      rw [hI₂.h22, hs]; omega
    refine (RS.ifT g (writeT_rs hE hI₂)).mono by_omega ztcvh
    obtain ⟨w15, w1, w2, ag₃⟩ := h₃
    have k₃ : ∀ r, r ∈ [83010, 83011, 83012, 83013, 83014] → c₃.nreg r = c₂.nreg r :=
      fun r hr => ag₃ r ztcyv ztcyv (by simp at hr ⊢; omega)
    obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ := F c₃ k₃
    have e12 : ztsho := k₃ _ by_simp
    refine ⟨f1, f2, f3, f4, f5, f6, f7, fun _ => ⟨w15, fun h => ?_, fun h => ?_⟩, f8, f9⟩
    · omega
    omega
  · have g : ¬ c₂.nreg 83022 < c₂.nreg 83014 := by
      omega
    refine (RS.ifF g (RS.skip (K := 0) (Q := fun c' => c' = c₂) hI₂ rfl)).mono by_omega
      ztcvh
    zunbh
    grind

/-! ## The start -/
theorem tInit_rs (_hE : TGood P W M N c₀) (hI : TInv W c₀ c) :
    RS P W c₀ tInit c 2 (fun c' => c'.nreg 83011 = 0 ∧ c'.nreg 83014 = 0 ∧
      Agr c c' [83011, 83014]) := by
  refine RS.seq (K₂ := 1) (RS.const hI (r := 83011) ztevi
    ztbg)
    ztbzx
  refine (RS.const hI₁ (r := 83014) ztevi ztbg).mono
    le_rfl (fun c₂ h₂ => ⟨?_, ?_, fun q _ _ hq => ?_⟩)
  · simp_all
  · simp_all
  simp_all

/-! ## The shot stage -/
theorem holeList_congr {c c' : Config} (h : ∀ r, 84009 ≤ r → r ≤ 84015 → c'.nreg r = c.nreg r) :
    ShotList.holeList c' 84000 = ShotList.holeList c 84000 := by
  unfold ShotList.holeList
  rw [show c'.nreg _ = c.nreg _ from h _ by_norm_num by_norm_num]
  zucfh
  zun
  simp only [List.mem_range] at hj
  unfold ShotList.holeAt
  grind
theorem holeOut_congr {Q : Polygon} {z : Point} {c c' : Config}
    (h : ∀ r, 84009 ≤ r → r ≤ 84015 → c'.nreg r = c.nreg r) (ho : HoleOut M Q c z) :
    HoleOut M Q c' z := by
  obtain ⟨h9, hb, hcov, hnear⟩ := ho
  have hl := holeList_congr h
  refine ⟨by_simp_all, fun j hj => ?_, by_simp_all,
    by simp_all⟩
  grind

/-- The registers `hitCp` writes. -/
def hitW : List ℕ := [83011, 83012, 83013]
theorem hitCp_rs (hI : TInv W c₀ c) :
    RS P W c₀ hitCp c 3 (fun c' => c'.nreg 83011 = c.nreg 84020 ∧ c'.nreg 83012 = c.nreg 84021 ∧
      c'.nreg 83013 = c.nreg 84022 ∧ Out c c' hitW) := by
  obtain ⟨c₁, e₁, v₁, o₁⟩ := out_instr (P := P) (Exec.copyN hI.hw 83011 84020)
  obtain ⟨c₂, e₂, v₂, o₂⟩ := out_instr (P := P) (Exec.copyN e₁.wb_right 83012 84021)
  obtain ⟨c₃, e₃, v₃, o₃⟩ := out_instr (P := P) (Exec.copyN e₂.wb_right 83013 84022)
  have ho : Out c c₃ hitW := ((o₁.trans o₂).trans o₃).mono (fun r hr => by
    tauto)
  refine RS.out hI (fun r hr => by
      simp only [hitW, List.mem_cons, List.not_mem_nil, or_false] at hr; unfold Scr; omega)
    ztwrj by_omega ho ⟨?_, ?_, ?_, ho⟩
  · rw [o₃.1 _ by_simp, o₂.1 _ by_simp, v₁]
  · rw [o₃.1 _ by_simp, v₂, o₁.1 _ by_simp]
  · rw [v₃, o₂.1 _ by_simp, o₁.1 _ by_simp]

/-- The cost bound of the shot stage. -/
def shotAK (Fg A : ℕ) : ℕ := buildK A + (100 + (9 + (shotCostG Fg shK A + 3)))

/-- **The result of the shot stage** from the start `c₀`, at `c'`: the hit bit, and a set `A`
between the arc points outside the holes and all arc points (for an array listing the arcs of
the region and holes near the candidate) on which the ray first hits at the arrival position, or
which it misses. -/
def ShotRes (P : Polygon) (M : Model) (N : NF) (c₀ c' : Config) : Prop :=
  c'.nreg 83011 ≤ 1 ∧
    ∃ (m : ℕ → ℕ) (B : ℕ) (hs : List ztqx) (A : Set Point),
      (∀ j, j < (N.region ztco).arcs.length →
        ShotList.arcAt m B j = nArc M zta N ztco j) ∧
      Near M zta hs ztwkk ∧
      loSet M zta m B (N.region ztco).arcs.length hs ⊆ A ∧
      A ⊆ hiSet M zta m B (N.region ztco).arcs.length ∧
      (c'.nreg 83011 = 1 → ∃ t, FirstHit A ztwkk ztjs t ∧
        ProperPos M zta P.n ztha ∧ c'.nreg 83012 < M.W.n ∧
        M.pos zta ztha =
          Visibility.rayPt ztwkk ztjs t) ∧
      ztbamv

/-- **The shot stage.** -/
theorem shotA_rsb {X : MemCtx} {Ok : Polygon → Model → Prop} {sh : Stmt} {Bs Bo : Finset ℕ}
    {F : ℕ → ℕ} (hE : TGood P W M N c₀) (hI : TInv W c₀ c)
    (hX : X.holds P c₀.nmem zthvz ztdq)
    (hcap : c₀.nreg 83003 ≤ X.cap P c₀.nmem zthvz) (hXl : X.CapLocal) (hOk : Ok P M)
    (hne : (N.F M zta).Nonempty) (hsg : M.Semigranular ztwiv ztqkd)
    (hsh : ShooterOK sh Bs F X Ok) (hBs : Bs ⊆ Bo) (hB8 : bRestore ∉ Bo)
    (hBo : oracleBands ⊆ Bo)
    (hroom : c.nreg ALLOC +
      shotAK ztgdr (N.region ztco).arcs.length ≤ W) :
    RSB ztjtu P W c₀ ztwdv c
      (shotAK ztgdr (N.region ztco).arcs.length)
      (fun c' => ShotRes P M N c₀ c' ∧ c'.nreg 83010 = c.nreg 83010 ∧
        c'.nreg 83014 = c.nreg 83014) := by
  set K := (N.region _).arcs.length with hK
  have h4K : 4 * K ≤ buildK K := by unfold buildK bodyK normK; nlinarith
  unfold shotAK at hroom ⊢
  refine RSB.seq (RSB.of_RS Finset.subset_union_left (arcBuild_rs hE hne hI by_grind))
    ztiy
  obtain ⟨b81, bA, b31, barr, ag₁⟩ := h₁
  refine RSB.seq (RSB.of_RS Finset.subset_union_left (holeS_rs hE hI₁))
    ztcne
  obtain ⟨hho, o₂⟩ := h₂
  refine RSB.seq (RSB.of_RS Finset.subset_union_left (shPrep_rs hE hI₂))
    ztcnf
  obtain ⟨hcp, h03, o₃⟩ := h₃
  -- the registers of the shot block
  have cp := hcp
  have in2 := hI₂.hin
  have k12 := o₂.1
  have hA21 : zteic := k12 _ by_decide
  have hA32 : ztbox := o₃.1 _ by_decide
  have hm21 := o₂.2.2.1
  have hm32 := o₃.2.2.1
  have h00 : c₃.nreg 84000 = c₀.nreg 83000 := by
    rw [cp ztsuj by_decide, in2 _ by_norm_num by_norm_num]
  have h01 : c₃.nreg 84001 = c.nreg ALLOC := by
    rw [cp ztsuk by_decide, k12 _ by_decide, b81]
  have h02 : c₃.nreg 84002 = K := by
    rw [cp ztsul by_decide, k12 _ by_decide, b31]
  have h04 : c₃.nreg 84004 = c₀.nreg 83005 := by
    rw [cp ztsum by_decide, in2 _ by_norm_num by_norm_num]
  have h05 : c₃.nreg 84005 = c₀.nreg 83006 := by
    rw [cp ztsun by_decide, in2 _ by_norm_num by_norm_num]
  have h06 : c₃.nreg 84006 = c₀.nreg 83008 := by
    rw [cp ztsuo by_decide, in2 _ by_norm_num by_norm_num]
  have h07 : c₃.nreg 84007 = c₀.nreg 83003 := by
    rw [cp ztsup by_decide, in2 _ by_norm_num by_norm_num]
  have h08 : c₃.nreg 84008 = c₀.nreg 83004 := by
    rw [cp ztsuq by_decide, in2 _ by_norm_num by_norm_num]
  have hB : c.nreg ALLOC + 4 * K ≤ c₃.nreg ALLOC := by_omega
  have harr : ∀ j, j < K → ShotList.arcAt c₃.nmem ztm j =
      nArc M zta N ztco j := by_simp_all
  have hho₃ : HoleOut M _ c₃ _ :=
    holeOut_congr ztgrm hho
  have hpre := shotPre_of hE hI₃ hX hcap hXl hOk hne hsg h00 h01 h02 h03 h04
    h05 h07 h08 hB harr hho₃
  have hroom₃ : c₃.nreg ALLOC + shotCostG (F (c₃.nreg 84007)) shK (c₃.nreg 84002) ≤ W := by
    grind
  refine RSB.seq ((shot_rsb hE hI₃ hsh hBs hXl hB8 hBo hpre hroom₃).mono
    by_simp_all ztb) (fun c₄ hI₄ hA₄ h₄ => ?_)
  obtain ⟨hpost, keep⟩ := h₄
  refine RSB.of_RS Finset.subset_union_left ((hitCp_rs hI₄).mono le_rfl ztqnm)
  obtain ⟨v11, v12, v13, o₅⟩ := h₅
  -- the wrapper's postcondition at the model and the candidate
  have hMD : ModelDescAt c₃.nmem _ _ M := hpre.2.2.2.2.2.1
  have hOI : OriginIn c₃ (RS0 + 3) ztbadp := ⟨h03, h04, h05⟩
  obtain ⟨hfl, A, hlo, hhi, hyes, hno⟩ := hpost M ztbadp hMD hOI
  have hdir : dirOf (c₃.nreg (RS0 + 6)) = dirOf ztbkn := by
    show dirOf (c₃.nreg 84006) = _; rw [h06]
  rw [hdir] at hyes hno
  have hl3 : ShotList.holeList c₃ RS0 = ShotList.holeList c₂ 84000 :=
    holeList_congr ztgrm
  refine ⟨⟨by zuovj; tauto, c₃.nmem, c.nreg ALLOC, ShotList.holeList c₃ RS0, A, harr, ?_,
    ?_, ?_, fun h => ?_, fun h => ?_⟩, ?_, ?_⟩
  · rw [hl3]; exact hho.2.2.2
  · have := hlo; rw [show c₃.nreg zttbu = c.nreg ALLOC from h01,
      show c₃.nreg zttbv = K from h02] at this; omega
  · have := hhi; rw [show c₃.nreg zttbu = c.nreg ALLOC from h01,
      show c₃.nreg zttbv = K from h02] at this; omega
  · obtain ⟨t, hfh, hpp, hpe, hpos⟩ := hyes (by show c₄.nreg 84020 = 1; omega)
    exact ⟨t, hfh, by zuonh; tauto, by rw [v12]; tauto, by zuonh; tauto⟩
  · exact hno (by show c₄.nreg 84020 ≠ 1; omega)
  · rw [o₅.1 _ by_decide, keep _ by_norm_num by_norm_num, o₃.1 _ by_decide,
      k12 _ by_decide, ag₁ _ by_norm_num by_norm_num by_decide]
  · rw [o₅.1 _ by_decide, keep _ by_norm_num by_norm_num, o₃.1 _ by_decide,
      k12 _ by_decide, ag₁ _ by_norm_num by_norm_num by_decide]
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Set Filter Topology
open Chazelle.Chain (sidePt SideAttach sideLeft)
open Chazelle.Visibility (rayPt)
open ShotList ShotListG Machine SweepPrim
variable {P : Polygon} {M : Model} {N : NF}

/-- **A point of a proper position is off the domain.** -/
theorem pos_off (hGM : GoodModel M) {Q : Polygon} {x : WPos} (hxe : x.edge < M.W.n)
    (hx0 : 0 ≤ M.param Q x) (hx1 : M.param Q x ≤ 1) : M.pos Q x ∉ M.D :=
  (walkAx_of_goodModel hGM).trace x.edge hxe _ hx0 hx1

/-- **Every arc of the region is listed** in an array holding the normalised arcs of the
region record. -/
theorem arcs_listed (hNF : IsNF M zta N) {reg : ℕ → Set Point}
    (hregs : NFRegs M zta N reg) {r : ℕ} (hr : r < N.nRegions) {m : ℕ → ℕ} {B : ℕ}
    (harr : ∀ j, j < (N.region r).arcs.length → ShotList.arcAt m B j = nArc M zta N r j) :
    ∀ a b, M.IsArc ztwiv ztcz a b →
      ∃ j < (N.region r).arcs.length, M.key zta (ShotList.arcAt m B j).1 = a ∧
        M.key zta (ShotList.arcAt m B j).2 = b := by
  zujat
  zucdm
  zubtr
  obtain ⟨i, hi, hir, hia, hib⟩ := hArcs.2.2.1 r hr a b hab
  have hmem := (hArcs.2.2.2 r hr i).2 by_omega
  obtain ⟨j, hj, hji⟩ := List.getElem_of_mem hmem
  have hat : arcAt N r j = i := by
    rw [arcAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some, hji]
  zuc
  have hps : ProperPos M zta P.n (N.arc i).s := by_simp_all
  have hpe : ProperPos M zta P.n (N.arc i).e := by_simp_all
  refine ⟨j, hj, ?_, ?_⟩
  · rw [harr j hj, nArc, hat, (normOf_facts hps).2.2.2.1, hia]
  · rw [harr j hj, nArc, hat, (normOf_facts hpe).2.2.2.1, hib]

/-- The direction of a bit is `± 1`. -/
theorem dir_pm (v : ℕ) : dirOf v = 1 ∨ dirOf v = -1 := dirOf_pm v

/-- **The mathematics of a hit.** -/
theorem hit_math (hGM : GoodModel M) (hNF : IsNF M zta N) {reg : ℕ → Set Point}
    (hregs : NFRegs M zta N reg) {r : ℕ} (hr : r < N.nRegions) {x : WPos} {σb : ℕ}
    (hx : ProperPos M zta P.n x) (hxe : x.edge < M.W.n) (hv : ValidB M P N r x σb)
    (htop : ∀ C : Chain, M = chainModel C → (M.pos zta x).2 ≤ C.top.2)
    {m : ℕ → ℕ} {B : ℕ} {hs : List ztqx} {A : Set Point}
    (harr : ∀ j, j < (N.region r).arcs.length → ShotList.arcAt m B j = nArc M zta N r j)
    (hnear : Near M zta hs ztwlu)
    (hlo : loSet M zta m B (N.region r).arcs.length hs ⊆ A)
    (hhi : A ⊆ hiSet M zta m B (N.region r).arcs.length) {t : ℝ}
    (hfh : FirstHit A ztwlu ztbem t) :
    rayPt ztwlu ztbem t ∉ M.D ∧
      (∀ s, 0 < s → s < t → rayPt ztwlu ztbem s ∈ reg r) ∧
      chordOf ztwlu ztbem t ∈ M.Adm ∧
      (∃ p t', SideAttach M.W (chordOf ztwlu ztbem t) p t' ∧
        sidePt M.W p t' = rayPt ztwlu ztbem t) :=
  firstHit_exit hGM hNF.1 ztobe ztvpc ztqup
    ztmpi htop ztqdp hnear hlo hhi hfh

/-- **The shot hits** when the ray from a valid candidate leaves the domain. -/
theorem noHit_false (hGM : GoodModel M) (hNF : IsNF M zta N) {reg : ℕ → Set Point}
    (hregs : NFRegs M zta N reg) {r : ℕ} (hr : r < N.nRegions) {x : WPos} {σb : ℕ}
    (hx : ProperPos M zta P.n x) (hxe : x.edge < M.W.n) (hv : ValidB M P N r x σb)
    (htop : ∀ C : Chain, M = chainModel C → (M.pos zta x).2 ≤ C.top.2)
    {m : ℕ → ℕ} {B : ℕ} {hs : List ztqx} {A : Set Point}
    (harr : ∀ j, j < (N.region r).arcs.length → ShotList.arcAt m B j = nArc M zta N r j)
    (hnear : Near M zta hs ztwlu)
    (hlo : loSet M zta m B (N.region r).arcs.length hs ⊆ A) {T : ℝ} (hT : 0 < T)
    (hout : rayPt ztwlu ztbem T ∉ M.D)
    (hno : NoHit A ztwlu ztbem) : False :=
  not_noHit hGM hNF.1 ztobe ztvpc ztqup
    ztmpi htop ztqdp hnear hlo hT
    hout hno

/-! ## Sizes of the region records -/

/-- A duplicate-free list mapped injectively into a finite set is no longer than the set. -/
theorem length_le_ncard {α β : Type*} {L : List α} (hL : L.Nodup) {f : α → β} {S : Set β}
    (hS : S.Finite) (hinj : ∀ a ∈ L, ∀ b ∈ L, f a = f b → a = b) (hmem : ∀ a ∈ L, f a ∈ S) :
    L.length ≤ S.ncard := by
  classical
  have hnd : (L.map f).Nodup := List.Nodup.map_on by_omega hL
  have hlen : L.length = (L.map f).toFinset.card := by
    zuewt
  rw [hlen, ← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard (fun y hy => by
    simp only [Finset.mem_coe, List.mem_toFinset, List.mem_map] at hy
    grind) hS
variable {Q : Polygon} {W : ℕ} {c₀ : Config}
/-- **A region has at most as many exit-chord records as its degree.** -/
theorem chords_le_deg (hNF : IsNF M Q N) {reg : ℕ → Set Point}
    (hregs : NFRegs M Q N reg) {r : ℕ} (hr : r < N.nRegions) :
    (N.region r).chords.length ≤ M.deg ztdu ztcz := by
  zufig
  obtain ⟨hmem, hnd, -, -⟩ := hRg r hr
  have hfin : {c | c ∈ N.F M Q ∧ Chazelle.Chain.TouchesIn M.D c ztcz}.Finite :=
    hNF.1.1.subset by_simp_all
  refine length_le_ncard (f := fun i => (N.chord i).toSet M Q) hnd hfin
    ztmji ztts
  · exact hNF.2.1 a b by_simp_all by_simp_all h
  · exact ⟨chord_toSet_mem' by_simp_all, by_simp_all⟩

/-- **A region has at most one more arc record than its degree.** -/
theorem arcs_le_deg (hGM : GoodModel M) (hNF : IsNF M Q N) {reg : ℕ → Set Point}
    (hregs : NFRegs M Q N reg) {r : ℕ} (hr : r < N.nRegions) :
    (N.region r).arcs.length ≤ M.deg ztdu ztcz + 1 := by
  obtain ⟨hRC, -, hArcs, hRg⟩ := hregs
  obtain ⟨-, -, hnd, -⟩ := hRg r hr
  obtain ⟨hfin, hcard⟩ := arcsPerRegion M Q _ hGM hNF.1 _ ztdhm
  refine le_trans (length_le_ncard (f := fun j => ztbyr)
    hnd hfin ztmji ztts) hcard
  · zueax
    obtain ⟨hbN, hbr⟩ := (hArcs.2.2.2 r hr b).1 hb
    exact hArcs.2.1 a b haN hbN (har.trans hbr.symm) by_simp_all
  · zueax
    have := (hArcs.1 a haN).2
    simp_all

/-! ## The run of the test -/

/-- The cost of a run of the test for a region with `A` arcs and `D` exit chords. -/
def testK (A D Fg : ℕ) : ℕ :=
  4 + (2 + (validK 11010 20000 5200 A D + ((shotAK Fg A + (postHitK D + 2)) + 2)))

/-- **The facts of a run of the test** from `c₀` at its end `c'`. -/
def TestFacts (P : Polygon) (M : Model) (N : NF) (c₀ c' : Config) : Prop :=
  c'.nreg 83010 ≤ 1 ∧
  ztxsb ∧
  c'.nreg 83011 ≤ 1 ∧ c'.nreg 83014 ≤ 1 ∧
  (c'.nreg 83011 = 1 → c'.nreg 83010 = 1) ∧ (c'.nreg 83014 = 1 → c'.nreg 83011 = 1) ∧
  (c'.nreg 83010 = 1 → ∃ (m : ℕ → ℕ) (B : ℕ) (hs : List ztqx) (A : Set Point),
    (∀ j, j < (N.region ztco).arcs.length →
      ShotList.arcAt m B j = nArc M zta N ztco j) ∧
    Near M zta hs ztwkk ∧
    loSet M zta m B (N.region ztco).arcs.length hs ⊆ A ∧
    A ⊆ hiSet M zta m B (N.region ztco).arcs.length ∧
    (c'.nreg 83011 = 1 → ∃ (t : ℝ) (f₀ : WPos),
      FirstHit A ztwkk ztjs t ∧
      ProperPos M zta P.n f₀ ∧ f₀.edge < M.W.n ∧
      M.pos zta f₀ = rayPt ztwkk ztjs t ∧
      ProperPos M zta P.n ztha ∧ c'.nreg 83012 < M.W.n ∧
      M.pos zta ztha = M.pos zta f₀ ∧
      (∀ C : Chain, M = chainModel C → Sweep.Arrival M.W (M.pos zta f₀)
        ztjs ztfgi
        ztwzk) ∧
      (M = interiorModel zta → c'.nreg 83012 = f₀.edge ∧ c'.nreg 83013 = f₀.hgt) ∧
      (c'.nreg 83014 = 1 ↔
        2 ≤ cntP (fun t => SideHit M P N ztwmu
          ztwtq ztwne)
          (N.region ztco).chords.length ∧
        2 ≤ cntP (fun t => SideHit M P N ztwtq
          ztwmu ztwne)
          (N.region ztco).chords.length) ∧
      (c'.nreg 83014 = 1 → c'.nreg 83015 = c₀.nreg 83007 ∧
        ztgrf ∧
        ztgrg)) ∧
    ztbamv)

/-- The candidate of a chain model is at most at the height of the top. -/
theorem TGood.x_top (hE : TGood P W M N c₀) :
    ∀ C : Chain, M = chainModel C → (M.pos zta ztfy).2 ≤ C.top.2 := fun C hM =>
  C.snd_le_top_of_mem_set ztjxg

/-- A region with an exit chord record has a nonempty chord family. -/
theorem family_ne (hNF : IsNF M Q N) {r : ℕ} (hr : r < N.nRegions)
    (hch : (N.region r).chords ≠ []) : (N.F M Q).Nonempty := by
  obtain ⟨-, -, -, reg, -, -, -, hRg, -⟩ := hNF
  obtain ⟨i, hi⟩ := List.exists_mem_of_ne_nil _ hch
  exact ⟨_, chord_toSet_mem' (((hRg r hr).1 i).1 hi).1⟩

/-- The validity bit of a run: an `NFRegs` correspondence of the normal form. -/
theorem TGood.regs (hE : TGood P W M N c₀) :
    ∃ reg : ℕ → Set Point, NFRegs M zta N reg := by
  zucbc

/-- **A run of the test.** -/
theorem testS_rsb {X : MemCtx} {Ok : Polygon → Model → Prop} {sh : Stmt} {Bs Bo : Finset ℕ}
    {F : ℕ → ℕ} (hsh : ShooterOK sh Bs F X Ok) (hBs : Bs ⊆ Bo) (hXl : X.CapLocal)
    (hB8 : bRestore ∉ Bo) (hBo : oracleBands ⊆ Bo) {W : ℕ} {c₀ : Config}
    (hw : WordsBounded W c₀) (hE : TGood P W M N c₀)
    (hX : X.holds P c₀.nmem zthvz ztdq)
    (hcap : c₀.nreg 83003 ≤ X.cap P c₀.nmem zthvz) (hOk : Ok P M)
    (hsg : M.Semigranular ztwiv ztqkd)
    (hroom : c₀.nreg ALLOC + testK (N.region ztco).arcs.length
      (N.region ztco).chords.length ztgdr ≤ W) :
    RSB ztjtu P W c₀ ztibi c₀ (testK (N.region ztco).arcs.length
      (N.region ztco).chords.length ztgdr) (TestFacts P M N c₀) := by
  obtain ⟨c₁', k₁', ex₁, hk₁, hI₁', rf₁⟩ := tSetup_exec (P := P) hw hE.hwfMD.1
  have S1 : RSB ztjtu P W c₀ tSetup c₀ 4 ztrpr :=
    ⟨c₁', k₁', ex₁, by_omega, hI₁', rf₁.mono Finset.subset_union_left le_rfl, trivial⟩
  unfold testK at hroom ⊢
  refine RSB.seq S1 (fun c₁ hI₁ hA₁ _ => ?_)
  refine RSB.seq (RSB.of_RS Finset.subset_union_left (tInit_rs hE hI₁)) ztcne
  obtain ⟨z11, z14, ag₂⟩ := h₂
  refine RSB.seq (RSB.of_RS Finset.subset_union_left
    (valid_rs gKey_ok gLeft_ok turn_ok hE hI₂ by_omega)) (fun c₃ hI₃ hA₃ h₃ => ?_)
  obtain ⟨b10, i10, ag₃⟩ := h₃
  have y11 : c₃.nreg 83011 = 0 := by
    rw [ag₃ _ by_norm_num by_norm_num by_decide, z11]
  have y14 : c₃.nreg 83014 = 0 := by
    rw [ag₃ _ by_norm_num by_norm_num by_decide, z14]
  by_cases hv : c₃.nreg 83010 = 1
  · have g : c₃.nreg 83022 < c₃.nreg 83010 := by rw [hI₃.h22, hv]; omega
    have hV : ztplh := i10.1 hv
    have hne := family_ne hE.hNF hE.hr hV.1
    obtain ⟨reg, hregs⟩ := hE.regs
    refine RSB.ifT g (RSB.seq (shotA_rsb hE hI₃ hX hcap hXl hOk hne hsg hsh hBs hB8 hBo
      by_omega) (fun c₄ hI₄ hA₄ h₄ => ?_))
    obtain ⟨⟨h11, m, B, hs, A, harr, hnear, hlo, hhi, hyes, hno⟩, e10, e14⟩ := h₄
    by_cases hh : c₄.nreg 83011 = 1
    · obtain ⟨t, hfh, hpp, hpe, hpos⟩ := hyes hh
      have g' : c₄.nreg 83022 < c₄.nreg 83011 := by rw [hI₄.h22, hh]; omega
      obtain ⟨-, -, -, p', t', hatt, hw'⟩ := hit_math hE.hGM hE.hNF hregs hE.hr hE.hxp hE.hxe hV
        hE.x_top harr hnear hlo hhi hfh
      have harrival := arrival_of_attach (dir_pm _) hfh.1 hatt hw'
      have hy : ∀ C : Chain, M = chainModel C →
          |(M.pos _ ⟨c₄.nreg 83012, c₄.nreg 83013⟩).2| < C.radius := fun C hM => by
        rw [hpos, Visibility.rayPt_snd]
        exact lt_of_le_of_lt (C.abs_le_coordBound_of_mem_set ztjxg).2
          C.coordBound_lt_radius
      have hex : ∀ C : Chain, M = chainModel C → ∃ p t, Sweep.Arrival M.W
          (M.pos _ ⟨c₄.nreg 83012, c₄.nreg 83013⟩) _ p t :=
        fun _ _ => ⟨p', t', by zvnbl; exact harrival⟩
      refine RSB.ifT g' (RSB.of_RS Finset.subset_union_left
        (postHit_rs hE hI₄ hpp hpe hy hex by_omega)) |>.mono le_rfl (fun c₅ h₅ => ?_)
      obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9, q10⟩ := h₅
      have v10 : c₅.nreg 83010 = 1 := by_omega
      have v11 : c₅.nreg 83011 = 1 := by_omega
      refine ⟨by_omega, by_grind, by_omega, q6, by_grind, by_grind,
        fun _ => ⟨m, B, hs, A, harr, hnear, hlo, hhi, by_grind, by_omega⟩⟩
    · have h0 : c₄.nreg 83011 = 0 := by_omega
      have g' : ¬ c₄.nreg 83022 < c₄.nreg 83011 := by_omega
      refine (RSB.ifF g' (RSB.skip
        (Q := fun c' => c' = c₄) hI₄ rfl)).mono le_rfl (fun c₅ h₅ => ?_)
      zueyl
      have v10 : c₄.nreg 83010 = 1 := by_omega
      refine ⟨by_omega, by_simp_all, by_omega, by_omega,
        by omega, by_simp_all,
        by grind⟩
  · have g : ¬ c₃.nreg 83022 < c₃.nreg 83010 := by_omega
    refine (RSB.ifF g (RSB.skip
      (Q := fun c' => c' = c₃) hI₃ rfl)).mono le_rfl (fun c₅ h₅ => ?_)
    zueyl
    refine ⟨b10, i10, by_omega, by_omega, by_simp_all,
      by simp_all, by_omega⟩
