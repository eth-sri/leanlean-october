module

meta import Chazelle.Programs.RamEval

public import Chazelle.Core.SweepEvInit3

/-!
# The sweep (WP-D), stages 2–3: the initialisation, part 4 (the whole program)

`initE = initRA ; symS ; md1S ; tabS ; cTB := ALLOC` and its run from the stage-0 state
(`initE_exec`, result `InitRes`): the constants (`Consts`, `MapK`, `OrgK`, `cGW`), the model
descriptor of `C₁` (`MD₁`, `CD₁`), the table of powers (`TBR`, `TLR`) and the table base
`cTB` (the final allocator); only the registers `sw 600 … 714`, the oracle bands and the allocator
change, the memory below the entry allocator is kept.
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep

@[expose] public section

set_option hygiene false in
/-- Register arithmetic on all named registers of the initialisation. -/
macro "swoInit4" : tactic =>
  `(tactic| (simp (config := { failIfUnchanged := false }) only [iX, iN, iP, iA, iV, iE, iH, iY,
                iL, iT, iG, iO, iB, MD₁, CD₁, K0, K1, K2, K3, K4, K5, K6, ALLOC, TBR, TLR, cTB,
                cT1, sw] at *; omega))

/-- **The initialisation of `sweepEvSpec`'s program.** -/
def initE : Stmt :=
  .seq initRA (.seq symS (.seq md1S (.seq tabS (.instr (.copyN cTB ALLOC)))))

/-- The facts established by the initialisation. -/
structure InitRes (P : Polygon) (J : Merge.Junction) (c c₀ : Config) : Prop where
  keep : ∀ r, bandOf r ∉ oracleBands → r ≠ ALLOC → (r < sw 600 ∨ sw 715 ≤ r) →
    c₀.nreg r = c.nreg r
  mem : MemEqBelow (c.nreg ALLOC) c₀.nmem c.nmem
  hA : c.nreg ALLOC ≤ c₀.nreg MD₁
  hK : Consts c₀
  hM : MapK J c₀
  hO : OrgK P J c₀
  hgw : c₀.nreg cGW = gW J
  md0 : c₀.nmem (c₀.nreg MD₁) = 0
  mdc : ∀ i, i < 5 → c₀.nmem (c₀.nreg MD₁ + 1 + i) = c.nmem (c.nreg (sw 20) + i)
  hcd : c₀.nreg CD₁ = c₀.nreg MD₁ + 1
  hTBR : c₀.nreg TBR = c₀.nreg MD₁ + 6
  hTLR : c₀.nreg TLR =
    Nat.clog 2 (c.nmem (c.nreg (sw 3) + 1) + c.nmem (c.nreg (sw 4) + 1) + 1)
  htab : ∀ j, j < c₀.nreg TLR → c₀.nmem (c₀.nreg TBR + j) = 2 ^ j
  hAl : c₀.nreg ALLOC = c₀.nreg TBR + c₀.nreg TLR
  hTA : c₀.nreg cTB = c₀.nreg ALLOC

/-- A normal form protected below `E` has its header below `E`. -/
theorem nfWithin_lt' {m : ℕ → ℕ} {B E : ℕ} {N : NF} (h : NFWithin m B E N) : B + 1 < E := by
  by_contra hc
  have := (h (upd m (B + 1) (N.arcs.length + 1)) (fun a ha => by
    ram_finish)).2.1
  simp_all

/-- The number of edges of a chain with a well-formed descriptor. -/
theorem chain_m_le' {P : Polygon} {E : ℕ} {m : ℕ → ℕ} {bw : ℕ} {H : Host} {C : Chain}
    (hwf : ChainWF P E m bw) (hC : ChainDescAt m bw (Qof P) H C) : 2 * C.m + 2 ≤ 128 * P.n := by
  obtain ⟨hl, hHW, -, -⟩ := hwf.2 H C hC
  have h1 := C.add_one_le
  have h2 := NFLoc.chain_n_le hC hl hHW
  omega

/-- The walk of `C` fits twice in the word bound. -/
theorem walk_two_le {P : Polygon} {W E : ℕ} {m : ℕ → ℕ} {bw : ℕ} {H : Host} {C : Chain}
    (hwf : ChainWF P E m bw) (hC : ChainDescAt m bw (Qof P) H C) (hW : hostWords P.n ≤ W) :
    2 * (chainModel C).W.n ≤ W := by
  have := chain_m_le' hwf hC
  rw [cm_n]; unfold hostWords at hW; omega

/-- The chain context of a descriptor of a junction chain (host regular by `JunctionWF`). -/
theorem chainCtx_of {P : Polygon} {W : ℕ} {c : Config} {H : Host} {J : Merge.Junction}
    {d : ℕ} {C : Chain} (hG : GoodEnv P) (hWh : hostWords P.n ≤ W) (hP : C.P.Simple)
    (hJ : JunctionAt c.nmem (c.nreg (sw 0)) (c.nreg (sw 1)) (c.nreg (sw 2)) (Qof P) H J)
    (hJW : JunctionWF P (c.nreg ALLOC) c.nmem (c.nreg (sw 0)) (c.nreg (sw 1)) (c.nreg (sw 2)))
    (hd : ChainDescAt c.nmem (c.nreg d) (Qof P) H C) (hw : ChainWF P (c.nreg ALLOC) c.nmem (c.nreg d)) :
    ChainCtx P W c d C := by
  have := chain_m_le' hw hd
  unfold hostWords at hWh
  exact ⟨hG, by reg_omega, hw, ⟨H, hd, hJW.2.2.2 H hJ.2.2.1⟩, hP, by omega⟩

set_option maxRecDepth 20000 in
/-- **The run of the initialisation** from the stage-0 state. -/
theorem initE_exec {P : Polygon} {W : ℕ} {c : Config} {H : Host} {J : Merge.Junction}
    (hw : WordsBounded W c) (h0 : St0S P c H J) (hG : GoodEnv P) (hWh : hostWords P.n ≤ W)
    (hP : J.P.Simple) (h3 : c.nreg (sw 3) + 1 < c.nreg ALLOC)
    (h4 : c.nreg (sw 4) + 1 < c.nreg ALLOC)
    (hroom : c.nreg ALLOC + 31100 +
      2 * (c.nmem (c.nreg (sw 3) + 1) + c.nmem (c.nreg (sw 4) + 1) + 1) ≤ W) :
    ∃ c₀ k, Exec P W initE c c₀ k ∧
      k ≤ 31100 + 6 * Nat.clog 2 (c.nmem (c.nreg (sw 3) + 1) + c.nmem (c.nreg (sw 4) + 1) + 1) ∧
      Frame ioBands c c₀ k ∧ InitRes P J c c₀ := by
  set a₁ := c.nmem (c.nreg (sw 3) + 1) with ha₁
  set a₂ := c.nmem (c.nreg (sw 4) + 1) with ha₂
  have h0' := h0
  obtain ⟨h90, h91, h92, h93, hJ, hJW, d20, w20, d21, w21, -⟩ := h0'
  have hWn : 2 * J.wholeModel.W.n ≤ W := walk_two_le hJW.2.2.1 hJ.2.2 hWh
  -- part A
  obtain ⟨c₁, kA, eA, hkA, mA, rrA, rmA, oA, keepA, KA, MA, gwA, o2m, om, otop, oS, o2m6⟩ :=
    initRA_exec (P := P) hw h0 hWn
  have hA₁ : c₁.nreg ALLOC = c.nreg ALLOC := keepA _ (by reg_omega)
  have fA := frame_regs kA (fun r hr => keepA r (by
    by_contra h; exact hr (sw_io (by unfold sw at h; omega) (by unfold sw at h; omega)))) rrA mA rmA oA
  -- the top of `C₁`
  have k20 : c₁.nreg (sw 20) = c.nreg (sw 20) := keepA _ (by reg_omega)
  have hctx := (chainCtx_of hG hWh hP hJ hJW d20 w20).transport k20 (fun a _ => by rw [mA])
      (by rw [hA₁])
  obtain ⟨c₂, kS, eS, hkS, fS, ⟨s, hs, hsl, hse⟩, keepS⟩ :=
    symS_exec (P := P) eA.wb_right hctx (by rw [hA₁]; omega)
  have hA₂ := fS.2.2.2.2.2.2
  have hA₂' := fS.2.2.2.2.2.1
  have kS' := fun r h1 h2 h3 h4 =>
    keepS r (not_oracle_sw h1 h2) (by reg_omega) h3 h4
  -- the model descriptor
  have KS : Consts c₂ := by
    obtain ⟨a, b, d, e, f, g, i⟩ := KA
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    [rw [← a]; rw [← b]; rw [← d]; rw [← e]; rw [← f]; rw [← g]; rw [← i]] <;>
    exact kS' _ (by swoInit2) (by swoInit2) (by swoInit2) (by swoInit2)
  have k20' : c₂.nreg (sw 20) = c.nreg (sw 20) := by
    ram_finish [kS', k20]
  obtain ⟨c₃, kM, eM, hkM, aM, mdM, cdM, m0M, mcM, mlM, keepM, rrM, rmM, oM⟩ :=
    md1S_exec (P := P) eS.wb_right KS (by rw [k20']; have := w20.1; omega)
      (by omega)
  have fM : Frame ioBands c₂ c₃ kM := ⟨fun r hb hr => by
      refine keepM r hr ?_ ?_ ?_ ?_ <;> rintro rfl <;> exact hb (sw_io (by swoInit2) (by swoInit2)),
    fun r _ => by rw [rrM], mlM, fun a _ => by rw [rmM], oM, by omega, by omega⟩
  -- the table
  have kM' : ∀ r, 240000 ≤ r → r < 250000 → r ≠ MD₁ → r ≠ CD₁ → r ≠ iA → r ≠ iV →
      c₃.nreg r = c₂.nreg r := fun r h1 h2 a b d e => keepM r (by reg_omega) a b d e
  have K1₃ : c₃.nreg K1 = 1 := by rw [kM' _ (by swoInit2) (by swoInit2) (by swoInit2) (by swoInit2) (by swoInit2) (by swoInit2)]; exact KS.2.1
  have s3 : c₃.nreg (sw 3) = c.nreg (sw 3) := by
    ram_post
  have s4 : c₃.nreg (sw 4) = c.nreg (sw 4) := by
    ram_post
  have mem₃ : MemEqBelow (c.nreg ALLOC) c₃.nmem c.nmem := fun a ha => by
    ram_rw [mlM a, fS.2.2.1 a, mA]
  have ea₁ : c₃.nmem (c₃.nreg (sw 3) + 1) = a₁ := by rw [s3, mem₃ _ h3]
  have ea₂ : c₃.nmem (c₃.nreg (sw 4) + 1) = a₂ := by rw [s4, mem₃ _ h4]
  have hw₃ := eM.wb_right
  obtain ⟨c₄, kT, eT, hkT, tB, tL, tA, ttab, tmem, keepT, rrT, rmT, oT⟩ :=
    tabS_exec (P := P) hw₃ K1₃ (by rw [s3]; have := hw.1 ALLOC; omega)
      (by rw [s4]; have := hw.1 ALLOC; omega) (by rw [ea₁, ea₂, aM]; omega)
  rw [ea₁, ea₂] at hkT tL
  have fT : Frame ioBands c₃ c₄ kT := ⟨fun r hr hrA => by
      refine keepT r hrA ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> rintro rfl <;>
        exact hr (sw_io (by swoInit4) (by swoInit4)),
    fun r _ => by rw [rrT], tmem, fun a _ => by rw [rmT], oT, by omega, by omega⟩
  -- the table base
  have hw₄ := eT.wb_right
  have eC := Exec.copyN (P := P) hw₄ cTB ALLOC
  set c₅ : Config := { c₄ with nreg := upd c₄.nreg cTB (c₄.nreg ALLOC) } with hc₅
  have fC : Frame ioBands c₄ c₅ 1 := frame_regs 1 (fun r hr => by
    simp only [hc₅]; rw [upd_other _ _ _ (by rintro rfl; exact hr (sw_io (by swoInit2) (by swoInit2)))])
    rfl rfl rfl rfl
  have k5 : ∀ r, r ≠ cTB → c₅.nreg r = c₄.nreg r := fun r h => by
    simp only [hc₅]; rw [upd_other _ _ _ h]
  -- registers kept from part `A` on
  have keepR : ∀ r, bandOf r ∉ oracleBands → r ≠ ALLOC → (r < sw 645 ∨ sw 647 < r) →
      (r < sw 700 ∨ sw 715 ≤ r) → r ≠ MD₁ → r ≠ CD₁ → r ≠ TBR → r ≠ TLR → r ≠ cTB →
      c₅.nreg r = c₁.nreg r := fun r ho hA h1 h2 a b d e f => by
    rw [k5 r f, keepT r hA d e (by rintro rfl; swoInit4) (by rintro rfl; swoInit4) (by rintro rfl; swoInit4)
      (by rintro rfl; swoInit4) (by rintro rfl; swoInit4), keepM r hA a b (by rintro rfl; swoInit2)
      (by rintro rfl; swoInit2), keepS r ho hA h1 (by swoInit2)]
  have kc : ∀ i, 610 ≤ i → i ≤ 660 → (i < 645 ∨ 647 < i) → i ≠ 650 → i ≠ 651 →
      c₅.nreg (sw i) = c₁.nreg (sw i) := fun i h1 h2 h3 h4 h5 =>
    keepR _ (not_oracle_sw (by swoInit2) (by swoInit2)) (by swoInit2) (by swoInit2) (by swoInit2) (by swoInit2) (by swoInit2)
      (by swoInit2) (by swoInit2) (by swoInit2)
  refine ⟨c₅, kA + (kS + (kM + (kT + 1))), (by ram_path), ?_,
    frame_ioB (fA.trans (frame_ioB (fS.trans (frame_ioB (fM.trans (frame_ioB (fT.trans fC))))))),
    ⟨fun r ho hA hr => ?_, fun a ha => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [hkM, hkT]; omega
  · rw [keepR r ho hA (by swoInit2) (by swoInit2) (by rintro rfl; swoInit2) (by rintro rfl; swoInit2)
      (by rintro rfl; swoInit2) (by rintro rfl; swoInit2) (by rintro rfl; swoInit2)]
    exact keepA r (by swoInit2)
  · show c₄.nmem a = c.nmem a
    ram_rw [tmem a, mem₃ a ha]
  · rw [k5 MD₁ (by swoInit2), keepT MD₁ (by swoInit4) (by swoInit4) (by swoInit4) (by swoInit4) (by swoInit4) (by swoInit4)
      (by swoInit4) (by swoInit4), mdM]; omega
  · obtain ⟨a, b, d, e, f, g, i⟩ := KA
    exact ⟨((ram_app% (kc 610 ?_ ?_ ?_ ?_ ?_))).trans a,
      ((ram_app% (kc 611 ?_ ?_ ?_ ?_ ?_))).trans b,
      ((ram_app% (kc 612 ?_ ?_ ?_ ?_ ?_))).trans d,
      ((ram_app% (kc 613 ?_ ?_ ?_ ?_ ?_))).trans e,
      ((ram_app% (kc 614 ?_ ?_ ?_ ?_ ?_))).trans f,
      ((ram_app% (kc 615 ?_ ?_ ?_ ?_ ?_))).trans g,
      ((ram_app% (kc 616 ?_ ?_ ?_ ?_ ?_))).trans i⟩
  · obtain ⟨a, b, d, e, f, g, i, j⟩ := MA
    exact ⟨((ram_app% (kc 652 ?_ ?_ ?_ ?_ ?_))).trans a,
      ((ram_app% (kc 653 ?_ ?_ ?_ ?_ ?_))).trans b,
      ((ram_app% (kc 654 ?_ ?_ ?_ ?_ ?_))).trans d,
      ((ram_app% (kc 655 ?_ ?_ ?_ ?_ ?_))).trans e,
      ((ram_app% (kc 656 ?_ ?_ ?_ ?_ ?_))).trans f,
      ((ram_app% (kc 657 ?_ ?_ ?_ ?_ ?_))).trans g,
      ((ram_app% (kc 658 ?_ ?_ ?_ ?_ ?_))).trans i,
      ((ram_app% (kc 660 ?_ ?_ ?_ ?_ ?_))).trans j⟩
  · refine ⟨((ram_app% (kc 640 ?_ ?_ ?_ ?_ ?_))).trans o2m,
      ((ram_app% (kc 641 ?_ ?_ ?_ ?_ ?_))).trans om,
      ((ram_app% (kc 642 ?_ ?_ ?_ ?_ ?_))).trans otop,
      ((ram_app% (kc 643 ?_ ?_ ?_ ?_ ?_))).trans oS,
      ((ram_app% (kc 644 ?_ ?_ ?_ ?_ ?_))).trans o2m6,
      s, ?_, hsl, hse⟩
    have t : ∀ i, 645 ≤ i → i ≤ 647 → c₅.nreg (sw i) = c₂.nreg (sw i) := fun i h1 h2 => by
      rw [k5 (sw i) (by swoInit2), keepT (sw i) (by swoInit4) (by swoInit4) (by swoInit4) (by swoInit4) (by swoInit4)
        (by swoInit4) (by swoInit4) (by swoInit4), keepM (sw i) (by swoInit2) (by swoInit2) (by swoInit2) (by swoInit2) (by swoInit2)]
    exact symPtIn_transport hs (t 645 (by norm_num) (by norm_num))
      (t 646 (by norm_num) (by norm_num)) (t 647 (by norm_num) (by norm_num))
  · exact ((ram_app% (kc 659 ?_ ?_ ?_ ?_ ?_))).trans gwA
  · show c₄.nmem (c₅.nreg MD₁) = 0
    ram_rw [k5 MD₁ (by swoInit2), keepT MD₁ (by swoInit4) (by swoInit4) (by swoInit4) (by swoInit4) (by swoInit4) (by swoInit4)
      (by swoInit4) (by swoInit4), mdM, tmem, m0M]
  · intro i hi
    show c₄.nmem (c₅.nreg MD₁ + 1 + i) = _
    ram_rw [k5 MD₁ (by swoInit2), keepT MD₁ (by swoInit4) (by swoInit4) (by swoInit4) (by swoInit4) (by swoInit4) (by swoInit4)
      (by swoInit4) (by swoInit4), mdM, tmem, mcM i hi, k20', fS.2.2.1 _ (by
        have := w20.1; omega), mA]
  · rw [k5 CD₁ (by swoInit2), k5 MD₁ (by swoInit2), keepT CD₁ (by swoInit4) (by swoInit4) (by swoInit4) (by swoInit4)
      (by swoInit4) (by swoInit4) (by swoInit4) (by swoInit4), keepT MD₁ (by swoInit4) (by swoInit4) (by swoInit4) (by swoInit4)
      (by swoInit4) (by swoInit4) (by swoInit4) (by swoInit4), mdM, cdM]
  · rw [k5 TBR (by swoInit2), k5 MD₁ (by swoInit2), keepT MD₁ (by swoInit4) (by swoInit4) (by swoInit4) (by swoInit4)
      (by swoInit4) (by swoInit4) (by swoInit4) (by swoInit4), tB, aM, mdM]
  · assumption
  · ram_simp [k5, tB] <;> reg_omega
  · ram_simp [k5, tA, tB] 
  · rfl

end

end SweepEv

end Chazelle.Core
