module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.ShootCutCutter2
public import Chazelle.Core.NFBuildMain

/-!
# WP-G, part 36: the arc-cutter meets `CutterOK`

`cutter_ok`: the arc-cutter `cutter` (the set-up, the core with `cutEmit`, the finish) meets
`CutterOK` for the grade-table context, with `G(γ) = κc (⌈log₂ γ⌉ + 1)` pieces and steps and
granularity `cutGran γ`.
-/


namespace Chazelle.Core

namespace ShootCut

open Machine Machine.Stmt Programs SignK NFLoc
open Chazelle.Chain (sideInArc)

@[expose] public section

/-- The registers the arc-cutter writes: bands `1, 5, 14, 15` and the allocator. -/
def Bcut (r : ℕ) : Bool :=
  decide (r / 10000 = 1) || decide (r / 10000 = 5) || decide (r / 10000 = 14) ||
    decide (r / 10000 = 15) || decide (r = 9999)

theorem wrM_cutter : BuildRam.wrM Bcut cutter = true := by decide

/-- The real registers the arc-cutter writes: bands `1, 5, 14, 15`. -/
def BcutR (r : ℕ) : Bool :=
  decide (r / 10000 = 1) || decide (r / 10000 = 5) || decide (r / 10000 = 14) ||
    decide (r / 10000 = 15)

theorem wrM2_cutter : BuildRam.wrM2 Bcut BcutR cutter = true := by decide

theorem BcutR_false {r : ℕ} (hr : bandOf r ∉ oracleBands) : BcutR r = false := by
  have h1 : (1 : ℕ) ∈ oracleBands := by decide
  have h5 : (5 : ℕ) ∈ oracleBands := by decide
  have h14 : (14 : ℕ) ∈ oracleBands := by decide
  have h15 : (15 : ℕ) ∈ oracleBands := by decide
  core_grind

theorem chainModel_ne_interior' (C : Chain) (Q : Polygon) : chainModel C ≠ interiorModel Q := by
  intro h
  have := congrArg (fun M : Model => M.counted 0) h
  core_grind

section
variable {m : ℕ → ℕ} {B : ℕ} {Q : Polygon}
/-- The model descriptor of a chain model holds a chain descriptor. -/
theorem modelDesc_chain {M : Model} {C : Chain}
    (h : ModelDescAt m B Q M) (hM : M = chainModel C) :
    m B = 0 ∧ ∃ H C', ChainDescAt m (B + 1) Q H C' ∧ M = chainModel C' := by
  rcases h with ⟨h0, H, C', hC, hM'⟩ | ⟨-, -, hI⟩
  · ram_grind
  · exact absurd (hM.symm.trans hI) (chainModel_ne_interior' C Q)

/-- **A chain descriptor determines the chain.** -/
theorem chainDesc_unique {H H' : Host} {C C' : Chain}
    (h : ChainDescAt m B Q H C) (h' : ChainDescAt m B Q H' C') : C = C' := by
  obtain ⟨h1, h2, h3, h4, -⟩ := h
  obtain ⟨h1', h2', h3', h4', -⟩ := h'
  have hH : H = H' := NFLoc.hostAt_unique h1 h1'
  subst hH
  obtain ⟨P, s, m, a, b⟩ := C
  obtain ⟨P', s', m', a', b'⟩ := C'
  simp_all


end

/-- The constant of the arc-cutter. -/
def κc : ℕ := 2500000

theorem Bcut_false {r : ℕ} (hr : bandOf r ∉ oracleBands) (ha : r ≠ ALLOC) : Bcut r = false := by
  have h1 : (1 : ℕ) ∈ oracleBands := by decide
  have h5 : (5 : ℕ) ∈ oracleBands := by decide
  have h14 : (14 : ℕ) ∈ oracleBands := by decide
  have h15 : (15 : ℕ) ∈ oracleBands := by decide
  unfold bandOf at hr
  unfold Bcut
  have a1 : r / 10000 ≠ 1 := fun h => hr (h ▸ h1)
  have a5 : r / 10000 ≠ 5 := fun h => hr (h ▸ h5)
  have a14 : r / 10000 ≠ 14 := fun h => hr (h ▸ h14)
  have a15 : r / 10000 ≠ 15 := fun h => hr (h ▸ h15)
  aesop

/-- **The arc-cutter meets `CutterOK`.** -/
theorem cutter_ok (O : OracleIface) :
    CutterOK cutter oracleBands (fun γ => κc * (Nat.clog 2 γ + 1)) cutGran (gradeCtx O)
      OkModel := by
  intro P W c hw hpre hcost
  obtain ⟨hG, hHW, hX, hcap, hMDWF, M, hMD, hOk, hsP, heP, hs1, he1, -, hin2, hwt⟩ := hpre
  -- the inputs
  set MD := c.nreg 150000 with hMDd
  set γ := c.nreg 150009 with hγd
  set h := c.nreg 150013 with hhd
  set A₀ := c.nreg ALLOC with hA₀
  set m₀ := c.nmem with hm₀
  set s : WPos := ⟨c.nreg 150001, c.nreg 150002⟩ with hsd
  set e : WPos := ⟨c.nreg 150003, c.nreg 150004⟩ with hed
  replace hX : Robust A₀ m₀ (fun m' => GradeRaw O P m' h A₀) := hX
  replace hcap : γ ≤ 2 ^ (m₀ h - 1) := hcap
  replace hMDWF : ModelDescWF P A₀ m₀ MD := hMDWF
  replace hMD : ModelDescAt m₀ MD (Qof P) M := hMD
  replace hsP : ProperPos M (Qof P) P.n s := hsP
  replace heP : ProperPos M (Qof P) P.n e := heP
  replace hs1 : s.edge < M.W.n := hs1
  replace he1 : e.edge < M.W.n := he1
  replace hin2 : e.hgt = 0 ∨ M.InnerPt (M.pos (Qof P) e) := hin2
  replace hwt : M.arcWt (M.key (Qof P) s) (M.key (Qof P) e) ≤ γ := hwt
  replace hcost : A₀ + κc * (Nat.clog 2 γ + 1) ≤ W := hcost
  -- the chain
  obtain ⟨H₀, C₀, -, -, -, -, hM₀⟩ := hOk
  obtain ⟨h0, H, C, hD, hMC⟩ := modelDesc_chain hMD hM₀
  subst hMC
  obtain ⟨hMD6, hwf6⟩ := hMDWF
  obtain ⟨hD5, hwfC⟩ := hwf6 h0
  obtain ⟨hlen, hHwf, hHA, hsC⟩ := hwfC H C hD
  have hn3 : 3 ≤ P.n := Chazelle.Jordan.simple_three_le hG.1
  have hAW : A₀ ≤ W := by omega
  have hnW : (chainModel C).W.n = 2 * C.m + 7 := chainModel_n C
  rw [hnW] at hs1 he1
  have S : SEnv O P C H (m₀ (MD + 1)) h γ m₀ A₀ W :=
    ⟨hD.2.1, hD.1, hHA, hHwf, hlen, hsC, hX, hcap, hAW, hHW, by omega, hG⟩
  have hin : e.hgt = 0 ∨ (chainModel C).InnerPt ((chainModel C).pos (Qof P) e) := hin2
  -- `2 γ ≤ W`
  have hγW : 2 * γ ≤ W := by
    have hG0 := hX.holds
    have hΛ := hG0.1
    have h2 : 2 ^ (m₀ h - 1) ≤ 2 ^ topGrade P.n := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 := Setup.pow_topGrade_le (n := P.n) (by omega)
    grind [hostWords]
  have hlog := Nat.log_le_clog 2 γ
  have hκ : κc = 2500000 := rfl
  -- the set-up
  obtain ⟨c₁, k₁, Nmax, e₁, hk₁, hI₁, hlt, fr₁, m₁⟩ := cutInit_exec (P := P) c hw (m₀ := m₀)
    (fun a _ => rfl) rfl rfl hγW (by ram_grind)
  have g₁ : ∀ x, 150000 ≤ x → x < 150100 → c₁.nreg x = c.nreg x := fun x h1 h2 =>
    fr₁ x (by omega)
  -- the core
  obtain ⟨c₂, k₂, ps, e₂, hk₂, hI₂, arc, hok, hl, hm₂⟩ := core_exec S (cutEmit_ok S _)
    (ps₀ := []) (MD := MD) (mode := c.nreg 150020) (s := s) (e := e) hD
    (by omega) rfl c₁ e₁.wb_right (fun a _ => by rw [m₁]) (g₁ _ (by omega) (by omega))
    (g₁ _ (by omega) (by omega)) (g₁ _ (by omega) (by omega)) (g₁ _ (by omega) (by omega))
    (g₁ _ (by omega) (by omega)) (g₁ _ (by omega) (by omega)) (g₁ _ (by omega) (by omega))
    (g₁ _ (by omega) (by omega)) hI₁ hsP heP hs1 he1 hin hwt
  rw [List.nil_append] at hI₂
  have hq : ps.length ≤ Nmax := by linarith
  -- the finish
  obtain ⟨c₃, k₃, e₃, hk₃, o10, om, omo, oA, oAk, or₃, orr, orm, oo⟩ :=
    cutFin_exec (P := P) c₂ e₂.wb_right hI₂ hq
  have ex : Exec P W cutter c c₃ (k₁ + (k₂ + k₃)) := by
    unfold cutter; exact .seq e₁ (.seq e₂ e₃)
  have fM := BuildRam.exec_frameM ex wrM_cutter
  have fR := BuildRam.exec_frameM2 ex wrM2_cutter
  have hA₂ : c₂.nreg ALLOC = A₀ := hI₂.alloc
  have hrec := hI₂.recs
  rw [List.take_of_length_le hq] at hrec
  have hne := arc.ne
  have hpos : 0 < ps.length := List.length_pos_of_ne_nil hne
  refine ⟨c₃, k₁ + (k₂ + k₃), ex, ?_, ?_, ?_⟩
  · -- the cost
    show k₁ + (k₂ + k₃) ≤ κc * (Nat.clog 2 γ + 1)
    grind [coreCost, genCost]
  · -- the pieces
    intro M' hM'
    have hM'C : M' = chainModel C := by
      rcases (show ModelDescAt m₀ MD (Qof P) M' from hM') with ⟨-, H', C', hC', hM''⟩ | ⟨h1, -⟩
      · rw [hM'', chainDesc_unique hC' hD]
      omega
    subst hM'C
    have hL : rd c₃ bCut 10 = A₀ := o10
    have hq3 : c₃.nmem A₀ = ps.length := om
    have hpc : ∀ a, A₀ < a → c₃.nmem a = c₂.nmem a := fun a ha => omo a (by omega)
    have hm₃ : ∀ a, a < A₀ → c₃.nmem a = m₀ a := fun a ha => by
      ram_grind
    -- the words of the records
    have w0 : ∀ i (hi : i < ps.length), c₃.nmem (A₀ + 1 + 7 * i + 0) = (ps[i]'hi).s.edge :=
      fun i hi => by rw [hpc _ (by omega), Nat.add_zero]; exact (hrec i hi).1
    have w1 : ∀ i (hi : i < ps.length), c₃.nmem (A₀ + 1 + 7 * i + 1) = (ps[i]'hi).s.hgt :=
      fun i hi => by rw [hpc _ (by omega)]; exact (hrec i hi).2.1
    have w2 : ∀ i (hi : i < ps.length), c₃.nmem (A₀ + 1 + 7 * i + 2) = (ps[i]'hi).e.edge :=
      fun i hi => by rw [hpc _ (by omega)]; exact (hrec i hi).2.2.1
    have w3 : ∀ i (hi : i < ps.length), c₃.nmem (A₀ + 1 + 7 * i + 3) = (ps[i]'hi).e.hgt :=
      fun i hi => by rw [hpc _ (by omega)]; exact (hrec i hi).2.2.2.1
    have w4 : ∀ i (hi : i < ps.length), c₃.nmem (A₀ + 1 + 7 * i + 4) = (ps[i]'hi).kind :=
      fun i hi => by rw [hpc _ (by omega)]; exact (hrec i hi).2.2.2.2.1
    have w56 : ∀ i (hi : i < ps.length), (ps[i]'hi).kind = 1 →
        c₃.nmem (A₀ + 1 + 7 * i + 5) = c₃.nmem (ps[i]'hi).entry ∧
        c₃.nmem (A₀ + 1 + 7 * i + 6) = c₃.nmem ((ps[i]'hi).entry + 1) := fun i hi hk => by
      have he := entry_lt S (hok _ (List.getElem_mem hi)) hk
      obtain ⟨b5, b6⟩ := (hrec i hi).2.2.2.2.2 hk
      rw [hpc (A₀ + 1 + 7 * i + 5) (by omega), hpc (A₀ + 1 + 7 * i + 6) (by omega), b5, b6,
        hm₃ (ps[i]'hi).entry (by omega), hm₃ ((ps[i]'hi).entry + 1) (by omega)]
      omega
    have kS : ∀ i (hi : i < ps.length), (chainModel C).key (Qof P)
        ⟨c₃.nmem (A₀ + 1 + 7 * i + 0), c₃.nmem (A₀ + 1 + 7 * i + 1)⟩ =
        (chainModel C).key (Qof P) (ps[i]'hi).s := fun i hi => by rw [w0 i hi, w1 i hi]
    have kE : ∀ i (hi : i < ps.length), (chainModel C).key (Qof P)
        ⟨c₃.nmem (A₀ + 1 + 7 * i + 2), c₃.nmem (A₀ + 1 + 7 * i + 3)⟩ =
        (chainModel C).key (Qof P) (ps[i]'hi).e := fun i hi => by rw [w2 i hi, w3 i hi]
    dsimp only
    rw [hL, hq3]
    refine ⟨le_rfl, by rw [oA], ?_, hpos, ?_, ?_, fun i hi => ?_, fun i hi => ?_,
      fun i hi hk => ?_, fun i hi hk => ?_, fun i hi => ?_, fun i hi => ?_⟩
    · show ps.length ≤ κc * (Nat.clog 2 γ + 1)
      rw [hκ]; linarith
    · rw [kS 0 hpos]
      have : (ps[0]'hpos) = ps.head hne := (List.head_eq_getElem hne).symm
      rw [this, arc.hs]; rfl
    · rw [kE _ (by omega)]
      have : (ps[ps.length - 1]'(by omega)) = ps.getLast hne := (List.getLast_eq_getElem hne).symm
      rw [this, arc.he]; rfl
    · rw [kE i (by omega), kS (i + 1) hi, arc.ch i hi]
    · rw [kS i (by omega), kE i (by omega)]
      exact arc.e6 i hi
    · rw [kS i hi, kE i hi]
      have hk' : (ps[i]'hi).kind = 0 := by rw [← w4 i hi]; exact hk
      exact (hok _ (List.getElem_mem hi)).2.2.2.2.2.1 hk'
    · have hk' : (ps[i]'hi).kind = 1 := by rw [← w4 i hi]; exact hk
      obtain ⟨b5, b6⟩ := w56 i hi hk'
      rw [kS i hi, kE i hi, b5, b6, w0 i hi, w1 i hi, w2 i hi, w3 i hi]
      have := kind1_facts (hok _ (List.getElem_mem hi)) hk' hX hm₃ (A' := c₃.nreg ALLOC)
        (by omega)
      exact this
    · have hp := hok _ (List.getElem_mem hi)
      rw [w0 i hi, w1 i hi, w2 i hi, w3 i hi, hnW]
      exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1⟩
    · rw [w4 i hi]
      rcases (hok _ (List.getElem_mem hi)).2.2.2.2.1 with h | h <;> omega
  · -- the frame
    refine ⟨fun r hr ha => fM.1 r (Bcut_false hr ha), fun r hr => fR r (BcutR_false hr),
      fun a ha => ?_, fun a _ => by rw [fM.2.2.1], fM.2.2.2, by omega, ?_⟩
    · ram_grind
    omega

end

end ShootCut

end Chazelle.Core
