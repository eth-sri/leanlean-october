module

public import Chazelle.Core.SweepIoLab0L
public import Chazelle.Core.SweepIoS0CandBsMain

/-!
# The sweep RAM (WP-D), answers: the label candidates of a side-0 query (`Lab0Spec`)

`lab0S ls sh`:

1. the binary search in the log (`ls`, `S0C.LSearchSpec`) for the arrival position `(zP, zPh)`
   of the query point: the number `t` of log keys before its key;
2. the list address `gL` and the gap regions (`gapS`): six words, the three regions at each of
   the two copies of the top at the slit of `C₂`;
3. the entries `t - 2, t - 1, t` and the twelve label slots (`slotsOf slotPairs`);
4. the gather of the arcs of the eighteen listed regions of `N₂` (`gather`), and the shot from the
   symbolic point `sO` at them in the model of `C₂`, offered with tag `1` (`symShot`).

**`lab0_of : S0C.LSearchSpec → Lab0Spec`**, **`lab0 : Lab0Spec`**.  Soundness: every candidate is
a hit of the shot (`symShot_irs`).  Completeness: the log entry `i` of the position is `t` or
`t - 1` (`logIdx_cases`), so the labels of `i` and `i - 1` are among the slots (`label_mem`); the
gap labels are among the gap regions (`gap_pos`, `gap_reg`); a ray starting in a listed region
exits on the gathered arcs (`exit_mem_gather`).
-/

namespace Chazelle.Core

namespace SweepIo

namespace Lab0

open Set
open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Merge (FreeAt)

@[expose] public section

/-! ## The program -/

/-- The log entries `t, t - 1, t - 2`. -/
def eIn : List Instr := [.copyN eR2 S0C.lsI, .subN eR1 eR2 K1, .subN eR0 eR1 K1]

/-- The inputs of the gather: the normal form of `C₂`, eighteen regions. -/
def gIn : List Instr := [.copyN gNF (sw 4), .constN gC 18]

/-- **The label candidates of a side-0 query.** -/
def lab0S (ls sh : Stmt) : Stmt :=
  .seq (.seq (block lsIn) ls) (.seq gapS (.seq (block eIn) (.seq (slotsOf slotPairs)
    (.seq (block gIn) (.seq (gather (sw 21)) (symShot sh (sw 31) gBase gK (sw 21) K1))))))

/-- The bound on the gather. -/
def gB (D : ℕ) : ℕ := 11 + 18 * (regK (D + 1) + 2)

/-- The total budget. -/
def lab0Kt (κL T Fg D : ℕ) : ℕ :=
  (2 + κL * (T + 1)) + (gapK T + (3 + (slotK * 12 + (2 + (gB D + symShotK Fg (18 * (D + 1)))))))

theorem lab0_cost (κL T Fg D : ℕ) :
    lab0Kt κL T Fg D ≤ (κL + 20000000) * (D + 2) * (Fg + T + 1) := by
  unfold lab0Kt gapK lh1K slotK gB regK arcK symShotK ShotList.shotCost offerK
  have h1 : κL * (T + 1) ≤ κL * (D + 2) * (Fg + T + 1) := by
    rw [mul_assoc]
    apply Nat.mul_le_mul_left
    nlinarith
  have h2 : (18 * (D + 1) + 1) * (16 * Fg + 500000) ≤ 9500000 * (D + 2) * (Fg + 1) := by
    nlinarith
  have h3 : 9500000 * (D + 2) * (Fg + 1) ≤ 9500000 * (D + 2) * (Fg + T + 1) := by
    apply Nat.mul_le_mul_left; omega
  have h4 : 5500 * (T + 1) ≤ 5500 * (D + 2) * (Fg + T + 1) := by
    rw [mul_assoc]
    apply Nat.mul_le_mul_left
    nlinarith
  have h5 : (D + 2) ≤ (D + 2) * (Fg + T + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have e : (κL + 20000000) * (D + 2) * (Fg + T + 1) =
      κL * (D + 2) * (Fg + T + 1) + 20000000 * ((D + 2) * (Fg + T + 1)) := by ring
  rw [e]
  have e2 : 9500000 * (D + 2) * (Fg + T + 1) = 9500000 * ((D + 2) * (Fg + T + 1)) := by ring
  have e3 : 5500 * (D + 2) * (Fg + T + 1) = 5500 * ((D + 2) * (Fg + T + 1)) := by ring
  rw [e2] at h3
  rw [e3] at h4
  nlinarith

theorem symShotK_mono {Fg K K' : ℕ} (h : K ≤ K') : symShotK Fg K ≤ symShotK Fg K' := by
  unfold symShotK ShotList.shotCost
  have := Nat.mul_le_mul_right (16 * Fg + 500000) (Nat.add_le_add_right h 1)
  omega

section Run

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

theorem eIn_val (m f : ℕ → ℕ) (hk : f K1 = 1) :
    regB m eIn f eR2 = f S0C.lsI ∧ regB m eIn f eR1 = f S0C.lsI - 1 ∧
    regB m eIn f eR0 = f S0C.lsI - 1 - 1 ∧
    ∀ q, q ≠ eR0 → q ≠ eR1 → q ≠ eR2 → regB m eIn f q = f q := by
  have hk' : f 240611 = 1 := hk
  refine ⟨?_, ?_, ?_, fun q h0 h1 h2 => regB_other _ _ _ (fun i hi => ?_)⟩
  · simp only [eIn, regB, regI, upd, eR0, eR1, eR2, S0C.lsI, K1, sw]
    simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false]
  · simp only [eIn, regB, regI, upd, eR0, eR1, eR2, S0C.lsI, K1, sw]
    simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false, hk']
  · simp only [eIn, regB, regI, upd, eR0, eR1, eR2, S0C.lsI, K1, sw]
    simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false, hk']
  · simp only [eIn, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;> simp only [dstI] <;> intro h <;> subst h <;> simp_all

theorem gIn_val (m f : ℕ → ℕ) :
    regB m gIn f gNF = f (sw 4) ∧ regB m gIn f gC = 18 ∧
    ∀ q, q ≠ gNF → q ≠ gC → regB m gIn f q = f q := by
  refine ⟨?_, ?_, fun q h0 h1 => regB_other _ _ _ (fun i hi => ?_)⟩
  · simp only [gIn, regB, regI, upd, gNF, gC, sw]
    simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false]
  · simp only [gIn, regB, regI, upd, gNF, gC, sw]
    simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false]
  · simp only [gIn, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> simp only [dstI] <;> intro h <;> subst h <;> simp_all

end Run

/-! ## The contract -/

theorem acc_regs {j : ℕ} (hj : j ≤ 12) : 240000 ≤ accA + j ∧ accA + j < 250000 ∧
    ¬ (sw 1000 ≤ accA + j ∧ accA + j ≤ sw 1119) ∧ ¬ (sw 4000 ≤ accA + j ∧ accA + j ≤ sw 4037) ∧
    accA + j ≠ ALLOC := by
  unfold accA sw ALLOC; omega

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 40000 in
/-- **The label candidates of a side-0 query** from the binary search in the log. -/
theorem lab0_of (hLS : S0C.LSearchSpec) : Lab0Spec := by
  obtain ⟨ls, κL, hls⟩ := lsBody_of hLS
  refine ⟨lab0S ls, fun D => (κL + 20000000) * (D + 2), ?_⟩
  intro sh Bs F X Ok hsh hBs hXl P W c₀ c J H N₁ N₂ E L s z hA hI hz hzs hzt hfree hzPn hpp
    harr hs hsl hseval hbR hacc hroom
  beta_reduce at hroom ⊢
  have hcost := lab0_cost κL (c₀.nreg TLR) (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6))
  have hroom' : c.nreg ALLOC + lab0Kt κL (c₀.nreg TLR) (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6)) ≤ W :=
    le_trans (Nat.add_le_add_left hcost _) hroom
  unfold lab0Kt at hroom'
  have hK := hA.hK
  have hP : J.right.P.Simple := hA.hP
  have hN := hA.hNF₂
  have nO : ∀ q, 240000 ≤ q → q < 250000 → bandOf q ∉ oracleBands := fun q h1 h2 =>
    not_oracle_sw h1 h2
  unfold lab0S
  -- 1. the binary search
  refine (IRS.seq (K₁ := 2 + κL * (c₀.nreg TLR + 1))
    (K₂ := gapK (c₀.nreg TLR) + (3 + (slotK * 12 + (2 + (gB (c₀.nreg (sw 6)) + symShotK (F (c₀.nreg (sw 5))) (18 * (c₀.nreg (sw 6) + 1)))))))
    (search_irs hls hA hI hz hzPn hpp harr (by omega)) ?_).mono
    (le_trans (le_of_eq rfl) hcost) (fun _ h => h)
  rintro c₂ hI₂ hA₂ hA₂' ⟨t_le, t_lt, t_ge, fr2, m2⟩
  set t := c₂.nreg S0C.lsI with ht
  set G := c₂.nreg ALLOC with hG
  -- 2. the gap regions
  refine IRS.seq (K₁ := gapK (c₀.nreg TLR)) (K₂ := 3 + (slotK * 12 + (2 + (gB (c₀.nreg (sw 6)) + symShotK (F (c₀.nreg (sw 5))) (18 * (c₀.nreg (sw 6) + 1))))))
    (gap_irs hA hI₂ (by omega)) ?_
  rintro c₃ hI₃ hA₃ hA₃' ⟨g1, g2, g3, g4, j₁, j₂, hj₁, hj₂, g5⟩
  -- 3. the entries
  have k3 := hK.fix hI₃
  refine IRS.seq (K₁ := 3) (K₂ := slotK * 12 + (2 + (gB (c₀.nreg (sw 6)) + symShotK (F (c₀.nreg (sw 5))) (18 * (c₀.nreg (sw 6) + 1)))))
    ((IRS.block eIn hI₃ ⟨iscr_sw (by decide) (by decide), iscr_sw (by decide) (by decide),
      iscr_sw (by decide) (by decide), trivial⟩).mono (by simp [eIn]) (fun _ h => h)) ?_
  rintro c₄ hI₄ hA₄ hA₄' rfl
  obtain ⟨e2v, e1v, e0v, eo⟩ := eIn_val c₃.nmem c₃.nreg k3.2.1
  set c₄ : Config := { c₃ with nreg := regB c₃.nmem eIn c₃.nreg } with hc₄
  have tl3 : c₃.nreg S0C.lsI = t :=
    g4 _ (nO _ (by decide) (by decide)) (by decide) (by decide) (by decide)
  have eA4 : c₄.nreg ALLOC = G + 6 := by
    show regB _ _ _ _ = _; rw [eo _ (by decide) (by decide) (by decide), g2]
  have egL4 : c₄.nreg gL = G := by
    show regB _ _ _ _ = _; rw [eo _ (by decide) (by decide) (by decide), g1]
  have em4 : c₄.nmem = c₃.nmem := rfl
  -- 4. the slots
  have hK₄ := hK.fix hI₄
  have f300 : ∀ c', IInv W c₀ c' → c'.nreg (sw 300) = rd c₀ bSweep 300 := fun c' h =>
    h.hin _ (by unfold IFix sw; omega)
  have f301 : ∀ c', IInv W c₀ c' → c'.nreg (sw 301) = rd c₀ bSweep 301 := fun c' h =>
    h.hin _ (by unfold IFix sw; omega)
  have hlog := hA.hlog
  have hitems : ∀ p ∈ slotPairs, ¬ SlotW p.1 ∧ ¬ SlotW p.2 ∧ p.1 ≠ ALLOC ∧ p.2 ≠ ALLOC ∧
      c₄.nreg p.2 ≤ 3 := by
    intro p hp
    obtain ⟨h1, h2⟩ := slotPairs_facts p hp
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rcases h1 with h | h | h <;> rw [h] <;> unfold SlotW <;> decide
    · rcases h2 with h | h | h | h <;> rw [h] <;> unfold SlotW <;> decide
    · rcases h1 with h | h | h <;> rw [h] <;> decide
    · rcases h2 with h | h | h | h <;> rw [h] <;> decide
    · rcases h2 with h | h | h | h <;> rw [h]
      · rw [hK₄.1]; omega
      · rw [hK₄.2.1]; omega
      · rw [hK₄.2.2.2.2.2.1]; omega
      · rw [hK₄.2.2.2.2.2.2]
  refine IRS.seq (K₁ := slotK * 12) (K₂ := 2 + (gB (c₀.nreg (sw 6)) + symShotK (F (c₀.nreg (sw 5))) (18 * (c₀.nreg (sw 6) + 1))))
    (slots_irs slotPairs hI₄ hK hitems
      (by rw [f300 _ hI₄, f301 _ hI₄]; have := hI₄.hA; omega) (by rw [egL4, eA4]; omega)
      (by rw [eA4]; simp [slotPairs]; omega)) ?_
  rintro c₅ hI₅ hA₅ hA₅' ⟨s1, s2, s3, s4⟩
  simp only [show slotPairs.length = 12 from rfl] at s1 s4
  -- 5. the inputs of the gather
  refine IRS.seq (K₁ := 2) (K₂ := gB (c₀.nreg (sw 6)) + symShotK (F (c₀.nreg (sw 5))) (18 * (c₀.nreg (sw 6) + 1)))
    ((IRS.block gIn hI₅ ⟨iscr_sw (by decide) (by decide),
      ⟨iscr_sw (by decide) (by decide), by have := hA.hWm; omega⟩, trivial⟩).mono
      (by simp [gIn]) (fun _ h => h)) ?_
  rintro c₆ hI₆ hA₆ hA₆' rfl
  obtain ⟨n6, c6v, go⟩ := gIn_val c₅.nmem c₅.nreg
  set c₆ : Config := { c₅ with nreg := regB c₅.nmem gIn c₅.nreg } with hc₆
  have egL6 : c₆.nreg gL = G := by
    show regB _ _ _ _ = _
    rw [go _ (by decide) (by decide), s2 _ (by unfold SlotW gL sV sA sX sN sE sw; omega)
      (by decide), egL4]
  have eA6 : c₆.nreg ALLOC = G + 18 := by
    show regB _ _ _ _ = _
    rw [go _ (by decide) (by decide), s1, eA4]
  have em6 : c₆.nmem = c₅.nmem := rfl
  -- the words of the list
  have hI4m : ∀ a, a < c₀.nreg ALLOC → c₄.nmem a = c₀.nmem a := fun a ha => hI₄.hm a ha
  have gap1 : ∀ i, i < 3 → c₆.nmem (G + i) = (Sweep.nbrRegs N₂ j₁).getD i 0 := fun i hi => by
    rw [em6, s3 _ (by rw [eA4]; omega), em4]; exact (g5 i hi).1
  have gap2 : ∀ i, i < 3 → c₆.nmem (G + 3 + i) = (Sweep.nbrRegs N₂ j₂).getD i 0 := fun i hi => by
    rw [em6, s3 _ (by rw [eA4]; omega), em4]; exact (g5 i hi).2
  have slotw : ∀ idx, idx < 12 → c₆.nmem (G + 6 + idx) =
      slotVal c₄.nmem (rd c₀ bSweep 300) (rd c₀ bSweep 301) (c₄.nmem G)
        (c₄.nreg (slotPairs.getD idx (0, 0)).1) (c₄.nreg (slotPairs.getD idx (0, 0)).2) := by
    intro idx hidx
    rw [em6, show G + 6 + idx = c₄.nreg ALLOC + idx by rw [eA4], s4 idx hidx, f300 _ hI₄,
      f301 _ hI₄, egL4]
  have nbr_lt : ∀ j, j < N₂.arcs.length → ∀ i, i < 3 → (Sweep.nbrRegs N₂ j).getD i 0 < N₂.nRegions :=
    fun j hj i hi => nbrRegs_lt hN hj _ (by
      rw [List.getD_eq_getElem _ _ (by simp [Sweep.nbrRegs]; omega)]; exact List.getElem_mem _)
  have hg0 : c₄.nmem G < N₂.nRegions := by
    have := (g5 0 (by norm_num)).1
    rw [add_zero] at this
    rw [em4, this]; exact nbr_lt j₁ hj₁.1 0 (by norm_num)
  have slot_lt : ∀ v w, w ≤ 3 →
      slotVal c₄.nmem (rd c₀ bSweep 300) (rd c₀ bSweep 301) (c₄.nmem G) v w < N₂.nRegions := by
    intro v w hw
    unfold slotVal
    split_ifs with hc
    · obtain ⟨hv, hwn⟩ := hc
      rw [hI4m _ (by omega)] at hwn ⊢
      exact label_valid hA hv hwn hw
    · exact hg0
  have valid : ∀ i, i < 18 → c₆.nmem (G + i) < N₂.nRegions := by
    intro i hi
    rcases (show i < 3 ∨ (3 ≤ i ∧ i < 6) ∨ 6 ≤ i by omega) with h | ⟨h1, h2⟩ | h
    · rw [gap1 i h]; exact nbr_lt j₁ hj₁.1 i h
    · rw [show G + i = G + 3 + (i - 3) by omega, gap2 (i - 3) (by omega)]
      exact nbr_lt j₂ hj₂.1 _ (by omega)
    · rw [show G + i = G + 6 + (i - 6) by omega, slotw (i - 6) (by omega)]
      have hmem : slotPairs.getD (i - 6) (0, 0) ∈ slotPairs := by
        rw [List.getD_eq_getElem _ _ (by simp [slotPairs]; omega)]; exact List.getElem_mem _
      exact slot_lt _ _ (hitems _ hmem).2.2.2.2
  -- 6. the gather
  set rs : List ℕ := (List.range 18).map (fun i => c₆.nmem (G + i)) with hrs_def
  have hrs_len : rs.length = 18 := by simp [rs]
  have hrs_get : ∀ j, j < 18 → rs.getD j 0 = c₆.nmem (G + j) := fun j hj => by
    simp [rs, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
  have mem_rs : ∀ i, i < 18 → c₆.nmem (G + i) ∈ rs := fun i hi =>
    List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩
  have hrs : ∀ r ∈ rs, r < N₂.nRegions := by
    intro r hr
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hr
    exact valid i (List.mem_range.1 hi)
  obtain ⟨hAr, -⟩ := region_bounds' hP hN hA.hdeg₂
  have hArs : ∀ r ∈ rs, (N₂.region r).arcs.length ≤ c₀.nreg (sw 6) + 1 := fun r hr =>
    hAr r (hrs r hr)
  have hgK : gatherK N₂ rs ≤ gB (c₀.nreg (sw 6)) := by
    have := gatherK_le hArs
    rw [hrs_len] at this
    unfold gB; omega
  have n6' : c₆.nreg gNF = c₀.nreg (sw 4) := by
    show regB _ _ _ _ = _; rw [n6]; exact hI₅.hin _ (by unfold IFix sw; omega)
  refine IRS.seq (K₁ := gB (c₀.nreg (sw 6)))
    (K₂ := symShotK (F (c₀.nreg (sw 5))) (18 * (c₀.nreg (sw 6) + 1)))
    ((gather_irs (C := J.right) (N := N₂) (B := c₀.nreg (sw 4)) (E := E) (rs := rs) hI₆ hK
      (hA.ctxR hI₆) ⟨by decide, by decide, by unfold GSet sw; omega⟩ hP hN
      (hA.hN₂.transport (fun a ha => hI₆.hm a (by have := hA.hE; omega))) n6'
      (hA.hE.trans hI₆.hA) hrs (fun j hj => by rw [egL6, hrs_get j (by omega)])
      (by rw [egL6, eA6, hrs_len]) (by show regB _ _ _ _ = _; rw [c6v, hrs_len])
      (by rw [eA6]; have := hA₆'; omega)).mono hgK (fun _ h => h)) ?_
  rintro c₇ hI₇ hA₇ hA₇' ⟨⟨w1, w2, w3, w4, w5, w6, -, -, -⟩, hctx7⟩
  -- 7. the shot
  have hlen : (regArcs N₂ rs).length ≤ 18 * (c₀.nreg (sw 6) + 1) := by
    have := regArcs_length_le hArs
    rw [hrs_len] at this; exact this
  have keep7 : ∀ r, bandOf r ∉ oracleBands → ¬ (sw 1000 ≤ r ∧ r ≤ sw 1119) →
      ¬ (sw 4000 ≤ r ∧ r ≤ sw 4037) → r ≠ ALLOC → c₇.nreg r = c.nreg r := by
    intro r h1 h2 h3 h4
    unfold sw at h2 h3
    rw [w6 r h1 (by unfold GSet sw; omega) h4]
    show regB _ _ _ _ = _
    rw [go r (by unfold gNF sw; omega) (by unfold gC sw; omega),
      s2 r (by unfold SlotW sV sA sX sN sE sw; omega) h4]
    show regB _ _ _ _ = _
    rw [eo r (by unfold eR0 sw; omega) (by unfold eR1 sw; omega) (by unfold eR2 sw; omega),
      g4 r h1 (by unfold gL sw; omega) (by unfold sw; omega) h4,
      fr2 r h1 (by unfold sw; omega) h4]
  have qD7 : c₇.nreg qD = c.nreg qD :=
    keep7 _ (nO _ (by decide) (by decide)) (by decide) (by decide) (by decide)
  have hs7 : SymPtIn c₇ sO s := symPtIn_copy hs
    (keep7 _ (nO _ (by decide) (by decide)) (by decide) (by decide) (by decide))
    (keep7 _ (nO _ (by decide) (by decide)) (by decide) (by decide) (by decide))
    (keep7 _ (nO _ (by decide) (by decide)) (by decide) (by decide) (by decide))
  have hacc7 : AccOK P accA (ModB J (c.nreg bL) (c.nreg bR)) J.whole.radius z
      (dirOf (c₇.nreg qD)) L c₇ := by
    rw [qD7]
    refine hacc.transport (fun j hj => ?_)
    obtain ⟨hj1, hj2, hj3, hj4, hj5⟩ := acc_regs hj
    exact keep7 _ (nO _ hj1 hj2) hj3 hj4 hj5
  have hK₇ := hK.fix hI₇
  have hzD : z ∈ J.right.dom := S0C.z_mem_right_dom hA.hP hz hzs hzt
  have hbox := J.right.dom_subset_box hzD
  have hMod : ModB J (c.nreg bL) (c.nreg bR) (c₇.nreg K1) = J.right := by
    rw [hK₇.2.1, hbR]; simp [ModB]
  have harcs : ∀ j, j < c₇.nreg gK →
      ShotList.PieceOK (chainModel J.right) (Qof P) P.n
        (ShotList.arcAt c₇.nmem (c₇.nreg gBase) j) ∧
      (chainModel J.right).arcWt
        ((chainModel J.right).key (Qof P) (ShotList.arcAt c₇.nmem (c₇.nreg gBase) j).1)
        ((chainModel J.right).key (Qof P) (ShotList.arcAt c₇.nmem (c₇.nreg gBase) j).2) ≤
        c₀.nreg (sw 5) := by
    intro j hj
    rw [w2] at hj
    rw [w1, w4 j hj]
    exact nArc_piece hP hN hA.hsg₂ (regArcs_lt hN hrs _ (by
      rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem _))
  refine (symShot_irs (C := J.right) (H := H) (md := sw 31) (base := gBase) (cnt := gK)
    (dsc := sw 21) (tg := K1) hsh hBs hXl hI₇ hK hA.hG hA.hWh hA.hX hA.hcap hA.hOk₂
    (hA.mdR hI₇) hA.hostReg hctx7 harcs (by rw [w1, w2, w3]) hs7 hsl hseval hzD hbox.1 hbox.2
    hzt hacc7 (by rw [hK₇.2.1]; omega) hMod rfl
    ⟨by unfold SRegOK; decide, by unfold SRegOK; decide, by unfold SRegOK; decide,
      by unfold SRegOK; decide, by unfold SRegOK; decide⟩
    (by rw [w2]; have := symShotK_mono (Fg := F (c₀.nreg (sw 5))) hlen; omega)).mono
    (by rw [w2]; exact symShotK_mono hlen) ?_
  rintro c' ⟨L', hacc', hL', hcomp, k8, hA8, hm8⟩
  rw [qD7] at hacc' hL' hcomp
  refine ⟨⟨L', hacc', ?_, fun τ hτ => ?_, ?_⟩, fun r h1 h2 h3 h4 h5 => ?_, ?_, fun a ha => ?_⟩
  · rcases hL' with rfl | ⟨τ, rfl, -⟩
    · exact le_rfl
    · exact Set.subset_insert _ _
  · rcases hL' with rfl | ⟨τ', rfl, hτ0, hon⟩
    · exact Or.inl hτ
    · rcases hτ with rfl | hτ
      · exact Or.inr ⟨hτ0, hon⟩
      · exact Or.inl hτ
  · intro ls' hlsl hlsrec i hidx V hV hcase hray
    have hσ : dirOf (c.nreg qD) = 1 ∨ dirOf (c.nreg qD) = -1 := SweepPrim.dirOf_cases _
    have eR2v : c₄.nreg eR2 = t := by show regB _ _ _ _ = _; rw [e2v, tl3]
    have eR1v : c₄.nreg eR1 = t - 1 := by show regB _ _ _ _ = _; rw [e1v, tl3]
    have eR0v : c₄.nreg eR0 = t - 1 - 1 := by show regB _ _ _ _ = _; rw [e0v, tl3]
    have lab : ∀ e eR, (eR = eR0 ∨ eR = eR1 ∨ eR = eR2) → c₄.nreg eR = e → e < ls'.length →
        V ∈ logLab J (Qof P) N₂ ls' e →
        ∃ q, q < 18 ∧ regOf (chainModel J.right) (Qof P) N₂ (c₆.nmem (G + q)) = V := by
      intro e eR heR hev he hVe
      obtain ⟨k, hk3, hkn, hkV⟩ := label_mem hlsrec he hVe
      obtain ⟨idx, hidx', h1, h2⟩ := slotPairs_cover heR hk3
      refine ⟨6 + idx, by omega, ?_⟩
      rw [← add_assoc, slotw idx hidx', h1, hev, h2 c₄ hK₄]
      unfold slotVal
      rw [hI4m (rd c₀ bSweep 300 + 7 * e + 2) (by omega),
        ite_eq_left ⟨by omega, hkn⟩, hI4m (rd c₀ bSweep 300 + 7 * e + 3 + k) (by omega)]
      exact hkV
    have hti := logIdx_cases hA t_le t_lt t_ge hlsl hlsrec hidx
    obtain ⟨q, hq18, hqV⟩ : ∃ q, q < 18 ∧
        regOf (chainModel J.right) (Qof P) N₂ (c₆.nmem (G + q)) = V := by
      rcases hcase with h | ⟨hi0, h⟩ | h
      · have hi := hidx.1
        rcases hti with hti | hti
        · exact lab i eR2 (Or.inr (Or.inr rfl)) (by rw [eR2v, hti]) hi h
        · exact lab i eR1 (Or.inr (Or.inl rfl)) (by rw [eR1v]; omega) hi h
      · have hi := hidx.1
        rcases hti with hti | hti
        · exact lab (i - 1) eR1 (Or.inr (Or.inl rfl)) (by rw [eR1v]; omega) (by omega) h
        · exact lab (i - 1) eR0 (Or.inl rfl) (by rw [eR0v]; omega) (by omega) h
      · obtain ⟨hV', hW⟩ := gap_pos J h
        have hn2 : (chainModel J.right).W.n = 2 * J.right.m + 7 := cm_n J.right
        rcases hW with hW | hW
        · obtain ⟨r, hr, hrV⟩ := gap_reg hP hN (p := 2 * J.right.m + 6) (by omega) (by omega)
            hj₁.1 hj₁.2.1 hj₁.2.2 hV' (Or.inl hW)
          obtain ⟨ii, hii, hir⟩ := List.mem_iff_getElem.1 hr
          have hii3 : ii < 3 := by simpa [Sweep.nbrRegs] using hii
          refine ⟨ii, by omega, ?_⟩
          rw [gap1 ii hii3, List.getD_eq_getElem _ _ hii, hir, hrV]
        · obtain ⟨r, hr, hrV⟩ := gap_reg hP hN (p := 6) (by omega) (by omega)
            hj₂.1 hj₂.2.1 hj₂.2.2 hV' (Or.inr hW)
          obtain ⟨ii, hii, hir⟩ := List.mem_iff_getElem.1 hr
          have hii3 : ii < 3 := by simpa [Sweep.nbrRegs] using hii
          refine ⟨3 + ii, by omega, ?_⟩
          rw [← add_assoc, gap2 ii hii3, List.getD_eq_getElem _ _ hii, hir, hrV]
    obtain ⟨hfreeR, hexit⟩ := exit_mem_gather hP hN (rs := rs) (m := c₇.nmem)
      (A := c₆.nreg ALLOC) w4 (valid q hq18) (mem_rs q hq18) hzt hσ (by rw [hqV]; exact hray)
    exact hcomp hfreeR (by rw [w1, w2]; exact hexit)
  · unfold sw at h2 h3 h4
    rw [k8 r h1 (by unfold RS; omega) (by unfold accA sw; omega) h5]
    exact keep7 r h1 (by unfold sw; omega) (by unfold sw; omega) h5
  · omega
  · rw [hm8 a (by omega), w5 a (by omega), em6, s3 a (by omega), em4, g3 a (by omega), m2 a ha]


end

end Lab0

@[expose] public section

/-- **The label candidates of a side-0 query** (piece E). -/
theorem lab0 : Lab0Spec := Lab0.lab0_of S0C.lsearchSpec

end

end SweepIo

end Chazelle.Core
