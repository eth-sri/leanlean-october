module

public import Chazelle.Core.SweepIoS0CandInitStop

/-!
# The sweep RAM (WP-D), answers: the slot table of the side-0 candidates (the table loop)

`tbHit_irs`: a table entry with flag `1` (its end position, the class test, and for a regular
entry the search of its position and the write of its slot); `tbOne_irs`: a table entry;
`tbB_irs`: the two entries of a chord; `tbLoop_irs`: all chords.
-/

namespace Chazelle.Core

namespace SweepIo

namespace S0C

open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep SweepEv

@[expose] public section

/-- The cost of a table entry with flag `1`. -/
def kTb (κL TL : ℕ) : ℕ := 11141 + κL * (TL + 1)

section tab

variable {P : Polygon} {W : ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop} {J : Merge.Junction}
  {H : Host} {N₁ N₂ : NF} {Eb : ℕ} {c₀ c : Config} {rs : List (ℕ × ℕ × ℕ × ℕ × ℕ)}
  {ls : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)}

set_option maxHeartbeats 8000000 in
/-- **A table entry with flag `1`.** -/
theorem tbHit_irs {lsS : Stmt} {κL : ℕ} (hls : LSBody lsS κL)
    (e : IE P W X Ok J H N₁ N₂ Eb c₀ rs ls) (hI : IInv W c₀ c)
    (hB : c.nreg ipB = c₀.nreg ALLOC)
    (hAl : c₀.nreg ALLOC + 6 * c₀.nreg (sw 301) ≤ c.nreg ALLOC)
    (hM5 : c.nreg ipM5 = 2 * J.right.m + 5) (hM6 : c.nreg ipM6 = 6 + midT J.right)
    {k s : ℕ} (hk : c.nreg ipJ = k) (hkK : k < N₂.nChords) (hs : c.nreg ipS = s) (hs1 : s ≤ 1)
    (ha : c.nreg ipA = c₀.nreg (sw 302) + 3 * (2 * k + s))
    (hf : c.nmem (c₀.nreg (sw 302) + 3 * (2 * k + s)) = 1)
    (hS : SInv P J N₂ (c₀.nreg (sw 200)) (c₀.nreg (sw 300)) (c₀.nreg (sw 301))
      (c₀.nreg (sw 302)) (c₀.nreg ALLOC) c.nmem (c₀.nreg (sw 201)) (2 * k + s))
    (hroom : c.nreg ALLOC + kTb κL (c₀.nreg TLR) ≤ W) :
    IRS P W c₀ (tbHit lsS) c (kTb κL (c₀.nreg TLR)) (fun c' =>
      (∀ r, PReg r → c'.nreg r = c.nreg r) ∧ c.nreg ALLOC ≤ c'.nreg ALLOC ∧
      SInv P J N₂ (c₀.nreg (sw 200)) (c₀.nreg (sw 300)) (c₀.nreg (sw 301))
        (c₀.nreg (sw 302)) (c₀.nreg ALLOC) c'.nmem (c₀.nreg (sw 201)) (2 * k + s + 1)) := by
  set AS := c₀.nreg (sw 200) with hASd
  set S := c₀.nreg (sw 201) with hSd
  set AL := c₀.nreg (sw 300) with hALd
  set E := c₀.nreg (sw 301) with hEd
  set AT := c₀.nreg (sw 302) with hATd
  set B := c₀.nreg ALLOC with hBd
  set j := 2 * k + s with hjd
  have hK : Consts c := e.hA.hK.fix hI
  have hst := e.hA.hstops
  have hlog := e.hA.hlog
  have htw := e.hA.htabw
  simp only [rd_sw] at hst hlog htw
  have hAc := hI.hA
  have hWc := hI.hw.1 ALLOC
  have mc : ∀ (d : Config), IInv W c₀ d → ∀ a, a < B → d.nmem a = c.nmem a :=
    fun d hd a ha => (hd.hm a ha).trans (hI.hm a ha).symm
  have hj : j < 2 * N₂.nChords := by omega
  have od := e.odc (m := c.nmem) hI.hm
  simp only [rd_sw] at od
  obtain ⟨-, hpw⟩ := od.tw j hj
  have pw := hpw hf
  unfold tbHit
  -- the chord and the end
  have hb1 := IRS.block (P := P) [.copyN oK ipJ, .copyN oS ipS] hI (by
    simp [okB, okI, oK, oS, sw, IScr])
  refine IRS.seq (K₁ := 2) (K₂ := kTb κL (c₀.nreg TLR) - 2) hb1 ?_ |>.mono
    (by unfold kTb; omega) (fun _ h => h)
  rintro c₁ hI₁ hA₁ hA₁' rfl
  set c₁ : Config := { c with nreg := regB c.nmem [.copyN oK ipJ, .copyN oS ipS] c.nreg }
    with hc₁
  have v1 : ∀ r, r ≠ oK → r ≠ oS → c₁.nreg r = c.nreg r := fun r h1 h2 => by
    simp only [hc₁, regB, regI]; rw [upd_other _ _ _ h2, upd_other _ _ _ h1]
  have vK : c₁.nreg oK = k := by
    simp only [hc₁, regB, regI]; rw [upd_other _ _ _ (by unfold oK oS sw; omega), upd_same, hk]
  have vS : c₁.nreg oS = s := by
    simp only [hc₁, regB, regI]; rw [upd_same, upd_other _ _ _ (by unfold oK ipS sw; omega), hs]
  refine IRS.seq (K₁ := 11100) (K₂ := kTb κL (c₀.nreg TLR) - 2 - 11100)
    (orgHead_irs hI₁ e.hA.hK (e.hA.ctxR hI₁) e.hA.hNF₂ (e.nw hI₁) le_rfl
      (by rw [vK]; exact hkK) (by rw [vS]; exact hs1) (by unfold kTb at hroom; omega)) ?_ |>.mono
    (by unfold kTb; omega) (fun _ h => h)
  rintro c₂ hI₂ hA₂ hA₂' ⟨-, -, -, -, vE, vC, -, -, fr₂, hAl₂, hm₂⟩
  rw [vK, vS] at vE vC
  have k21 : ∀ r, bandOf r ∉ oracleBands → (r < sw 2200 ∨ sw 2217 < r) → r ≠ ALLOC →
      c₂.nreg r = c.nreg r := fun r h1 h2 h3 =>
    (fr₂ r h1 (by unfold sw at *; omega) h3).trans
      (v1 r (by unfold oK sw at *; omega) (by unfold oS sw at *; omega))
  have mem2 : ∀ a, a < c.nreg ALLOC → c₂.nmem a = c.nmem a := fun a ha => hm₂ a ha
  -- the class test
  have hK₂ : Consts c₂ := e.hA.hK.fix hI₂
  refine IRS.seq (K₁ := 19) (K₂ := kTb κL (c₀.nreg TLR) - 2 - 11100 - 19) (cls_irs hI₂ hK₂) ?_
    |>.mono (by unfold kTb; omega) (fun _ h => h)
  rintro c₃ hI₃ hA₃ hA₃' ⟨vV, vV1, fr₃, hm₃⟩
  have e5 : c₂.nreg ipM5 = 2 * J.right.m + 5 :=
    (k21 _ (not_oracle_sw (by unfold ipM5 sw; omega) (by unfold ipM5 sw; omega))
      (by unfold ipM5 sw; omega) (by unfold ipM5 ALLOC sw; omega)).trans hM5
  have e6 : c₂.nreg ipM6 = 6 + midT J.right :=
    (k21 _ (not_oracle_sw (by unfold ipM6 sw; omega) (by unfold ipM6 sw; omega))
      (by unfold ipM6 sw; omega) (by unfold ipM6 ALLOC sw; omega)).trans hM6
  have e41 : c₂.nreg (sw 41) = cstR J 1 := (e.fix hI₂ (k := 41) (by norm_num)).trans e.st0.2.1
  rw [e5, e6, e41, vE, vC, ← valid_test e.hA.hP e.hA.hNF₂ hkK hs1] at vV
  have k3 : ∀ r, bandOf r ∉ oracleBands → (r < sw 2200 ∨ sw 2217 < r) → r ≠ ALLOC → r ≠ ipV →
      c₃.nreg r = c.nreg r := fun r h1 h2 h3 h4 => (fr₃ r h4).trans (k21 r h1 h2 h3)
  have mem3 : ∀ a, a < c.nreg ALLOC → c₃.nmem a = c.nmem a := fun a ha => by
    rw [hm₃]; exact mem2 a ha
  have hp3 : ∀ r, PReg r → c₃.nreg r = c.nreg r := fun r hr => by
    apply k3 r
    · rcases hr with rfl | rfl | rfl | rfl | rfl <;>
        exact not_oracle_sw (by simp [ipB, ipM6, ipM5, ipJ, ipKc, sw])
          (by simp [ipB, ipM6, ipM5, ipJ, ipKc, sw])
    · rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [ipB, ipM6, ipM5, ipJ, ipKc, sw]
    · rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [ipB, ipM6, ipM5, ipJ, ipKc, ALLOC, sw]
    · rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [ipB, ipM6, ipM5, ipJ, ipKc, ipV, sw]
  have hK₃ : Consts c₃ := e.hA.hK.fix hI₃
  by_cases hv : c₃.nreg ipV < c₃.nreg K1
  · -- not regular
    have hv0 : ¬ ValidO J (Qof P) N₂ j := by
      intro h; have := vV.2 h; rw [this, hK₃.2.1] at hv; omega
    refine (IRS.ifT (K := 0) hv (IRS.skip hI₃ (Q := fun c' =>
      (∀ r, PReg r → c'.nreg r = c.nreg r) ∧ c.nreg ALLOC ≤ c'.nreg ALLOC ∧
      SInv P J N₂ AS AL E AT B c'.nmem S (j + 1)) ⟨hp3, by omega, ?_⟩)).mono
      (by unfold kTb; omega) (fun _ h => h)
    exact (hS.congr (fun a ha => mem3 a (by omega)) (by omega) (by omega) (by omega)).tabSkip
      (fun h => hv0 h.1)
  -- regular
  have hvo : ValidO J (Qof P) N₂ j := vV.1 (by rw [hK₃.2.1] at hv; omega)
  refine IRS.ifF (K := kTb κL (c₀.nreg TLR) - 2 - 11100 - 19 - 2) hv ?_ |>.mono
    (by unfold kTb; omega) (fun _ h => h)
  have a3 : c₃.nreg ipA = AT + 3 * j := (k3 _ (not_oracle_sw (by unfold ipA sw; omega)
    (by unfold ipA sw; omega)) (by unfold ipA sw; omega) (by unfold ipA ALLOC sw; omega)
    (by unfold ipA ipV sw; omega)).trans ha
  refine IRS.seq (K₁ := 6) (K₂ := kTb κL (c₀.nreg TLR) - 2 - 11100 - 19 - 2 - 6)
    (tbTg_irs hI₃ hK₃ a3 (by omega)) ?_ |>.mono (by unfold kTb; omega) (fun _ h => h)
  rintro c₄ hI₄ hA₄ hA₄' ⟨g1, g2, g3, g4, gfr, gm⟩
  have q1 : c₄.nreg lsxE = c.nmem (AT + 3 * j + 1) := by rw [g3, mem3 _ (by omega)]
  have q2 : c₄.nreg lsxH = c.nmem (AT + 3 * j + 2) := by rw [g4, mem3 _ (by omega)]
  refine IRS.seq (K₁ := κL * (c₀.nreg TLR + 1)) (K₂ := 12)
    (e.search hls hI₄ (by rw [q1, q2]; exact pw) (by unfold kTb at hroom; omega)) ?_ |>.mono
    (by unfold kTb; omega) (fun _ h => h)
  rintro c₅ hI₅ hA₅ hA₅' ⟨s1, s2, sfr, sA, sm⟩
  have hq : (⟨c₄.nreg lsxE, c₄.nreg lsxH⟩ : WPos) =
      ⟨c₄.nmem (AT + 3 * (2 * k + s) + 1), c₄.nmem (AT + 3 * (2 * k + s) + 2)⟩ := by
    rw [q1, q2, mc c₄ hI₄ _ (by omega), mc c₄ hI₄ (AT + 3 * (2 * k + s) + 2) (by omega)]
  rw [hq] at s1 s2
  have od₄ := e.odc (m := c₄.nmem) hI₄.hm
  simp only [rd_sw] at od₄
  have hf₄ : c₄.nmem (AT + 3 * (2 * k + s)) = 1 := by rw [mc c₄ hI₄ _ (by omega)]; exact hf
  obtain ⟨ht, e1, e2, hvl⟩ := tab_step od₄ e.hA.hNF₂ rfl hkK hs1 hvo hf₄ s1 s2
  -- registers after the search
  have k5 : ∀ r, sw 4100 ≤ r → r ≤ sw 4129 → r ≠ ipV → r ≠ ipE → r ≠ ipH → r ≠ ipA →
      c₅.nreg r = c.nreg r := by
    intro r h1 h2 n1 n2 n3 n4
    rw [sfr r (not_oracle_sw (by unfold sw at *; omega) (by unfold sw at *; omega))
      (by unfold LSet sw at *; omega) (by unfold ALLOC sw at *; omega),
      gfr r n2 n3 n4 (by unfold lsxE sw at *; omega) (by unfold lsxH sw at *; omega)]
    exact k3 r (not_oracle_sw (by unfold sw at *; omega) (by unfold sw at *; omega))
      (by unfold sw at *; omega) (by unfold ALLOC sw at *; omega) n1
  have k5S : c₅.nreg ipS = s := (k5 ipS (by unfold ipS sw; omega) (by unfold ipS sw; omega)
    (by unfold ipS ipV sw; omega) (by unfold ipS ipE sw; omega) (by unfold ipS ipH sw; omega)
    (by unfold ipS ipA sw; omega)).trans hs
  have k5B : c₅.nreg ipB = B := (k5 ipB (by unfold ipB sw; omega) (by unfold ipB sw; omega)
    (by unfold ipB ipV sw; omega) (by unfold ipB ipE sw; omega) (by unfold ipB ipH sw; omega)
    (by unfold ipB ipA sw; omega)).trans hB
  have k5E : c₅.nreg ipE = c₃.nreg oE := by
    rw [sfr _ (not_oracle_sw (by unfold ipE sw; omega) (by unfold ipE sw; omega))
      (by unfold LSet ipE sw; omega) (by unfold ALLOC ipE sw; omega), g1]
  have k5H : c₅.nreg ipH = c₃.nreg oC := by
    rw [sfr _ (not_oracle_sw (by unfold ipH sw; omega) (by unfold ipH sw; omega))
      (by unfold LSet ipH sw; omega) (by unfold ALLOC ipH sw; omega), g2]
  have c3E : c₃.nreg oE = (endPos N₂ k s).edge := by
    rw [fr₃ _ (by unfold oE ipV sw; omega)]; exact vE
  have c3C : c₃.nreg oC = nhgt (chainModel J.right) (Qof P) (endPos N₂ k s) := by
    rw [fr₃ _ (by unfold oC ipV sw; omega)]; exact vC
  have hK₅ : Consts c₅ := e.hA.hK.fix hI₅
  refine (slotSt_irs hI₅ hK₅ k5B rfl k5S le_rfl (by
    have := hI₅.hw.1 ALLOC
    omega)).mono le_rfl ?_
  rintro c' ⟨w1, w2⟩
  have wA := w2 ALLOC (by unfold ALLOC ipT sw; omega)
  refine ⟨fun r hr => ?_, by omega, ?_⟩
  · have hT : r ≠ ipT := by
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [ipT, ipB, ipM6, ipM5, ipJ, ipKc, sw]
    rw [w2 r hT]
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      exact k5 _ (by simp [ipB, ipM6, ipM5, ipJ, ipKc, sw])
        (by simp [ipB, ipM6, ipM5, ipJ, ipKc, sw])
        (by simp [ipB, ipM6, ipM5, ipJ, ipKc, ipV, sw])
        (by simp [ipB, ipM6, ipM5, ipJ, ipKc, ipE, sw])
        (by simp [ipB, ipM6, ipM5, ipJ, ipKc, ipH, sw])
        (by simp [ipB, ipM6, ipM5, ipJ, ipKc, ipA, sw])
  · rw [w1]
    have m5 : ∀ a, a < B + 6 * E → c₅.nmem a = c.nmem a := fun a ha => by
      rw [sm a (by omega), gm, mem3 a (by omega)]
    have hS₅ := hS.congr m5 (by omega) (by omega) (by omega)
    have hv' : SlotVal P J ⟨c₅.nreg ipE, c₅.nreg ipH⟩ ((2 * k + s) % 2)
        (logPt P J c₄.nmem AL (c₅.nreg lsI)) := by
      rw [k5E, k5H, c3E, c3C, show (2 * k + s) % 2 = s by omega]
      exact hvl
    have h := hS₅.tabStep (m₂ := c₄.nmem) (fun a ha => (mc c₄ hI₄ a ha).trans
      (mc c₅ hI₅ a ha).symm) (by omega) (by omega) (by omega) ht e1 e2 hv'
    rw [show (2 * k + s) % 2 = s by omega] at h
    exact h

set_option maxHeartbeats 4000000 in
/-- **A table entry.** -/
theorem tbOne_irs {lsS : Stmt} {κL : ℕ} (hls : LSBody lsS κL)
    (e : IE P W X Ok J H N₁ N₂ Eb c₀ rs ls) (hI : IInv W c₀ c)
    (hB : c.nreg ipB = c₀.nreg ALLOC)
    (hAl : c₀.nreg ALLOC + 6 * c₀.nreg (sw 301) ≤ c.nreg ALLOC)
    (hM5 : c.nreg ipM5 = 2 * J.right.m + 5) (hM6 : c.nreg ipM6 = 6 + midT J.right)
    {sr k s : ℕ} (hsr : sr = K0 ∨ sr = K1) (hsv : c.nreg sr = s) (hs1 : s ≤ 1)
    (hk : c.nreg ipJ = k) (hkK : k < N₂.nChords)
    (hS : SInv P J N₂ (c₀.nreg (sw 200)) (c₀.nreg (sw 300)) (c₀.nreg (sw 301))
      (c₀.nreg (sw 302)) (c₀.nreg ALLOC) c.nmem (c₀.nreg (sw 201)) (2 * k + s))
    (hroom : c.nreg ALLOC + (kTb κL (c₀.nreg TLR) + 9) ≤ W) :
    IRS P W c₀ (tbOne lsS sr) c (kTb κL (c₀.nreg TLR) + 9) (fun c' =>
      (∀ r, PReg r → c'.nreg r = c.nreg r) ∧ c.nreg ALLOC ≤ c'.nreg ALLOC ∧
      SInv P J N₂ (c₀.nreg (sw 200)) (c₀.nreg (sw 300)) (c₀.nreg (sw 301))
        (c₀.nreg (sw 302)) (c₀.nreg ALLOC) c'.nmem (c₀.nreg (sw 201)) (2 * k + s + 1)) := by
  have htw := e.hA.htabw
  simp only [rd_sw] at htw
  have hAc := hI.hA
  have hWc := hI.hw.1 ALLOC
  have hsr' : sr < sw 4100 ∨ sw 4129 < sr := by
    rcases hsr with rfl | rfl <;> simp [K0, K1, sw]
  unfold tbOne
  refine IRS.seq (K₁ := 7) (K₂ := kTb κL (c₀.nreg TLR) + 2)
    (tbLd_irs hI hsr' (e.fix hI (k := 302) (by norm_num)) hk hsv (by omega)) ?_ |>.mono
    (by omega) (fun _ h => h)
  rintro c₁ hI₁ hA₁ hA₁' ⟨l1, l2, l3, lfr, lm⟩
  have hp1 : ∀ r, PReg r → c₁.nreg r = c.nreg r := fun r hr => by
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      exact lfr _ (by simp [ipB, ipM6, ipM5, ipJ, ipKc, ipS, sw])
        (by simp [ipB, ipM6, ipM5, ipJ, ipKc, ipA, sw])
        (by simp [ipB, ipM6, ipM5, ipJ, ipKc, ipT, sw])
        (by simp [ipB, ipM6, ipM5, ipJ, ipKc, ipF, sw])
  have hS₁ : SInv P J N₂ (c₀.nreg (sw 200)) (c₀.nreg (sw 300)) (c₀.nreg (sw 301))
      (c₀.nreg (sw 302)) (c₀.nreg ALLOC) c₁.nmem (c₀.nreg (sw 201)) (2 * k + s) := by
    rw [lm]; exact hS
  have hK₁ : Consts c₁ := e.hA.hK.fix hI₁
  by_cases hf : c₁.nreg ipF < c₁.nreg K1
  · refine (IRS.ifT (K := 0) hf (IRS.skip hI₁ (Q := fun c' =>
      (∀ r, PReg r → c'.nreg r = c.nreg r) ∧ c.nreg ALLOC ≤ c'.nreg ALLOC ∧
      SInv P J N₂ (c₀.nreg (sw 200)) (c₀.nreg (sw 300)) (c₀.nreg (sw 301))
        (c₀.nreg (sw 302)) (c₀.nreg ALLOC) c'.nmem (c₀.nreg (sw 201)) (2 * k + s + 1))
      ⟨hp1, hA₁, hS₁.tabSkip (fun h => by rw [l3, ← lm] at hf; rw [hK₁.2.1] at hf; omega)⟩)).mono
      (by omega) (fun _ h => h)
  · have od := e.odc (m := c.nmem) hI.hm
    simp only [rd_sw] at od
    have hfl := (od.tw (2 * k + s) (by omega)).1
    have hf1 : c₁.nmem (c₀.nreg (sw 302) + 3 * (2 * k + s)) = 1 := by
      rw [lm]; rw [l3, hK₁.2.1] at hf; omega
    refine IRS.ifF hf ?_
    refine (tbHit_irs hls e hI₁ ((hp1 _ (Or.inl rfl)).trans hB) (by omega)
      ((hp1 _ (Or.inr (Or.inr (Or.inl rfl)))).trans hM5) ((hp1 _ (Or.inr (Or.inl rfl))).trans hM6)
      ((hp1 _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))).trans hk) hkK l1 hs1 l2 hf1 hS₁
      (by omega)).mono le_rfl ?_
    rintro c' ⟨g1, g2, g3⟩
    exact ⟨fun r hr => (g1 r hr).trans (hp1 r hr), by omega, g3⟩

set_option maxHeartbeats 4000000 in
/-- **The two entries of a chord.** -/
theorem tbB_irs {lsS : Stmt} {κL : ℕ} (hls : LSBody lsS κL)
    (e : IE P W X Ok J H N₁ N₂ Eb c₀ rs ls) (hI : IInv W c₀ c)
    (hB : c.nreg ipB = c₀.nreg ALLOC)
    (hAl : c₀.nreg ALLOC + 6 * c₀.nreg (sw 301) ≤ c.nreg ALLOC)
    (hM5 : c.nreg ipM5 = 2 * J.right.m + 5) (hM6 : c.nreg ipM6 = 6 + midT J.right)
    (hkK : c.nreg ipJ < N₂.nChords)
    (hS : SInv P J N₂ (c₀.nreg (sw 200)) (c₀.nreg (sw 300)) (c₀.nreg (sw 301))
      (c₀.nreg (sw 302)) (c₀.nreg ALLOC) c.nmem (c₀.nreg (sw 201)) (2 * c.nreg ipJ))
    (hroom : c.nreg ALLOC + (2 * (kTb κL (c₀.nreg TLR) + 9) + 1) ≤ W) :
    IRS P W c₀ (tbB lsS) c (2 * (kTb κL (c₀.nreg TLR) + 9) + 1) (fun c' =>
      c'.nreg ipJ = c.nreg ipJ + 1 ∧ (∀ r, PReg r → r ≠ ipJ → c'.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧
      SInv P J N₂ (c₀.nreg (sw 200)) (c₀.nreg (sw 300)) (c₀.nreg (sw 301))
        (c₀.nreg (sw 302)) (c₀.nreg ALLOC) c'.nmem (c₀.nreg (sw 201)) (2 * (c.nreg ipJ + 1))) := by
  have hK : Consts c := e.hA.hK.fix hI
  unfold tbB
  refine IRS.seq (K₁ := kTb κL (c₀.nreg TLR) + 9) (K₂ := kTb κL (c₀.nreg TLR) + 9 + 1)
    (tbOne_irs hls e hI hB hAl hM5 hM6 (Or.inl rfl) hK.1 (by norm_num) rfl hkK
      (by simpa using hS) (by omega)) ?_ |>.mono (by omega) (fun _ h => h)
  rintro c₁ hI₁ hA₁ hA₁' ⟨g1, g2, g3⟩
  have hK₁ : Consts c₁ := e.hA.hK.fix hI₁
  have pJ : PReg ipJ := Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  refine IRS.seq (K₁ := kTb κL (c₀.nreg TLR) + 9) (K₂ := 1)
    (tbOne_irs hls e hI₁ ((g1 _ (Or.inl rfl)).trans hB) (by omega)
      ((g1 _ (Or.inr (Or.inr (Or.inl rfl)))).trans hM5) ((g1 _ (Or.inr (Or.inl rfl))).trans hM6)
      (Or.inr rfl) hK₁.2.1 le_rfl (g1 _ pJ) hkK g3 (by omega)) ?_
  rintro c₂ hI₂ hA₂ hA₂' ⟨h1, h2, h3⟩
  have hK₂ : Consts c₂ := e.hA.hK.fix hI₂
  have j2 : c₂.nreg ipJ = c.nreg ipJ := (h1 _ pJ).trans (g1 _ pJ)
  refine (IRS.instr1 (i := .addN ipJ ipJ K1) hI₂ ⟨iscr_sw (by unfold ipJ sw; omega)
    (by unfold ipJ sw; omega), by
      rw [j2, hK₂.2.1]; have := hI.hw.1 ALLOC; have := e.hA.htabw; have := hI.hA
      simp only [rd_sw] at *; omega⟩).mono le_rfl ?_
  rintro c' rfl
  refine ⟨?_, fun r hr hrJ => ?_, ?_, ?_⟩
  · simp only [regI, upd_same]; rw [j2, hK₂.2.1]
  · simp only [regI]
    rw [upd_other _ _ _ hrJ, h1 r hr, g1 r hr]
  · simp only [regI]
    rw [upd_other _ _ _ (by unfold ALLOC ipJ sw; omega)]; omega
  · simp only
    rw [show 2 * (c.nreg ipJ + 1) = 2 * c.nreg ipJ + 1 + 1 by ring]
    exact h3

/-- **The table loop.** -/
theorem tbLoop_irs {lsS : Stmt} {κL : ℕ} (hls : LSBody lsS κL)
    (e : IE P W X Ok J H N₁ N₂ Eb c₀ rs ls) (hI : IInv W c₀ c)
    (hB : c.nreg ipB = c₀.nreg ALLOC)
    (hAl : c₀.nreg ALLOC + 6 * c₀.nreg (sw 301) ≤ c.nreg ALLOC)
    (hM5 : c.nreg ipM5 = 2 * J.right.m + 5) (hM6 : c.nreg ipM6 = 6 + midT J.right)
    (hJ : c.nreg ipJ = 0) (hKc : c.nreg ipKc = N₂.nChords)
    (hS : SInv P J N₂ (c₀.nreg (sw 200)) (c₀.nreg (sw 300)) (c₀.nreg (sw 301))
      (c₀.nreg (sw 302)) (c₀.nreg ALLOC) c.nmem (c₀.nreg (sw 201)) 0)
    (hroom : c.nreg ALLOC + (2 * (kTb κL (c₀.nreg TLR) + 9) + 3) * N₂.nChords ≤ W) :
    IRS P W c₀ (tbLoop lsS) c ((2 * (kTb κL (c₀.nreg TLR) + 9) + 3) * N₂.nChords + 2)
      (fun c' => c.nreg ALLOC ≤ c'.nreg ALLOC ∧ c'.nreg ipB = c.nreg ipB ∧
        SInv P J N₂ (c₀.nreg (sw 200)) (c₀.nreg (sw 300)) (c₀.nreg (sw 301))
          (c₀.nreg (sw 302)) (c₀.nreg ALLOC) c'.nmem (c₀.nreg (sw 201)) (2 * N₂.nChords)) := by
  let I : Config → Prop := fun d => (∀ r, PReg r → r ≠ ipJ → d.nreg r = c.nreg r) ∧
    c.nreg ALLOC ≤ d.nreg ALLOC ∧ d.nreg ipJ ≤ N₂.nChords ∧
    SInv P J N₂ (c₀.nreg (sw 200)) (c₀.nreg (sw 300)) (c₀.nreg (sw 301))
      (c₀.nreg (sw 302)) (c₀.nreg ALLOC) d.nmem (c₀.nreg (sw 201)) (2 * d.nreg ipJ)
  have pKc : PReg ipKc := Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  have nKc : ipKc ≠ ipJ := by unfold ipKc ipJ sw; omega
  have h := IRS.while (P := P) (c₀ := c₀) (a := ipJ) (b := ipKc) (body := tbB lsS) I
    (fun d => N₂.nChords - d.nreg ipJ) (2 * (kTb κL (c₀.nreg TLR) + 9) + 1)
    (fun d hd hlt => by rw [hd.1 _ pKc nKc, hKc] at hlt; omega)
    (fun d hId hd hlt hr => by
      obtain ⟨d1, d2, d3, d4⟩ := hd
      rw [d1 _ pKc nKc, hKc] at hlt
      refine (tbB_irs hls e hId ((d1 ipB (Or.inl rfl) (by unfold ipB ipJ sw; omega)).trans hB)
        (by omega) ((d1 ipM5 (Or.inr (Or.inr (Or.inl rfl))) (by unfold ipM5 ipJ sw; omega)).trans hM5)
        ((d1 ipM6 (Or.inr (Or.inl rfl)) (by unfold ipM6 ipJ sw; omega)).trans hM6) hlt d4
        hr).mono le_rfl ?_
      rintro d' ⟨g1, g2, g3, g4⟩
      exact ⟨⟨fun r hr hrJ => (g2 r hr hrJ).trans (d1 r hr hrJ), by omega, by omega,
        by rw [g1]; exact g4⟩, by omega⟩)
    hI ⟨fun _ _ _ => rfl, le_rfl, by omega, by rw [hJ]; exact hS⟩ (by rw [hJ]; simpa using hroom)
  rw [hJ] at h
  simp only [Nat.sub_zero] at h
  refine h.mono le_rfl ?_
  rintro d ⟨⟨d1, d2, d3, d4⟩, d5⟩
  rw [d1 _ pKc nKc, hKc] at d5
  have : d.nreg ipJ = N₂.nChords := by omega
  rw [this] at d4
  exact ⟨d2, d1 _ (Or.inl rfl) (by unfold ipB ipJ sw; omega), d4⟩

end tab

end

end S0C

end SweepIo

end Chazelle.Core
