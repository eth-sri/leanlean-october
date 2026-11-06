module

public import Chazelle.Core.SweepIoS0CandInitEnv

/-!
# The sweep RAM (WP-D), answers: the slot table of the side-0 candidates (the stop loop)

`stB_irs`: one stop record (its origin, the search of its key, the write of its slot) extends the
slot invariant `SInv` by one record; `stLoop_irs`: all stop records.
-/

namespace Chazelle.Core

namespace SweepIo

namespace S0C

open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep SweepEv

@[expose] public section

/-- The cost of one stop record. -/
def kSt (κL TL : ℕ) : ℕ := 11137 + κL * (TL + 1)

theorem sOf_eq {b : ℕ} (hb : b ≤ 1) : 1 - b = sOf b := by unfold sOf; split_ifs <;> omega

/-- A run step also gives the invariant at its end. -/
theorem IRS.withInv {P : Polygon} {W : ℕ} {c₀ c : Config} {s : Stmt} {K : ℕ}
    {Q : Config → Prop} (h : IRS P W c₀ s c K Q) :
    IRS P W c₀ s c K (fun c' => Q c' ∧ IInv W c₀ c') := by
  obtain ⟨c', k, ex, hk, hI, hfr, hq⟩ := h
  exact ⟨c', k, ex, hk, hI, hfr, hq, hI⟩

/-- The persistent registers of the loops. -/
def PReg (r : ℕ) : Prop := r = ipB ∨ r = ipM6 ∨ r = ipM5 ∨ r = ipJ ∨ r = ipKc

section stop

variable {P : Polygon} {W : ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop} {J : Merge.Junction}
  {H : Host} {N₁ N₂ : NF} {Eb : ℕ} {c₀ c : Config} {rs : List (ℕ × ℕ × ℕ × ℕ × ℕ)}
  {ls : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)}

set_option maxHeartbeats 8000000 in
/-- **One stop record.** -/
theorem stB_irs {lsS : Stmt} {κL : ℕ} (hls : LSBody lsS κL)
    (e : IE P W X Ok J H N₁ N₂ Eb c₀ rs ls) (hI : IInv W c₀ c)
    (hB : c.nreg ipB = c₀.nreg ALLOC)
    (hAl : c₀.nreg ALLOC + 6 * c₀.nreg (sw 301) ≤ c.nreg ALLOC)
    (hx : c.nreg ipX < c₀.nreg (sw 201))
    (hS : SInv P J N₂ (c₀.nreg (sw 200)) (c₀.nreg (sw 300)) (c₀.nreg (sw 301))
      (c₀.nreg (sw 302)) (c₀.nreg ALLOC) c.nmem (c.nreg ipX) 0)
    (hroom : c.nreg ALLOC + kSt κL (c₀.nreg TLR) ≤ W) :
    IRS P W c₀ (stB lsS) c (kSt κL (c₀.nreg TLR)) (fun c' =>
      c'.nreg ipX = c.nreg ipX + 1 ∧ (∀ r, PReg r → c'.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧
      SInv P J N₂ (c₀.nreg (sw 200)) (c₀.nreg (sw 300)) (c₀.nreg (sw 301))
        (c₀.nreg (sw 302)) (c₀.nreg ALLOC) c'.nmem (c.nreg ipX + 1) 0) := by
  set AS := c₀.nreg (sw 200)
  set S := c₀.nreg (sw 201)
  set AL := c₀.nreg (sw 300)
  set E := c₀.nreg (sw 301)
  set AT := c₀.nreg (sw 302)
  set B := c₀.nreg ALLOC
  set x := c.nreg ipX
  have hK : Consts c := e.hA.hK.fix hI
  have hst := e.hA.hstops
  have hlog := e.hA.hlog
  have htw := e.hA.htabw
  simp only [rd_sw] at hst hlog htw
  have od := e.odc (m := c.nmem) hI.hm
  simp only [rd_sw] at od
  obtain ⟨pw, hkind, hb1, hkk⟩ := od.stopR hx
  have mc : ∀ (d : Config), IInv W c₀ d → ∀ a, a < B → d.nmem a = c.nmem a :=
    fun d hd a ha => (hd.hm a ha).trans (hI.hm a ha).symm
  unfold stB
  -- read the record
  refine IRS.seq (K₁ := 14) (K₂ := kSt κL (c₀.nreg TLR) - 14)
    (stLd_irs hI hK (e.fix hI (k := 200) (by norm_num)) rfl (by omega)) ?_ |>.mono
    (by unfold kSt; omega) (fun _ h => h)
  rintro c₁ hI₁ hA₁ hA₁' ⟨l1, l2, l3, l4, l5, lfr, lm⟩
  -- the origin
  refine IRS.seq (K₁ := 11110) (K₂ := kSt κL (c₀.nreg TLR) - 14 - 11110)
    (stOrg_irs e hI₁ l3 l4 (by rw [l5]; exact sOf_eq hb1) hkind hkk
      (by unfold kSt at hroom; omega)) ?_ |>.mono (by unfold kSt; omega) (fun _ h => h)
  rintro c₂ hI₂ hA₂ hA₂' ⟨o1, o2, ofr, oA, om⟩
  have k21 : ∀ r, bandOf r ∉ oracleBands → sw 2217 < r → r ≠ ipE → r ≠ ipH → r ≠ ALLOC →
      c₂.nreg r = c₁.nreg r := fun r h1 h2 h3 h4 h5 => ofr r h1 (Or.inr h2) h3 h4 h5
  have q1 : c₂.nreg lsxE = c.nmem (AS + 5 * x) :=
    (k21 _ (not_oracle_sw (by unfold lsxE sw; omega) (by unfold lsxE sw; omega))
      (by unfold lsxE sw; omega) (by unfold lsxE ipE sw; omega) (by unfold lsxE ipH sw; omega)
      (by unfold lsxE ALLOC sw; omega)).trans l1
  have q2 : c₂.nreg lsxH = c.nmem (AS + 5 * x + 1) :=
    (k21 _ (not_oracle_sw (by unfold lsxH sw; omega) (by unfold lsxH sw; omega))
      (by unfold lsxH sw; omega) (by unfold lsxH ipE sw; omega) (by unfold lsxH ipH sw; omega)
      (by unfold lsxH ALLOC sw; omega)).trans l2
  -- the search
  refine IRS.seq (K₁ := κL * (c₀.nreg TLR + 1)) (K₂ := 13)
    (e.search hls hI₂ (by rwa [q1, q2]) (by unfold kSt at hroom; omega)) ?_ |>.mono
    (by unfold kSt; omega) (fun _ h => h)
  rintro c₃ hI₃ hA₃ hA₃' ⟨s1, s2, sfr, sA, sm⟩
  have hq : (⟨c₂.nreg lsxE, c₂.nreg lsxH⟩ : WPos) =
      ⟨c₂.nmem (AS + 5 * x), c₂.nmem (AS + 5 * x + 1)⟩ := by
    rw [q1, q2, mc c₂ hI₂ _ (by omega), mc c₂ hI₂ (AS + 5 * x + 1) (by omega)]
  rw [hq] at s1 s2
  have od₂ := e.odc (m := c₂.nmem) hI₂.hm
  simp only [rd_sw] at od₂
  obtain ⟨ht, e1, e2, hv⟩ := stop_step od₂ e.hA.hP e.hA.hNF₂ rfl hx s1 s2
  rw [mc c₂ hI₂ (AS + 5 * x + 2) (by omega), mc c₂ hI₂ (AS + 5 * x + 3) (by omega),
    mc c₂ hI₂ (AS + 5 * x + 4) (by omega)] at hv
  -- registers after the search
  have keep : ∀ r, 244100 ≤ r → r ≤ 244129 → r ≠ ipA → r ≠ ipK → r ≠ ipKk → r ≠ ipBb →
      r ≠ ipS → r ≠ ipE → r ≠ ipH → c₃.nreg r = c.nreg r := by
    intro r h1 h2 n1 n2 n3 n4 n5 n6 n7
    rw [sfr r (not_oracle_sw (by omega) (by omega)) (by unfold LSet sw; omega)
      (by unfold ALLOC; omega), k21 r (not_oracle_sw (by omega) (by omega)) (by unfold sw; omega)
      n6 n7 (by unfold ALLOC; omega)]
    exact lfr r (by unfold lsxE; unfold sw; omega) (by unfold lsxH; unfold sw; omega) n1 n2 n3 n4 n5
  have k3S : c₃.nreg ipS = sOf (c.nmem (AS + 5 * x + 4)) := by
    rw [sfr _ (not_oracle_sw (by unfold ipS sw; omega) (by unfold ipS sw; omega))
      (by unfold LSet ipS sw; omega) (by unfold ALLOC ipS sw; omega),
      k21 _ (not_oracle_sw (by unfold ipS sw; omega) (by unfold ipS sw; omega))
      (by unfold ipS sw; omega) (by unfold ipS ipE sw; omega) (by unfold ipS ipH sw; omega)
      (by unfold ALLOC ipS sw; omega), l5, sOf_eq hb1]
  have k3E : c₃.nreg ipE = c₂.nreg ipE := sfr _ (not_oracle_sw (by unfold ipE sw; omega)
    (by unfold ipE sw; omega)) (by unfold LSet ipE sw; omega) (by unfold ALLOC ipE sw; omega)
  have k3H : c₃.nreg ipH = c₂.nreg ipH := sfr _ (not_oracle_sw (by unfold ipH sw; omega)
    (by unfold ipH sw; omega)) (by unfold LSet ipH sw; omega) (by unfold ALLOC ipH sw; omega)
  have k3B : c₃.nreg ipB = B := (keep ipB (by unfold ipB sw; omega) (by unfold ipB sw; omega)
    (by unfold ipB ipA sw; omega) (by unfold ipB ipK sw; omega) (by unfold ipB ipKk sw; omega)
    (by unfold ipB ipBb sw; omega) (by unfold ipB ipS sw; omega) (by unfold ipB ipE sw; omega)
    (by unfold ipB ipH sw; omega)).trans hB
  have hK₃ : Consts c₃ := e.hA.hK.fix hI₃
  -- the slot
  refine IRS.seq (K₁ := 12) (K₂ := 1) (slotSt_irs hI₃ hK₃ k3B rfl k3S le_rfl (by
    have := hI₃.hw.1 ALLOC
    have : c₀.nreg (sw 301) = E := rfl
    have hs1 := ini_sOf_le (c.nmem (AS + 5 * x + 4))
    omega)) ?_
  rintro c₄ hI₄ hA₄ hA₄' ⟨w1, w2⟩
  have k1 : c₄.nreg K1 = 1 := (e.hA.hK.fix hI₄).2.1
  have k4X : c₄.nreg ipX = x := by
    rw [w2 _ (by unfold ipX ipT sw; omega)]
    exact keep ipX (by unfold ipX sw; omega) (by unfold ipX sw; omega)
      (by unfold ipX ipA sw; omega) (by unfold ipX ipK sw; omega) (by unfold ipX ipKk sw; omega)
      (by unfold ipX ipBb sw; omega) (by unfold ipX ipS sw; omega) (by unfold ipX ipE sw; omega)
      (by unfold ipX ipH sw; omega)
  refine (IRS.instr1 (i := .addN ipX ipX K1) hI₄ ⟨iscr_sw (by unfold ipX sw; omega)
    (by unfold ipX sw; omega), by rw [k4X, k1]; have := hI₄.hw.1 ALLOC; omega⟩).mono le_rfl ?_
  rintro c' rfl
  refine ⟨?_, fun r hr => ?_, ?_, ?_⟩
  · simp only [regI, upd_same]; rw [k4X, k1]
  · have hx' : r ≠ ipX := by
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [ipX, ipB, ipM6, ipM5, ipJ, ipKc, sw]
    have hT : r ≠ ipT := by
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [ipT, ipB, ipM6, ipM5, ipJ, ipKc, sw]
    simp only [regI]
    rw [upd_other _ _ _ hx', w2 r hT]
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      exact keep _ (by simp [ipB, ipM6, ipM5, ipJ, ipKc, sw])
        (by simp [ipB, ipM6, ipM5, ipJ, ipKc, sw])
        (by simp [ipB, ipM6, ipM5, ipJ, ipKc, ipA, sw])
        (by simp [ipB, ipM6, ipM5, ipJ, ipKc, ipK, sw])
        (by simp [ipB, ipM6, ipM5, ipJ, ipKc, ipKk, sw])
        (by simp [ipB, ipM6, ipM5, ipJ, ipKc, ipBb, sw])
        (by simp [ipB, ipM6, ipM5, ipJ, ipKc, ipS, sw])
        (by simp [ipB, ipM6, ipM5, ipJ, ipKc, ipE, sw])
        (by simp [ipB, ipM6, ipM5, ipJ, ipKc, ipH, sw])
  · simp only [regI]
    rw [upd_other _ _ _ (by unfold ALLOC ipX sw; omega)]
    omega
  · simp only
    rw [w1]
    -- the invariant at the memory before the write
    have m3 : ∀ a, a < B + 6 * E → c₃.nmem a = c.nmem a := fun a ha => by
      rw [sm a (by omega), om a (by omega), lm]
    have hS₃ := hS.congr m3 (by omega) (by omega) (by omega)
    have hv' : SlotVal P J ⟨c₃.nreg ipE, c₃.nreg ipH⟩ (sOf (c₂.nmem (AS + 5 * x + 4)))
        (logPt P J c₂.nmem AL (c₃.nreg lsI)) := by
      rwa [k3E, k3H, o1, o2, mc c₂ hI₂ (AS + 5 * x + 4) (by omega)]
    have r4 : c₃.nmem (AS + 5 * x + 4) = c.nmem (AS + 5 * x + 4) := mc c₃ hI₃ _ (by omega)
    have h := hS₃.stopStep (m₂ := c₂.nmem) (fun a ha => (mc c₂ hI₂ a ha).trans
      (mc c₃ hI₃ a ha).symm) (by omega) (by omega) (by omega) ht e1 e2 hv'
    rwa [r4] at h

/-- **The stop loop.** -/
theorem stLoop_irs {lsS : Stmt} {κL : ℕ} (hls : LSBody lsS κL)
    (e : IE P W X Ok J H N₁ N₂ Eb c₀ rs ls) (hI : IInv W c₀ c)
    (hB : c.nreg ipB = c₀.nreg ALLOC)
    (hAl : c₀.nreg ALLOC + 6 * c₀.nreg (sw 301) ≤ c.nreg ALLOC) (hx : c.nreg ipX = 0)
    (hS : SInv P J N₂ (c₀.nreg (sw 200)) (c₀.nreg (sw 300)) (c₀.nreg (sw 301))
      (c₀.nreg (sw 302)) (c₀.nreg ALLOC) c.nmem 0 0)
    (hroom : c.nreg ALLOC + (kSt κL (c₀.nreg TLR) + 2) * c₀.nreg (sw 201) ≤ W) :
    IRS P W c₀ (stLoop lsS) c ((kSt κL (c₀.nreg TLR) + 2) * c₀.nreg (sw 201) + 2) (fun c' =>
      (∀ r, PReg r → c'.nreg r = c.nreg r) ∧ c.nreg ALLOC ≤ c'.nreg ALLOC ∧
      SInv P J N₂ (c₀.nreg (sw 200)) (c₀.nreg (sw 300)) (c₀.nreg (sw 301))
        (c₀.nreg (sw 302)) (c₀.nreg ALLOC) c'.nmem (c₀.nreg (sw 201)) 0) := by
  have f201 : ∀ d : Config, IInv W c₀ d → d.nreg (sw 201) = c₀.nreg (sw 201) :=
    fun d hd => e.fix hd (k := 201) (by norm_num)
  let I : Config → Prop := fun d => (∀ r, PReg r → d.nreg r = c.nreg r) ∧
    c.nreg ALLOC ≤ d.nreg ALLOC ∧ d.nreg ipX ≤ c₀.nreg (sw 201) ∧
    SInv P J N₂ (c₀.nreg (sw 200)) (c₀.nreg (sw 300)) (c₀.nreg (sw 301))
      (c₀.nreg (sw 302)) (c₀.nreg ALLOC) d.nmem (d.nreg ipX) 0 ∧ d.nreg (sw 201) = c₀.nreg (sw 201)
  have hpB : PReg ipB := Or.inl rfl
  have h := IRS.while (P := P) (c₀ := c₀) (a := ipX) (b := sw 201) (body := stB lsS) I
    (fun d => c₀.nreg (sw 201) - d.nreg ipX) (kSt κL (c₀.nreg TLR))
    (fun d hd hlt => by rw [hd.2.2.2.2] at hlt; omega)
    (fun d hId hd hlt hr => by
      obtain ⟨d1, d2, d3, d4, -⟩ := hd
      rw [f201 d hId] at hlt
      refine (IRS.withInv (stB_irs hls e hId ((d1 ipB hpB).trans hB) (by omega) hlt d4 hr)).mono le_rfl ?_
      rintro d' ⟨⟨g1, g2, g3, g4⟩, hId'⟩
      refine ⟨⟨fun r hr => (g2 r hr).trans (d1 r hr), by omega, by omega, by rwa [g1],
        f201 d' hId'⟩, by omega⟩)
    hI ⟨fun _ _ => rfl, le_rfl, by omega, by rwa [hx], f201 c hI⟩ (by rw [hx]; simpa using hroom)
  rw [hx] at h
  simp only [Nat.sub_zero] at h
  refine h.mono le_rfl ?_
  rintro d ⟨⟨d1, d2, d3, d4, d6⟩, d5⟩
  rw [d6] at d5
  have : d.nreg ipX = c₀.nreg (sw 201) := by omega
  rw [this] at d4
  exact ⟨d1, d2, d4⟩

end stop

end

end S0C

end SweepIo

end Chazelle.Core
