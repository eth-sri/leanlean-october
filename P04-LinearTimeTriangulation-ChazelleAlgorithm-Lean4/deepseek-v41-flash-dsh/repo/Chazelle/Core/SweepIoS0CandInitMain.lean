module

public import Chazelle.Golf

public import Chazelle.Core.SweepIoS0CandInitTab

/-!
# The sweep RAM (WP-D), answers: the slot table of the side-0 candidates (the contract)

**`SweepIo.S0C.initPart (hL : LSearchSpec) : InitPartSpec`**: the initialisation `initC`
(`SweepIoS0CandInitProg`) establishes `AuxCore` (from the slot invariant `SInv` after all stop
records and table entries, `auxCore_of_sinv`), hence `Aux` (`aux_of_core`); `Aux` survives a
write of `sw 11` (`aux_sw11`).
-/

namespace Chazelle.Core

namespace SweepIo

namespace S0C

open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep SweepEv

@[expose] public section

/-- **The slot table from the invariant.** -/
theorem auxCore_of_sinv {P : Polygon} {J : Merge.Junction} {N₂ : NF} {c : Config}
    (h1 : c.nreg sB + 6 * c.nreg (sw 301) ≤ c.nreg ALLOC)
    (h2 : c.nreg (sw 300) + 7 * c.nreg (sw 301) ≤ c.nreg ALLOC)
    (h3 : c.nreg (sw 200) + 5 * c.nreg (sw 201) ≤ c.nreg ALLOC)
    (h4 : c.nreg (sw 302) + 3 * (2 * N₂.nChords) ≤ c.nreg ALLOC)
    (hS : SInv P J N₂ (c.nreg (sw 200)) (c.nreg (sw 300)) (c.nreg (sw 301)) (c.nreg (sw 302))
      (c.nreg sB) c.nmem (c.nreg (sw 201)) (2 * N₂.nChords)) : AuxCore P J N₂ c :=
  ⟨h1, h2, h3, h4, hS.1, hS.2.1, hS.2.2⟩

/-- `midT` from the fields of the chain descriptor. -/
theorem midT_desc {C : Chain} {m : ℕ → ℕ} {B : ℕ} {Q : Polygon} {H : Host}
    (h : ChainDescAt m B Q H C) :
    (if m (B + 4) = 1 then 2 * m (B + 2) - 2 * m (B + 3)
      else if m (B + 3) < m (B + 2) then 2 * m (B + 3) else 0) = midT C := by
  obtain ⟨-, -, -, h2, h3, h4⟩ := h
  Ξ h2, h3
  unfold midT
  by_cases hb : C.sideBeta = true
  · Ξ ite_eq_left (h4.2 hb), ite_eq_left hb
  · Ξ ite_eq_right (fun h => hb (h4.1 h)), ite_eq_right hb

/-- The cost constant. -/
def kIn (κL : ℕ) : ℕ := 30000 + 2 * κL

theorem cost_le (κL S E K t : ℕ) (ht : 1 ≤ t) :
    27 + (4 * (6 * E) + 2) + ((kSt κL (t - 1) + 2) * S + 2) +
        ((2 * (kTb κL (t - 1) + 9) + 3) * K + 2) + 1 ≤
      kIn κL * (S + E + 2 * K + 1) * t := by
  obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, ⋄⟩
  ϴ Nat.add_sub_cancel
  unfold kSt kTb kIn
  nlinarith [Nat.zero_le (κL * u * S), Nat.zero_le (κL * u * K), Nat.zero_le (κL * u * E),
    Nat.zero_le (κL * u), Nat.zero_le (u * S), Nat.zero_le (u * E), Nat.zero_le (u * K),
    Nat.zero_le u, Nat.zero_le (κL * E), Nat.zero_le κL]

/-- The cost of the run part of the initialisation. -/
def kRun (κL TL S E K : ℕ) : ℕ :=
  27 + (4 * (6 * E) + 2) + ((kSt κL TL + 2) * S + 2) + ((2 * (kTb κL TL + 9) + 3) * K + 2)

section main

variable {P : Polygon} {W : ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop} {J : Merge.Junction}
  {H : Host} {N₁ N₂ : NF} {Eb : ℕ} {c : Config} {rs : List (ℕ × ℕ × ℕ × ℕ × ℕ)}
  {ls : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)}


/-- **The run part of the initialisation** (all but the final write of `sw 620`). -/
theorem body_irs {lsS : Stmt} {κL : ℕ} (hls : LSBody lsS κL)
    (e : IE P W X Ok J H N₁ N₂ Eb c rs ls) (hw : WordsBounded W c)
    (hroom : c.nreg ALLOC + kRun κL (c.nreg TLR) (c.nreg (sw 201)) (c.nreg (sw 301))
      N₂.nChords + 1 ≤ W) :
    IRS P W c (.seq hdr (.seq zeroLoop (.seq (stLoop lsS) (tbLoop lsS)))) c
      (kRun κL (c.nreg TLR) (c.nreg (sw 201)) (c.nreg (sw 301)) N₂.nChords) (fun c' =>
        c'.nreg ipB = c.nreg ALLOC ∧ c.nreg ALLOC + 6 * c.nreg (sw 301) ≤ c'.nreg ALLOC ∧
        SInv P J N₂ (c.nreg (sw 200)) (c.nreg (sw 300)) (c.nreg (sw 301)) (c.nreg (sw 302))
          (c.nreg ALLOC) c'.nmem (c.nreg (sw 201)) (2 * N₂.nChords)) := by
  have hI0 : IInv W c c := ⟨hw, fun _ _ => rfl, le_rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  have hK := e.hA.hK
  obtain ⟨-, -, -, -, -, -, -, -, d21, w21, -⟩ := e.hA.hst
  have hWc := hw.1 ALLOC
  have hd : c.nreg (sw 21) + 5 ≤ W := by have := w21.1; omega
  have f2 := d21.2.2.2.1
  have f3 := d21.2.2.2.2.1
  have hTm : c.nmem (c.nreg (sw 21) + 3) ≤ c.nmem (c.nreg (sw 21) + 2) := by
    rw [f2, f3]; exact J.right.topIdx_le
  have hWm := e.hA.hWm
  have hmm : J.right.m ≤ J.whole.m := sideChain_m_le J 1
  have h2m : 2 * c.nmem (c.nreg (sw 21) + 2) + 6 ≤ W := by rw [f2]; omega
  have hst := e.st0
  unfold kRun at hroom ⊢
  refine (IRS.seq (K₁ := 27) (K₂ := (4 * (6 * c.nreg (sw 301)) + 2) + (((kSt κL (c.nreg TLR) + 2) * c.nreg (sw 201) + 2) + ((2 * (kTb κL (c.nreg TLR) + 9) + 3) * N₂.nChords + 2)))
    (hdr_irs hI0 hK hd (⋄) hTm h2m) ?_).mono (⋄) (fun _ h => h)
  rintro c₁ hI₁ hA₁ hA₁' ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩
  have c1A : c₁.nreg ALLOC = c.nreg ALLOC := a8 _ (Or.inl (by unfold ALLOC sw; omega))
  have hK₁ : Consts c₁ := hK.fix hI₁
  refine IRS.seq (K₁ := 4 * (6 * c.nreg (sw 301)) + 2) (K₂ := ((kSt κL (c.nreg TLR) + 2) * c.nreg (sw 201) + 2) + ((2 * (kTb κL (c.nreg TLR) + 9) + 3) * N₂.nChords + 2)) ((zeroLoop_irs hI₁ hK₁ a2 (⋄)
    (⋄)).mono (⋄) (fun _ h => h)) ?_
  rintro c₂ hI₂ hA₂ hA₂' ⟨z1, z2, z3, z4⟩
  rw [c1A] at z3
  have nA : ∀ r, r = ipB ∨ r = ipX ∨ r = ipJ ∨ r = ipKc ∨ r = ipM5 ∨ r = ipM6 → r ≠ ALLOC := by
    rintro r (rfl | rfl | rfl | rfl | rfl | rfl) <;> simp [ipB, ipX, ipJ, ipKc, ipM5, ipM6, ALLOC, sw]
  have b2 : c₂.nreg ipB = c.nreg ALLOC := (z2 _ (nA _ (Or.inl rfl))).trans a1
  have hS₂ : SInv P J N₂ (c.nreg (sw 200)) (c.nreg (sw 300)) (c.nreg (sw 301))
      (c.nreg (sw 302)) (c.nreg ALLOC) c₂.nmem 0 0 :=
    SInv.zero (fun a h1 h2 => z3 a h1 (⋄))
  have hfix : ∀ k, k < 700 → c.nreg (sw k) = c.nreg (sw k) := fun _ _ => rfl
  refine IRS.seq (K₁ := (kSt κL (c.nreg TLR) + 2) * c.nreg (sw 201) + 2) (K₂ := ((2 * (kTb κL (c.nreg TLR) + 9) + 3) * N₂.nChords + 2))
    (stLoop_irs hls e hI₂ b2 (⋄) ((z2 _ (nA _ (Or.inr (Or.inl rfl)))).trans a3) hS₂
      (⋄)) ?_
  rintro c₃ hI₃ hA₃ hA₃' ⟨p1, p2, p3⟩
  have pr : ∀ r, PReg r → c₃.nreg r = c₁.nreg r := fun r hr => by
    Ξ p1 r hr
    exact z2 r (by rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      simp [ipB, ipJ, ipKc, ipM5, ipM6, ALLOC, sw])
  refine (tbLoop_irs hls e hI₃ ((pr _ (Or.inl rfl)).trans a1) (⋄)
    ((pr _ (Or.inr (Or.inr (Or.inl rfl)))).trans (by rw [a6, hst.2.2]; omega))
    ((pr _ (Or.inr (Or.inl rfl))).trans (by rw [a7, midT_desc d21]; omega))
    ((pr _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))).trans a4)
    ((pr _ (Or.inr (Or.inr (Or.inr (Or.inr rfl))))).trans (a5.trans e.hA.hK₂)) p3
    (⋄)).mono le_rfl ?_
  rintro c' ⟨t1, t2, t3⟩
  exact ⟨t2.trans ((pr _ (Or.inl rfl)).trans a1), ⋄, t3⟩


/-- **The initialisation of the side-0 stop and table candidates.** -/
theorem initPart (hL : LSearchSpec) : InitPartSpec := by
  obtain ⟨lsS, κL, hls⟩ := hL
  refine ⟨initC lsS, fun _ => kIn κL, fun P W X Ok J H N₁ N₂ Eb c hw hA hroom => ?_,
    fun P J N₂ c v h => aux_sw11 h⟩
  obtain ⟨rs, ls, od⟩ := OD.of_out hA.hout
  have e : IE P W X Ok J H N₁ N₂ Eb c rs ls := ⟨hA, od⟩
  simp only [rd_sw] at hroom ⊢
  have hcost := cost_le κL (c.nreg (sw 201)) (c.nreg (sw 301)) N₂.nChords (c.nreg TLR + 1)
    (⋄)
  simp only [Nat.add_sub_cancel] at hcost
  obtain ⟨c₁, k₁, ex₁, hk₁, hI₁, hfr₁, q1, q2, q3⟩ :=
    body_irs hls e hw (by unfold kRun; omega)
  unfold kRun at hk₁
  have ex := Exec.seq ex₁ (Exec.copyN (P := P) hI₁.hw sB ipB)
  obtain ⟨r₁, rr₁, o₁, a₁, b₁⟩ := hfr₁
  have nS : ∀ r, bandOf r ∉ sweepBands ∪ oracleBands → r ≠ sB := by
    rintro r hr rfl
    exact hr (by rw [band_sw (by unfold sB sw; omega) (by unfold sB sw; omega)]; exact bSweep_mem)
  have hsA : ALLOC ≠ sB := by unfold ALLOC sB sw; omega
  refine ⟨_, k₁ + 1, ex, ⋄, ?_, fun j hj hj' => ?_, ?_⟩
  · refine ⟨fun r hr hra => ?_, fun r hr => rr₁ r hr, fun a ha => hI₁.hm a ha,
      fun a ha => hI₁.hrm a ha, o₁, ?_, ?_⟩
    · simp only
      Ξ upd_other _ _ _ (nS r hr)
      exact r₁ r hr hra
    · simp only; rw [upd_other _ _ _ hsA]; exact a₁
    · simp only; rw [upd_other _ _ _ hsA]; omega
  · simp only
    Ξ upd_other _ _ _ (by unfold sB sw; omega)
    exact hI₁.hin _ (by unfold IFix sw; omega)
  · apply aux_of_core
    have fx : ∀ k, k < 700 → k ≠ 620 →
        (upd c₁.nreg sB (c₁.nreg ipB)) (sw k) = c.nreg (sw k) := fun k hk h620 => by
      Ξ upd_other _ _ _ (by unfold sB sw; omega)
      exact hI₁.hin _ (by unfold IFix sw; omega)
    have hB : (upd c₁.nreg sB (c₁.nreg ipB)) sB = c.nreg ALLOC := Ρ upd_same, q1
    have hAl : (upd c₁.nreg sB (c₁.nreg ipB)) ALLOC = c₁.nreg ALLOC := upd_other _ _ _ hsA
    have hlog := hA.hlog
    have hst := hA.hstops
    have htw := hA.htabw
    simp only [rd_sw] at hlog hst htw
    refine auxCore_of_sinv ?_ ?_ ?_ ?_ ?_
    · simp only
      rw [hB, hAl, fx 301 (⊛) (⊛)]; exact q2
    · simp only
      rw [hAl, fx 300 (⊛) (⊛), fx 301 (⊛) (⊛)]; omega
    · simp only
      rw [hAl, fx 200 (⊛) (⊛), fx 201 (⊛) (⊛)]; omega
    · simp only
      rw [hAl, fx 302 (⊛) (⊛)]; omega
    · simp only
      rw [hB, fx 200 (⊛) (⊛), fx 201 (⊛) (⊛),
        fx 300 (⊛) (⊛), fx 301 (⊛) (⊛),
        fx 302 (⊛) (⊛)]
      exact q3

end main

end

end S0C

end SweepIo

end Chazelle.Core
