module

public import Chazelle.Golf

public import Chazelle.Core.DownPhaseDrvRSplH

/-!
# Down-phase driver (RAM side): the splice meets its specification

**`splice_meets`** (`DownPhaseDrvRSplF` for the statement): stages A (`splA_exec`), B1
(`splB1_exec`), B2 (`splB2_exec`) and the tail (`splT_exec`).
-/

namespace Chazelle.Core

namespace DrvR

open Machine Machine.Stmt Programs SortL BuildRam SignK
open BuildNF (codeLe)

@[expose] public section

/-- The registers of `bDownDrv` the splice keeps. -/
theorem spl_keep {r : ℕ}
    (hr : 210000 ≤ r ∧ r < 210002 ∨ 210006 ≤ r ∧ r < 210025 ∨ 210074 ≤ r ∧ r < 220000) :
    bandOf r ∉ ({bSort, bSign, bBuild} : Finset ℕ) ∧ Bs56 r = false ∧ Bcp r = false ∧
      (r < 210002 ∨ 210005 < r) ∧ r ≠ 210068 ∧ r ≠ 210069 ∧ r ≠ ALLOC ∧
      (r < 210034 ∨ 210059 < r) ∧ (r < 210031 ∨ 210033 < r) ∧ BsA r = false ∧
      210000 ≤ r ∧ r < 220000 := by
  refine ⟨band21_notin (⋄) (⋄), ?_, ?_, ⋄, ⋄, ⋄,
    by unfold ALLOC; omega, ⋄, ⋄, ?_, ⋄, ⋄⟩
  · simp only [Bs56, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
  · simp only [Bcp, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
  · simp only [BsA, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega

/-- The registers outside the bands of the splice. -/
theorem spl_out {r : ℕ} (hr : bandOf r ∉ ({bDownDrv, bBuild, bSort, bSign} : Finset ℕ)) :
    bandOf r ∉ ({bSort, bSign, bBuild} : Finset ℕ) ∧ (r ≠ ALLOC → Bs56 r = false) ∧
      Bcp r = false ∧ (r < 210002 ∨ 210005 < r) ∧ r ≠ 210068 ∧ r ≠ 210069 ∧
      (r < 210034 ∨ 210059 < r) ∧ (r < 210031 ∨ 210033 < r) ∧ (r ≠ ALLOC → BsA r = false) := by
  have hb : ¬ (r / 10000 = 21 ∨ r / 10000 = 4 ∨ r / 10000 = 3 ∨ r / 10000 = 1) := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, bandOf, bDownDrv, bBuild, bSort,
      bSign] using hr
  refine ⟨?_, fun hra => ?_, ?_, ⋄, ⋄, ⋄, ⋄, ⋄, fun hra => ?_⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton, bandOf, bSort, bSign, bBuild]; omega
  · have h9 : r ≠ 9999 := hra
    simp only [Bs56, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
  · simp only [Bcp, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
  · have h9 : r ≠ 9999 := hra
    simp only [BsA, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega

section exec

variable {P : Polygon} {W : ℕ}

set_option maxHeartbeats 4000000 in
/-- **The splice.** -/
theorem splice_meets {sB : Stmt} {κB : ℕ} (hB : SortedMeets sB κB) :
    Meets (splS sB) {bDownDrv, bBuild, bSort, bSign} SplPre SplPost (fun _ c => splCost κB c) := by
  intro P W c hw hpre hroom
  obtain ⟨hG, hWn, hwf, M, L, L₂, E, hM, hgood, hK, hB0, hCL, hK₂, hB₂, hCL₂, hok, hSEb, hSE,
    hperm, hsort, hBBb, hbk, hmono, hMb⟩ := hpre
  ϴ' rd, bandReg, bDownDrv, Nat.reduceMul, Nat.reduceAdd at hK hB0 hCL hK₂ hB₂ hCL₂ hSEb hSE hBBb hbk hmono hMb hM hwf
  set K := L.length with hKd
  set K₂ := L₂.length with hK₂d
  set A := c.nreg 210023 with hAd
  set Mb := c.nreg 210024 with hMbd
  set A₀ := c.nreg ALLOC with hA₀
  set BB := c.nreg 210022 with hBBd
  set bk : ℕ → ℕ := fun q => c.nmem (BB + q) with hbkd
  have hcost : splCost κB c = κSpl κB * (K + K₂ + A + 1) * (Nat.clog 2 Mb + 1) := by
    unfold splCost; simp only [rd, bandReg, bDownDrv, Nat.reduceMul, Nat.reduceAdd]; Ξ hK, hK₂
  have hroom' : A₀ + κSpl κB * (K + K₂ + A + 1) * (Nat.clog 2 Mb + 1) ≤ W := by
    rw [← hcost]; exact hroom
  have hcl : 1 ≤ Nat.clog 2 Mb + 1 := ⋄
  have hbase : K + K₂ + A + 1 ≤ (K + K₂ + A + 1) * (Nat.clog 2 Mb + 1) :=
    Nat.le_mul_of_pos_right _ (⋄)
  have hB2c := splB2Cost_le (bk := bk) (n := 2 * K₂) (A := A) (Mb := Mb) (fun q hq => hbk q hq)
    (fun b => hMb b)
  have hκ : κSpl κB * (K + K₂ + A + 1) * (Nat.clog 2 Mb + 1) =
      120000 * ((K + K₂ + A + 1) * (Nat.clog 2 Mb + 1)) +
        κB * ((K + K₂ + A + 1) * (Nat.clog 2 Mb + 1)) := by unfold κSpl; ring
  have hB2c' : 11200 * (2 * K₂ + A + 1) * (Nat.clog 2 Mb + 1) ≤
      22400 * ((K + K₂ + A + 1) * (Nat.clog 2 Mb + 1)) := by
    have : 2 * K₂ + A + 1 ≤ 2 * (K + K₂ + A + 1) := ⋄
    calc 11200 * (2 * K₂ + A + 1) * (Nat.clog 2 Mb + 1)
        ≤ 11200 * (2 * (K + K₂ + A + 1)) * (Nat.clog 2 Mb + 1) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ this)
      _ = 22400 * ((K + K₂ + A + 1) * (Nat.clog 2 Mb + 1)) := ⋆
  have hκB : κB * (K + K₂ + 1) ≤ κB * ((K + K₂ + A + 1) * (Nat.clog 2 Mb + 1)) :=
    Nat.mul_le_mul_left _ (⋄)
  Ξ' hκ at hroom'
  -- stage A: the new chord list
  obtain ⟨c₁, k₁, e₁, hk₁, w₁, a25, a26, a27, a28, a29, a34, aA, aCL, alow, af, arr⟩ :=
    splA_exec (P := P) (W := W) c hw (B := c.nreg 210002) (K := K) (B₂ := c.nreg 210020)
      (K₂ := K₂) (L := L) (L₂ := L₂) rfl hK rfl hK₂ rfl rfl hCL hCL₂ hB0 hB₂ (⋄)
  have g₁ := af.1
  have b21 : ∀ r, 210000 ≤ r → r < 220000 → bandOf r ∉ ({bSort, bSign, bBuild} : Finset ℕ) := by
    intro r h1 h2
    simp only [Finset.mem_insert, Finset.mem_singleton, bandOf, bSort, bSign, bBuild]; omega
  set L' := L ++ L₂ with hL'
  have hlen : L'.length = K + K₂ := Ρ hL', List.length_append
  -- stage B1: the records
  obtain ⟨c₂, k₂, e₂, hk₂, w₂, d40, d42, d421, d31, d32, d33, dA, drec, dlow, -, dfr, drr, drm, dout⟩ :=
    splB1_exec (P := P) (W := W) hWn c₁ w₁ (D := c.nreg 210001) (B' := A₀) (K := K) (K₂ := K₂)
      (A := A) (M := M) (L' := L') (Ρ g₁ _ (⌖)) a26 a25 a27 a28
      (Ρ g₁ _ (⌖)) hlen hok aCL aA (by rw [aA]; omega)
  Ξ' aA at d42 dA drec dlow drm
  -- registers of band `bDownDrv` kept by stage B1
  have dk : ∀ r, 210000 ≤ r → r < 220000 → (r < 210031 ∨ 210033 < r) → c₂.nreg r = c₁.nreg r :=
    fun r h1 h2 h3 => dfr r (b21 r h1 h2) h3 (by unfold ALLOC; omega)
  -- memory below `A₀`
  have hlow2 : ∀ a, a < A₀ → c₂.nmem a = c.nmem a := fun a ha => Ρ dlow a (⋄), alow a ha
  obtain ⟨hM₂, hwf₂⟩ := desc_agree hwf hM (m' := c₂.nmem) fun a ha => hlow2 a ha
  -- stage B2: the sorted new codes
  have hroomB2 : c₂.nreg ALLOC + splB2Cost bk (2 * K₂) A + 1 ≤ W := by rw [dA]; omega
  obtain ⟨c₃, k₃, e₃, hk₃, w₃, f48, fperm, fsort, fRb, fA, flow, f40, f42, f421, f34, ffr, frr, frm,
    fout⟩ := splB2_exec (P := P) (W := W) hG hWn c₂ w₂ (D := c.nreg 210001) (T := A₀ + 3 * (K + K₂))
      (BB := BB) (n := 2 * K₂) (A := A) (base := 2 * K) (M := M) (L' := L') (bk := bk)
      (Ρ dk _ (⊛) (⊛) (⊛), g₁ _ (⌖)) d31 d32 d33 d40
      d42 (Ρ d421, hlen) (hwf₂.mono (by rw [dA]; omega)) hM₂ hok drec
      (by rw [dA, hlen]; omega) (by rw [hlen]; omega) (by rw [dA]; omega)
      (fun q hq => Ρ hlow2 _ (⋄)) (fun q hq => hbk q hq)
      (fun q q' hq hq' h => hmono q q' hq hq' h) hroomB2
  Ξ' dA at f48 fA flow frm
  -- registers of band `bDownDrv` kept by stage B2
  have fk : ∀ r, 210000 ≤ r → r < 220000 → (r < 210034 ∨ 210059 < r) → c₃.nreg r = c₂.nreg r :=
    fun r h1 h2 h3 => ffr r (b21 r h1 h2) h3 (by unfold ALLOC; omega)
  have hlow3 : ∀ a, a < A₀ + 3 * (K + K₂) + 10 * (K + K₂) → c₃.nmem a = c₂.nmem a := flow
  have hA₃lo : A₀ + 13 * (K + K₂) ≤ c₃.nreg ALLOC := by have := fRb; Ξ' f48 at this; omega
  have hCC : splCCost K K₂ ≤ 22066 * (K + K₂) + 40 := by unfold splCCost; omega
  -- the registers at `c₃`
  have t01 : c₃.nreg 210001 = c.nreg 210001 := by
    rw [fk _ (⊛) (⊛) (⊛), dk _ (⊛) (⊛) (⊛),
      g₁ _ (⌖)]
  have t04 : c₃.nreg 210004 = c.nreg 210004 := by
    rw [fk _ (⊛) (⊛) (⊛), dk _ (⊛) (⊛) (⊛),
      g₁ _ (⌖)]
  have t25 : c₃.nreg 210025 = K + K₂ := by
    rw [fk _ (⊛) (⊛) (⊛), dk _ (⊛) (⊛) (⊛),
      a25]
  have t26 : c₃.nreg 210026 = A₀ := by
    rw [fk _ (⊛) (⊛) (⊛), dk _ (⊛) (⊛) (⊛),
      a26]
  have t27 : c₃.nreg 210027 = 2 * K := by
    rw [fk _ (⊛) (⊛) (⊛), dk _ (⊛) (⊛) (⊛),
      a27]
  have t28 : c₃.nreg 210028 = 2 * K₂ := by
    rw [fk _ (⊛) (⊛) (⊛), dk _ (⊛) (⊛) (⊛),
      a28]
  have t29 : c₃.nreg 210029 = 2 * (K + K₂) := by
    rw [fk _ (⊛) (⊛) (⊛), dk _ (⊛) (⊛) (⊛),
      a29]
  -- the memory at `c₃`
  have hm3 : ∀ a, a < A₀ → c₃.nmem a = c.nmem a := fun a ha => by
    Ξ hlow3 a (⋄), hlow2 a ha
  obtain ⟨hM₃, hwf₃⟩ := desc_agree hwf hM (m' := c₃.nmem) hm3
  have hCL₃ : ChordListAt c₃.nmem A₀ (L ++ L₂) := fun i hi => by
    obtain ⟨x1, x2, x3⟩ := aCL i hi
    Ξ' hlen at hi
    exact ⟨by rw [hlow3 _ (⋄), dlow _ (⋄)]; exact x1,
      by rw [hlow3 _ (⋄), dlow _ (⋄)]; exact x2,
      by rw [hlow3 _ (⋄), dlow _ (⋄)]; exact x3⟩
  have hrec₃ : RecsAt c₃.nmem (A₀ + 3 * (K + K₂)) L' := fun q hq => by
    obtain ⟨r1, r2, r3, r4⟩ := drec q hq
    Ξ' hlen at hq
    exact ⟨by rw [hlow3 _ (⋄)]; exact r1, by rw [hlow3 _ (⋄)]; exact r2,
      by rw [hlow3 _ (⋄)]; exact r3, by rw [hlow3 _ (⋄)]; exact r4⟩
  have hE₃ : seg c₃.nmem (c.nreg 210004) (2 * K) = E := by
    rw [seg_congr (m' := c.nmem) fun i hi => hm3 _ (⋄)]; exact hSE
  -- the tail
  obtain ⟨c₄, k₄, e₄, hk₄, tAlo, tAhi, t2, t3, t4lo, t4hi, tseg, t5lo, tnf, tlow, tfr, trr, trm,
    tout⟩ := splT_exec (P := P) (W := W) hB hG hWn c₃ w₃ (D := c.nreg 210001)
      (T := A₀ + 3 * (K + K₂)) (SE := c.nreg 210004) (Rb := c₃.nreg 210048) (A₀ := A₀) (M := M)
      (L := L) (L₂ := L₂) (E := E) (E₂ := seg c₃.nmem (c₃.nreg 210048) (2 * K₂))
      t01 t25 t26 t27 t28 t29 t04 rfl f34 f40 f42 (Ρ f421, hlen) (⋄)
      (hwf₃.mono (⋄)) hM₃ hgood hok hCL₃ hrec₃ (⋄) hE₃ (⋄) rfl (⋄)
      hperm hsort fperm fsort (by rw [← hKd, ← hK₂d]; omega)
  obtain ⟨sP, sS⟩ := DownDrv.splice_ok hperm hsort fperm fsort
  Ξ' List.length_append at sP
  refine ⟨c₄, k₁ + (k₂ + (k₃ + k₄)), .seq e₁ (.seq e₂ (.seq e₃ e₄)), ?_, ⟨fun r hr => ?_, ?_⟩,
    fun r hr hra => ?_, fun r hr => ?_, fun a ha => ?_, fun a ha => ?_, ?_, ⋄, ⋄⟩
  · -- the cost
    show k₁ + (k₂ + (k₃ + k₄)) ≤ splCost κB c
    Ξ hcost
    unfold splTCost at hk₄
    Ξ' ← hKd, ← hK₂d at hk₄
    omega
  · -- the registers kept
    obtain ⟨x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12⟩ := spl_keep hr
    Ξ tfr r x1 x2 x3 x4 x5 x6 x7, fk r x11 x12 x8, dk r x11 x12 x9, g₁ r x10
  · -- the outputs
    intro M₀ L₀ L₂₀ hM₀ hK₀ hCL₀ hK₂₀ hCL₂₀
    ϴ' rd, bandReg, bDownDrv, Nat.reduceMul, Nat.reduceAdd at hM₀ hK₀ hCL₀ hK₂₀ hCL₂₀ ⊢
    have e1 : M₀ = M := NFLoc.modelDesc_unique hM₀ hM
    have e2 : L₀ = L := BuildNF.chordListAt_unique hCL₀ hCL (⋄)
    have e3 : L₂₀ = L₂ := BuildNF.chordListAt_unique hCL₂₀ hCL₂ (⋄)
    Ξ e1, e2, e3, t2, t3, tseg
    refine ⟨rfl, le_refl _, ⋄, fun i hi => ?_, ⋄, t4hi, sP, sS, ⋄, tnf⟩
    obtain ⟨x1, x2, x3⟩ := hCL₃ i hi
    Ξ' List.length_append at hi
    exact ⟨by rw [tlow _ (⋄)]; exact x1, by rw [tlow _ (⋄)]; exact x2,
      by rw [tlow _ (⋄)]; exact x3⟩
  · -- the frame: registers
    obtain ⟨x1, x2, x3, x4, x5, x6, x7, x8, x9⟩ := spl_out hr
    Ξ tfr r x1 (x2 hra) x3 x4 x5 x6 hra, ffr r x1 x7 hra, dfr r x1 x8 hra, g₁ r (x9 hra)
  · -- real registers
    obtain ⟨x1, -, -, -, -, -, x7, -, -⟩ := spl_out hr
    Ξ trr r x1, frr r x1 x7, drr r x1, arr
  · Ξ tlow a (⋄), hm3 a ha
  · Ξ trm a (⋄), frm a (⋄), drm a (⋄), af.2.2.1
  · Ξ tout, fout, dout, af.2.2.2

end exec

end

end DrvR

end Chazelle.Core
