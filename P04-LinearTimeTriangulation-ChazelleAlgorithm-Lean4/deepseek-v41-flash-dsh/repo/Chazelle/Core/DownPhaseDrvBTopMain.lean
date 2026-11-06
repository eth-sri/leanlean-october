module

public import Chazelle.Golf

public import Chazelle.Golf

public import Chazelle.Core.DownPhaseDrvBTopMath

/-!
# Down-phase base (D9), top level, part 3: `DrvR.BaseSpec`

**`baseSpec_of`**: from the contract of the region loop (`RegLoopSpec`), `DropAugSpec` and
`BuildNFSortedSpec`, the program `topS sR sD sB` meets the base-case contract
`DrvR.BaseSpec X cnt n₀` (for every up-phase context `X`, count function `cnt` and threshold
`n₀`).  **`baseSpec_of_regLoop`**: the instance with `dropAug` and `buildNFSorted`.

From `Inv(λ)` with `λ < 16` or `n < n₀` (so `λ < Λ = max 16 (n₀ + 1)`): reserve `10 n` words, run
the region loop with `S₀ = 5 γ + 8`, `Cm = γ + 2` (`γ = 2^(⌈βλ⌉+12)`, `reg_sizes`), splice the
new chords `L₂ = newLB` into `(L, E)` (`DrvR.splice_meets`), drop the chords that are not vertex
chords (`dropAug`) and build the normal form of the rest (`buildNFSorted`).  Its family is
`famL (L ++ L₂) ∩ Full = Full` (`newLB_facts`).  Cost: `K ≤ cnt λ (2^p + 1) ≤ Cc (2 n + 3)` with
`Cc = Σ_{λ < Λ} cnt λ`, and the region loop costs a constant per region (`top_cost`).
-/

namespace Chazelle.Core

namespace DrvB

open Machine Machine.Stmt Programs SignK BuildRam
open BuildNF (codeLe)
open SortL (seg)
open Chazelle.Visibility (chords)
open BTop

@[expose] public section


/-- **The top level of the base case meets `DrvR.BaseSpec`.** -/
theorem baseSpec_of {X : MemCtx} {cnt : ℕ → ℕ} {n₀ : ℕ} (hRL : RegLoopSpec)
    (hDA : DropAugSpec) (hBS : BuildNFSortedSpec) : DrvR.BaseSpec X cnt n₀ := by
  obtain ⟨sR, κR, hsR⟩ := hRL
  obtain ⟨sD, κD, hsD⟩ := hDA
  obtain ⟨sB, κB, hsB⟩ := hBS
  obtain ⟨Λ, hΛ⟩ : ∃ x, x = max 16 (n₀ + 1) := ⟨_, rfl⟩
  obtain ⟨Γ, hΓ⟩ : ∃ x, x = 2 ^ (Λ + 12) := ⟨_, rfl⟩
  obtain ⟨Cc, hCc⟩ : ∃ x, x = ∑ i ∈ Finset.range Λ, cnt i := ⟨_, rfl⟩
  obtain ⟨κT, hκT⟩ : ∃ x, x = topK κR (DrvR.κSpl κB) κD κB Cc Γ := ⟨_, rfl⟩
  refine ⟨topS sR sD sB, κT, ?_⟩
  intro P W c hw hpre hroom
  replace hroom : c.nreg ALLOC + κT * (P.n + 1) ≤ W := hroom
  obtain ⟨hE, lam, hlamp, hlam, hInv⟩ := hpre
  obtain ⟨hG, -, hWh, -, -, -⟩ := hE
  obtain ⟨hD6, hDa, L, E, hK, hLb, hLa, hEb, hEa, hok, hperm, hsort, hNW, hdeg, hwt, hcnt⟩ := hInv
  ϴ' rd, bandReg, bDownDrv, Nat.reduceMul, Nat.reduceAdd at hD6 hDa hK hLb hLa hEb hEa hNW
  -- the polygon
  have hQ : (Qof P).Simple := (shearInvariance (epsOf P) P).1 hG.1
  have hn : (Qof P).n = P.n := shear_n _ _
  have hn3 : 3 ≤ P.n := by have := hQ.1; omega
  have hWn : 256 * P.n + 16 ≤ W := hWh
  have hGM : GoodModel (interiorModel (Qof P)) := Or.inr ⟨Qof P, hQ, rfl⟩
  -- the level and the constants
  have h16 : 16 ≤ Λ := by rw [hΛ]; exact le_max_left _ _
  have hn0 : n₀ + 1 ≤ Λ := by rw [hΛ]; exact le_max_right _ _
  have hlΛ : lam < Λ := by have := topGrade_le' P.n; rcases hlam with h | h <;> omega
  have hγΓ : 2 ^ (Cost.ceilBeta lam + 12) ≤ Γ := by
    rw [hΓ]; exact Nat.pow_le_pow_right (⊛) (by have := Cost.ceilBeta_le lam; omega)
  have hKc : L.length ≤ Cc * (2 * P.n + 3) := by
    have h1 := count_le hcnt
    have h2 : cnt lam ≤ Cc := by rw [hCc]; exact cnt_le_sum cnt hlΛ
    have h3 : 2 ^ topGrade P.n ≤ 2 * P.n := Setup.pow_topGrade_le (⋄)
    exact h1.trans (Nat.mul_le_mul h2 (⋄))
  have hκTge : 20 * Γ + 73 ≤ κT := by rw [hκT]; exact topK_ge (by unfold DrvR.κSpl; omega)
  have hκTn : κT ≤ κT * (P.n + 1) := Nat.le_mul_of_pos_right _ (⋄)
  -- the facts of the level
  have hMD0 := hDa.holds
  have hli : liBit c.nmem (c.nreg 210001) = true ↔ Mountain.LeftInside (Qof P) := liBit_iff hMD0
  obtain ⟨hS, hC0, hCm⟩ := reg_sizes (γ := 2 ^ (Cost.ceilBeta lam + 12)) hG hok hperm hsort hdeg
    hwt hli
  obtain ⟨hok', hfull⟩ := newLB_facts hG hok hperm hsort hli
  have hElen : E.length = 2 * L.length := Ρ hperm.length_eq, List.length_range
  have hAle := DrvD.arcs_length_le (M := interiorModel (Qof P)) (Q := Qof P) (L := L) hElen
  have hH7 : c.nreg 210005 + 7 < c.nreg ALLOC := (Gran.nf_areas hNW).1
  generalize hγ : 2 ^ (Cost.ceilBeta lam + 12) = γ at hS hC0 hCm hγΓ
  -- 1. `B₂ := ALLOC`
  obtain ⟨c₁, k₁, e₁, hk₁, a19, a01, a02, a03, f₁⟩ := tPre_exec (P := P) c hw (⋄)
  have g₁ := f₁.1
  have A₁ : c₁.nreg ALLOC = c.nreg ALLOC := g₁ _ (⌖)
  have m₁ := f₁.2.2.1
  -- 2. the reservation
  have T₁ := top_cost (n := P.n) (K := L.length) (K₂ := 0) (A := 0) (K' := 0) (S₀ := 5 * γ + 8)
    (Cm := γ + 2) (Mb := 0) (Cc := Cc) (Γ := Γ) (κR := κR) (κS := DrvR.κSpl κB) (κD := κD)
    (κB := κB) hKc (⋄) (⋄) (⋄) (⋄) (⋄) (⋄)
  Ξ' ← hκT at T₁
  obtain ⟨c₂, k₂, e₂, hk₂, A₂, f₂, RF₂⟩ := tRes_exec (P := P) e₁.wb_right a03 a02 a01
    (by rw [A₁]; omega) (c.nreg ALLOC)
  Ξ' A₁ at A₂
  have g₂ := f₂.1
  have m₂ : c₂.nmem = c.nmem := Ρ f₂.2.2.1, m₁
  have K2 : ∀ r, 210000 ≤ r → r < 210030 → c₂.nreg r = c.nreg r := fun r h1 h2 => by
    Ξ g₂ r (bres_false (⋄) (⋄)), g₁ r (bpre_false (⋄) (⋄))
  have B19 : c₂.nreg 212019 = c.nreg ALLOC := by
    Ξ g₂ _ (bres_false (⊛) (⊛)), a19
  -- 3. the region loop
  have hMD₂ : ModelDescAt c₂.nmem (c₂.nreg 210001) (Qof P) (interiorModel (Qof P)) := by
    rw [m₂, K2 210001 (⊛) (⊛)]; exact hMD0
  have hli₂ : liBit c₂.nmem (c₂.nreg 210001) = liBit c.nmem (c.nreg 210001) := by
    Ξ m₂, K2 210001 (⊛) (⊛)
  have hpre₂ : RegPre P W c₂ L E (5 * γ + 8) (γ + 2) := by
    refine ⟨hG, hWh, by rw [K2 210003 (⊛) (⊛)]; exact hK, hok, hperm, hsort, hdeg,
      ?_, hMD₂, ?_, ?_, ?_, hC0, hCm⟩
    · rw [m₂, K2 210005 (⊛) (⊛), B19]; exact hNW
    · rw [K2 210001 (⊛) (⊛), B19]; exact hD6
    · rw [B19, A₂]; omega
    · intro r hr; rw [hli₂]; exact hS r hr
  obtain ⟨c₃, k₃, e₃, hk₃, post₃, RF₃⟩ := hsR P W c₂ L E (5 * γ + 8) (γ + 2) e₂.wb_right hpre₂
    (by rw [A₂]; omega)
  obtain ⟨pk, pkB, pcnt, plen, plist, pbkle, pmono, pbcnt, pmx⟩ := post₃
  Ξ' hli₂ at pcnt plen plist pbkle pmono pbcnt
  Ξ' B19 at plist pbkle pmono pbcnt RF₃
  generalize hL₂ : newLB (liBit c.nmem (c.nreg 210001)) (Qof P) L E = L₂
    at pcnt plen plist pbkle pmono pbcnt hok' hfull
  have hlow3 : ∀ a, a < c.nreg ALLOC → c₃.nmem a = c.nmem a := fun a ha => by
    Ξ RF₃.2.2.1 a ha, m₂
  have A₃ := RF₃.2.2.2.2.2.1
  have A₃' := RF₃.2.2.2.2.2.2
  have K3 : ∀ r, 210000 ≤ r → r < 210030 → c₃.nreg r = c.nreg r := fun r h1 h2 => by
    Ξ pk r h1 h2, K2 r h1 h2
  have hW3 : c₃.nreg ALLOC ≤ W := e₃.wb_right.1 ALLOC
  -- 4. the arguments of the splice
  obtain ⟨c₄, k₄, e₄, hk₄, s20, s21, s22, s23, s24, f₄⟩ := tArgs_exec (P := P) c₃ e₃.wb_right
    (B₂ := c.nreg ALLOC) (H := c.nreg 210005) (MX := c₃.nreg 212018) (K₂ := L₂.length)
    (Ρ pkB, B19) (K3 _ (⊛) (⊛)) rfl pcnt (⋄)
    (⋄) (⋄)
  have g₄ := f₄.1
  have m₄ := f₄.2.2.1
  have A₄ : c₄.nreg ALLOC = c₃.nreg ALLOC := g₄ _ (⌖)
  have K4 : ∀ r, 210000 ≤ r → r < 210020 → c₄.nreg r = c.nreg r := fun r h1 h2 => by
    Ξ g₄ r (bargs_false (⋄) (⋄)), K3 r h1 (⋄)
  have hlow4 : ∀ a, a < c.nreg ALLOC → c₄.nmem a = c.nmem a := fun a ha => by
    Ξ m₄, hlow3 a ha
  have s23' : c₄.nreg 210023 =
      (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).arcs.length := by
    rw [s23, hlow3 (c.nreg 210005 + 1) (⋄)]; exact hNW.holds.2.1
  have hMD₄ : ModelDescAt c₄.nmem (c.nreg 210001) (Qof P) (interiorModel (Qof P)) :=
    hDa c₄.nmem hlow4
  -- 5. the splice
  have T₂ := top_cost (n := P.n) (K := L.length) (K₂ := L₂.length)
    (A := (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).arcs.length) (K' := 0)
    (S₀ := 5 * γ + 8) (Cm := γ + 2) (Mb := 4 * c₃.nreg 212018) (Cc := Cc) (Γ := Γ) (κR := κR)
    (κS := DrvR.κSpl κB) (κD := κD) (κB := κB) hKc plen hAle (⋄) (⋄) (⋄)
    (⋄)
  Ξ' ← hκT at T₂
  have hspl : DrvR.splCost κB c₄ = DrvR.κSpl κB * (L.length + L₂.length +
      (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).arcs.length + 1) *
      (Nat.clog 2 (4 * c₃.nreg 212018) + 1) := by
    unfold DrvR.splCost
    ϴ rd, bandReg, bDownDrv, Nat.reduceMul, Nat.reduceAdd
    Ξ K4 210003 (⊛) (⊛), hK, s21, s23', s24
  obtain ⟨c₅, k₅, e₅, hk₅, ⟨keepS, postS⟩, F₅⟩ := DrvR.splice_meets hsB P W c₄ e₄.wb_right
    ⟨hG, hWh, by
      show ModelDescWF P (c₄.nreg ALLOC) c₄.nmem (c₄.nreg 210001)
      rw [K4 210001 (⊛) (⊛)]; exact descWF_int hMD₄ (⋄),
      interiorModel (Qof P), L, L₂, E, by
      show ModelDescAt c₄.nmem (c₄.nreg 210001) (Qof P) (interiorModel (Qof P))
      rw [K4 210001 (⊛) (⊛)]; exact hMD₄, hGM, by
      show c₄.nreg 210003 = _; rw [K4 210003 (⊛) (⊛)]; exact hK, by
      show c₄.nreg 210002 + 3 * L.length ≤ c₄.nreg ALLOC
      rw [K4 210002 (⊛) (⊛)]; omega, by
      show ChordListAt c₄.nmem (c₄.nreg 210002) L
      rw [K4 210002 (⊛) (⊛)]; exact hLa c₄.nmem hlow4, by
      show c₄.nreg 210021 = _; exact s21, by
      show c₄.nreg 210020 + 3 * L₂.length ≤ c₄.nreg ALLOC
      rw [s20]; omega, by
      show ChordListAt c₄.nmem (c₄.nreg 210020) L₂
      rw [s20, m₄]; exact plist, hok', by
      show c₄.nreg 210004 + 2 * L.length ≤ c₄.nreg ALLOC
      rw [K4 210004 (⊛) (⊛)]; omega, by
      show seg c₄.nmem (c₄.nreg 210004) (2 * L.length) = E
      rw [K4 210004 (⊛) (⊛)]; exact hEa c₄.nmem hlow4, hperm, hsort, by
      show c₄.nreg 210022 + 2 * L₂.length ≤ c₄.nreg ALLOC
      rw [s22]; omega, fun q hq => by
      show c₄.nmem (c₄.nreg 210022 + q) ≤ c₄.nreg 210023
      rw [s22, s23', m₄]; exact pbkle q hq, fun q q' hq hq' hb => by
      refine pmono q q' hq hq' ?_
      have e1 : DrvR.bkOf c₄ q = c₃.nmem (c.nreg ALLOC + 6 * P.n + q) := by
        show c₄.nmem (c₄.nreg 210022 + q) = _; Ξ s22, m₄
      have e2 : DrvR.bkOf c₄ q' = c₃.nmem (c.nreg ALLOC + 6 * P.n + q') := by
        show c₄.nmem (c₄.nreg 210022 + q') = _; Ξ s22, m₄
      Ξ' e1, e2 at hb; exact hb, fun b => by
      show DrvR.bcnt (DrvR.bkOf c₄) (2 * L₂.length) b ≤ c₄.nreg 210024
      Ξ s24
      have e : DrvR.bkOf c₄ = fun q => c₃.nmem (c.nreg ALLOC + 6 * P.n + q) := by
        funext q; show c₄.nmem (c₄.nreg 210022 + q) = _; Ξ s22, m₄
      rw [e]; exact pbcnt b⟩
    (by show c₄.nreg ALLOC + DrvR.splCost κB c₄ ≤ W; rw [hspl, A₄]; omega)
  obtain ⟨p3, p2l, p2b, p2, p4l, p4b, pperm, psort, p5l, pNW⟩ := postS (interiorModel (Qof P)) L L₂
    (by show ModelDescAt c₄.nmem (c₄.nreg 210001) (Qof P) (interiorModel (Qof P))
        rw [K4 210001 (⊛) (⊛)]; exact hMD₄)
    (by show c₄.nreg 210003 = _; rw [K4 210003 (⊛) (⊛)]; exact hK)
    (by show ChordListAt c₄.nmem (c₄.nreg 210002) L
        rw [K4 210002 (⊛) (⊛)]; exact hLa c₄.nmem hlow4)
    (by show c₄.nreg 210021 = _; exact s21)
    (by show ChordListAt c₄.nmem (c₄.nreg 210020) L₂; rw [s20, m₄]; exact plist)
  ϴ' rd, bandReg, bDownDrv, Nat.reduceMul, Nat.reduceAdd at p3 p2l p2b p2 p4l p4b
  ϴ' rd, bandReg, bDownDrv, Nat.reduceMul, Nat.reduceAdd at pperm psort p5l pNW
  have hk₅' : k₅ ≤ DrvR.κSpl κB * (L.length + L₂.length +
      (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).arcs.length + 1) *
      (Nat.clog 2 (4 * c₃.nreg 212018) + 1) := by rw [← hspl]; exact hk₅
  have A₅ := F₅.2.2.2.2.2.1
  have A₅' := F₅.2.2.2.2.2.2
  have hlow5 : ∀ a, a < c.nreg ALLOC → c₅.nmem a = c.nmem a := fun a ha => by
    Ξ F₅.2.2.1 a (⋄), hlow4 a ha
  have r51 : c₅.nreg 210001 = c.nreg 210001 := by
    Ξ keepS 210001 (Or.inl ⟨⊛, ⊛⟩), K4 210001 (⊛) (⊛)
  have hLL : (L ++ L₂).length = L.length + L₂.length := List.length_append
  -- 6. the arguments of `dropAug`
  obtain ⟨c₆, k₆, e₆, hk₆, d00, d01, d02, d03, f₆⟩ := tDrop_exec (P := P) c₅ e₅.wb_right
  have g₆ := f₆.1
  have m₆ := f₆.2.2.1
  have A₆ : c₆.nreg ALLOC = c₅.nreg ALLOC := g₆ _ (⌖)
  -- 7. `dropAug`
  obtain ⟨c₇, k₇, e₇, hk₇, postD, F₇⟩ := hsD P W c₆ e₆.wb_right
    ⟨hG, hWh, by
      show c₆.nreg 200000 + 2 ≤ c₆.nreg ALLOC
      rw [d00, r51, A₆]; omega, by
      show c₆.nmem (c₆.nreg 200000 + 1) = 1 ↔ Mountain.LeftInside (Qof P)
      rw [d00, r51, m₆, hlow5 (c.nreg 210001 + 1) (⋄)]; exact (desc_int hMD0).2,
      L ++ L₂, by
      show c₆.nreg 200002 = _; rw [d02, p3, hLL], by
      show c₆.nreg 200001 + 3 * (L ++ L₂).length ≤ c₆.nreg ALLOC
      rw [d01, A₆, hLL]; exact p2b, by
      show ChordListAt c₆.nmem (c₆.nreg 200001) (L ++ L₂)
      rw [d01, m₆]; exact p2, hok', by
      show c₆.nreg 200003 + 2 * (L ++ L₂).length ≤ c₆.nreg ALLOC
      rw [d03, A₆, hLL]; exact p4b, by
      show (seg c₆.nmem (c₆.nreg 200003) (2 * (L ++ L₂).length)).Perm
        (List.range (2 * (L ++ L₂).length))
      rw [d03, m₆, hLL]; exact pperm, by
      show (seg c₆.nmem (c₆.nreg 200003) (2 * (L ++ L₂).length)).Pairwise
        (codeLe (interiorModel (Qof P)) (Qof P) (L ++ L₂))
      rw [d03, m₆, hLL]; exact psort⟩
    (by show c₆.nreg ALLOC + κD * (c₆.nreg 200002 + 1) ≤ W
        rw [d02, p3, A₆]; omega)
  obtain ⟨d4l, d4b, dCL, d5, d6l, d6b, dseg, dfam, dok, dperm, dsort⟩ := postD (L ++ L₂)
    (by show c₆.nreg 200002 = _; rw [d02, p3, hLL])
    (by show ChordListAt c₆.nmem (c₆.nreg 200001) (L ++ L₂); rw [d01, m₆]; exact p2)
  ϴ' rd, bandReg, bDown, Nat.reduceMul, Nat.reduceAdd at d4l d4b dCL d5 d6l d6b dseg
  ϴ' rd, bandReg, bDown, Nat.reduceMul, Nat.reduceAdd at dfam dok dperm dsort
  have hKLlen : (DownBase.keepL (liBit c₆.nmem (c₆.nreg 200000)) (Qof P).n (L ++ L₂)).length ≤
      L.length + L₂.length := by
    rw [← hLL]; unfold DownBase.keepL; exact List.length_filter_le _ _
  have hk₇' : k₇ ≤ κD * (L.length + L₂.length + 1) := by
    have h := hk₇
    ϴ' rd, bandReg, bDown, Nat.reduceMul, Nat.reduceAdd at h
    Ξ' d02, p3 at h; exact h
  generalize hKL : DownBase.keepL (liBit c₆.nmem (c₆.nreg 200000)) (Qof P).n (L ++ L₂) = KL
    at d4b dCL d5 d6b dseg dfam dok dperm dsort hKLlen
  generalize hDE : DownBase.dropE (liBit c₆.nmem (c₆.nreg 200000)) (Qof P).n (L ++ L₂)
    (seg c₆.nmem (c₆.nreg 200003) (2 * (L ++ L₂).length)) = DE
    at dseg dperm dsort
  have A₇ := F₇.2.2.2.2.2.1
  have A₇' := F₇.2.2.2.2.2.2
  have hlow7 : ∀ a, a < c.nreg ALLOC → c₇.nmem a = c.nmem a := fun a ha => by
    Ξ F₇.2.2.1 a (⋄), m₆, hlow5 a ha
  have r71 : c₇.nreg 210001 = c.nreg 210001 := by
    Ξ F₇.1 _ (⌖) (by unfold ALLOC; norm_num), g₆ _ (⌖), r51
  -- 8. the arguments of `buildNFSorted`
  obtain ⟨c₈, k₈, e₈, hk₈, b00, b01, b02, b04, f₈⟩ := tBld_exec (P := P) c₇ e₇.wb_right
  have g₈ := f₈.1
  have m₈ := f₈.2.2.1
  have A₈ : c₈.nreg ALLOC = c₇.nreg ALLOC := g₈ _ (⌖)
  have hlow8 : ∀ a, a < c.nreg ALLOC → c₈.nmem a = c.nmem a := fun a ha => by
    Ξ m₈, hlow7 a ha
  have hMD₈ : ModelDescAt c₈.nmem (c.nreg 210001) (Qof P) (interiorModel (Qof P)) :=
    hDa c₈.nmem hlow8
  -- 9. `buildNFSorted`
  have T₃ := top_cost (n := P.n) (K := L.length) (K₂ := L₂.length)
    (A := (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).arcs.length) (K' := KL.length)
    (S₀ := 5 * γ + 8) (Cm := γ + 2) (Mb := 4 * c₃.nreg 212018) (Cc := Cc) (Γ := Γ) (κR := κR)
    (κS := DrvR.κSpl κB) (κD := κD) (κB := κB) hKc plen hAle hKLlen (⋄) (⋄)
    (⋄)
  Ξ' ← hκT at T₃
  obtain ⟨c₉, k₉, e₉, hk₉, postB, F₉⟩ := hsB P W c₈ e₈.wb_right
    ⟨hG, hWh, by
      show ModelDescWF P (c₈.nreg ALLOC) c₈.nmem (c₈.nreg 40000)
      rw [b00, r71]; exact descWF_int hMD₈ (⋄),
      interiorModel (Qof P), KL, DE, by
      show ModelDescAt c₈.nmem (c₈.nreg 40000) (Qof P) (interiorModel (Qof P))
      rw [b00, r71]; exact hMD₈, hGM, by
      show c₈.nreg 40002 = _; rw [b02, d5], by
      show c₈.nreg 40001 + 3 * KL.length ≤ c₈.nreg ALLOC
      rw [b01, A₈]; exact d4b, by
      show ChordListAt c₈.nmem (c₈.nreg 40001) KL
      rw [b01, m₈]; exact dCL, dok, by
      show c₈.nreg 40004 + 2 * KL.length ≤ c₈.nreg ALLOC
      rw [b04, A₈]; exact d6b, by
      show seg c₈.nmem (c₈.nreg 40004) (2 * KL.length) = DE
      rw [b04, m₈]; exact dseg, dperm, dsort⟩
    (by show c₈.nreg ALLOC + κB * (c₈.nreg 40002 + 1) ≤ W
        rw [b02, d5, A₈]; omega)
  obtain ⟨b3l, bNW, bNF, -, -⟩ := postB (interiorModel (Qof P)) KL
    (by show ModelDescAt c₈.nmem (c₈.nreg 40000) (Qof P) (interiorModel (Qof P))
        rw [b00, r71]; exact hMD₈)
    (by show c₈.nreg 40002 = _; rw [b02, d5])
    (by show ChordListAt c₈.nmem (c₈.nreg 40001) KL; rw [b01, m₈]; exact dCL)
  have hk₉' : k₉ ≤ κB * (KL.length + 1) := by
    have h := hk₉
    ϴ' rd, bandReg, bBuild, Nat.reduceMul, Nat.reduceAdd at h
    Ξ' b02, d5 at h; exact h
  -- 10. the output
  obtain ⟨c₁₀, k₁₀, e₁₀, hk₁₀, o06, f₁₀⟩ := tOut_exec (P := P) c₉ e₉.wb_right
  have m₁₀ := f₁₀.2.2.1
  have A₁₀ : c₁₀.nreg ALLOC = c₉.nreg ALLOC := f₁₀.1 _ (⌖)
  -- frames
  have RF₁ : Restore.RF DrvR.drvBands (c.nreg ALLOC) c c₁ k₁ := DrvD.rf_of_frameB inDrv_pre f₁
  have RF₄ : Restore.RF DrvR.drvBands (c.nreg ALLOC) c₃ c₄ k₄ := DrvD.rf_of_frameB inDrv_args f₄
  have RF₅ : Restore.RF DrvR.drvBands (c.nreg ALLOC) c₄ c₅ k₅ :=
    (Restore.RF.of_frame F₅ (⋄)).mono DrvD.splBands_sub le_rfl
  have RF₆ : Restore.RF DrvR.drvBands (c.nreg ALLOC) c₅ c₆ k₆ := DrvD.rf_of_frameB inDrv_drop f₆
  have RF₇ : Restore.RF DrvR.drvBands (c.nreg ALLOC) c₆ c₇ k₇ :=
    (Restore.RF.of_frame F₇ (⋄)).mono (⌖) le_rfl
  have RF₈ : Restore.RF DrvR.drvBands (c.nreg ALLOC) c₇ c₈ k₈ := DrvD.rf_of_frameB inDrv_bld f₈
  have RF₉ : Restore.RF DrvR.drvBands (c.nreg ALLOC) c₈ c₉ k₉ :=
    (Restore.RF.of_frame F₉ (⋄)).mono (⌖) le_rfl
  have RF₁₀ : Restore.RF DrvR.drvBands (c.nreg ALLOC) c₉ c₁₀ k₁₀ :=
    DrvD.rf_of_frameB (DrvD.inDrv_eq (q := 210006) (⊛) (⊛)
      (by unfold ALLOC; norm_num)) f₁₀
  have RFall := RF₁.trans (RF₂.trans (RF₃.trans (RF₄.trans (RF₅.trans (RF₆.trans (RF₇.trans
    (RF₈.trans (RF₉.trans RF₁₀))))))))
  refine ⟨c₁₀, k₁ + (k₂ + (k₃ + (k₄ + (k₅ + (k₆ + (k₇ + (k₈ + (k₉ + k₁₀)))))))),
    Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ (Exec.seq e₄ (Exec.seq e₅ (Exec.seq e₆ (Exec.seq e₇
      (Exec.seq e₈ (Exec.seq e₉ e₁₀)))))))), ?_, ?_, RFall⟩
  · show _ ≤ κT * (P.n + 1)
    omega
  · refine ⟨_, ?_, bNF, ?_⟩
    · show Robust (c₁₀.nreg ALLOC) c₁₀.nmem (fun m => NFAt m (c₁₀.nreg 210006) _)
      rw [A₁₀, m₁₀, o06]; exact bNW
    · Ξ F_build
      exact dfam.trans (Set.inter_eq_right.2 hfull)

/-- **The base case from the region loop** (with `dropAug` and `buildNFSorted`). -/
theorem baseSpec_of_regLoop {X : MemCtx} {cnt : ℕ → ℕ} {n₀ : ℕ} (hRL : RegLoopSpec) :
    DrvR.BaseSpec X cnt n₀ :=
  baseSpec_of hRL DownBase.dropAug buildNFSorted

end

end DrvB

end Chazelle.Core
