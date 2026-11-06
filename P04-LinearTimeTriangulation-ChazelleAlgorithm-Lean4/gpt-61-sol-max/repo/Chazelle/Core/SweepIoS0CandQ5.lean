module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SweepIoS0CandQ4
public import Chazelle.Core.SweepIoS0CandBsMain

/-!
# The sweep RAM (WP-D), answers: the side-0 stop and table candidates of a query, part 5

* `candQ_spec`: the per-query clause of `S0CandSpec` for `candQ ls` (with a binary search `ls`
  meeting the body of `LSearchSpec`), cost `qK κL (TLR + 1)`;
* `initSpec_mono`: `InitSpec` for a larger cost function;
* **`s0CandSpec_of`**: `S0CandSpec` from the contract of the initialisation (`InitPartSpec`).
-/

namespace Chazelle.Core

namespace SweepIo

namespace S0C

open Set
open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Chain (sidePt SideAttach)
open Chazelle.Merge (FreeAt)

@[expose] public section

/-- The body of `LSearchSpec` for a given statement and constant. -/
def LSearchOK (lsearch : Stmt) (κ : ℕ) : Prop :=
  ∀ (P : Polygon) (W : ℕ) (J : Merge.Junction) (c₀ c : Config),
    IInv W c₀ c → Consts c₀ → ChainCtx P W c (sw 2) J.whole →
    (∀ j, j < c.nreg TLR → c.nmem (c.nreg TBR + j) = 2 ^ j) →
    c.nreg TBR + c.nreg TLR ≤ c.nreg ALLOC →
    c.nreg (sw 301) < 2 ^ c.nreg TLR →
    c.nreg (sw 300) + 7 * c.nreg (sw 301) ≤ c.nreg ALLOC →
    c.nreg (sw 40) < (chainModel J.whole).W.n →
    (∀ j, j < c.nreg (sw 301) → SweepEv.PosW P J (c.nmem (c.nreg (sw 300) + 7 * j))
      (c.nmem (c.nreg (sw 300) + 7 * j + 1))) →
    SweepEv.PosW P J (c.nreg lsxE) (c.nreg lsxH) →
    (∀ i j, i ≤ j → j < c.nreg (sw 301) →
      lsPr P J c.nmem (c.nreg (sw 300)) (c.nreg (sw 40)) ⟨c.nreg lsxE, c.nreg lsxH⟩ j →
      lsPr P J c.nmem (c.nreg (sw 300)) (c.nreg (sw 40)) ⟨c.nreg lsxE, c.nreg lsxH⟩ i) →
    c.nreg ALLOC + κ * (c.nreg TLR + 1) ≤ W →
    IRS P W c₀ lsearch c (κ * (c.nreg TLR + 1)) (fun c' =>
      c'.nreg lsI ≤ c.nreg (sw 301) ∧
      (∀ j, j < c'.nreg lsI →
        lsPr P J c.nmem (c.nreg (sw 300)) (c.nreg (sw 40)) ⟨c.nreg lsxE, c.nreg lsxH⟩ j) ∧
      (∀ j, c'.nreg lsI ≤ j → j < c.nreg (sw 301) →
        ¬ lsPr P J c.nmem (c.nreg (sw 300)) (c.nreg (sw 40)) ⟨c.nreg lsxE, c.nreg lsxH⟩ j) ∧
      (∀ r, bandOf r ∉ oracleBands → ¬ LSet r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a))

theorem lsearchOK_of (h : LSearchSpec) : ∃ ls κ, LSearchOK ls κ := h

/-- The constant of the per-query cost. -/
def qK (κL : ℕ) : ℕ := κL + checkK + 10

/-- The predicate of the search does not depend on the memory outside the log. -/
theorem lsPr_congr {P : Polygon} {J : Merge.Junction} {m m' : ℕ → ℕ} {AL G E : ℕ} {x : WPos}
    {j : ℕ} (hm : ∀ a, a < AL + 7 * E → m a = m' a) (hj : j < E) :
    lsPr P J m AL G x j ↔ lsPr P J m' AL G x j := by
  core_grind

theorem frQ_partFr {c c' : Config} (h : FrQ c c') : PartFr c c' :=
  ⟨fun r hr h1 _ h3 hra => h.1 r hr (fun hq => by
      omega_nf) hra, h.2.1, h.2.2⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **The per-query clause of `S0CandSpec`** for `candQ ls`. -/
theorem candQ_spec {ls : Stmt} {κL : ℕ} (hLs : LSearchOK ls κL) :
    ∀ (P : Polygon) (W : ℕ) (X : MemCtx) (Ok : Polygon → Model → Prop) (J : Merge.Junction)
      (H : Host) (N₁ N₂ : NF) (E : ℕ) (c₀ c : Config) (L : Set ℝ) (z : Point),
      AEnv P W X Ok J H N₁ N₂ E c₀ → Aux P J N₂ c₀ → IInv W c₀ c →
      z ∈ J.left.set → z ≠ J.shared → z.2 ≤ J.right.top.2 →
      FreeAt J.whole z (dirOf (c.nreg qD)) →
      c.nreg zP < (chainModel J.whole).W.n →
      ProperPos (chainModel J.whole) (Qof P) P.n ⟨c.nreg zP, c.nreg zPh⟩ →
      Arrival (chainModel J.whole).W z (-dirOf (c.nreg qD)) (c.nreg zP)
        ((chainModel J.whole).param (Qof P) ⟨c.nreg zP, c.nreg zPh⟩) →
      c.nreg bL = 1 → c.nreg bR = 1 →
      AccOK P accA (ModB J (c.nreg bL) (c.nreg bR)) J.whole.radius z (dirOf (c.nreg qD)) L c →
      c.nreg ALLOC + qK κL * (c₀.nreg TLR + 1) ≤ W →
      IRS P W c₀ (candQ ls) c (qK κL * (c₀.nreg TLR + 1))
        (fun c' =>
          (∃ L', AccOK P accA (ModB J (c.nreg bL) (c.nreg bR)) J.whole.radius z
              (dirOf (c.nreg qD)) L' c' ∧ L ⊆ L' ∧
            (∀ τ ∈ L', τ ∈ L ∨ (0 < τ ∧ OnCB J.whole (rayPt z (dirOf (c.nreg qD)) τ))) ∧
            (∀ (rs : List (ℕ × ℕ × ℕ × ℕ × ℕ)), rs.length = rd c₀ bSweep 201 →
              StopRecsAt c₀.nmem (rd c₀ bSweep 200) rs →
              ∀ r ∈ rs, r.1 = c.nreg zP →
                (chainModel J.whole).param (Qof P) ⟨r.1, r.2.1⟩ =
                  (chainModel J.whole).param (Qof P) ⟨c.nreg zP, c.nreg zPh⟩ →
                dirOf r.2.2.2.2 = -dirOf (c.nreg qD) →
                ∀ τ, 0 < τ → stopOrig J (Qof P) N₂ r.2.2.1 r.2.2.2.1 r.2.2.2.2 =
                  rayPt z (dirOf (c.nreg qD)) τ → τ ∈ L') ∧
            (∀ j, j < 2 * N₂.nChords →
              tabOf J (Qof P) c₀.nmem (rd c₀ bSweep 302) j =
                some (c.nreg zP, (chainModel J.whole).param (Qof P) ⟨c.nreg zP, c.nreg zPh⟩) →
              endDir j = -dirOf (c.nreg qD) → endOrigin J (Qof P) N₂ j ∈ J.right.set →
              endOrigin J (Qof P) N₂ j ≠ J.shared → endOrigin J (Qof P) N₂ j ≠ J.right.top →
              ∀ τ, 0 < τ → endOrigin J (Qof P) N₂ j = rayPt z (dirOf (c.nreg qD)) τ →
                τ ∈ L')) ∧
          PartFr c c') := by
  intro P W X Ok J H N₁ N₂ E c₀ c L z hA hAux hI hz hzs hz2 _hfree hzP hzPp harr hbL hbR hacc
    hroom
  have hX : AuxCore P J N₂ c₀ := core_of_aux hAux
  rw [hbL, hbR] at hacc ⊢
  have hK := hA.hK
  
  set zp := c.nreg zP with hzpdef
  set zh := c.nreg zPh with hzhdef
  set d := c.nreg qD with hddef
  have hm : ∀ a, a < c₀.nreg ALLOC → c.nmem a = c₀.nmem a := hI.hm
  
  have hA0 := hI.hA
  
  -- copy the query position
  have hcost : cIn.length + (κL * (c₀.nreg TLR + 1) + (checkK + 2)) ≤
      qK κL * (c₀.nreg TLR + 1) := by
    have : cIn.length = 2 := by simp [cIn]
    rw [this]; unfold qK
    ring_nf <;> omega
  refine IRS.seq (K₁ := cIn.length) (K₂ := κL * (c₀.nreg TLR + 1) + (checkK + 2))
    (IRS.block cIn hI (cIn_ok _ _)) ?_ |>.mono hcost (fun _ h => h)
  rintro c₁ hI₁ hA₁ hA₁' rfl
  obtain ⟨v1E, v1H, k1⟩ := cIn_val c.nmem c.nreg
  set c₁ : Config := { c with nreg := regB c.nmem cIn c.nreg } with hc₁
  have nk1 : ∀ q, (q < sw 4020 ∨ sw 4021 < q) → c₁.nreg q = c.nreg q := fun q hq =>
    k1 q (by core_grind) (by core_grind)
  have fix1 : ∀ k, k < 700 → c₁.nreg (sw k) = c₀.nreg (sw k) := fun k hk =>
    hI₁.hin _ (by omega_nf)
  have hAc₁ : c₁.nreg ALLOC = c.nreg ALLOC := nk1 _ (by omega_nf)
  have hxE1 : c₁.nreg lsxE = zp := v1E
  have hxH1 : c₁.nreg lsxH = zh := v1H
  have hlog := hA.hlog
  rw [rd_sw, rd_sw] at hlog
  have hm1 : ∀ a, a < c₀.nreg ALLOC → c₁.nmem a = c₀.nmem a := hm
  have h6z : zh = 0 → 6 ≤ zp := fun h0 => query_h6 hz harr h0
  have hcongr : ∀ x : WPos, ∀ j, j < c₀.nreg (sw 301) →
      (lsPr P J c₁.nmem (c₁.nreg (sw 300)) (c₁.nreg (sw 40)) x j ↔
        lsPr P J c₀.nmem (rd c₀ bSweep 300) (c₀.nreg (sw 40)) x j) := fun x j hj => by
    rw [fix1 300 (by norm_num), fix1 40 (by norm_num)]
    exact lsPr_congr (E := c₀.nreg (sw 301)) (fun a ha => hm1 a (by omega)) hj
  have hTLR : c₁.nreg TLR = c₀.nreg TLR := fix1 601 (by norm_num)
  have hTBR : c₁.nreg TBR = c₀.nreg TBR := fix1 600 (by norm_num)
  -- the binary search
  have hsearch := hLs P W J c₀ c₁ hI₁ hK (hA.ctxW hI₁)
    (fun j hj => by
      rw [hTLR] at hj; rw [hTBR, hm1 _ (by have := hA.hTW; omega)]; exact hA.htab j hj)
    (by rw [hTBR, hTLR]; have := hA.hTW; omega)
    (by rw [fix1 301 (by norm_num), hTLR]; have := hA.hbigE; grind [rd_sw])
    (by grind)
    (by rw [fix1 40 (by norm_num), aenv_gW hA]; exact gW_lt_nat J)
    (fun j hj => by
      rw [fix1 301 (by norm_num)] at hj
      rw [fix1 300 (by norm_num), hm1 _ (by omega), hm1 _ (by omega)]
      exact log_posW hA hj)
    (by ram_grind)
    (fun i j hij hj hpr => by
      rw [fix1 301 (by norm_num)] at hj
      rw [hcongr _ i (by omega)]
      rw [hcongr _ j hj] at hpr
      exact log_mono hA _ hij hj hpr)
    (by rw [hTLR, hAc₁];  omega)
  rw [hTLR] at hsearch
  refine IRS.seq hsearch ?_
  rintro c₂ hI₂ hA₂ hA₂' ⟨ht0, hs1, hs2, k2, hal2, hm2⟩
  rw [fix1 301 (by norm_num)] at ht0 hs2
  rw [hxE1, hxH1] at hs1 hs2
  have hs1' : ∀ j, j < c₂.nreg lsI →
      lsPr P J c₀.nmem (rd c₀ bSweep 300) (c₀.nreg (sw 40)) ⟨zp, zh⟩ j := fun j hj =>
    (hcongr _ j (by omega)).1 (hs1 j hj)
  have hs2' : ∀ j, c₂.nreg lsI ≤ j → j < rd c₀ bSweep 301 →
      ¬ lsPr P J c₀.nmem (rd c₀ bSweep 300) (c₀.nreg (sw 40)) ⟨zp, zh⟩ j := fun j hj1 hj2 h =>
    hs2 j hj1 hj2 ((hcongr _ j hj2).2 h)
  have nk2 : ∀ q, bandOf q ∉ oracleBands → (q < sw 4000 ∨ sw 4021 < q) → q ≠ ALLOC →
      c₂.nreg q = c.nreg q := fun q hb hq hqa => by
    rw [k2 q hb (by unfold LSet sw at *; omega) hqa]
    grind [sw]
  have hfr2 : FrQ c c₂ := ⟨fun r hr hq hra => by
      rw [k2 r hr (fun h => hq (by right; unfold LSet at h; grind [sw])) hra]
      exact k1 r (fun h => hq (by subst h; omega_nf))
        (fun h => hq (by subst h; omega_nf)),
    by omega, fun a ha => by grind⟩
  have hd₂ : c₂.nreg qD = d := nk2 qD (nob (by omega_nf) (by omega_nf))
    (by omega_nf) (by omega_nf)
  have hacc₂ : AccOK P accA (ModB J 1 1) J.whole.radius z (dirOf d) L c₂ :=
    hacc.transport (fun j hj => nk2 (accA + j) (nob (by omega_nf)
      (by omega_nf)) (by omega_nf) (by omega_nf))
  have hxE2 : c₂.nreg lsxE = zp := by
    rw [k2 _ (nob (by omega_nf) (by omega_nf))
      (by omega_nf) (by omega_nf)]; exact hxE1
  have hxH2 : c₂.nreg lsxH = zh := by
    rw [k2 _ (nob (by omega_nf) (by omega_nf))
      (by omega_nf) (by omega_nf)]; exact hxH1
  have h301 : c₂.nreg (sw 301) = rd c₀ bSweep 301 := hI₂.hin _ (by omega_nf)
  -- the final assembly from the completeness of the slot read
  have fin : ∀ c' L', AccOK P accA (ModB J 1 1) J.whole.radius z (dirOf d) L' c' → L ⊆ L' →
      (∀ τ ∈ L', τ ∈ L ∨ (0 < τ ∧ OnCB J.whole (rayPt z (dirOf d) τ))) →
      HC P J c₀ z zp zh d L' → FrQ c c' →
      ((∃ L', AccOK P accA (ModB J 1 1) J.whole.radius z (dirOf d) L' c' ∧ L ⊆ L' ∧
            (∀ τ ∈ L', τ ∈ L ∨ (0 < τ ∧ OnCB J.whole (rayPt z (dirOf d) τ))) ∧
            (∀ (rs : List (ℕ × ℕ × ℕ × ℕ × ℕ)), rs.length = rd c₀ bSweep 201 →
              StopRecsAt c₀.nmem (rd c₀ bSweep 200) rs →
              ∀ r ∈ rs, r.1 = zp →
                (chainModel J.whole).param (Qof P) ⟨r.1, r.2.1⟩ =
                  (chainModel J.whole).param (Qof P) ⟨zp, zh⟩ →
                dirOf r.2.2.2.2 = -dirOf d →
                ∀ τ, 0 < τ → stopOrig J (Qof P) N₂ r.2.2.1 r.2.2.2.1 r.2.2.2.2 =
                  rayPt z (dirOf d) τ → τ ∈ L') ∧
            (∀ j, j < 2 * N₂.nChords →
              tabOf J (Qof P) c₀.nmem (rd c₀ bSweep 302) j =
                some (zp, (chainModel J.whole).param (Qof P) ⟨zp, zh⟩) →
              endDir j = -dirOf d → endOrigin J (Qof P) N₂ j ∈ J.right.set →
              endOrigin J (Qof P) N₂ j ≠ J.shared → endOrigin J (Qof P) N₂ j ≠ J.right.top →
              ∀ τ, 0 < τ → endOrigin J (Qof P) N₂ j = rayPt z (dirOf d) τ →
                τ ∈ L')) ∧
          PartFr c c') := fun c' L' hacc' hLL hsnd hHC hfr => by
    obtain ⟨hst, htb⟩ := compl_of hA hX harr hHC
    exact ⟨⟨L', hacc', hLL, hsnd, hst, htb⟩, frQ_partFr hfr⟩
  refine IRS.ite (fun ht => ?_) (fun ht => ?_)
  · rw [h301] at ht
    refine (check_irs hA hX hI₂ hz hzs hz2 hzP hzPp (by grind) hxE2 hxH2 ht
      hs1' hs2' (by rw [hd₂]; exact hacc₂) (by
        omega)).mono le_rfl ?_
    rintro c' ⟨L', hacc', hLL, hsnd, hHC, hfr⟩
    rw [hd₂] at hacc' hsnd hHC
    exact fin c' L' hacc' hLL hsnd hHC (hfr2.trans hfr)
  · rw [h301] at ht
    refine IRS.skip (K := checkK) hI₂ (fin c₂ L hacc₂ le_rfl (fun τ h => Or.inl h) ?_ hfr2)
    intro i hi h1 h2 _ o τ _ _ _
    exfalso
    have := search_eq hA hs1' hs2' hi (key_of_match h1 h2)
    omega

/-- **`InitSpec` for a larger cost function.** -/
theorem initSpec_mono {init : Stmt} {Aux' : Polygon → Merge.Junction → NF → Config → Prop}
    {κ κ' : ℕ → ℕ} (h : InitSpec init Aux' κ) (hκ : ∀ D, κ D ≤ κ' D) :
    InitSpec init Aux' κ' := by
  refine ⟨fun P W X Ok J H N₁ N₂ E c hw hA hroom => ?_, h.2⟩
  have hle : κ (c.nreg (sw 6)) * (rd c bSweep 201 + rd c bSweep 301 + 2 * N₂.nChords + 1) *
      (c.nreg TLR + 1) ≤ κ' (c.nreg (sw 6)) *
        (rd c bSweep 201 + rd c bSweep 301 + 2 * N₂.nChords + 1) * (c.nreg TLR + 1) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (hκ _))
  obtain ⟨c', k, ex, hk, hfr, hreg, hx⟩ := h.1 P W X Ok J H N₁ N₂ E c hw hA
    (le_trans (Nat.add_le_add_left hle _) hroom)
  grind

/-- **`S0CandSpec` from the initialisation contract.** -/
theorem s0CandSpec_of (hI : InitPartSpec) : S0CandSpec := by
  obtain ⟨initC, κI, hInit⟩ := hI
  obtain ⟨ls, κL, hLs⟩ := lsearchOK_of lsearchSpec
  refine ⟨initC, candQ ls, Aux, fun D => κI D + qK κL,
    initSpec_mono hInit (fun D => Nat.le_add_right _ _),
    fun P W J N₂ c₀ c h hI => aux_iinv h hI, ?_⟩
  intro P W X Ok J H N₁ N₂ E c₀ c L z hA hAux hI hz hzs hz2 hfree hzP hzPp harr hbL hbR hacc hroom
  have hle : qK κL * (c₀.nreg TLR + 1) ≤ (κI (c₀.nreg (sw 6)) + qK κL) * (c₀.nreg TLR + 1) :=
    Nat.mul_le_mul_right _ (Nat.le_add_left _ _)
  exact (candQ_spec hLs P W X Ok J H N₁ N₂ E c₀ c L z hA hAux hI hz hzs hz2 hfree hzP hzPp
    harr hbL hbR hacc (le_trans (Nat.add_le_add_left hle _) hroom)).mono hle (fun _ h => h)

end

end S0C

end SweepIo

end Chazelle.Core
