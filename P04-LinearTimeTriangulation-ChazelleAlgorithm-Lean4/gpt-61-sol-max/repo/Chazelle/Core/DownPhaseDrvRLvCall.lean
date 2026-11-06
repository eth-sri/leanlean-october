module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.DownPhaseDrvRLvD

/-!
# Down-phase driver (RAM side): one level, the calls of the region loop

`callH`, `callR`, `callX`: the host RAM, the region procedure and the extraction of region `j`,
from their contracts (`HostMeets`, `RegMeets`, `ExtMeets`) with the arguments in clean form;
`len_le_of_kept`, `regOK_len`: a kept list has at most `lvNch μ` triples (Lemma 2.3).
-/

namespace Chazelle.Core

namespace DrvR

open Machine Machine.Stmt Programs SignK BuildRam
open BuildNF (codeLe)

@[expose] public section

section exec

variable {P : Polygon} {W : ℕ}

theorem nRegions_bnf {M : Model} {Q : Polygon} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ} :
    (BuildNF.buildNF M Q L E).nRegions = L.length + 1 := by
  simp [NF.nRegions, BuildNF.buildNF]

open Classical in
/-- **The host RAM of region `j`.** -/
theorem callH {sH : Stmt} {κH : ℕ} (hH : HostMeets sH κH) (c : Config) (hw : WordsBounded W c)
    {L : List (ℕ × ℕ × ℕ)} {E : List ℕ} (hG : GoodEnv P) (hWh : hostWords P.n ≤ W) (hL : L ≠ [])
    (hok : ChordTriplesOK (interiorModel (Qof P)) (Qof P) L)
    (hperm : E.Perm (List.range (2 * L.length)))
    (hsort : E.Pairwise (codeLe (interiorModel (Qof P)) (Qof P) L))
    (hdeg : (interiorModel (Qof P)).DegLe
      ((BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).F (interiorModel (Qof P)) (Qof P)) 4)
    (hnf : NFWithin c.nmem (c.nreg 215000) (c.nreg ALLOC)
      (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E))
    (hli : c.nreg 215002 ≤ 1) (hli' : c.nreg 215002 = 1 ↔ Mountain.LeftInside (Qof P))
    {j : ℕ} (hj0 : c.nreg 215001 = j) (hj : j < L.length + 1)
    (hroom : c.nreg ALLOC + κH ≤ W) :
    ∃ c' k, Exec P W sH c c' k ∧ k ≤ κH ∧ Frame {bDownDrv} c c' k ∧
      (∀ q, bandOf q = bDownDrv → (q < 215000 ∨ 216000 ≤ q) → c'.nreg q = c.nreg q) ∧
      c.nreg ALLOC ≤ c'.nreg 215010 ∧
      c'.nreg 215010 + 3 * (regHost (decide (Mountain.LeftInside (Qof P))) (Qof P).n
        (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E) j).length + 1 ≤ c'.nreg ALLOC ∧
      HostAt c'.nmem (c'.nreg 215010) (regHost (decide (Mountain.LeftInside (Qof P))) (Qof P).n
        (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E) j) ∧
      c'.nreg 215012 = ((regHost (decide (Mountain.LeftInside (Qof P))) (Qof P).n
        (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E) j).pts (Qof P).n).length := by
  obtain ⟨c', k, ex, hk, ⟨hkeep, hpost⟩, hfr⟩ := hH P W c hw
    ⟨hG, hWh, hli, hli', L, E, hL, hok, hperm, hsort, hdeg, hnf,
      by simp_all [nRegions_bnf] ⟩ hroom
  have hdec : decide (c.nreg 215002 = 1) = decide (Mountain.LeftInside (Qof P)) :=
    decide_eq_decide.mpr hli'
  obtain ⟨h1, h2, h3, -, h5⟩ := hpost L E hL hok hperm hsort hnf.nfAt
  rw [hdec, hj0] at h2 h3 h5
  exact ⟨c', k, ex, hk, hfr, hkeep, h1, h2, h3, h5⟩

/-- **The region procedure of region `j`.** -/
theorem callR {O : OracleIface} {sR : Stmt} {κR : ℕ} (hR : RegMeets O sR κR) (c : Config)
    (hw : WordsBounded W c) (hG : GoodEnv P) (hWh : hostWords P.n ≤ W)
    {HB μ γ₀ g : ℕ} {H : Host}
    (h00 : c.nreg 219200 = HB) (h01 : c.nreg 219201 = (H.pts (Qof P).n).length)
    (h02 : c.nreg 219202 = μ) (h03 : c.nreg 219203 = 2 ^ μ) (h04 : c.nreg 219204 = γ₀)
    (h05 : c.nreg 219205 = g)
    (hX : (gradeCtx O).holds P c.nmem g (c.nreg ALLOC)) (h7 : 7 ≤ μ) (hμg : μ ≤ c.nmem g)
    (hg0 : 2 * gradeGran μ ≤ γ₀) (hg1 : 128 ≤ γ₀) (hg2 : γ₀ ≤ 4096 * 2 ^ Cost.ceilBeta μ)
    (hcap : γ₀ + 129 ≤ (gradeCtx O).cap P c.nmem g)
    (hHA : Robust (c.nreg ALLOC) c.nmem (fun m => HostAt m HB H))
    (hHB : HB + 3 * H.length + 1 ≤ c.nreg ALLOC) (h20 : H.length ≤ 20)
    (hwf : HostWF (Qof P).n H) (hreg : HostRegular (Qof P).n H) (hsimp : (H.poly (Qof P)).Simple)
    (h3 : 3 ≤ (H.pts (Qof P).n).length) (hrun : ∀ a ℓ, HostItem.run a ℓ ∈ H → ℓ ≤ 2 * 2 ^ μ)
    (hroom : c.nreg ALLOC + κR * (lemma41Nat μ + 1) ≤ W) :
    ∃ c' k, Exec P W sR c c' k ∧ k ≤ κR * (lemma41Nat μ + 1) ∧ Frame drvBands c c' k ∧
      (∀ q, bandOf q = bDownDrv → (q < 218000 ∨ 220000 ≤ q) → c'.nreg q = c.nreg q) ∧
      c.nreg ALLOC ≤ c'.nreg 219210 ∧ c.nreg ALLOC ≤ c'.nreg 219211 ∧
      γ₀ ≤ c'.nreg 219212 ∧ c'.nreg 219212 ≤ γ₀ + 128 ∧
      ModelDescWF P (c'.nreg ALLOC) c'.nmem (c'.nreg 219210) ∧
      Robust (c'.nreg ALLOC) c'.nmem
          (fun m => m (c'.nreg 219210) = 0 ∧
            ChainDescAt m (c'.nreg 219210 + 1) (Qof P) H (hostChainOf (Qof P) H h3) ∧
            m (c'.nreg 219210 + 1) = HB) ∧
        ∃ N, NFWithin c'.nmem (c'.nreg 219211) (c'.nreg ALLOC) N ∧
          IsCanonicalNF (chainModel (hostChainOf (Qof P) H h3)) (Qof P) N (c'.nreg 219212)
            regCap := by
  obtain ⟨c', k, ex, hk, ⟨hkeep, a10, a11, a12, a12', hwfd, hpost⟩, hfr⟩ := hR P W c hw
    ⟨hG, hWh, by ram_simp, by omega, by omega_nf,
      by ram_simp, by omega_nf, by omega,
      by omega_nf, by omega_nf,
      H, by ram_simp, by omega, h20, hwf, hreg, hsimp, h01,
      by omega, by grind⟩
    (by simp_all)
  have hk' : k ≤ κR * (lemma41Nat μ + 1) := by
    grind
  obtain ⟨hrob, N, hN, hc⟩ := hpost H (hostChainOf (Qof P) H h3) (by rw [h00]; exact hHA.holds)
    rfl rfl (hostChainOf_m _ _ h3)
  grind

open Classical in
/-- **The extraction of region `j`.** -/
theorem callX {sX : Stmt} {κX : ℕ} (hX : ExtMeets sX κX) (c : Config) (hw : WordsBounded W c)
    {L : List (ℕ × ℕ × ℕ)} {E : List ℕ} {reg : ℕ → Set Point} (hG : GoodEnv P)
    (hWh : hostWords P.n ≤ W) (hL : L ≠ [])
    (hok : ChordTriplesOK (interiorModel (Qof P)) (Qof P) L)
    (hperm : E.Perm (List.range (2 * L.length)))
    (hsort : E.Pairwise (codeLe (interiorModel (Qof P)) (Qof P) L))
    (hdeg : (interiorModel (Qof P)).DegLe
      ((BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).F (interiorModel (Qof P)) (Qof P)) 4)
    (hregs : Restore.NFRegs (interiorModel (Qof P)) (Qof P)
      (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E) reg)
    (hnf : NFWithin c.nmem (c.nreg 217000) (c.nreg ALLOC)
      (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E))
    (hli : c.nreg 217002 ≤ 1) (hli' : c.nreg 217002 = 1 ↔ Mountain.LeftInside (Qof P))
    {j HB MD : ℕ} (hj0 : c.nreg 217001 = j) (hj : j < L.length + 1)
    (h03 : c.nreg 217003 = HB) (h05 : c.nreg 217005 = MD)
    (hHA : Robust (c.nreg ALLOC) c.nmem (fun m => HostAt m HB
      (regHost (decide (Mountain.LeftInside (Qof P))) (Qof P).n
        (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E) j)))
    (hHB : HB + 3 * (regHost (decide (Mountain.LeftInside (Qof P))) (Qof P).n
        (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E) j).length + 1 ≤ c.nreg ALLOC)
    (h04 : c.nreg 217004 = ((regHost (decide (Mountain.LeftInside (Qof P))) (Qof P).n
        (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E) j).pts (Qof P).n).length)
    {C : Chain} (hCP : C.P = (regHost (decide (Mountain.LeftInside (Qof P))) (Qof P).n
        (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E) j).poly (Qof P))
    (hCs : C.s = 0) (hCm : C.m + 1 = C.P.n)
    (hmwf : ModelDescWF P (c.nreg ALLOC) c.nmem MD)
    (hmd : Robust (c.nreg ALLOC) c.nmem (fun m => m MD = 0 ∧
      ChainDescAt m (MD + 1) (Qof P) (regHost (decide (Mountain.LeftInside (Qof P))) (Qof P).n
        (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E) j) C ∧ m (MD + 1) = HB))
    {NR : NF} (hNR : NFWithin c.nmem (c.nreg 217006) (c.nreg ALLOC) NR)
    (hNRi : IsNF (chainModel C) (Qof P) NR)
    (hroom : c.nreg ALLOC + κX * (NR.chords.length + 1) ≤ W) :
    ∃ c' k, Exec P W sX c c' k ∧ k ≤ κX * (NR.chords.length + 1) ∧
      Frame {bDownDrv, bSign, bLocate, bBuild, bSort} c c' k ∧
      (∀ q, bandOf q = bDownDrv → (q < 217000 ∨ 218000 ≤ q) → c'.nreg q = c.nreg q) ∧
      ∃ Lx : List (ℕ × ℕ × ℕ),
          c.nreg ALLOC ≤ c'.nreg 217010 ∧ c'.nreg 217010 + 3 * Lx.length ≤ c'.nreg ALLOC ∧
          c.nreg ALLOC ≤ c'.nreg 217012 ∧ c'.nreg 217012 + 2 * Lx.length ≤ c'.nreg ALLOC ∧
          c'.nreg 217011 = Lx.length ∧ ChordListAt c'.nmem (c'.nreg 217010) Lx ∧
          {x | ∃ y ∈ Lx, x = (recOf y).toSet (interiorModel (Qof P)) (Qof P)} =
            Extract.kept (reg j) (NR.F (chainModel C) (Qof P)) ∧
          (Lx.map fun y => (recOf y).toSet (interiorModel (Qof P)) (Qof P)).Nodup ∧
          (∀ y ∈ Lx, (recOf y).Attached (interiorModel (Qof P)) (Qof P) ∧ y.1 < (Qof P).n) ∧
          ∀ q, q < 2 * Lx.length →
            c'.nmem (c'.nreg 217012 + q) = keyBkt (Qof P)
              (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E) (endPos Lx q) ∧
            ∃ j' ∈ ((BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).region j).arcs,
              OnArcKey (Qof P) (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E) j'
                (endPos Lx q) := by
  
  have hmdA : Robust (c.nreg ALLOC) c.nmem (fun m => ModelDescAt m MD (Qof P) (chainModel C)) :=
    fun m' hm' => Or.inl ⟨(hmd m' hm').1, _, C, (hmd m' hm').2.1, rfl⟩
  have hcd : Robust (c.nreg ALLOC) c.nmem (fun m => ChainDescAt m (MD + 1) (Qof P)
      (regHost (decide (Mountain.LeftInside (Qof P))) (Qof P).n
        (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E) j) C) :=
    fun m' hm' => (hmd m' hm').2.1
  have hNR0 : c.nmem (c.nreg 217006) = NR.chords.length := hNR.nfAt.1
  obtain ⟨c', k, ex, hk, ⟨hkeep, hpost⟩, hfr⟩ := hX P W c hw
    ⟨hG, hWh, hli, hli', L, E, C, NR, hL, hok, hperm, hsort, hdeg, hnf,
      by simp_all [nRegions_bnf] <;> omega_nf, by ram_simp,
      by ram_grind, by ram_simp,
      by ram_simp, hCs, hCm, by ram_simp, by ram_simp,
      by ram_simp, hNR, hNRi⟩
    (by ram_grind)
  have hk' : k ≤ κX * (NR.chords.length + 1) := by
    have : k ≤ κX * (c.nmem (c.nreg 217006) + 1) := hk
    rwa [hNR0] at this
  obtain ⟨Lx, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10⟩ := hpost L E C NR reg hL hok hperm hsort
    hnf.nfAt hregs (by ram_simp) hCs hCm hNR.nfAt hNRi
  rw [hj0] at x7 x10
  exact ⟨c', k, ex, hk', hfr, hkeep, Lx, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10⟩

theorem len_le_of_kept {α : Type*} {Lx : List α} {f : α → Set Point}
    {S F : Set (Set Point)} (hS : {x | ∃ y ∈ Lx, x = f y} = S) (hnd : (Lx.map f).Nodup)
    (hSF : S ⊆ F) (hF : F.Finite) : Lx.length ≤ F.ncard := by
  classical
  have e : {x | ∃ y ∈ Lx, x = f y} = ((Lx.map f).toFinset : Set (Set Point)) := by
    ext x; simp [eq_comm]
  have h1 : ({x | ∃ y ∈ Lx, x = f y} : Set (Set Point)).ncard = Lx.length := by
    rw [e, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd, List.length_map]
  rw [← h1, hS]
  exact Set.ncard_le_ncard hSF hF

/-- **The kept list of a region is short** (Lemma 2.3). -/
theorem regOK_len {P : Polygon} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ} {reg : ℕ → Set Point}
    {r μ : ℕ} {C : Chain} {NR : NF} {γR : ℕ} {Lx : List (ℕ × ℕ × ℕ)}
    (h : RegOK P L E reg (3 * 2 ^ (Cost.ceilBeta μ + 10)) r C NR γR Lx) (hP : C.P.Simple)
    (hm : C.m + 1 ≤ 10 * 2 ^ μ + 8) : Lx.length ≤ lvNch μ := by
  obtain ⟨-, -, -, hc, hγ, -, hk, hnd, -, -⟩ := h
  have h1 := nch_le hP hc hγ hm rfl
  have hF : (NR.F (chainModel C) (Qof P)).Finite := hc.1.1.1
  have h2 := len_le_of_kept hk hnd (fun x hx => hx.1) hF
  rw [Gran.ncard_F hc.1] at h2
  exact h2.trans h1

end exec

end

end DrvR

end Chazelle.Core
