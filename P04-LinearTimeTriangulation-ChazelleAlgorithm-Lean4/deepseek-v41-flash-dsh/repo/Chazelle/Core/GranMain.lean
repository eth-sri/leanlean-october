module

public import Chazelle.Golf

public import Chazelle.Core.GranCost
public import Chazelle.Core.GranRamLoop

/-!
# WP-F, part 19: the main path

`mainStmt = initStmt; loopStmt; outStmt` (`main_exec`): from a nonempty γ-semigranular submap
with degrees `≤ D`, the chord list of a γ-granular submap with degrees `≤ D` is written below the
allocator, ready for the construction of its normal form.
-/

namespace Chazelle.Core

namespace Gran

open Machine Machine.Stmt Programs SignK

@[expose] public section

/-- Initialisation, worklist, output. -/
def mainStmt : Stmt := .seq initStmt (.seq loopStmt outStmt)

theorem wrS_loop : wrS Bbody loopStmt = true := by
  simp only [loopStmt, wrS]; exact wrS_body

theorem natOnly_loop : natOnly loopStmt = true := ⌖

theorem natOnly_out : natOnly outStmt = true := ⌖


/-- **The main path.** -/
theorem main_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c)
    {MD NFH D γ : ℕ} {M : Model} {N : NF}
    (h0 : c.nreg 90000 = MD) (h1 : c.nreg 90001 = NFH) (h2 : c.nreg 90002 = D)
    (h3 : c.nreg 90003 = γ) (hG : GoodEnv P) (hWh : hostWords P.n ≤ W)
    (hwf : ModelDescWF P (c.nreg ALLOC) c.nmem MD) (hMD : ModelDescAt c.nmem MD (Qof P) M)
    (hGM : GoodModel M) (hNW : NFWithin c.nmem NFH (c.nreg ALLOC) N) (hNF : IsNF M (Qof P) N)
    (hne : (N.F M (Qof P)).Nonempty)
    (hdeg : M.DegLe (N.F M (Qof P)) D) (hsemi : M.Semigranular (N.F M (Qof P)) γ)
    (hroom : c.nreg ALLOC + costMain N.nChords N.arcs.length N.nRegions D ≤ W) :
    ∃ c' k L, Exec P W mainStmt c c' k ∧ k ≤ costMain N.nChords N.arcs.length N.nRegions D ∧
      c'.nreg 90000 = MD ∧ c'.nreg 90002 = D ∧ c'.nreg 90095 = L.length ∧
      L.length ≤ N.nChords ∧
      ChordListAt c'.nmem (c'.nreg 90028) L ∧ c'.nreg 90028 + 3 * L.length ≤ c'.nreg ALLOC ∧
      ChordTriplesOK M (Qof P) L ∧ lset M (Qof P) L ⊆ N.F M (Qof P) ∧
      M.DegLe (lset M (Qof P) L) D ∧ M.Granular (lset M (Qof P) L) γ ∧
      GF (c.nreg ALLOC) c c' k := by
  obtain ⟨reg, hRC, hCS, -, hRO, -⟩ := hNF.2.2.2
  have hK1 : 1 ≤ N.nChords := by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨i, hi, -⟩ := mem_F_iff.1 hx
    omega
  have hroomI := room_le N.nChords N.arcs.length N.nRegions D
  obtain ⟨c₈, k₈, e₈, hk₈, hMS, hI, hE, hDim, r52, r00, -, r02, -, r10, r13, r28, hal, G₈⟩ :=
    init_exec (P := P) hw h0 h1 h2 h3 hG hWh hwf hMD hGM hNW hNF hRC hCS hRO hne hdeg hsemi
      (by unfold costMain at hroom; omega)
  set E := envOf M P N reg γ D (c.nmem MD) (c.nmem (MD + 3)) with hEd
  set d := dmOf N.nChords N.arcs.length N.nRegions D (c.nreg ALLOC) with hd
  set K := N.nChords with hKd
  -- the worklist
  obtain ⟨c₉, k₉, st', e₉, hk₉, hMS', hI', htop, hR₉⟩ := loop_exec (P := P) hE hMS hI hDim
    le_rfl r52
  have FS₉ := exec_frameS e₉ wrS_loop
  have G₉ : GF (c.nreg ALLOC) c₈ c₉ k₉ := GF.of_nat e₉ natOnly_loop wrS_loop
    (fun r hr => by
      simp only [Bbody, Bool.or_eq_true, decide_eq_true_eq] at hr
      exact band9_gran (⋄) (by omega))
    (fun a ha => Ρ hMS'.low a ha, hMS.low a ha)
  -- the output
  have hNA := nf_areas hNW
  set CB := c.nmem (NFH + 3) with hCBd
  have hCB : CB + 5 * K ≤ c.nreg ALLOC := by
    have := hNA.2.1 (K - 1) (⋄)
    have e5 : 5 * (K - 1) + 5 = 5 * K := ⋄
    omega
  have hd0 : d.b0 = c.nreg ALLOC := rfl
  have hdK : d.K = K := rfl
  have hLB : d.oList + 3 * K = d.oEnd := rfl
  have hoL : K ≤ d.oList := by
    simp only [hd, dmOf, Dm.oList, Dm.oTmp, Dm.oStk, Dm.oPz, Dm.oEg, Dm.oPrv, Dm.oNxt, Dm.oCnt,
      Dm.oEx]
    omega
  have hbase := hDim.base
  have hOE : OutEnv W K CB (c.nreg ALLOC + d.oList) (c.nreg ALLOC) N st'.live c₉ :=
    { r30 := hMS'.cst.bLive
      r19 := hMS'.cst.one
      r21 := hMS'.cst.two
      r10 := by rw [hR₉ _ (⌖), r10]
      hlive := fun u hu => hMS'.enc.live u hu
      hl01 := fun u hu => hI'.live01 u hu
      hrec := fun u hu => by
        have hb := hNA.2.1 u hu
        have hr := (hNW.nfAt.2.2.2.2.2.1 u hu)
        refine ⟨?_, ?_, ?_⟩
        · rw [hMS'.low _ (⋄)]; exact hr.1
        · rw [hMS'.low _ (⋄)]; exact hr.2.1
        · rw [hMS'.low _ (⋄)]; exact hr.2.2.1
      hCB := ⋄
      hb0 := ⋄
      hW := ⋄ }
  obtain ⟨c₁₀, k₁₀, e₁₀, hk₁₀, r95, hlist, hmem, FS₁₀⟩ := out_exec (P := P) hMS'.wb hOE
    (by rw [hR₉ _ (⌖), r13]) (by rw [hR₉ _ (by decide), r28])
    (by unfold costMain at hroom; have := dmOf_oEnd N.nChords N.arcs.length N.nRegions D 0; omega)
  have G₁₀ : GF (c.nreg ALLOC) c₉ c₁₀ k₁₀ := GF.of_nat e₁₀ natOnly_out wrS_outStmt
    (fun r hr => by
      simp only [Binit, decide_eq_true_eq] at hr
      exact band9_gran (⋄) (by omega))
    (fun a ha => hmem a (by left; omega))
  have q28 : c₁₀.nreg 90028 = c.nreg ALLOC + d.oList := by
    rw [FS₁₀.1 _ (⌖), hR₉ _ (by decide), r28]
  have qA : c₁₀.nreg ALLOC = c₈.nreg ALLOC := by
    rw [FS₁₀.1 _ (⌖), hR₉ _ (by decide)]
  obtain ⟨hFeq, hok⟩ := outList_ok (st := st') hE
  obtain ⟨hgran, hdg⟩ := hI'.final hE htop
  have hlset : lset M (Qof P) (outList N st'.live K) = st'.F E := hFeq
  have hlen := outList_length_le N st'.live K
  refine ⟨c₁₀, _, outList N st'.live K, .seq e₈ (.seq e₉ e₁₀), ?_, ?_, ?_, r95, hlen,
    by rw [q28]; exact hlist, by rw [q28, qA]; omega, hok, ?_, ?_, ?_,
    (G₈.trans (G₉.trans G₁₀)).mono le_rfl⟩
  · have hm : st0 E d c₈.nmem = initSt E _ _ _ _ := rfl
    have hmeas : (st0 E d c₈.nmem).meas E = K + (D + 1) * K := by
      simp only [St.meas, st0, initSt]; rfl
    have hED : E.D = D := rfl
    rw [hmeas, hED] at hk₉
    unfold costMain
    omega
  · rw [FS₁₀.1 _ (⌖), hR₉ _ (by decide), r00]
  · rw [FS₁₀.1 _ (⌖), hR₉ _ (by decide), r02]
  · rw [hlset]; exact St.F_sub
  · rw [hlset]; exact hdg
  · rw [hlset]; exact hgran

end

end Gran

end Chazelle.Core
