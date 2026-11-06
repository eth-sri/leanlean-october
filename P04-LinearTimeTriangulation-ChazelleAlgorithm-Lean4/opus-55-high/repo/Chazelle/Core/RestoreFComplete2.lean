module

public import Chazelle.MacT
public import Chazelle.Core.RestoreFKind1
public import Chazelle.Core.OracleRamLoad
public import Chazelle.Core.DownPhaseDrvBCorner
public import Chazelle.Core.DownPhaseDrvDRound3
public import Chazelle.Core.DownPhaseOracleCuR1
public import Chazelle.Core.ShootCutGrade
public import Chazelle.Core.NFDecompBfs
public import Chazelle.Core.OracleQueryExec
public import Chazelle.Core.DownPhaseDrvBTopMain
public import Chazelle.Core.SweepPrimJun
public import Chazelle.Core.ShotListCut
public import Chazelle.Core.ShotListGLeaf
public import Chazelle.Core.SweepIoHoles
public import Chazelle.Core.OraclePrepMain
public import Chazelle.Core.SweepChainT

namespace Chazelle.Core
namespace Restore
@[expose] public section
open Set Filter Topology
open Chazelle.Chain (sideInArc SideAttach sidePt)
open DownHost ArcT

/-- **The region faced just after a walk vertex.** -/
theorem faced_after {M : Model} (hGM : GoodModel M) {Q : Polygon} {F : Set ztf}
    (hF : M.ChordFamily Q F) {p : ℕ} (hp : p < M.W.n) :
    ∃ U ∈ M.regions F, ∀ᶠ ε in 𝓝[>] (0 : ℝ), M.Faces p ε U := by
  zubm
  obtain ⟨t', ⟨ht0, ht1⟩, hfree⟩ := hM.exists_after hF.2.1 hF.1 hp le_rfl one_pos
  simp only [add_zero] at hfree
  set x : ℝ := p + t' / 2 with hx
  have hxc : ¬ M.IsCut F x := fun h => hfree x h ztbcx
  have hx0 : ztrzq := by_grind
  obtain ⟨U, hU, l, r, harc, hin⟩ := WalkEmbed.exists_arc_around hGM hF hx0 hxc
  refine ztraf
  -- the ends of the arc are not in `(p, p + t']`
  have hlr : (l ≤ p ∨ (p : ℝ) + t' < l) ∧ (r ≤ p ∨ (p : ℝ) + t' < r) := by
    obtain ⟨-, -, -, -, hc, -⟩ := harc
    grind
  have hconst : ∀ z : ℝ, (p : ℝ) < z → z ≤ p + t' → sideInArc l r z := by
    intro z hz1 hz2
    have e1 : l < z ↔ l < x := by
      grind
    have e2 : z < r ↔ x < r := by
      grind
    zucrh
    simp_all
  filter_upwards [Ioo_mem_nhdsGT ht0] with ε hε
  exact harc.2.2.2.2.2.2 p ε hp hε.1 by_grind (hconst _ by_simp_all
    by_grind)

/-- **Unwrapped offsets**: from the walk vertex `s`, the key `k` steps and `t` further on. -/
theorem unwrap_off {n s k : ℕ} {t : ℝ} (hs : s < n) (ht0 : 0 ≤ t) (hkn : (k : ℝ) + t < n) :
    unwrapK n s ztwvp = s + k + t := by
  have hk : k < n := by
    zujvw

  unfold unwrapK
  by_cases h : s + k < n
  · rw [Nat.mod_eq_of_lt h, ite_eq_left by_grind]; simp
  · have e : ztnj % n = s + k - n := by
      zul
    rw [e, ite_eq_right (by
      have : ((s + k - n : ℕ) : ℝ) = (s : ℝ) + k - n := by_simp_all
      grind)]
    rw [Nat.cast_sub by_omega]; grind

/-- **A key strictly inside a piece's walk.** -/
theorem off_sideInArc {n s m k : ℕ} {t : ℝ} (hs : s < n) (hmn : m < n) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (h0 : 0 < (k : ℝ) + t) (hm : (k : ℝ) + t < m) :
    sideInArc (s : ℝ) ((ztbnl % n : ℕ) : ℝ) ztwvp := by
  have hnR : (m : ℝ) < n := by_simp_all
  zufhd

  have he := unwrap_off (k := m) (t := 0) hs le_rfl by_linarith
  have hy := unwrap_off (k := k) (t := t) hs ht0 by_linarith
  zujof
  have hb : ztwxl :=
    ⟨Nat.cast_nonneg _, by exact_mod_cast Nat.mod_lt _ by_omega⟩
  have hyb : ztwuc := by
    have hkn : k < n := by
      zujvw

    have h1 : ztycd := Nat.mod_lt _ by_omega
    have h1' : ztxpi := by exact_mod_cast h1
    grind
  have hm0 : (0 : ℝ) < m := by_linarith
  exact (cyc_unwrap hs0 hs0 hb hyb (by rw [unwrapK_self, he]; linarith)).2
    ⟨by rw [unwrapK_self, hy]; linarith, by_grind⟩

/-- **A walk vertex in the closed key interval of a piece** is `d ≤ m` steps from its start. -/
theorem closed_offset {n s m p : ℕ} (hs : s < n) (hmn : m < n) (hm : 0 < m) (hp : p < n)
    (h : ClosedArc (s : ℝ) ((ztbnl % n : ℕ) : ℝ) (p : ℝ)) :
    ∃ d, d ≤ m ∧ ztbuf % n = p := by
  zufhd

  have he := unwrap_off (k := m) (t := 0) hs le_rfl by_simp_all
  zujof
  have hb : ztwxl :=
    ⟨Nat.cast_nonneg _, by exact_mod_cast Nat.mod_lt _ by_omega⟩
  have hpb : 0 ≤ (p : ℝ) ∧ (p : ℝ) < n := ⟨Nat.cast_nonneg p, by_simp_all⟩
  have hne : (s : ℝ) ≠ ((ztbnl % n : ℕ) : ℝ) := by
    zuhgj
    have h'' : s = ztbnl % n := by exact_mod_cast h'
    zuhtk
    · rw [Nat.mod_eq_of_lt hw] at h''; omega
    · zvnae at h''; omega
  obtain ⟨h1, h2⟩ := (closedArc_unwrap hs0 hb hpb hne).1 h
  zvmxm at h2
  -- the unwrapped vertex is `p` or `p + n`
  obtain ⟨Pn, hPn, hPm⟩ : ∃ Pn : ℕ, (Pn : ℝ) = unwrapK n s p ∧ Pn % n = p := by
    unfold unwrapK
    split_ifs
    · exact ztiok
    · exact ztdqt
  rw [← hPn] at h1 h2
  have h1' : s ≤ Pn := by exact_mod_cast h1
  have h2' : Pn ≤ s + m := by exact_mod_cast (by simp_all : (Pn : ℝ) ≤ ((s + m : ℕ) : ℝ))
  exact ⟨Pn - s, by_omega, by_simp_all⟩

/-! ## The descent's facts for a stretch of a kind-1 piece -/
variable {E : FEnv} {c₀ : Config}

/-- **The facts of a stretch holding the good vertex.** -/
theorem descGood_mk (hE : FGood E c₀) {reg : ℕ → Set Point}
    (hregs : NFRegs E.M zti E.N reg) (hch : (E.N.region E.r).chords ≠ [])
    {ai bi aj bj : ℝ} (hAi : E.M.IsArc ztwky ztbuw ai bi)
    (hAj : E.M.IsArc ztwky ztbuw aj bj) (hij : ai ≠ aj)
    {PR : ℕ} {Hs : Host} {Cα : Chain} {N : NF} {γ' : ℕ} (hK : K1Hyp E c₀ PR Hs Cα N γ')
    {s : ℕ} (hcnt : ∀ d, d < Cα.m → E.M.counted (ztbuf % E.M.W.n))
    (hsetD : ∀ x ∈ Cα.set, x ∉ E.M.D) (hinB : ∀ C : Chain, E.M = chainModel C → Cα.set ⊆ C.set)
    (hin : ∀ (k : ℕ) (t : ℝ), 0 ≤ t → t < 1 → 0 < (k : ℝ) + t → (k : ℝ) + t < Cα.m →
      sideInArc ai bi (((ztnj % E.M.W.n : ℕ) : ℝ) + t))
    {d0 g g' L dX : ℕ} (hg : g = (s + d0) % E.M.W.n) (hd0L : d0 + L ≤ Cα.m)
    (hg' : g' + dX < 2 * Cα.m + 7) (hX0 : 0 < dX) (hXL : dX < L)
    {σ T : ℝ} {σb : ℕ} (hσb : σb ≤ 1) (hdσ : dirOf σb = σ) {po : ℕ} {tq : ℝ}
    (hgc : GoodCand E.M zti ztwky ztbuw
      ⟨ztbmy % E.M.W.n, 0⟩ σ T)
    (hXA : SideAttach E.M.W ztxnn
      ztxlm 0)
    (hOA : SideAttach E.M.W ztxnn po tq)
    (hne : sidePt E.M.W ztxlm 0 ≠ sidePt E.M.W po tq)
    (hXi : ClosedArc ai bi ztwx)
    (hXj : ClosedArc aj bj ztdek)
    (hcount : CountOK E.M ztwky ztbuw
      ztwx ztdek) :
    ∃ regα Tα, DescGood E c₀ Cα N g g' L reg ai bi aj bj dX regα Tα := by
  have hcan := hK.hcan
  obtain ⟨-, -, -, regα, hRC, hCS, hArcs, hRg, -⟩ := hcan.1
  have hGα : GoodModel ztbdc :=
    Or.inl ⟨Cα, by rw [hK.hQ]; exact qof_simple hE, rfl⟩
  have hn7 : (chainModel Cα).W.n = 2 * Cα.m + 7 := chainModel_n Cα
  obtain ⟨U, hU, hfU⟩ := faced_after hGα hcan.1.1 (p := g' + dX) by_omega
  obtain ⟨Tα, hTα, hTU⟩ := hRC.2.2 U hU
  have hsn : ∀ d', ztsb % E.M.W.n = (s + (d0 + d')) % E.M.W.n := fun d' => by
    rw [hg, Nat.mod_add_mod, Nat.add_assoc]
  refine ⟨regα, Tα, ⟨hregs, hch, hAi, hAj, hij, fun d' hd' t ht0 ht1 hpos => ?_,
    fun d' hd' => ?_, hsetD, hinB, hX0, hXL, ⟨σb, hσb, T, by_grind⟩,
    ⟨_, po, tq, hgc.2.2.2.2.2.2.2.1, hXA, hOA, hne, hXi, hXj, hcount⟩,
    ⟨hRC, hCS, hArcs, hRg⟩, ⟨4, Dec.recTree_of hGα hcan.1 hcan.2.1⟩, hTα,
    by rw [hTU]; omega⟩⟩
  · zumoh
    exact hin _ t ht0 ht1 by_grind
      (by have : ((d0 + d' : ℕ) : ℝ) + 1 ≤ Cα.m := by exact_mod_cast by_omega
          grind)
  · zumoh
    exact hE.ehc _ (Nat.mod_lt _ (by have := hK.hs; omega)) (hcnt _ by_omega)
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Set Filter Topology
open Chazelle.Chain (sideInArc SideAttach sidePt)
open DownHost ArcT
variable {E : FEnv} {c₀ : Config}

/-- At most seven walk edges are uncounted. -/
theorem uncounted_le (hE : FGood E c₀) : {p | p < E.M.W.n ∧ ¬ E.M.counted p}.ncard ≤ 7 := by
  zubcv
  · have hn : ztpjf := by zvmzx; exact chainModel_n C
    have hsub : {p | p < E.M.W.n ∧ ¬ E.M.counted p} ⊆
        (([0, 1, 2, 3, 4, 5, 2 * C.m + 6].toFinset : Finset ℕ) : Set ℕ) := by
      zujge
      zuksx
      zughl
      simp only [List.coe_toFinset, List.mem_cons, List.not_mem_nil, or_false,
        mem_ofPred_eq]
      omega
    calc _ ≤ (([0, 1, 2, 3, 4, 5, 2 * C.m + 6].toFinset : Finset ℕ) : Set ℕ).ncard :=
          Set.ncard_le_ncard hsub ztgdv
      _ ≤ 7 := by rw [Set.ncard_coe_finset]; norm_num
  · have : {p | p < E.M.W.n ∧ ¬ E.M.counted p} = ∅ := by
      ext p; simp only [mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro _ h; apply h; zvmzx; trivial
    simp_all

/-- **A closed piece from unwrapped bounds.** -/
theorem closed_of_unwrap {n a x y z : ℝ} (ha : 0 ≤ a ∧ a < n) (hx : 0 ≤ x ∧ x < n)
    (hy : 0 ≤ y ∧ y < n) (hz : 0 ≤ z ∧ z < n) (hxz : unwrapK n a x < unwrapK n a z)
    (h1 : unwrapK n a x ≤ unwrapK n a y) (h2 : unwrapK n a y ≤ unwrapK n a z) :
    ClosedArc x z y := by
  zuff
  · zudt
    · exact Or.inl ((cyc_unwrap ha hx hz hy hxz).2 ztwo)
    · zulw
      rw [← wrapK_unwrapK (n := n) (l := a) hy, h2, wrapK_unwrapK hz]
  · zuhl
    rw [← wrapK_unwrapK (n := n) (l := a) hy, ← h1, wrapK_unwrapK hx]
theorem dir_bit {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    ∃ σb, σb ≤ 1 ∧ dirOf σb = σ := by
  zur
  · tauto
  · exact ⟨0, by_norm_num, by_rfl⟩

/-- **A pair run of the good vertex's arcs finds a success.** -/
theorem pair_complete (hE : FGood E c₀) {reg : ℕ → Set Point}
    (hregs : NFRegs E.M zti E.N reg) {X : WPos} {σ T : ℝ} {po : ℕ} {tq : ℝ}
    {ti tj : ℕ} (hG : GoodSet E reg X σ T po tq ti tj) {f : ℕ} (hpd : PairDone E c₀ ti tj f) :
    f = 1 := by
  obtain ⟨c₃, hI₃, hcp, h40, h41, hdone⟩ := hpd
  have hE₃ := hE.rebase hI₃
  zuclv
  set L := c₃.nreg 81076 with hLdef
  have hT := tile_of_cut hE hG.hch hG.hti hcp
  zuixp
  obtain ⟨hLq, -, hq1, -, -, -, -, hk0w, hk1w, hpos, hkind⟩ := hcp'
  -- the good vertex
  have hX0 : X.hgt = 0 := hG.hgc.1
  have hXe : X.edge < E.M.W.n := hG.hgc.2.1
  have hXX : ztplj := by cases X; tauto
  have hxk : ztgad := by
    have : (X.edge : ℝ) + 1 ≤ E.M.W.n := by exact_mod_cast hXe
    constructor <;> linarith [(Nat.cast_nonneg X.edge : (0 : ℝ) ≤ X.edge)]
  have hXi := hG.hXi
  unfold aK bK at hXi
  obtain ⟨u1, u2⟩ := (closedArc_unwrap hT.ha hT.hb hxk hT.hab).1 hXi
  obtain ⟨i', hi', hs1, hs2⟩ := tile_cover hT hxk u1 u2
  obtain ⟨-, -, hse, -⟩ := tile_mono hT i' hi'
  have hcl : ClosedArc (psK E c₃.nmem L i') (peK E c₃.nmem L i') ztgvr :=
    closed_of_unwrap hT.ha (hT.hs i' hi') hxk (hT.he i' hi') hse hs1 hs2
  zvncl at hcl
  have hspe : psK E c₃.nmem L i' ≠ peK E c₃.nmem L i' := fun h => by zvmwc at hse; linarith
  obtain ⟨σb, hσb, hdσ⟩ := dir_bit hG.hgc.2.2.1
  have hGA : GoodAt ztmau reg X.edge σb := ⟨T, by rw [hdσ, ← hXX]; exact hG.hgc⟩
  have hPD := hdone i' hi'
  have hk : c₃.nmem ztfnx ≤ 1 := hkind i' hi'
  rcases (show c₃.nmem ztquq = 0 ∨ c₃.nmem ztquq = 1 by
    show c₃.nmem ztfnx = 0 ∨ c₃.nmem ztfnx = 1; omega) with hk0 | hk1
  · -- a kind-0 piece
    obtain ⟨t, ht, htx⟩ := light_cover (uncounted_le hE) (hpos i' hi').1 (hpos i' hi').2.2.1
      (key_bounds (hpos i' hi').2.1 (hpos i' hi').2.2.2) hspe (hk0w i' hi' hk0) hXe hcl
    have e : ztgia % E.M.W.n = X.edge := htx
    exact hPD.1 hk0 reg hregs hG.hch t ht (by
      show VSet E ztzzz
      zvmwe; exact hG.hVX) σb hσb (by
      show GoodAt ztmau reg ztzzz σb
      zvmwe; omega)
  · -- a kind-1 piece
    obtain ⟨Hs, Cα, N, γ', hK, J, hV, htest, hst1, hst2⟩ := hPD.2 hk1
    obtain ⟨-, Hs', Cα', N', hCD', -, -, hset', hwt', hPW', -, -⟩ := hk1w i' hi' hk1
    have hCC : Cα' = Cα := ShootCut.chainDesc_unique hCD' hK.hCD
    subst hCC
    obtain ⟨hpw0, hpw3, -, hpwe, -⟩ := hPW'
    set n := E.M.W.n with hndef
    set s := c₃.nmem (L + 1 + 7 * i' + 0) with hsdef
    have hs : s < n := (hpos i' hi').2.2.1
    have hmn : Cα'.m < n := hK.hmn
    have hm1 := Cα'.one_le
    have kS : psK E c₃.nmem L i' = (s : ℝ) := by
      unfold psK; simp only at hpw0; rw [hpw0]; exact key_vtx' _ _ _
    have kE : peK E c₃.nmem L i' = ((zttzd % n : ℕ) : ℝ) := by
      unfold peK; simp only at hpw3 hpwe; rw [hpw3, hpwe]; exact key_vtx' _ _ _
    have hwt'' : E.M.arcWt (s : ℝ) ((zttzd % n : ℕ) : ℝ) = Cα'.m := by
      rw [← kS, ← kE]; tauto
    have hcnt := counted_of_wt (M := E.M) hs by_omega hmn hwt''
    rw [kS, kE] at hcl
    obtain ⟨d, hd, hdx⟩ := closed_offset hs hmn by_omega hXe hcl
    -- the piece's chain
    have hdir : (∀ e, e ≤ Cα'.m → E.M.W.vtx ztbaap = Cα'.vertex e) ∨
        (∀ e, e ≤ Cα'.m → E.M.W.vtx ztbaap = Cα'.vertex (Cα'.m - e)) := hK.hdir
    have hinB : ∀ C : Chain, E.M = chainModel C → Cα'.set ⊆ C.set := fun C hMC => by
      have hc := hcnt
      zumdj
      rw [hndef] at hdir'
      rw [hMC] at hc hdir'
      zulzl
    have hsetD : ∀ x ∈ Cα'.set, x ∉ E.M.D := by
      zuh
      rw [← hset'] at hx
      obtain ⟨p, t, hp, ht0, ht1, -, rfl⟩ := hx
      exact hM.trace p hp t ht0 ht1
    have hin : ∀ (k : ℕ) (t : ℝ), 0 ≤ t → t < 1 → 0 < (k : ℝ) + t → (k : ℝ) + t < Cα'.m →
        sideInArc ztydv ztydu
          ztwvp := fun k t ht0 ht1 h0 hm => by
      have h1 := off_sideInArc hs hmn ht0 ht1 h0 hm
      rw [← kS, ← kE] at h1
      have hb : ztwuc := by
        have h2 : ztycd := Nat.mod_lt _ by_omega
        have h2' : ztxpi := by exact_mod_cast h2
        exact ztomv
      exact tile_inner hT hi' hb h1
    -- the target
    have hAj := arc_isArc hE hregs hG.htj
    have haj : E.M.key zti (arcOf E.N E.r tj).s =
        E.M.key zti ztrby := by rw [h40, h41]
    have hAOK := hE.arcOK hG.hch hG.htj
    have htc : 0 < c₃.nreg 81141 ∨ c₃.nreg 81021 ≤ c₃.nreg 81140 :=
      far_range hE₃ (far := ztrby) (by show _ < n; rw [h40]; exact hAOK.se)
        (fun C hC => by
          show |(E.M.pos zti ⟨c₃.nreg 81140, c₃.nreg 81141⟩).2| < C.radius
          rw [h40, h41]; exact hAOK.sy C hC)
    have hij := hG.hij
    have hXj := hG.hXj
    simp only [aK, bK] at hij hXj
    -- the good vertex in the stretches
    have hgood : ∀ g dX : ℕ, ztbmy % n = X.edge →
        GoodCand E.M zti ztwky ztbuw ⟨ztbmy % n, 0⟩ σ T ∧
        SideAttach E.M.W ztxno ztzyt 0 ∧
        SideAttach E.M.W ztxno po tq ∧
        sidePt E.M.W ztzyt 0 ≠ sidePt E.M.W po tq ∧
        ClosedArc ztydv
          ztydu ztxqa ∧
        CountOK E.M ztwky ztbuw ztxqa
          ztdek := fun g dX h => by
      rw [h, ← hXX]
      exact ⟨hG.hgc, hG.hXA, hG.hOA, hG.hne, hXi, hG.hcnt⟩
    have hPRs : c₃.nmem (prOf L i') = s := rfl
    rcases Nat.eq_zero_or_pos d with rfl | hd0
    · refine htest reg hregs hG.hch X.edge ztenp hG.hVX σb hσb hGA
      rw [hPRs, ← hdx, Nat.add_zero, Nat.mod_eq_of_lt hs]
    rcases (show d = Cα'.m ∨ d < Cα'.m by omega) with rfl | hdm
    · exact htest reg hregs hG.hch X.edge (Or.inr (Or.inl (by zupak; exact hdx.symm)))
        hG.hVX σb hσb hGA
    have htl := WalkEmbed.tpos_lt Cα' J
    by_cases hone : WalkEmbed.tpos Cα' J + Cα'.m ≤ 2 * Cα'.m
    · zucxo
      obtain ⟨regα, Tα, hD⟩ := descGood_mk hE₃ hregs hG.hch ztlfz hAj hij hK
        hcnt hsetD hinB hin (g := s) (d0 := 0) (g' := 6 + WalkEmbed.tpos Cα' J) (L := Cα'.m)
        (dX := d) ztiio by_omega by_omega hd0 hdm hσb
        hdσ g1 g2 g3 g4 g5 hXj g6
      exact hst1 hone reg _ _ _ _ d regα Tα hD haj htc
    · obtain ⟨hs1', hs2'⟩ := hst2 by_omega
      set L₁ := 2 * Cα'.m - WalkEmbed.tpos Cα' J with hL₁
      rcases (show d < L₁ ∨ d = L₁ ∨ L₁ < d by omega) with h1 | h1 | h1
      · zucxo
        obtain ⟨regα, Tα, hD⟩ := descGood_mk hE₃ hregs hG.hch ztlfz hAj
          hij hK hcnt hsetD hinB hin (g := s) (d0 := 0) (g' := 6 + WalkEmbed.tpos Cα' J) (L := L₁)
          (dX := d) ztiio by_omega by_omega hd0 h1 hσb
          hdσ g1 g2 g3 g4 g5 hXj g6
        exact hs1' reg _ _ _ _ d regα Tα hD haj htc
      · zucuj
        exact htest reg hregs hG.hch X.edge (Or.inr (Or.inr ⟨by_omega, by zupak; exact hdx.symm⟩))
          hG.hVX σb hσb hGA
      · have hgx : (zttze % n + ztnxk) % n = X.edge := by
          rw [Nat.mod_add_mod, show s + L₁ + ztnxk = s + d by omega, hdx]
        obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hgood _ _ hgx
        obtain ⟨regα, Tα, hD⟩ := descGood_mk hE₃ hregs hG.hch ztlfz hAj
          hij hK hcnt hsetD hinB hin (g := zttze % n) (d0 := L₁) (g' := 6) (L := Cα'.m - L₁)
          (dX := d - L₁) rfl by_omega by_omega by_omega by_omega hσb hdσ g1 g2 g3 g4 g5
          hXj g6
        exact hs2' reg _ _ _ _ ztnxk regα Tα hD haj htc

/-- **Completeness of the search**: if the region has more exits than the full maps allow, the
pair runs set the flag. -/
theorem find_complete (hE : FGood E c₀) {f : ℕ}
    (hpd : ∀ i, i < kOf E → ∀ j, j < kOf E → PairDone E c₀ i j f) {reg : ℕ → Set Point}
    (hregs : NFRegs E.M zti E.N reg) (hfull : E.M.FullDegLe zti E.D)
    (hdeg : E.D < E.M.deg ztwky ztbuw) : f = 1 := by
  obtain ⟨X, σ, T, po, tq, ti, tj, hG⟩ := good_set hE hregs hfull hdeg
  have hk : kOf E = (E.N.region E.r).arcs.length := by unfold kOf; rw [ite_eq_right hG.hch]
  exact pair_complete hE hregs hG (hpd ti (by rw [hk]; exact hG.hti) tj (by rw [hk]; exact hG.htj))
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Chazelle.Chain (sideInArc)
open DownHost ArcT

/-- **The vertex count of an arc** (with distinct end keys) is at most its weight plus `8`. -/
theorem arcCnt_le_wt {M : Model} {Q : Polygon} {n0 : ℕ}
    (hunc : {p | p < M.W.n ∧ ¬ M.counted p}.ncard ≤ 7) {s e : WPos}
    (hs : ProperPos M Q n0 s) (he : ProperPos M Q n0 e) (hse : s.edge < M.W.n)
    (hee : e.edge < M.W.n) (hne : M.key Q s ≠ M.key Q e) :
    arcCnt M.W.n s.edge e.edge
      (if s.edge = e.edge ∧ M.key Q s < M.key Q e then 1 else 0) ≤
        M.arcWt ztenf ztfoc + 8 := by
  zukzu
  zuqi
  set a := M.key Q s with hadef
  set b := M.key Q e with hbdef
  have hka : ztiyv := rfl
  have hkb : b = e.edge + M.param Q e := rfl
  have hsR : ztgtr := by exact_mod_cast hse
  have heR : (e.edge : ℝ) + 1 ≤ n := by exact_mod_cast hee
  have ha : ztgaf := by constructor <;> linarith [hs.1, hs.2.1, (Nat.cast_nonneg s.edge : (0:ℝ) ≤ _)]
  have hb : ztphx := by constructor <;> linarith [he.1, he.2.1, (Nat.cast_nonneg e.edge : (0:ℝ) ≤ _)]
  have hpe : 0 ≤ (e.edge : ℝ) ∧ (e.edge : ℝ) < n := by_simp_all
  by_cases h1 : s.edge = e.edge ∧ a < b
  · zubel
    zuhqp
    simp_all
  zubmd
  -- the end vertex is on the closed arc
  have hcl : ClosedArc a b (e.edge : ℝ) := by
    zugse
    · zuhzd
      have hu1 : ztlyx := by unfold unwrapK; zuosu
      have hu2 : unwrapK n a b = b := by unfold unwrapK; rw [ite_eq_left (by linarith [hs.2.1, he.1])]
      exact (closedArc_unwrap ha hb hpe hne).2 ⟨by rw [hu1]; zuntj, by
        zunqc; zuntk⟩
    · have hba : ztsdo := by
        grind
      have hu1 : ztdbl := by
        zuiqg
      have hu2 : ztoro := by unfold unwrapK; simp_all
      exact (closedArc_unwrap ha hb hpe hne).2 ⟨by_grind, by
        zunqc; zuntk⟩
    · zuhzc
      have hu1 : ztdbl := by
        zuiqf
      have hu2 : ztoro := by
        unfold unwrapK; rw [ite_eq_right (by linarith [hs.1, he.2.1])]
      exact (closedArc_unwrap ha hb hpe hne).2 ⟨by_grind, by
        zunqc; zuntk⟩
  obtain ⟨t, ht, -, htu⟩ := steps_le (w := M.arcWt a b) hunc hs hse hb hne le_rfl hee hcl
  -- the vertex count is `t + 1`
  have hcnt : arcCnt n s.edge e.edge 0 = t + 1 := by
    zuhqp
    zugse
    · have hu1 : ztlyx := by
        zuhzd
        unfold unwrapK; zuosu
      zugen
      have h2 : s.edge + t = e.edge := by exact_mod_cast htu
      have h3 : e.edge + n - s.edge = t + n := by_omega
      rw [ite_eq_right by_omega, h3, Nat.add_mod_right, Nat.mod_eq_of_lt by_omega]
    · have hba : ztsdo := by
        grind
      have hu1 : ztdbl := by
        zuiqg
      zugen
      have : ztppy := by_simp_all
      rw [ite_eq_left by_omega, heq, show e.edge + n - e.edge = n by omega, Nat.mod_self]; omega
    · have hu1 : ztdbl := by
        zuhzc
        zuiqf
      zugen
      have h2 : ztppy := by exact_mod_cast htu
      have h3 : e.edge + n - s.edge = t := by_omega
      rw [ite_eq_right by_omega, h3, Nat.mod_eq_of_lt by_omega]
  omega
variable (C : Chain) {Cα : Chain}
/-- At most seven walk edges of a chain model are uncounted. -/
theorem chain_uncounted_le :
    {p | p < (chainModel C).W.n ∧ ¬ (chainModel C).counted p}.ncard ≤ 7 := by
  zucmi
  have hsub : {p | p < (chainModel C).W.n ∧ ¬ (chainModel C).counted p} ⊆
      (([0, 1, 2, 3, 4, 5, 2 * C.m + 6].toFinset : Finset ℕ) : Set ℕ) := by
    zujge
    zughl
    simp only [List.coe_toFinset, List.mem_cons, List.not_mem_nil, or_false, Set.mem_ofPred_eq]
    omega
  calc _ ≤ (([0, 1, 2, 3, 4, 5, 2 * C.m + 6].toFinset : Finset ℕ) : Set ℕ).ncard :=
        Set.ncard_le_ncard hsub ztgdv
    _ ≤ 7 := by rw [Set.ncard_coe_finset]; norm_num

/-- The weight of the whole walk of a chain model (the arc of the empty family). -/
theorem arcWt_zero_zero : (chainModel C).arcWt 0 0 = 2 * C.m := by
  rw [← MergeAsm.chainModel_size C]
  zultu
  zucr
  zufj
  zulrx
  constructor
  · simp_all
  · zubf
    refine ⟨h1, h2, 1 / 2, by_norm_num, by_norm_num, ?_⟩
    zujv

/-- **The vertex count of an arc of a granular normal form of a chain model.** -/
theorem lcnt_le {Q : Polygon} {N : NF} {γ' : ℕ}
    (hcan : IsCanonicalNF ztbdc Q N γ' 4) {r : ℕ} (hr : r < N.nRegions) {t : ℕ}
    (ht : t < (N.region r).arcs.length) : lcnt Cα Q N r ztgb t ≤ γ' + 8 := by
  obtain ⟨hnf, -, hgr, -⟩ := hcan
  have hnf' := hnf
  obtain ⟨hFam, -, -, reg, hRC, -, hArcs, hRg, -, -, hpp⟩ := hnf'
  have hn := chainModel_n Cα
  set j := lj N r t with hjdef
  have hjm : ztgav := by
    rw [hjdef, lj, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht, Option.getD_some]
    simp
  obtain ⟨hj, hjr⟩ := (hArcs.2.2.2 r hr j).1 hjm
  have harc := (hArcs.1 j hj).2
  zugdy
  zufud
  have hwt : (chainModel Cα).arcWt _
      _ ≤ γ' :=
    (WalkEmbed.arcWt_le_weight _ harc).trans (hgr.1 _ hU)
  obtain ⟨ha0, ha1, hb0, hb1, hc, -, -⟩ := harc
  have hps := (hpp j hj).1
  have hpe := (hpp j hj).2
  have hse : (N.arc j).s.edge < (chainModel Cα).W.n := by
    have hk : (chainModel Cα).key Q (N.arc j).s = (N.arc j).s.edge + (chainModel Cα).param Q (N.arc j).s := rfl
    have : ztict := by zupal
    zufc
  have hee : (N.arc j).e.edge < (chainModel Cα).W.n := by
    have hk : (chainModel Cα).key Q (N.arc j).e = (N.arc j).e.edge + (chainModel Cα).param Q (N.arc j).e := rfl
    have : ztics := by zupam
    zufc
  unfold lcnt
  rw [← hjdef, ← hn]
  rcases hc with ⟨hca, -, hne⟩ | ⟨hF, ha, hb⟩
  · -- a family with chords
    have hnc : 0 < N.nChords := by
      rcases Nat.eq_zero_or_pos N.nChords with h0 | h0
      · exfalso
        obtain ⟨c, hcF, -⟩ := hca
        zulhj
        rw [h0, Set.ncard_eq_zero (hs := hFam.1)] at h1
        simp_all
      omega
    have hw : wBit Cα Q N.nChords (N.arc j).s.edge (N.arc j).s.hgt (N.arc j).e.edge (N.arc j).e.hgt =
        if (N.arc j).s.edge = (N.arc j).e.edge ∧
          (chainModel Cα).key Q (N.arc j).s < (chainModel Cα).key Q (N.arc j).e then 1 else 0 := by
      unfold wBit
      simp_all
    zujjy
    have := arcCnt_le_wt (chain_uncounted_le Cα) hps hpe hse hee hne
    omega
  · -- the empty family: the whole walk
    have hs0 : (N.arc j).s.edge = 0 := by
      have hk : (chainModel Cα).key Q (N.arc j).s =
          (N.arc j).s.edge + (chainModel Cα).param Q (N.arc j).s := rfl
      have : ((N.arc j).s.edge : ℝ) ≤ 0 := by zupal
      have : ((N.arc j).s.edge : ℝ) = 0 := by_grind
      zufc
    have he0 : (N.arc j).e.edge = 0 := by
      have hk : (chainModel Cα).key Q (N.arc j).e =
          (N.arc j).e.edge + (chainModel Cα).param Q (N.arc j).e := rfl
      have : ((N.arc j).e.edge : ℝ) ≤ 0 := by zupam
      have : ((N.arc j).e.edge : ℝ) = 0 := by_grind
      zufc
    have hw : wBit Cα Q N.nChords (N.arc j).s.edge (N.arc j).s.hgt (N.arc j).e.edge
        (N.arc j).e.hgt = 0 := by
      unfold wBit
      zunjl; rintro ⟨h0, -⟩
      zulhj
      simp_all
    rw [hw, hs0, he0]
    rw [ha, hb, arcWt_zero_zero] at hwt
    zuhqp
    rw [ite_eq_left by_omega, hn, show 0 + ztgb - 0 = 2 * Cα.m + 7 by omega, Nat.mod_self]
    omega

/-- **The steps of a leaf.** -/
theorem lmuB_le {Q : Polygon} {N : NF} {γ' : ℕ} (hP : Cα.P.Simple)
    (hcan : IsCanonicalNF ztbdc Q N γ' 4) : lmuB Cα Q N ≤ 5 * ztkht := by
  zuiwd
  have hM := walkAx_of_goodModel hGα
  unfold lmuB
  refine Finset.sup_le fun r hr => ?_
  zudtk
  unfold lmu
  have hlen := region_arcs_le hM hcan.1 hcan.2.1 hr
  calc ∑ t ∈ Finset.range (N.region r).arcs.length, (lcnt Cα Q N r _ t + 1)
      ≤ ∑ t ∈ Finset.range (N.region r).arcs.length, ztkht :=
        Finset.sum_le_sum fun t ht => by
          have := lcnt_le hcan hr (Finset.mem_range.1 ht); omega
    _ = (N.region r).arcs.length * ztkht := by_simp
    _ ≤ 5 * ztkht := by_simp_all

/-! ## The piece bound -/

/-- Lemma 2.3 with its explicit constant. -/
theorem l23_explicit (M : Model) (Q : Polygon) (F : Set ztf) (γ D : ℕ) (hM : GoodModel M)
    (hF : M.ChordFamily Q F) (hdeg : M.DegLe F D) (hgran : M.Granular F γ) :
    F.ncard * ztgj ≤ (fun D => 140 * ztmo) D * ztcep := by
  zugc

  zubrr
  show F.ncard * ztgj ≤ 140 * ztmo * ztcep
  zucyo
  · zuqx
    · simp
    · zugkd
  · zucgc
    calc F.ncard * ztgj ≤ 2 * ztjis := by_nlinarith
      _ ≤ 2 * ztxun := Nat.mul_le_mul_left _ h
      _ ≤ 2 * ztwvy := by gcongr
      _ = 140 * ztmo * ztcep := by_ring
theorem halfK_le {n x : ℕ} (hn : 3 ≤ n) (hx : x ≤ 6720 * n + 20163) : halfK n x ≤ 120011 := by
  unfold halfK
  have : x / ztnfa ≤ 30000 := Nat.div_le_of_le_mul by_omega
  omega

/-- The bound of a piece's run. -/
def pK (E : FEnv) : ℕ := 10 ^ 9 * (tK E * ztmar)
variable {E : FEnv} {c₀ : Config}
theorem k0K_le : k0K E ≤ pK E := by
  have hT : 20 ≤ tK E := by unfold tK; omega
  have hP : tK E ≤ tK E * ztmar := by_grind
  unfold pK k0K tvK hvK
  omega

/-- **The bound of a kind-1 piece.** -/
theorem k1K_le (hE : FGood E c₀) {Cα : Chain} {N : NF} {γ' : ℕ} (hQ : Cα.P = Qof E.P)
    (hcan : IsCanonicalNF ztbdc zti N γ' 4) (hγ' : γ' ≤ E.H E.γ)
    (hm : Cα.m ≤ E.γ) : k1K E Cα N ≤ pK E := by
  have hP : Cα.P.Simple := by zvnao; exact qof_simple hE
  zuiwd
  zuhel
  set T := tK E with hTdef
  set a := Nat.clog 2 E.γ with hadef
  set h := E.H E.γ with hhdef
  have hT : 20 ≤ T := by rw [hTdef]; unfold tK; omega
  zumea
  zunx
  have hmP : Cα.m < E.P.n := by have := Cα.m_lt; simp_all
  zuiyp
  -- the chords
  have hnc :=
    MergeAsm.nChords_le_canonical l23_explicit hP hcan
  have hreg := Gran.nRegions_eq hcan.1 hMα
  -- the halving cost
  have hX : halfK E.P.n ztkas ≤ 120011 := halfK_le hn3 (by unfold maxCode; omega)
  -- the depth
  have hdd : decDepth 4 N.nChords + 1 ≤ 58 * ztdf := by
    unfold decDepth
    have h1 : N.nChords + 1 ≤ 2 ^ 14 * E.γ := by_omega
    have h2 : Nat.clog 2 zthbn ≤ 14 + a := by
      calc Nat.clog 2 _ ≤ Nat.clog 2 _ := MergeAsm.clog_mono h1
        _ ≤ Nat.clog 2 _ + Nat.clog 2 E.γ := MergeAsm.clog_mul_le _ _
        _ = 14 + a := by_rfl
    omega
  -- the leaf
  have hlm : lmuB Cα zti N ≤ 5 * zthhm := by
    have := lmuB_le hP hcan; omega
  -- the step costs
  have hdb : dbK E N + 2 ≤ 30000 * T := by
    unfold dbK ndK clK paK efK etK erK ehK wsK wcK scK
    grind
  have hlb : lbK E + 2 ≤ 2000 * T := by
    unfold lbK vsK tvK hvK csK
    linarith
  have hC : ztjtw * ztqlx ≤ 30000 * 58 * ztzuv := by
    calc ztjtw * ztqlx ≤ (30000 * T) * (58 * ztdf) :=
          Nat.mul_le_mul hdb hdd
      _ = 30000 * 58 * ztzuv := by_ring
  have hD : ztczt * lmuB Cα zti N ≤ 2000 * 5 * ztzuw := by
    calc ztczt * lmuB Cα _ N ≤ (2000 * T) * (5 * zthhm) := Nat.mul_le_mul hlb hlm
      _ = 2000 * 5 * ztzuw := by_ring
  have hR1 : T * ztdf ≤ T * ztcvs := by_grind
  have hR2 : T * zthhm ≤ 9 * ztzuu := by
    grind
  have hR3 : T ≤ T * ztcvs := by_grind
  have hdesc : descK E Cα N zthgk ≤ 10 ^ 8 * ztzuu := by
    unfold descK
    have hpa : paK E ztkas ≤ 120013 := by unfold paK; omega
    omega
  unfold k1K pK voK tvK hvK
  rw [← hTdef, ← hadef, ← hhdef]
  omega
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Machine Machine.Stmt Programs SweepPrim

/-- **The search** (Lemma 3.2). -/
def findS (sh cu : Stmt) : Stmt := .seq fInit ztyod

/-- The cost function of the search. -/
def findκ (d : ℕ) : ℕ := 10 ^ 10 * (testκ d + 21) * ztvq ^ 2
variable {E : FEnv} {c₀ : Config}

/-- The doubled walk length fits the word bound. -/
theorem hnW_of (hE : FGood E c₀) : 2 * E.M.W.n ≤ E.W := by
  zumct
  zudwh
  zunx
  zubcv
  · obtain ⟨hz, H, C', hC, hM'⟩ := chainDesc_of hE.hMD hM
    obtain ⟨hl, hHW, -, -⟩ := (hE.hwf.2 hz).2 H C' hC
    zuftr

    have hn : E.M.W.n = 2 * C'.m + 7 := by rw [hM']; exact chainModel_n C'
    omega
  · have hn : E.M.W.n = E.P.n := by
      zvmzx; show (interiorWalk zti).n = _; zunqd
    omega

/-- The arc count is at most the degree bound plus one. -/
theorem kOf_le (hE : FGood E c₀) : kOf E ≤ E.d + 1 := by
  unfold kOf
  split_ifs
  · omega
  · exact region_arcs_le (walkAx_of_goodModel hE.hGM) hE.hNF hE.hdeg hE.hr

/-- **The cost of the search** fits `findκ`. -/
theorem find_cost {t f g h a d k : ℕ} (hf : 1 ≤ f) (hg : 1 ≤ g) (hk : k ≤ d + 1) :
    30 + (17 + (((((70 + 11040 + 11040 + 7 + g + 3 +
      ((10 ^ 9 * ((t * ztbax + 20) * ztcvs) + 22) * g + 2)) + 3) * k + 4) + 2) * k + 2)) ≤
      10 ^ 10 * ztfuv * ztvq ^ 2 * f * g * ztcvs := by
  set S := h + a + 1 with hS
  have hS1 : 1 ≤ S := by_omega
  set T := t * ztbax + 20 with hT
  -- the piece bound
  have hTf : T ≤ 2 * ztubp * f := by
    zvncs; nlinarith
  have hKp : 10 ^ 9 * zttdi + 22 ≤ 10 ^ 9 * 2 * ztfuv * f * S := by
    have : T * S ≤ 2 * ztubp * f * S := Nat.mul_le_mul_right _ hTf
    nlinarith
  -- the pair bound
  set P := 10 ^ 9 * 2 * ztfuv * f * S with hP
  have hP1 : ztrzy := by
    omega
  have hpair : 70 + 11040 + 11040 + 7 + g + 3 + ztcrp + 3 ≤
      zttbh * g := by
    have : (10 ^ 9 * zttdi + 22) * g ≤ P * g := Nat.mul_le_mul_right _ hKp
    nlinarith
  have hk1 : k + 1 ≤ d + 2 := by_omega
  -- the loops
  have hloop : 30 + (17 + (((((70 + 11040 + 11040 + 7 + g + 3 +
      ztcrp) + 3) * k + 4) + 2) * k + 2)) ≤
      zthbv * g * ztvq ^ 2 := by
    generalize hX : 70 + 11040 + 11040 + 7 + g + 3 + ztcrp = X at hpair ⊢
    set Q := zttbh * g with hQ
    have h1 : ztteb * k ≤ Q * k := Nat.mul_le_mul_right _ hpair
    have h2 : (ztteb * k + 4 + 2) * k ≤ ztqbo * k := Nat.mul_le_mul_right _ by_omega
    have h3 : ztqbo * k ≤ ztzcy * ztet :=
      Nat.mul_le_mul (by have := Nat.mul_le_mul_left Q hk; omega) hk
    have h4 : ztzcy * ztet + 49 ≤ zthbv * g * ztvq ^ 2 := by
      have e : zthbv * g * ztvq ^ 2 = Q * ztvq ^ 2 + 100 * g * ztvq ^ 2 := by
        grind
      zui
      have : Q * ztet * ztet ≤ Q * ztvq ^ 2 := by
        rw [mul_assoc, ← pow_two]; exact Nat.mul_le_mul_left _ zttbd
      nlinarith
    omega
  calc _ ≤ zthbv * g * ztvq ^ 2 := hloop
    _ ≤ 10 ^ 10 * ztfuv * ztvq ^ 2 * f * g * ztcvs := by
      have : P + 22300 ≤ 10 ^ 10 * ztfuv * f * S := by
        grind
      calc zthbv * g * ztvq ^ 2 ≤ 10 ^ 10 * ztfuv * f * S * g * ztvq ^ 2 := by
            gcongr
        _ = _ := by_grind

/-- **The search meets `FindOK`.** -/
theorem findOK_of {sh cu : Stmt} {Bs Bc Bo : Finset ℕ} {F G H : ℕ → ℕ} {X : MemCtx}
    {Ok : Polygon → Model → Prop} (hBo : oracleBands ⊆ Bo) (hB8 : bRestore ∉ Bo)
    (hloc : X.CapLocal) (hhalf : X.Halves)
    (hOkM : ∀ P M, Ok P M → OkModel P M ∨ M = interiorModel zta) (hBs : Bs ⊆ Bo)
    (hBc : Bc ⊆ Bo) (hsh : ShooterOK sh Bs F X Ok) (hcu : CutterOK cu Bc G H X Ok) :
    FindOK (findS sh cu) findκ F G H X Ok Bo := by
  zuesx
  obtain ⟨hG, hWh, hX, hcap, hwf, hreg, hsimp, M, N, hMD, hGM, hOk, hNW, hNF, hdeg, hsg, hr⟩ := pre
  obtain ⟨c₀, k₀, ex₀, hk₀, nm, rr, rm, ro, fr, f07, hE⟩ := find_start hsh hBs hcu hBc hBo hB8
    hloc hhalf hOkM hw hG hWh hX hcap hwf hreg hsimp hMD hGM hOk hNW hNF hdeg hsg hr
  set E := fEnv P W M N X Ok cu ztibi Bc Bo F G H testκ c with hEdef
  have hA0 : ztsfw := fr _ (by unfold IniW ALLOC; omega)
  -- the oracles cost at least one step
  have hγ1 : 1 ≤ c.nreg 81003 := one_le_gamma hGM hNF.1 hsg
  obtain ⟨hF1, hG1⟩ := oracle_pos hsh hcu hw hG hWh hX hcap hwf hreg hMD hGM hOk hγ1
    zthyb zthyb zthyb
  -- the bands
  set B := restoreBands ∪ Bo with hBdef
  have hB : dBands ⊆ B := Finset.union_subset_union subset_rfl hBo
  have hBT : restoreBands ∪ E.Bo ⊆ B := subset_rfl
  -- the run from the initialised configuration
  have hI0 : FInv W c₀ c₀ := ⟨ex₀.wb_right, fun _ _ => rfl, le_rfl, fun _ _ => rfl⟩
  have hw0 : FWin E c₀ := ⟨by_omega, fun h => absurd h by_omega⟩
  set k := kOf E with hkdef
  set Kp := pK E with hKpdef
  have hkd : k ≤ c.nreg 81005 + 1 := kOf_le hE
  have hcost := find_cost (t := testκ ztghi) (h := H ztbol)
    (a := Nat.clog 2 ztbol) hF1 hG1 hkd
  have hc1 : 30 + ztzsp ≤ findκ ztghi *
      F ztbol * G ztbol * ztwwz :=
    hcost
  have hc2 : c.nreg ALLOC + findκ ztghi * F ztbol * G ztbol *
      ztwwz ≤ W := hroom
  have hA : ∀ t, t < k → ArcOK E t := fun t ht => by
    have hch : ztfdm := fun h => by
      zuexx
    zudzc
    exact hE.arcOK hch by_omega
  have hPG : ∀ t, t < k → PGood E c₀ Kp t := fun t ht => by
    have hch : ztfdm := fun h => by
      zuexx
    zudzc
    exact pgood_of hE hch by_omega k0K_le
      (fun Cα N γ' hQ hcan hγ' hm => k1K_le hE hQ hcan hγ' hm)
  have hrun : FRS B P W c₀ ztyod c₀
      ztzsp (fun c' => FWin E c' ∧
        ∀ i, i < k → ∀ j, j < k → PairDone E c₀ i j ztdzf) := by
    refine FRS.seq (K₁ := 17) (cnt_fs hE hB hI0) ztiy
    obtain ⟨h30, h32, f₁⟩ := h₁
    have hw₁ : ztmtb := hw0.congr' (fun q a b => f₁ q by_omega by_omega by_omega
      by_omega by_omega by_omega)
    exact (outerLoop_fs (k := k) hE hB hBT hI₁ hw₁ h32 h30 hA hPG (hnW_of hE)
      (by show c₁.nreg ALLOC + _ ≤ W; omega)).mono le_rfl
      (fun c' h' => ⟨h'.1, h'.2.2.2⟩)
  obtain ⟨c', k₁, ex₁, hk₁, hI', hrf, hw', hpd⟩ := hrun
  refine ⟨c', k₀ + k₁, .seq ex₀ ex₁, ?_, ⟨fun q h8 hq => ?_, hw'.1, ?_⟩, ?_⟩
  · -- the cost
    show k₀ + k₁ ≤ findκ ztghi * F ztbol * G ztbol *
      ztwwz
    omega
  · -- the caller's registers
    have h80 : 80000 ≤ q := by unfold bandOf bRestore at h8; omega
    rw [hI'.hin q ztbc, fr q ztggl]
  · -- soundness and completeness
    intro M' N' reg hMD' hNA' hNF' hregs'
    have hMM : M' = M := NFLoc.modelDesc_unique hMD' hMD
    subst hMM
    have hNp : patch N N' = N := nf_patch hNW.nfAt hNA'
    have hregs : NFRegs M' zta N reg := by
      have : NFRegs M' zta zttvs reg := hregs'
      grind
    have hF : N'.F M' zta = N.F M' zta := by
      have : (patch N N').F M' zta = N'.F M' zta := rfl
      grind
    zuguo
    exact ⟨fun h1 => hw'.2 h1 reg hregs, fun hfull hdg =>
      find_complete hE hpd hregs hfull hdg⟩
  · -- the frame
    have hf0 : Frame B c c₀ k₀ := ⟨fun r hr _ => fr r (fun h => hr (by
        unfold IniW at h; rw [hBdef]; apply Finset.mem_union_left
        have : bandOf r = bRestore := by unfold bandOf bRestore; omega
        zvmwk; decide)), fun r _ => by zuofy, fun a _ => by rw [nm],
      fun a _ => by zupas, ro, by rw [hA0], by_omega⟩
    have hf1 : Frame B c₀ c' k₁ := RF.to_frame hrf
    have := hf0.trans hf1
    grind

/-- **WP-E: the splitting step of Lemma 3.2 exists** (`FindSpec`). -/
theorem findSpec : FindSpec :=
  ⟨findS, findκ, fun _ _ _ _ _ _ _ _ _ _ hBo hB8 hloc hhalf hOkM hBs hBc hsh hcu =>
    findOK_of hBo hB8 hloc hhalf hOkM hBs hBc hsh hcu⟩
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace DrvD
open Machine Machine.Stmt Programs SignK BuildRam
open SortL (seg)
@[expose] public section
section exec
variable {P : Polygon} {W : ℕ}

/-- The constants and the round counter. -/
theorem initS_exec (c : Config) (hw : WordsBounded W c) (hW : 5 ≤ W) :
    ∃ c' k, Exec P W initS c c' k ∧ k = 6 ∧ c'.nreg 216002 = 1 ∧ c'.nreg 216003 = 0 ∧
      c'.nreg 216004 = 4 ∧ c'.nreg 216005 = 2 ∧ c'.nreg 216006 = 5 ∧ c'.nreg 216010 = 0 ∧
      FrameB (fun r => decide (216002 ≤ r ∧ r ≤ 216010)) c c' := by
  obtain ⟨c', k, ex, hk, q⟩ : ∃ c' k, Exec P W initS c c' k ∧ k = 6 ∧
      (c'.nreg 216002 = 1 ∧ c'.nreg 216003 = 0 ∧
      c'.nreg 216004 = 4 ∧ c'.nreg 216005 = 2 ∧ c'.nreg 216006 = 5 ∧ c'.nreg 216010 = 0) := by
    zujqm
    exec_block
    all_goals try omega
    simp
  exact ⟨c', k, ex, hk, q.1, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2.1, q.2.2.2.2.2,
    exec_frameB ex by_decide⟩
end exec

/-- The level state depends only on the registers `210001 … 210005`, the memory and the
allocator. -/
theorem stateAt_congr {P : Polygon} {c c' : Config} {L : List zte} {E : List ℕ}
    (h : DrvR.StateAt P c L E)
    (hr : ∀ i, 1 ≤ i → i ≤ 5 → c'.nreg ztjfn = c.nreg ztjfn)
    (hm : c'.nmem = c.nmem) (hA : c'.nreg ALLOC = c.nreg ALLOC) : DrvR.StateAt P c' L E := by
  zubtz
  have e1 := hr 1 by_norm_num by_norm_num
  have e2 := hr 2 by_norm_num by_norm_num
  have e3 := hr 3 by_norm_num by_norm_num
  have e4 := hr 4 by_norm_num by_norm_num
  have e5 := hr 5 by_norm_num by_norm_num
  zvmxv at e1 e2 e3 e4 e5
  zvmyi at h1 h2 h3 h4 h5 h6 h7 h11 ⊢
  unfold DrvR.StateAt
  zuju
  simp_all

/-- **All rounds.** -/
theorem rounds_exec {E : DEnv} (hE : DGood E) {c : Config} (hI : RInv E 0 c) :
    ∃ c' k, Exec E.P E.W (.whileLtN 216010 216000 ztkec) c c' k ∧
      RInv E E.d0 c' ∧ Restore.RF DrvR.drvBands E.A₀ c c' k ∧ k ≤ ztbgq * E.d0 + 2 := by
  obtain ⟨c', k, e, ⟨t, I'⟩, hx, RFl, hk⟩ := Restore.whileLtN_frame (P := E.P) (W := E.W)
    (a := 216010) (b := 216000) (body := roundBody E.sF E.sB) (B := DrvR.drvBands) (A₀ := E.A₀)
    (fun c => ∃ t, RInv E t c) (fun c => E.d0 - c.nreg 216010) E.Br
    ztdnu
    (fun c ⟨t, I⟩ ht => by
      rw [I.r10, I.r00] at ht
      zucxk
      exact ztfdc) ⟨0, hI⟩
  have ht : t = E.d0 := by
    rw [I'.r10, I'.r00] at hx; have := I'.t_le; omega
  zucfb
  zuhja

/-! ## The cost -/

/-- The per-round constant. -/
def C2 (κf : ℕ → ℕ) (κB d0 : ℕ) : ℕ :=
  κf d0 + 2 * (ztkes * ztcmy) + 70 + 8 * DrvR.κSpl κB

/-- **The constant of the rounds.** -/
def κR (κf : ℕ → ℕ) (κB : ℕ) (d0 : ℕ) : ℕ := 20 + d0 * (42 + C2 κf κB d0 * 2 ^ d0)

/-- The round bound is linear in the chord count, with the oracle factor. -/
theorem Br_le (E : DEnv) (hA : 1 ≤ E.F E.γ * E.G E.γ * ztdyl) :
    E.Br + 2 ≤ (42 + C2 E.κf E.κB E.d0 * 2 ^ E.d0) * ztbjj *
      (E.F E.γ * E.G E.γ * ztdyl) := by
  set A := E.F E.γ * E.G E.γ * ztdyl with hAd
  set T := 2 ^ E.d0 with hT
  zuinv
  have hBr : E.Br = 40 + ztcli * ztbmh + 8 * DrvR.κSpl E.κB * ztbmh := rfl
  have hBf : E.Bf = E.κf E.d0 * A + 2 * ztrt + 60 := by
    show Restore.costF E.κf E.F E.G E.Hc E.d0 E.γ + _ + 60 = _
    unfold Restore.costF; grind
  have hTK : 1 ≤ T * K1 := by_grind
  have h1 : E.Bf + 10 ≤ ztxga * A := by
    have e : ztxga * A =
        E.κf E.d0 * A + ztzay * A := by_ring
    have : 2 * ztrt + 70 ≤ ztzay * A :=
      by simp_all
    omega
  have h2 : ztcli * ztbmh + 8 * DrvR.κSpl E.κB * ztbmh ≤
      C2 E.κf E.κB E.d0 * A * ztbmh := by
    have h3 := Nat.mul_le_mul_right ztbmh h1
    have h4 : 8 * DrvR.κSpl E.κB * ztbmh ≤ 8 * DrvR.κSpl E.κB * A * ztbmh :=
      Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ hA)
    have h5 : C2 E.κf E.κB E.d0 * A * ztbmh =
        ztxga * A * ztbmh +
          8 * DrvR.κSpl E.κB * A * ztbmh := by unfold C2; ring
    omega
  grind

/-! ## The contract -/
set_option maxHeartbeats 16000000 in
/-- **The restoration rounds meet their contract**, for a splitting step with the interior
oracles' bands and a sorted build. -/
theorem roundsSpec_of {sF sB : Stmt} {κf : ℕ → ℕ} {κB : ℕ} {F G H : ℕ → ℕ} {X : MemCtx}
    (hF : Restore.FindOK sF κf F G H X DrvR.OkInt DrvR.ioBandsD) (hB : DrvR.SortedMeets sB κB)
    (hloc : X.CapLocal) (hF1 : ∀ γ, 1 ≤ F γ) (hG1 : ∀ γ, 1 ≤ G γ) :
    DrvR.RoundsSpec X F G H := by
  refine ⟨roundsS sF sB, κR κf κB, ?_⟩
  zuesx
  obtain ⟨hEnv, hd4, hγ1, hγn, L₀, E₀, hSt, hdeg, hsg⟩ := pre
  obtain ⟨hG, hW3, hWh, -, hXh, hcap⟩ := hEnv
  zubmr
  have hSt₀ := hSt
  obtain ⟨hD6, hDa, hK, -, -, -, -, -, -, -, -⟩ := hSt₀
  zvmyi at hD6 hDa hK
  have hc1 : coreReg 1 = 230001 := rfl
  zvmwl at hXh hcap
  -- the data
  set E : DEnv := ⟨P, W, c.nreg ALLOC, c.nmem, c.nreg, c.nreg 210001, c.nreg 216001,
    c.nreg 216000, c.nreg 230001, sF, sB, κf, κB, F, G, H, X,
    (BuildNF.buildNF ztwiq zta L₀ E₀).F ztwiq zta,
    L₀.length⟩ with hEd
  have hMD : ModelDescAt c.nmem _ _ _ := hDa.holds
  have hone : c.nmem _ = 1 := desc_one hMD
  have hE : DGood E := by
    refine ⟨hF, hB, hG, hWh, hXh, fun m hm => ?_, ⟨hD6, fun h0 => ?_⟩, hMD, hd4⟩
    · show c.nreg 216001 ≤ X.cap P m _
      rw [hloc P c.nmem m _ _ hm hXh]; omega
    simp_all
  -- the cost factor
  have hA1 : 1 ≤ F ztbuu * G ztbuu *
      ztwxa := by
    have := hF1 ztbuu; have := hG1 ztbuu
    have : 1 ≤ F _ * G _ := Nat.one_le_iff_ne_zero.2 by_positivity
    nlinarith
  have hBr := Br_le E hA1
  set A := F ztbuu * G ztbuu *
    ztwxa with hAd
  have hcost : κR κf κB zteqw * (c.nreg 210003 + 1) * F ztbuu *
      G ztbuu * ztwxa =
      κR κf κB zteqw * ztfny * A := by_grind
  zvmyi at hroom ⊢
  zuexw
  have hBig : ztbgq * E.d0 + 10 ≤ κR κf κB zteqw * ztfny * A := by
    have h1 : ztbgq * E.d0 ≤
        (ztyam * ztfny * A) *
          c.nreg 216000 := Nat.mul_le_mul_right _ hBr
    have h2 : κR κf κB zteqw * ztfny * A =
        20 * (ztfny * A) + (ztyam *
          ztfny * A) * c.nreg 216000 := by unfold κR; ring
    grind
  -- initialisation
  zudof
  obtain ⟨c₁, k₁, e₁, hk₁, i02, i03, i04, i05, i06, i10, f₁⟩ := initS_exec (P := P) c hw hW5
  have g₁ : ∀ q, ¬ (216002 ≤ q ∧ q ≤ 216010) → c₁.nreg q = c.nreg q := fun q hq =>
    f₁.1 q by_simp_all
  zuesu
  zucfz
  have hI0 : RInv E 0 c₁ := by
    refine ⟨e₁.wb_right, by_simp_all, by_simp_all, by_simp_all, i02, i03, i04, i05,
      i06, i10, by_simp_all, fun q hq => g₁ q (by unfold KeepR at hq; omega),
      ⟨L₀, E₀, stateAt_congr hSt by_grind m₁ A₁, subset_rfl,
        by simp_all, hsg,
        by simp_all⟩, by_simp_all, by rw [A₁],
      Nat.zero_le _, ?_⟩
    grind
  -- the rounds
  zudef
  have RF₁ : ztzjd :=
    rf_of_frameB (fun r hr => by
      zucy
      exact ztbgh) f₁
  refine ⟨c₂, k₁ + k₂, Exec.seq e₁ e₂, by_omega, ⟨I₂.keep, fun L E hSt' => ?_⟩,
    (RF₁.trans RF₂).to_frame⟩
  -- the post
  have hSt'' := hSt'
  obtain ⟨-, -, hK', -, hLa', -, hEa', -, -, -, -⟩ := hSt''
  obtain ⟨-, -, -, -, hLa, -, hEa, -, -, -, -⟩ := hSt
  zvmyi at hK' hLa' hEa' hLa hEa
  have hLL := BuildNF.chordListAt_unique hLa.holds hLa'.holds by_omega
  subst hLL
  have hEE := hEa.holds.symm.trans hEa'.holds
  subst hEE
  obtain ⟨L', E', hSt₂, hsub, hdeg₂, hsg₂, hcnt₂⟩ := I₂.state
  grind

/-! ## The restoration rounds of the down phase -/
variable (κ γ : ℕ)
theorem shCost_mono : DrvR.shCost κ γ ≤ DrvR.shCost ztkhv γ := by
  unfold DrvR.shCost
  grind
theorem cuCost_mono : DrvR.cuCost κ γ ≤ DrvR.cuCost ztkhv γ := by
  unfold DrvR.cuCost
  simp
theorem shCost_pos : 1 ≤ DrvR.shCost ztkhv γ := by
  unfold DrvR.shCost; omega
theorem cuCost_pos : 1 ≤ DrvR.cuCost ztkhv γ := by
  unfold DrvR.cuCost
  grind

/-- **D8: the restoration rounds of a down-phase level**, from the interior oracles. -/
theorem roundsSpec {O : OracleIface} (hio : DrvR.IntOraclesSpec O) :
    ∃ κo, DrvR.RoundsSpec ztsy (DrvR.shCost κo) (DrvR.cuCost κo) cutGran := by
  obtain ⟨sh, cu, κ, hsh, hcu⟩ := hio
  obtain ⟨mkF, κf, hmk⟩ := Restore.findSpec
  have hsh' := IOrc.shooterOK_weaken hsh ztijh (shCost_mono κ)
  have hcu' := IOrc.cutterOK_weaken hcu ztijh (cuCost_mono κ)
  have hF := hmk sh cu DrvR.ioBandsD DrvR.ioBandsD _ _
    cutGran _ DrvR.OkInt DrvR.ioBandsD DrvR.oracleBands_subset_ioBandsD
    DrvR.bRestore_notin_ioBandsD ztgjv ztqcs
    (fun _ _ h => Or.inr h) subset_rfl subset_rfl hsh' hcu'
  zufzb
  exact ⟨κ + 1, roundsSpec_of hF hB ztgjv (shCost_pos κ) (cuCost_pos κ)⟩
end
end DrvD
end Chazelle.Core
namespace Chazelle.Core
namespace DrvLT
open Machine Machine.Stmt Programs SignK BuildRam
open SortL (seg)
@[expose] public section
theorem inDrv_BL : DrvD.InDrv BL := by
  zuz
  simp only [BL, Bool.or_eq_true, decide_eq_true_eq] at hr
  zulfv
theorem BL_mono {B : ℕ → Bool} (h : ∀ r, B r = true → BL r = true) {c c' : Config}
    (hf : FrameM B c c') : FrameM BL c c' := hf.mono h
section exec
variable {P : Polygon} {W : ℕ}
variable (c : Config) (e : Config)
set_option maxHeartbeats 1000000 in
theorem ltInit_exec (hw : WordsBounded W c) (hW : 3 ≤ W) :
    ∃ c' k, Exec P W ltInit c c' k ∧ k = 5 ∧ c'.nreg 211100 = 1 ∧ c'.nreg 211101 = 3 ∧
      c'.nreg 210034 = 1 ∧ c'.nreg 211110 = c.nreg ALLOC ∧ c'.nreg 211111 = 0 ∧
      FrameB (fun r => decide (r = 211100 ∨ r = 211101 ∨ r = 210034 ∨ r = 211110 ∨
        r = 211111)) c c' := by
  obtain ⟨c', k, ex, hk, q⟩ : ∃ c' k, Exec P W ltInit c c' k ∧ k = 5 ∧
      (c'.nreg 211100 = 1 ∧ c'.nreg 211101 = 3 ∧ c'.nreg 210034 = 1 ∧
        c'.nreg 211110 = c.nreg ALLOC ∧ c'.nreg 211111 = 0) := by
    unfold ltInit
    exec_block
    all_goals try omega
    tauto
  zulzz

/-- The registers of the reservation. -/
def Bres (r : ℕ) : Bool := decide (r = 211111) || decide ztyc

/-- **The reservation** of `5 K₂` words. -/
theorem ltRes_exec {c : Config} (hw : WordsBounded W c) {K₂ : ℕ} (h12 : c.nreg 211012 = K₂)
    (h11 : c.nreg 211111 = 0) (h00 : c.nreg 211100 = 1) (hW : c.nreg ALLOC + 5 * K₂ + 1 ≤ W)
    (A₀ : ℕ) :
    ∃ c' k, Exec P W ltRes c c' k ∧ k ≤ 8 * K₂ + 2 ∧ c'.nreg ALLOC = c.nreg ALLOC + 5 * K₂ ∧
      c'.nreg 211111 = K₂ ∧ FrameB Bres c c' ∧ Restore.RF DrvR.drvBands A₀ c c' k := by
  let Inv : ℕ → Config → Prop := fun j e => WordsBounded W e ∧ e.nreg 211111 = j ∧
    e.nreg 211012 = K₂ ∧ e.nreg 211100 = 1 ∧ e.nreg ALLOC = c.nreg ALLOC + 5 * j ∧
    FrameB Bres c e ∧ j ≤ K₂
  have key : ∀ j e, j < K₂ → Inv j e → ∃ e' k, Exec P W ltResBody e e' k ∧ Inv ztl e' ∧
      Restore.RF DrvR.drvBands A₀ e e' k ∧ k = 6 := by
    zuos

    obtain ⟨e', k, ex, hk, q⟩ : ∃ e' k, Exec P W ltResBody e e' k ∧ k = 6 ∧
        (e'.nreg 211111 = j + 1 ∧ e'.nreg 9999 = c.nreg ALLOC + 5 * ztl) := by
      unfold ltResBody
      exec_block
      all_goals try (config_simp; (try simp only [h1, h3, h4']); omega)
      refine ztkw <;> config_simp <;> simp only [h1, h3, h4']; omega
    zudyy
    have hnot : ztdjz := fun r hr hra => by
      zucqs

    refine ⟨e', k, ex, ⟨ex.wb_right, q.1, (hf'.1 _ by_decide).trans h2,
      (hf'.1 _ by_decide).trans h3, by show e'.nreg 9999 = _; zuouy, hf.trans hf', hj⟩,
      ⟨fun r hr hra => hf'.1 r ztlpu, fun r _ =>
        WalkKey.exec_rframe ex (B := fun _ => false) by_decide r rfl, fun a _ => by zuodj,
        fun a _ => by zuodk, hf'.2.2.2.2, ?_, ?_⟩, hk⟩
    · show e.nreg 9999 ≤ e'.nreg 9999
      omega
    · show e'.nreg 9999 ≤ e.nreg 9999 + k
      omega
  have I0 : ztpki := ⟨hw, h11, h12, h00, by_simp, FrameB.refl _ _, Nat.zero_le _⟩
  obtain ⟨c', k, ex, ⟨j, w', h1, h2, -, h4, hf, hjle⟩, hx, RFl, hk⟩ := Restore.whileLtN_frame
    (P := P) (W := W) (a := 211111) (b := 211012) (body := ltResBody) (B := DrvR.drvBands)
    (A₀ := A₀) ztfrn (fun e => K₂ - e.nreg 211111) 6 ztfro
    (fun e ⟨j, hI⟩ ht => by
      zueo

      exact ztcox) ⟨0, I0⟩
  have hjR : j = K₂ := by_omega
  subst hjR
  refine zthmn
  omega
set_option maxHeartbeats 1000000 in
theorem ltMid_exec (hw : WordsBounded W c) {K₂ A T : ℕ}
    (h12 : c.nreg 211012 = K₂) (h10 : c.nreg 211110 = A) (h09 : c.nreg 211009 = T)
    (hW : A + 3 * K₂ ≤ W) :
    ∃ c' k, Exec P W ltMid c c' k ∧ k = 7 ∧ c'.nreg 211112 = A + 3 * K₂ ∧
      c'.nreg 211113 = A ∧ c'.nreg 211114 = A + 3 * K₂ ∧ c'.nreg 211130 = 0 ∧
      c'.nreg 211131 = T ∧
      FrameB (fun r => decide (r = 211147 ∨ ztnfo ∨ r = 211130 ∨
        r = 211131)) c c' := by
  obtain ⟨c', k, ex, hk, q⟩ : ∃ c' k, Exec P W ltMid c c' k ∧ k = 7 ∧
      (c'.nreg 211112 = A + 3 * K₂ ∧ c'.nreg 211113 = A ∧ c'.nreg 211114 = A + 3 * K₂ ∧
        c'.nreg 211130 = 0 ∧ c'.nreg 211131 = T) := by
    unfold ltMid
    exec_block
    all_goals try (config_simp; (try simp only [h12, h10, h09]); omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩ <;> config_simp <;> (try simp only [h12, h10, h09]) <;>
      omega
  zulzz

/-- The registers `ltB1` writes. -/
def B1 (r : ℕ) : Bool := decide (211140 ≤ r ∧ r ≤ 211145) || decide ztdez
set_option maxHeartbeats 2000000 in
theorem ltB1_exec (hw : WordsBounded W e) {p D : ℕ} (h31 : e.nreg 211131 = p)
    (h00 : e.nreg 211100 = 1) (h13 : e.nreg 211113 = D) (hW : p + 2 ≤ W)
    (hW3 : 3 * e.nmem (p + 1) ≤ W) :
    ∃ e' k, Exec P W ltB1 e e' k ∧ k = 11 ∧ e'.nreg 211140 = e.nmem p ∧
      e'.nreg 211143 = e.nmem (p + 1 + 1) ∧ e'.nreg 211144 = 3 * e.nmem (p + 1) ∧
      e'.nreg 211145 = 2 * e.nmem (p + 1) ∧ e'.nreg 210061 = 3 * e.nmem (p + 1) ∧
      e'.nreg 210062 = e.nmem p ∧ e'.nreg 210063 = D ∧ e'.nmem = e.nmem ∧ FrameB B1 e e' := by
  obtain ⟨e', k, ex, hk, q⟩ : ∃ e' k, Exec P W ltB1 e e' k ∧ k = 11 ∧
      (e'.nreg 211140 = e.nmem p ∧
      e'.nreg 211143 = e.nmem (p + 1 + 1) ∧ e'.nreg 211144 = 3 * e.nmem (p + 1) ∧
      e'.nreg 211145 = 2 * e.nmem (p + 1) ∧ e'.nreg 210061 = 3 * e.nmem (p + 1) ∧
      e'.nreg 210062 = e.nmem p ∧ e'.nreg 210063 = D) := by
    unfold ltB1
    exec_block
    all_goals try (config_simp; (try simp only [h31, h00, h13]); omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> config_simp <;>
      (try simp only [h31, h00, h13]) <;> (try omega)
  have hf := exec_frameB ex (B := B1) (by decide)
  exact ⟨e', k, ex, hk, q.1, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2.1, q.2.2.2.2.2.1,
    q.2.2.2.2.2.2, hf.2.2.1, hf⟩

/-- The registers `ltB2` writes. -/
def B2 (r : ℕ) : Bool := decide (r = 211113) || decide ztdez
set_option maxHeartbeats 1000000 in
theorem ltB2_exec (hw : WordsBounded W e) {a ℓ b D₂ : ℕ}
    (h13 : e.nreg 211113 = a) (h44 : e.nreg 211144 = 3 * ℓ) (h45 : e.nreg 211145 = 2 * ℓ)
    (h43 : e.nreg 211143 = b) (h14 : e.nreg 211114 = D₂) (hW : a + 3 * ℓ ≤ W) :
    ∃ e' k, Exec P W ltB2 e e' k ∧ k = 4 ∧ e'.nreg 211113 = a + 3 * ℓ ∧
      e'.nreg 210061 = 2 * ℓ ∧ e'.nreg 210062 = b ∧ e'.nreg 210063 = D₂ ∧ e'.nmem = e.nmem ∧
      FrameB B2 e e' := by
  obtain ⟨e', k, ex, hk, q⟩ : ∃ e' k, Exec P W ltB2 e e' k ∧ k = 4 ∧
      (e'.nreg 211113 = a + 3 * ℓ ∧ e'.nreg 210061 = 2 * ℓ ∧ e'.nreg 210062 = b ∧
        e'.nreg 210063 = D₂) := by
    unfold ltB2
    exec_block
    all_goals try (config_simp; (try simp only [h13, h44, h45, h43, h14]); omega)
    simp_all
  have hf := exec_frameB ex (B := B2) by_decide
  exact ⟨e', k, ex, hk, q.1, q.2.1, q.2.2.1, q.2.2.2, hf.2.2.1, hf⟩

/-- The registers `ltB3` writes. -/
def B3 (r : ℕ) : Bool := decide (r = 211114) || decide (r = 211131) || decide (r = 211130)
set_option maxHeartbeats 1000000 in
theorem ltB3_exec (hw : WordsBounded W e) {D₂ ℓ p j : ℕ}
    (h14 : e.nreg 211114 = D₂) (h45 : e.nreg 211145 = 2 * ℓ) (h31 : e.nreg 211131 = p)
    (h01 : e.nreg 211101 = 3) (h30 : e.nreg 211130 = j) (h00 : e.nreg 211100 = 1)
    (hW : D₂ + 2 * ℓ ≤ W) (hW2 : p + 3 ≤ W) (hW3 : j + 1 ≤ W) :
    ∃ e' k, Exec P W ltB3 e e' k ∧ k = 3 ∧ e'.nreg 211114 = D₂ + 2 * ℓ ∧
      e'.nreg 211131 = p + 3 ∧ e'.nreg 211130 = j + 1 ∧ e'.nmem = e.nmem ∧
      FrameB B3 e e' := by
  obtain ⟨e', k, ex, hk, q⟩ : ∃ e' k, Exec P W ltB3 e e' k ∧ k = 3 ∧
      (e'.nreg 211114 = D₂ + 2 * ℓ ∧ e'.nreg 211131 = p + 3 ∧ e'.nreg 211130 = j + 1) := by
    unfold ltB3
    exec_block
    all_goals try (config_simp; (try simp only [h14, h45, h31, h01, h30, h00]); omega)
    simp_all
  have hf := exec_frameB ex (B := B3) by_decide
  exact ⟨e', k, ex, hk, q.1, q.2.1, q.2.2, hf.2.2.1, hf⟩
set_option maxHeartbeats 2000000 in
theorem ltArgs_exec (hw : WordsBounded W c) {A K₂ BB K M : ℕ}
    (h10 : c.nreg 211110 = A) (h12 : c.nreg 211012 = K₂) (h112 : c.nreg 211112 = BB)
    (h03 : c.nreg 210003 = K) (h13 : c.nreg 211013 = M) (h01 : c.nreg 211101 = 3)
    (hW : 4 * K + 3 ≤ W) (hW' : 4 * M ≤ W) :
    ∃ c' k, Exec P W ltArgs c c' k ∧ k = 10 ∧ c'.nreg 210020 = A ∧ c'.nreg 210021 = K₂ ∧
      c'.nreg 210022 = BB ∧ c'.nreg 210023 = 4 * K + 3 ∧ c'.nreg 210024 = 4 * M ∧
      c'.nmem = c.nmem ∧
      FrameB (fun r => decide ((210020 ≤ r ∧ r ≤ 210024) ∨ r = 211150 ∨ r = 211151)) c c' := by
  obtain ⟨c', k, ex, hk, q⟩ : ∃ c' k, Exec P W ltArgs c c' k ∧ k = 10 ∧
      (c'.nreg 210020 = A ∧ c'.nreg 210021 = K₂ ∧
      c'.nreg 210022 = BB ∧ c'.nreg 210023 = 4 * K + 3 ∧ c'.nreg 210024 = 4 * M) := by
    unfold ltArgs
    exec_block
    all_goals try (config_simp; (try simp only [h10, h12, h112, h03, h13, h01]); omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩ <;> config_simp <;>
      (try simp only [h10, h12, h112, h03, h13, h01]) <;> (try omega)
  have hf := exec_frameB ex
    (B := fun r => decide ((210020 ≤ r ∧ r ≤ 210024) ∨ r = 211150 ∨ r = 211151)) (by decide)
  exact ⟨c', k, ex, hk, q.1, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2, hf.2.2.1, hf⟩
set_option maxHeartbeats 1000000 in
theorem ltRd_exec (hw : WordsBounded W c) (hW : 134 ≤ W) :
    ∃ c' k, Exec P W ltRd c c' k ∧ k = 2 ∧ c'.nreg 216000 = 134 ∧
      c'.nreg 216001 = c.nreg 211007 ∧ c'.nmem = c.nmem ∧
      FrameB (fun r => decide ztogm) c c' := by
  obtain ⟨c', k, ex, hk, q⟩ : ∃ c' k, Exec P W ltRd c c' k ∧ k = 2 ∧
      (c'.nreg 216000 = 134 ∧ c'.nreg 216001 = c.nreg 211007) := by
    unfold ltRd
    exec_block
    all_goals try omega
    simp
  have hf := exec_frameB ex (B := fun r => decide ztogm) by_decide
  exact ⟨c', k, ex, hk, q.1, q.2, hf.2.2.1, hf⟩
end exec
end
end DrvLT
end Chazelle.Core
namespace Chazelle.Core
namespace DrvLT
open Machine Machine.Stmt Programs SignK BuildRam
open SortL (seg)
@[expose] public section
structure GEnv where
  P : Polygon
  W : ℕ
  A₀ : ℕ
  m₀ : ℕ → ℕ
  r₀ : ℕ → ℕ
  T : ℕ
  B : ℕ
  R : ℕ
  Mx : ℕ
  Q : Polygon
  N : NF
  Lx : ℕ → List zte
namespace GEnv
variable (G : GEnv)

/-- The first `j` kept lists. -/
def flat (j : ℕ) : List zte := (List.range j).flatMap G.Lx

/-- The total kept length. -/
def K₂ : ℕ := (G.flat G.R).length
end GEnv

/-- **The facts of the gather's data.** -/
structure GGood (G : GEnv) : Prop where
  hTB : G.T + 3 * G.R ≤ G.B
  hBA : G.B ≤ G.A₀
  hmem : ∀ r, r < G.R → DrvR.RegMem G.m₀ G.A₀ G.T G.B G.Q G.N r (G.Lx r)
  hMx : ∀ r, r < G.R → (G.Lx r).length ≤ G.Mx
  room : G.A₀ + 5 * G.K₂ + 1 ≤ G.W

/-- **The state after `j` regions.** -/
structure LInv (G : GEnv) (j : ℕ) (e : Config) : Prop where
  wb : WordsBounded G.W e
  r30 : e.nreg 211130 = j
  r11 : e.nreg 211011 = G.R
  r31 : e.nreg 211131 = G.T + 3 * j
  r00 : e.nreg 211100 = 1
  r01 : e.nreg 211101 = 3
  r34 : e.nreg 210034 = 1
  r10 : e.nreg 211110 = G.A₀
  r12 : e.nreg 211112 = G.A₀ + 3 * G.K₂
  r13 : e.nreg 211113 = G.A₀ + 3 * (G.flat j).length
  r14 : e.nreg 211114 = G.A₀ + 3 * G.K₂ + 2 * (G.flat j).length
  alloc : e.nreg ALLOC = G.A₀ + 5 * G.K₂
  keep : ∀ r, BL r = false → r ≠ ALLOC → e.nreg r = G.r₀ r
  low : ∀ a, a < G.A₀ → e.nmem a = G.m₀ a
  list : ChordListAt e.nmem G.A₀ ztpzc
  bkt : ∀ q, q < 2 * (G.flat j).length →
    e.nmem ztnlf = DrvR.keyBkt G.Q G.N (DrvR.endPos ztpzc q)
  jle : j ≤ G.R
theorem seg_pt {m m' : ℕ → ℕ} {a b n q : ℕ} (h : seg m' a n = seg m b n) (hq : q < n) :
    m' zttei = m (b + q) := by
  have := congrArg ztpbr h
  zugze
theorem B1_BL : ∀ r, B1 r = true → BL r = true := by
  intro r h; simp only [B1, BL, Bool.or_eq_true, decide_eq_true_eq] at h ⊢; omega
theorem B2_BL : ∀ r, B2 r = true → BL r = true := by
  intro r h; simp only [B2, BL, Bool.or_eq_true, decide_eq_true_eq] at h ⊢; omega
theorem B3_BL : ∀ r, B3 r = true → BL r = true := by
  intro r h; simp only [B3, BL, Bool.or_eq_true, decide_eq_true_eq] at h ⊢; omega
theorem Bcp_BL : ∀ r, DrvR.Bcp r = true → BL r = true := by
  intro r h; simp only [DrvR.Bcp, BL, Bool.or_eq_true, decide_eq_true_eq] at h ⊢; omega
set_option maxHeartbeats 4000000 in
/-- **One region of the gather.** -/
theorem body_step {G : GEnv} (hG : GGood G) {j : ℕ} {e : Config} (hI : LInv G j e)
    (hj : j < G.R) :
    ∃ e' k, Exec G.P G.W ltBody e e' k ∧ LInv G ztl e' ∧
      Restore.RF DrvR.drvBands G.A₀ e e' k ∧ k ≤ 35 * G.Mx + 30 := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := hG.hmem j hj
  have hTB := hG.hTB
  have hBA := hG.hBA
  zumer
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, (G.Lx j).length = ℓ := zths
  obtain ⟨F, hF⟩ : ∃ F, (G.flat j).length = F := zths
  rw [hℓ] at g1 g3 g6
  have hF1 : (G.flat ztl).length = F + ℓ := by
    show ((List.range ztl).flatMap G.Lx).length = _
    rw [flat_succ, List.length_append, ← hℓ, ← hF]; rfl
  have hFK : F + ℓ ≤ G.K₂ := by
    rw [← hF1]; exact flat_length_mono G.Lx by_omega
  have hℓM : ℓ ≤ G.Mx := hℓ ▸ hG.hMx j hj
  have r13 := hI.r13
  have r14 := hI.r14
  zvoij at r13 r14
  -- the table entry
  have t0 : e.nmem ztgdw = G.m₀ ztgdw := hI.low _ by_omega
  have t1 : e.nmem (G.T + 3 * j + 1) = ℓ := by rw [hI.low _ by_omega]; exact g1
  have t2 : e.nmem (G.T + 3 * j + 1 + 1) = G.m₀ zthaq := hI.low _ by_omega
  -- 1. the entry
  obtain ⟨e₁, k₁, x₁, hk₁, a40, a43, a44, a45, a61, a62, a63, m₁, f₁⟩ :=
    ltB1_exec (P := G.P) e hI.wb hI.r31 hI.r00 r13 by_omega by_omega
  rw [t0] at a40 a62
  rw [t1] at a44 a45 a61
  rw [t2] at a43
  zubcr
  have k₁r : ∀ r, B1 r = false → e₁.nreg r = e.nreg r := f₁.1
  -- 2. the triples
  obtain ⟨e₂, k₂, x₂, hk₂, w₂, sg₂, mo₂, f₂⟩ := DrvR.cpS_exec (P := G.P) (W := G.W) w₁
    (S := G.m₀ ztgdw) (D := G.A₀ + 3 * F) a61 a62 a63
    (by rw [k₁r _ by_decide]; exact hI.r34) ztec by_omega by_omega
  have k₂r : ∀ r, DrvR.Bcp r = false → e₂.nreg r = e₁.nreg r := f₂.1
  -- 3. the bucket arguments
  obtain ⟨e₃, k₃, x₃, hk₃, a13, b61, b62, b63, m₃, f₃⟩ := ltB2_exec (P := G.P) e₂ w₂
    (a := G.A₀ + 3 * F) (ℓ := ℓ) (b := G.m₀ zthaq)
    (D₂ := G.A₀ + 3 * G.K₂ + 2 * F)
    (by rw [k₂r _ by_decide, k₁r _ by_decide, r13])
    (by rw [k₂r _ by_decide, a44]) (by rw [k₂r _ by_decide, a45])
    (by rw [k₂r _ by_decide, a43])
    (by rw [k₂r _ by_decide, k₁r _ by_decide, r14]) by_omega
  zuchd
  have k₃r : ∀ r, B2 r = false → e₃.nreg r = e₂.nreg r := f₃.1
  -- 4. the buckets
  obtain ⟨e₄, k₄, x₄, hk₄, w₄, sg₄, mo₄, f₄⟩ := DrvR.cpS_exec (P := G.P) (W := G.W) w₃
    (S := G.m₀ zthaq) (D := G.A₀ + 3 * G.K₂ + 2 * F) b61 b62 b63
    (by rw [k₃r _ by_decide, k₂r _ by_decide, k₁r _ by_decide]; exact hI.r34)
    ztec by_omega by_omega
  have k₄r : ∀ r, DrvR.Bcp r = false → e₄.nreg r = e₃.nreg r := f₄.1
  -- 5. the pointers
  have r4 : ∀ r, B1 r = false → DrvR.Bcp r = false → B2 r = false →
      e₄.nreg r = e.nreg r := fun r h1 h2 h3 => by
    grind
  obtain ⟨e₅, k₅, x₅, hk₅, c14, c31, c30, m₅, f₅⟩ := ltB3_exec (P := G.P) e₄ w₄
    (D₂ := G.A₀ + 3 * G.K₂ + 2 * F) (ℓ := ℓ) (p := G.T + 3 * j) (j := j)
    (by rw [r4 _ by_decide by_decide by_decide, r14])
    (by rw [k₄r _ by_decide, k₃r _ by_decide, k₂r _ by_decide, a45])
    (by rw [r4 _ by_decide by_decide by_decide, hI.r31])
    (by rw [r4 _ by_decide by_decide by_decide, hI.r01])
    (by rw [r4 _ by_decide by_decide by_decide, hI.r30])
    (by rw [r4 _ by_decide by_decide by_decide, hI.r00]) by_omega by_omega
    by_omega
  have k₅r : ∀ r, B3 r = false → e₅.nreg r = e₄.nreg r := f₅.1
  -- the memory
  have mem5 : ∀ a, e₅.nmem a = if G.A₀ + 3 * G.K₂ + 2 * F ≤ a ∧
      a < G.A₀ + 3 * G.K₂ + 2 * F + 2 * ℓ then e₄.nmem a
      else if G.A₀ + 3 * F ≤ a ∧ a < G.A₀ + 3 * F + 3 * ℓ then e₂.nmem a else e.nmem a := by
    zumgj
    zunjy
    zupi
    · rfl
    · grind
    grind
  have low5 : ∀ a, a < G.A₀ → e₅.nmem a = e.nmem a := fun a ha => by
    rw [mem5 a, ite_eq_right by_omega, ite_eq_right by_omega]
  -- the frame
  have fr : FrameM BL e e₅ :=
    ((((BL_mono B1_BL (BuildRam.FrameB.toM f₁)).trans (BL_mono Bcp_BL f₂)).trans
      (BL_mono B2_BL (BuildRam.FrameB.toM f₃))).trans
      (BL_mono Bcp_BL f₄)).trans (BL_mono B3_BL (BuildRam.FrameB.toM f₅))
  have r5 : ∀ r, BL r = false → e₅.nreg r = e.nreg r := fun r hr => fr.1 r hr
  have r5' : ∀ r, B1 r = false → DrvR.Bcp r = false → B2 r = false → B3 r = false →
      e₅.nreg r = e.nreg r := fun r h1 h2 h3 h4 => by_grind
  refine ⟨e₅, k₁ + ztwqm, Exec.seq x₁ (Exec.seq x₂ (Exec.seq x₃
    ztsxc)), ?_, DrvD.rf_of_frameM inDrv_BL fr low5, by_omega⟩
  refine ⟨x₅.wb_right, by rw [c30], by rw [r5 _ by_decide, hI.r11], by_omega,
    by rw [r5' _ by_decide by_decide by_decide by_decide, hI.r00],
    by rw [r5' _ by_decide by_decide by_decide by_decide, hI.r01],
    by rw [r5' _ by_decide by_decide by_decide by_decide, hI.r34],
    by rw [r5' _ by_decide by_decide by_decide by_decide, hI.r10],
    by rw [r5' _ by_decide by_decide by_decide by_decide, hI.r12], ?_, by_omega,
    by rw [r5 _ by_decide, hI.alloc],
    fun r hr hra => by rw [r5 r hr, hI.keep r hr hra], fun a ha => by rw [low5 a ha, hI.low a ha],
    ?_, ?_, by_omega⟩
  · -- the triple pointer
    have : e₅.nreg 211113 = e₄.nreg 211113 := k₅r _ by_decide
    rw [this, k₄r _ by_decide, a13, hF1]; ring
  · -- the triples
    show ChordListAt e₅.nmem G.A₀ ((List.range ztl).flatMap G.Lx)
    rw [flat_succ]
    refine DrvR.chordListAt_append ?_ ?_
    · refine DrvR.clAt_congr hI.list fun x hx1 hx2 => ?_
      have hF' : ((List.range j).flatMap G.Lx).length = F := hF
      rw [mem5 x, ite_eq_right by_omega, ite_eq_right by_omega]
    · have e3 : (List.range j).flatMap G.Lx = G.flat j := rfl
      rw [e3, hF]
      refine DrvR.chordListAt_of_seg (m := G.m₀) (B := G.m₀ ztgdw) g4 ?_
      rw [hℓ]
      zuhav
      zucfh
      zug
      zucpm
      rw [mem5, ite_eq_right by_omega, ite_eq_left by_omega, seg_pt sg₂ hi, m₁, hI.low _ by_omega]
  · -- the buckets
    zuco
    rw [hF1] at hq
    have e1 : G.flat ztl = G.flat j ++ G.Lx j := flat_succ G.Lx j
    zukd
    rcases Nat.lt_or_ge q (2 * F) with hq1 | hq1
    · rw [mem5, ite_eq_right by_omega, ite_eq_right by_omega, hI.bkt q by_omega,
        DrvLM.endPos_append_left by_omega]
    · obtain ⟨q', rfl⟩ : ∃ q', q = 2 * F + q' := ⟨q - 2 * F, by_omega⟩
      have ea := DrvLM.endPos_append_right ztpzc (G.Lx j) q'
      zvoij at ea
      rw [ea, mem5, ite_eq_left by_omega,
        show G.A₀ + 3 * G.K₂ + (2 * F + q') = G.A₀ + 3 * G.K₂ + 2 * F + q' by ring,
        seg_pt sg₄ by_omega, m₃, mo₂ _ by_omega, m₁, hI.low _ by_omega]
      grind
set_option maxHeartbeats 1000000 in
/-- **The gather loop.** -/
theorem loop_exec {G : GEnv} (hG : GGood G) {e : Config} (hI : LInv G 0 e) :
    ∃ e' k, Exec G.P G.W ltLoop e e' k ∧ LInv G G.R e' ∧
      Restore.RF DrvR.drvBands G.A₀ e e' k ∧ k ≤ ztpuj * G.R + 2 := by
  obtain ⟨e', k, ex, ⟨j, hJ⟩, hx, RFl, hk⟩ := Restore.whileLtN_frame (P := G.P) (W := G.W)
    (a := 211130) (b := 211011) (body := ltBody) (B := DrvR.drvBands) (A₀ := G.A₀)
    (fun e => ∃ j, LInv G j e) (fun e => G.R - e.nreg 211130) (35 * G.Mx + 30)
    (fun e ⟨_, h⟩ => h.wb)
    (fun e ⟨j, hJ⟩ ht => by
      rw [hJ.r30, hJ.r11] at ht
      obtain ⟨e', k, ex, hJ', RF', hk⟩ := body_step hG hJ ht
      exact ⟨e', k, ex, ⟨j + 1, hJ'⟩, RF', hk, by rw [hJ.r30, hJ'.r30]; omega⟩) ⟨0, hI⟩
  have hjR : j = G.R := by rw [hJ.r30, hJ.r11] at hx; have := hJ.jle; omega
  subst hjR
  refine ⟨e', k, ex, hJ, RFl, ?_⟩
  rw [hI.r30] at hk
  omega
end
end DrvLT
end Chazelle.Core
namespace Chazelle.Core
namespace DrvLT
open Machine Machine.Stmt Programs SignK BuildRam
open SortL (seg)
@[expose] public section
theorem nRegions_build (M : Model) (Q : Polygon) (L : List zte) (E : List ℕ) :
    (BuildNF.buildNF M Q L E).nRegions = L.length + 1 := by
  zudvx
set_option maxHeartbeats 4000000 in
/-- **The gather.** -/
theorem gather_exec {G : GEnv} (hG : GGood G) {c : Config} (hw : WordsBounded G.W c)
    (hA : c.nreg ALLOC = G.A₀) (hm : c.nmem = G.m₀) (hr : c.nreg = G.r₀)
    (h12 : c.nreg 211012 = G.K₂) (h11 : c.nreg 211011 = G.R) (h09 : c.nreg 211009 = G.T)
    (h13 : c.nreg 211013 = G.Mx) {K : ℕ} (h03 : c.nreg 210003 = K) (hWK : 4 * K + 3 ≤ G.W)
    (hWM : 4 * G.Mx ≤ G.W) :
    ∃ e k, Exec G.P G.W gatherS c e k ∧ k ≤ 8 * G.K₂ + ztpuj * G.R + 26 ∧
      WordsBounded G.W e ∧
      e.nreg 210020 = G.A₀ ∧ e.nreg 210021 = G.K₂ ∧ e.nreg 210022 = G.A₀ + 3 * G.K₂ ∧
      e.nreg 210023 = 4 * K + 3 ∧ e.nreg 210024 = 4 * G.Mx ∧
      e.nreg ALLOC = G.A₀ + 5 * G.K₂ ∧
      (∀ r, BL r = false → r ≠ ALLOC → e.nreg r = c.nreg r) ∧
      (∀ a, a < G.A₀ → e.nmem a = G.m₀ a) ∧
      ChordListAt e.nmem G.A₀ ztuyx ∧
      (∀ q, q < 2 * G.K₂ →
        e.nmem ztnlf = DrvR.keyBkt G.Q G.N (DrvR.endPos ztuyx q)) ∧
      Restore.RF DrvR.drvBands G.A₀ c e k := by
  zumer
  -- 1. constants
  obtain ⟨c₁, k₁, x₁, hk₁, i00, i01, i34, i10, i11, f₁⟩ :=
    ltInit_exec (P := G.P) c hw by_omega
  have g₁ : ∀ r, ¬ (r = 211100 ∨ r = 211101 ∨ r = 210034 ∨ r = 211110 ∨ r = 211111) →
      c₁.nreg r = c.nreg r := fun r h => f₁.1 r by_simp_all
  zubcr
  have A₁ : c₁.nreg ALLOC = G.A₀ := by rw [g₁ _ by_decide, hA]
  -- 2. the reservation
  obtain ⟨c₂, k₂, x₂, hk₂, A₂, j11, f₂, RF₂⟩ := ltRes_exec (P := G.P) w₁ (K₂ := G.K₂)
    by_grind i11 i00 by_omega G.A₀
  zugbn
  have g₂ : ∀ r, r ≠ 211111 → r ≠ 9999 → c₂.nreg r = c₁.nreg r := fun r h1 h2 =>
    f₂.1 r ztljo
  zuboj
  -- 3. the set-up
  obtain ⟨c₃, k₃, x₃, hk₃, s12, s13, s14, s30, s31, f₃⟩ := ltMid_exec (P := G.P) c₂ w₂
    (K₂ := G.K₂) (A := G.A₀) (T := G.T)
    by_grind
    by_grind
    by_grind by_omega
  have g₃ : ∀ r, ¬ (r = 211147 ∨ ztnfo ∨ r = 211130 ∨ r = 211131) →
      c₃.nreg r = c₂.nreg r := fun r h => f₃.1 r by_grind
  zuchd
  have back : ∀ r, BL r = false → r ≠ ALLOC → c₃.nreg r = c.nreg r := by
    zujbl
    simp only [BL, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr
    zugzy
    rw [g₃ r by_omega, g₂ r by_omega hra, g₁ r by_omega]
  have I0 : LInv G 0 c₃ := by
    refine ⟨w₃, s30, ?_, by_omega, ?_, ?_, ?_, ?_, s12, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      Nat.zero_le _⟩
    · grind
    · grind
    · grind
    · grind
    · grind
    · rw [s13]; rfl
    · rw [s14]; rfl
    · rw [g₃ _ by_decide, A₂]
    · grind
    · zulmm
      rw [f₃.2.2.1, f₂.2.2.1, f₁.2.2.1, hm]
    · intro i hi; simp [GEnv.flat] at hi
    · intro q hq; simp [GEnv.flat] at hq
  -- 4. the loop
  obtain ⟨c₄, k₄, x₄, I₄, RF₄, hk₄⟩ := loop_exec hG I0
  -- 5. the arguments
  obtain ⟨c₅, k₅, x₅, hk₅, v20, v21, v22, v23, v24, m₅, f₅⟩ := ltArgs_exec (P := G.P) c₄ I₄.wb
    (A := G.A₀) (K₂ := G.K₂) (BB := G.A₀ + 3 * G.K₂) (K := K) (M := G.Mx) I₄.r10
    (by rw [I₄.keep _ by_decide by_decide, ← hr, h12]) I₄.r12
    (by rw [I₄.keep _ by_decide by_decide, ← hr, h03])
    (by rw [I₄.keep _ by_decide by_decide, ← hr, h13]) I₄.r01 hWK hWM
  have g₅ : ∀ r, ¬ (ztcku ∨ r = 211150 ∨ r = 211151) →
      c₅.nreg r = c₄.nreg r := fun r h => f₅.1 r by_grind
  -- frames
  have RF₁ : Restore.RF DrvR.drvBands G.A₀ c c₁ k₁ :=
    DrvD.rf_of_frameB (fun r hr => by
      zucy
      exact ztbbi) f₁
  have RF₃ : Restore.RF DrvR.drvBands G.A₀ c₂ c₃ k₃ :=
    DrvD.rf_of_frameB (fun r hr => by
      zucy
      exact ztbbi) f₃
  have RF₅ : Restore.RF DrvR.drvBands G.A₀ c₄ c₅ k₅ :=
    DrvD.rf_of_frameB (fun r hr => by
      zucy
      exact ztbbi) f₅
  refine ⟨c₅, k₁ + ztwqm, Exec.seq x₁ (Exec.seq x₂ (Exec.seq x₃
    ztsxc)), by_omega, x₅.wb_right, v20, v21, v22, v23, v24, ?_, ?_, ?_, ?_, ?_,
    RF₁.trans ztmcg⟩
  · rw [g₅ _ by_decide, I₄.alloc]
  · intro r hb hra
    zuixn
    simp only [BL, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hb'
    rw [g₅ r by_omega, I₄.keep r hb hra, ← hr]
  · intro a ha; rw [m₅, I₄.low a ha]
  · zunjy; exact I₄.list
  · intro q hq; zunjy; exact I₄.bkt q (by unfold GEnv.K₂ at hq; omega)
theorem n_le_top (P : Polygon) : (Qof P).n ≤ 2 ^ topGrade P.n + 1 := by
  zuc
  have := Nat.le_pow_clog (b := 2) by_norm_num ztch
  zuhrf
  omega
theorem pow12 (e : ℕ) : 2 ^ (e + 12) = 4 * 2 ^ (e + 10) := by
  grind
set_option maxHeartbeats 64000000 in
/-- **D12: the tail of a level.** -/
theorem lvTailSpec {O : OracleIface} (hio : DrvR.IntOraclesSpec O) : DrvR.LvTailSpec O := by
  classical
  zufzb
  obtain ⟨κo, sRd, κRd, hRd⟩ := DrvD.roundsSpec hio
  obtain ⟨κc, hκc⟩ := DrvLC.lvCostSpec.2 κo
  refine ⟨tailS sB sRd, 300 + 48 * κc + 5 * DrvR.κSpl κB * κc + κRd 134 * κc, ?_⟩
  intro Kb P W c₁ c L E reg lam X hI3 hInv hroom
  obtain ⟨hw, -, h11, hfix, hlow, -, hnreg, -, -, hA1, -, C, NR, γR, Lx, h12, hMx, hMor, hreg⟩ :=
    hInv
  -- the registers of the context
  have hfx : ∀ q, DrvR.LvFixed q → c.nreg q = c₁.nreg q := hfix
  have c00 : c.nreg 210000 = lam := by rw [hfx _ by_tauto, X.r00]
  have c01 : c.nreg 210001 = c₁.nreg 210001 := hfx _ by_tauto
  have c02 : c.nreg 210002 = c₁.nreg 210002 := hfx _ by_tauto
  have c03 : c.nreg 210003 = L.length := by rw [hfx _ by_tauto, X.r03]
  have c04 : c.nreg 210004 = c₁.nreg 210004 := hfx _ by_tauto
  have c07 : c.nreg 211007 = 2 ^ ztxdm := by
    rw [hfx _ ztqfw, X.r07]
  have c09 : c.nreg 211009 = c₁.nreg 211009 := hfx _ ztqfw
  have hT : c₁.nreg 211009 + 3 * ztkr = c₁.nreg ALLOC := X.r09
  have hK : ztmsl := List.length_pos_iff_exists_mem.2 (List.exists_mem_of_ne_nil _ X.hL)
  have hnR : (BuildNF.buildNF ztwiq zta L E).nRegions = L.length + 1 :=
    nRegions_build _ _ _ _
  have hμ15 : 15 ≤ DrvR.nextLvl lam := by
    unfold DrvR.nextLvl; zuovp; have := X.h16; omega
  have hp10 : 128 ≤ 2 ^ ztyds :=
    le_trans by_norm_num (Nat.pow_le_pow_right by_norm_num (show 7 ≤ _ by omega))
  have hγ₀ : c₁.nreg 211006 + 128 ≤ 2 ^ ztxdm := by
    rw [X.r06, pow12]; omega
  -- the math of the level
  obtain ⟨-, hlm⟩ := DrvLM.levelMathSpec P L E reg lam X.good X.hL X.ok X.perm X.sort X.deg X.wt
    X.regs
  obtain ⟨hsize, hok', hbk, hcode, hbcnt, hfam⟩ := hlm ztvmp ztqhr C NR γR
    Lx hγ₀ (fun r hr => by
      rw [hnR] at hr
      obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩, -⟩ := hreg r hr
      exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, hMx r hr⟩)
  rw [hnR] at hsize hok' hbk hcode hbcnt hfam
  -- the sizes
  have hlen : ∀ r, r < L.length + 1 → (Lx r).length ≤ DrvR.lvNch ztbbo :=
    fun r hr => by
      have := hsize r hr
      rw [X.r06] at this
      exact le_lvNch this
  have hMν : c.nreg 211013 ≤ DrvR.lvNch ztbbo := by
    rcases hMor with h | ⟨r, hr, h⟩
    · omega
    · zvmwc; exact hlen r hr
  have hK₂ : ((List.range ztkr).flatMap Lx).length ≤ ztkr * c.nreg 211013 :=
    flat_length_le Lx _ _ hMx
  obtain ⟨hc1, hc2, hc3⟩ := hκc ztbbo hμ15
  have hc3' : (DrvR.lvNch ztbbo + 1) *
      (DrvR.shCost κo ztxcd * DrvR.cuCost κo ztxcd *
        (cutGran ztxcd + Nat.clog 2 ztxcd + 1)) ≤
      κc * ztzmm := by
    refine le_trans ztkad hc3; ring
  have hcost := cost_le (R := L.length + 1) (K := L.length)
    (K₂ := ((List.range ztkr).flatMap Lx).length) (M := c.nreg 211013)
    (ν := DrvR.lvNch ztbbo) (Λ := lemma41Nat ztbbo + 1) (κc := κc)
    (κS := DrvR.κSpl κB) (κr := κRd 134) rfl hK₂ hMν by_omega hc1 hc2 hc3'
  obtain ⟨hW134, hWK, hWM⟩ := room_small (R := L.length + 1) (K := L.length)
    (M := c.nreg 211013) (κc := κc) (κS := DrvR.κSpl κB) (κr := κRd 134) rfl hMν by_omega hc1
  set κ := 300 + 48 * κc + 5 * DrvR.κSpl κB * κc + κRd 134 * κc with hκ
  set B := κ * ztkr * ztzmm with hBd
  set K₂ := ((List.range ztkr).flatMap Lx).length with hK₂d
  set L₂ := (List.range ztkr).flatMap Lx with hL₂d
  -- 1. the gather
  let G : GEnv := ⟨P, W, c.nreg ALLOC, c.nmem, c.nreg, c₁.nreg 211009, c₁.nreg ALLOC,
    L.length + 1, c.nreg 211013, Qof P, BuildNF.buildNF ztwiq zta L E, Lx⟩
  have hGK : G.K₂ = K₂ := rfl
  have hGG : GGood G := ⟨by show c₁.nreg 211009 + 3 * ztkr ≤ c₁.nreg ALLOC; omega,
    hA1, fun r hr => (hreg r hr).2, hMx, by show c.nreg ALLOC + 5 * G.K₂ + 1 ≤ W; omega⟩
  obtain ⟨cg, kg, xg, hkg0, wg, v20₀, v21₀, v22₀, v23, v24₀, Ag₀, keepg, lowg₀, CLg₀, bkg₀, RFg₀⟩ :=
    gather_exec (G := G) hGG hw rfl rfl rfl h12 h11 (by rw [c09]) rfl c03
      (by show 4 * L.length + 3 ≤ W; omega) (by show 4 * c.nreg 211013 ≤ W; omega)
  have hkg : kg ≤ 8 * K₂ + (35 * c.nreg 211013 + 32) * ztkr + 26 := hkg0
  have v20 : cg.nreg 210020 = c.nreg ALLOC := v20₀
  have v21 : cg.nreg 210021 = K₂ := v21₀
  have v22 : cg.nreg 210022 = c.nreg ALLOC + 3 * K₂ := v22₀
  have v24 : cg.nreg 210024 = 4 * c.nreg 211013 := v24₀
  have Ag : cg.nreg ALLOC = c.nreg ALLOC + 5 * K₂ := Ag₀
  have lowg : ∀ a, a < c.nreg ALLOC → cg.nmem a = c.nmem a := lowg₀
  have CLg : ChordListAt cg.nmem ztm L₂ := CLg₀
  have bkg : ∀ q, q < 2 * K₂ → cg.nmem (c.nreg ALLOC + 3 * K₂ + q) =
      DrvR.keyBkt zta ztbaja
        ztnkn := bkg₀
  have RFg : Restore.RF DrvR.drvBands ztm c cg kg := RFg₀
  have gk : ∀ r, BL r = false → r ≠ ALLOC → cg.nreg r = c.nreg r := keepg
  have g01 : cg.nreg 210001 = c₁.nreg 210001 := by rw [gk _ by_decide by_decide, c01]
  have g02 : cg.nreg 210002 = c₁.nreg 210002 := by rw [gk _ by_decide by_decide, c02]
  have g03 : cg.nreg 210003 = L.length := by rw [gk _ by_decide by_decide, c03]
  have g04 : cg.nreg 210004 = c₁.nreg 210004 := by rw [gk _ by_decide by_decide, c04]
  have g00 : cg.nreg 210000 = lam := by rw [gk _ by_decide by_decide, c00]
  have g07 : cg.nreg 211007 = 2 ^ ztxdm := by
    rw [gk _ by_decide by_decide, c07]
  -- the memory below the table
  have hTA : c₁.nreg 211009 ≤ c.nreg ALLOC := by_omega
  have memg : ∀ a, a < c₁.nreg 211009 → cg.nmem a = c₁.nmem a := fun a ha => by
    rw [lowg a by_omega]; exact hlow a ha
  have hMD : ModelDescAt cg.nmem ztqkf zta ztwiq :=
    X.md cg.nmem memg
  have hone : cg.nmem ztqkf = 1 := DrvD.desc_one hMD
  have hmdA := X.mdA
  have hlA := X.lA
  have heA := X.eA
  have hGM : GoodModel ztwiq :=
    Or.inr ⟨Qof P, (shearInvariance ztbhs P).1 X.good.1, rfl⟩
  -- the buckets
  have hbkOf : ∀ q, q < 2 * K₂ → DrvR.bkOf cg q =
      DrvR.keyBkt zta ztbaja
        ztnkn := fun q hq => by
    show cg.nmem (cg.nreg 210022 + q) = _
    zuodg; exact bkg q hq
  have harcs : (BuildNF.buildNF ztwiq zta L E).arcs.length ≤
      2 * L.length + 1 := DrvD.arcs_length_le (by rw [X.perm.length_eq, List.length_range])
  -- 2. the splice
  have hsplCost : DrvR.splCost κB cg = DrvR.κSpl κB * ztihh *
      ztkqe := by
    unfold DrvR.splCost
    zuju
    rw [g03, v21, v23, v24]
  obtain ⟨cs, ks, xs, hks, ⟨keepS, postS⟩, Fs⟩ := DrvR.splice_meets hB P W cg wg
    ⟨X.good, X.wh, by
      show ModelDescWF P _ cg.nmem ztqjq
      zuodr
      exact ztgy,
      interiorModel zta, L, L₂, E, by
      show ModelDescAt cg.nmem ztqjq _ _
      zuodr; omega, hGM, by show cg.nreg 210003 = _; omega, by
      show cg.nreg 210002 + 3 * L.length ≤ cg.nreg ALLOC
      omega, by
      show ChordListAt cg.nmem ztvle L
      zuovq; exact X.lmem cg.nmem memg, by
      show cg.nreg 210021 = _; zunry, by
      show cg.nreg 210020 + 3 * L₂.length ≤ cg.nreg ALLOC
      omega, by
      show ChordListAt cg.nmem ztvlf L₂
      zuods; omega, hok', by
      show cg.nreg 210004 + 2 * L.length ≤ cg.nreg ALLOC
      omega, by
      show seg cg.nmem (cg.nreg 210004) _ = E
      rw [g04]; exact X.emem cg.nmem memg, X.perm, X.sort, by
      show cg.nreg 210022 + 2 * L₂.length ≤ cg.nreg ALLOC
      omega,
      fun q hq => by
        show DrvR.bkOf cg q ≤ cg.nreg 210023
        rw [hbkOf q hq, v23]
        have := hbk q hq
        omega,
      fun q q' hq hq' hb => by
        rw [hbkOf q hq, hbkOf q' hq'] at hb
        exact hcode q q' hq hq' hb,
      fun b => by
        show DrvR.bcnt _ _ b ≤ cg.nreg 210024
        rw [v24, DrvLM.bcnt_congr
          hbkOf]
        exact hbcnt b⟩
    (by show cg.nreg ALLOC + DrvR.splCost κB cg ≤ W; omega)
  have ws := xs.wb_right
  have hks' : ks ≤ DrvR.κSpl κB * ztihh *
      ztkqe := by
    have h : ks ≤ DrvR.splCost κB cg := hks
    omega
  obtain ⟨p3, p2l, p2b, p2, p4l, p4b, pperm, psort, p5l, pNW⟩ := postS ztwiq L L₂
    (by show ModelDescAt cg.nmem ztqjq _ _; zuodr; omega)
    (by show cg.nreg 210003 = _; omega)
    (by show ChordListAt cg.nmem ztvle L; zuovq; exact X.lmem cg.nmem memg)
    (by show cg.nreg 210021 = _; zunry)
    (by show ChordListAt cg.nmem ztvlf L₂; zuods; omega)
  zufl

  zujzl
  have As : cg.nreg ALLOC ≤ cs.nreg ALLOC := Fs.2.2.2.2.2.1
  have As' : cs.nreg ALLOC ≤ cg.nreg ALLOC + ks := Fs.2.2.2.2.2.2
  set E' := seg cs.nmem (cs.nreg 210004) ztxdl with hE'
  have hperm' : E'.Perm ztiqa := by rw [hLL]; omega
  have hsort' : E'.Pairwise (BuildNF.codeLe ztwiq zta ztfi) := psort
  obtain ⟨fsub, fdeg, fsg, fcnt⟩ := hfam E' hperm' hsort'
  -- 3. the arguments of the rounds
  obtain ⟨cr, kr0, xr0, hkr0, u00, u01, mr, fr⟩ := ltRd_exec (P := P) cs ws by_omega
  have gr : ∀ q, q ≠ 216000 → q ≠ 216001 → cr.nreg q = cs.nreg q := fun q h1 h2 =>
    fr.1 q zthfj
  have wr := xr0.wb_right
  have Ar : cr.nreg ALLOC = cs.nreg ALLOC := gr _ by_decide by_decide
  have r1 : cr.nreg 210001 = c₁.nreg 210001 := by
    rw [gr _ by_norm_num by_norm_num, keepS _ by_omega, g01]
  have rγ : cr.nreg 216001 = 2 ^ ztxdm := by
    rw [u01, keepS _ by_omega, g07]
  -- the frames so far
  have RFs : Restore.RF DrvR.drvBands ztm cg cs ks :=
    (Restore.RF.of_frame Fs by_omega).mono DrvD.splBands_sub le_rfl
  have RFr : Restore.RF DrvR.drvBands ztm cs cr kr0 :=
    DrvD.rf_of_frameB (fun r hr => by
      zucy
      exact ztbbi) fr
  have RF3 := RFg.trans (RFs.trans RFr)
  have memr : ∀ a, a < c₁.nreg 211009 → cr.nmem a = c₁.nmem a := fun a ha => by
    rw [RF3.2.2.1 a by_omega]; exact hlow a ha
  have hcore : ∀ i, i < 10000 → cr.nreg ztfgz = c₁.nreg ztfgz := fun i hi => by
    have hb : bandOf ztfgz ∉ DrvR.drvBands := by
      rw [DrvR.coreReg_band i hi]; decide
    rw [RF3.1 _ hb ztswt, hnreg _ hb ztswt]
  have Acr : c.nreg ALLOC ≤ cr.nreg ALLOC := RF3.2.2.2.2.2.1
  -- the state after the splice
  have hst : DrvR.StateAt P cr ztfi E' := by
    have r2 : cr.nreg 210002 = cs.nreg 210002 := gr _ by_norm_num by_norm_num
    have r3 : cr.nreg 210003 = cs.nreg 210003 := gr _ by_norm_num by_norm_num
    have r4 : cr.nreg 210004 = cs.nreg 210004 := gr _ by_norm_num by_norm_num
    have r5 : cr.nreg 210005 = cs.nreg 210005 := gr _ by_norm_num by_norm_num
    refine ztfcy <;>
      zuju
    · zvnal; omega
    · zvnal; exact (X.md.transport memr).mono by_omega
    · omega
    · omega
    · rw [r2, Ar, mr]; exact DrvD.chordListAt_robust p2 by_omega
    · omega
    · rw [r4, Ar, mr, hLL]; exact DrvD.seg_robust by_omega
    · rw [r5, Ar, mr]; omega
  -- 4. the rounds
  have hcostR : κRd ztvly * ztily *
      DrvR.shCost κo ztfha * DrvR.cuCost κo ztfha *
      ztyiy =
      κRd 134 * (L.length + K₂ + 1) *
        (DrvR.shCost κo ztxcd *
          DrvR.cuCost κo ztxcd *
          (cutGran ztxcd +
            Nat.clog 2 ztxcd + 1)) := by
    have e3 : rd cr bDownDrv 3 = L.length + K₂ := by
      show cr.nreg 210003 = _
      rw [gr _ by_norm_num by_norm_num, p3]
    rw [e3, u00, rγ]
    unfold DrvR.lvGr
    ring
  obtain ⟨c', k₄, x₄, hk₄, ⟨keepR, postR⟩, F₄⟩ := hRd P W cr wr
    ⟨X.envD (hcore 0 by_norm_num) (hcore 1 by_norm_num) memr by_omega, by_omega,
      by omega, by zuovr; exact X.big2, L ++ L₂, E', hst,
      by rw [u00]; exact fdeg, by zuovr; omega⟩
    (by
      show cr.nreg ALLOC + κRd _ * ztily *
        DrvR.shCost κo _ * DrvR.cuCost κo _ *
        (cutGran _ + Nat.clog 2 _ + 1) ≤ W
      rw [hcostR, Ar]; omega)
  obtain ⟨L', E'', st', sub', deg', sg', cnt'⟩ := postR ztfi E' hst
  have hk₄' : k₄ ≤ κRd ztvly * ztily *
      DrvR.shCost κo ztfha * DrvR.cuCost κo ztfha *
      ztyiy := hk₄
  rw [hcostR] at hk₄'
  have RF4 : Restore.RF DrvR.drvBands ztm cr c' k₄ :=
    Restore.RF.of_frame F₄ Acr
  have RFall := RF3.trans RF4
  refine ⟨c', kg + (ks + (kr0 + k₄)), Exec.seq xg (Exec.seq xs (Exec.seq xr0 x₄)), ?_,
    (RFall.mono subset_rfl by_omega).to_frame, ?_, ?_⟩
  · -- the cost
    omega
  · -- the level register
    rw [keepR _ ztp, gr _ by_norm_num by_norm_num,
      keepS _ by_omega, g00]
  · -- `Inv(μ)`
    obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩ := st'
    refine ⟨s1, s2, L', E'', s3, s4, s5, s6, s7, s8, s9, s10, s11, deg', by rw [← rγ]; omega,
      ?_⟩
    have h2 : L'.length + 1 ≤ 2 ^ ztnko * ((L ++ L₂).length + 1) := by
      rw [u00] at cnt'; exact cnt'
    exact i3_step X.h16 X.hlp hI3 (n_le_top P) X.r06 fcnt h2
end
end DrvLT
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft freeIn regionsIn)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd hseg)
open Chazelle.Geometry (lerp point_ext)
open Chazelle.Merge (FreeAt)
open WalkEmbed
namespace Sweep
section Machine
variable (J : Merge.Junction)

/-- The tour position of the second copy of the shared vertex. -/
theorem tpos_second : tpos J.whole ztbv =
    ztevy % ztjex := by
  unfold tpos
  zuljp
  grind

/-- **The shared vertex is not the top of `C`** (arithmetic form): neither copy of the shared vertex
is at the ends of the tour.  (When it is, the box block of `C` lies between the two stretches.) -/
def VNotTop : Prop :=
  0 < tpos J.whole J.m₁ ∧ tpos J.whole J.m₁ + 2 * J.m₂ ≠ 2 * J.whole.m

/-- The two stretches fill the walk of `C` (the shared vertex is not the top of `C`). -/
theorem rlen_add_llen (hv : VNotTop J) : rlen J + llen J = (chainModel J.whole).W.n := by
  zuero

  zucz
  zuebc
  zubdb
  unfold rlen llen
  zuezn
  zucjr

  · zulpi
    grind
  · rw [show tpos J.whole J.m₁ + 2 * J.m₂ = (tpos J.whole J.m₁ + 2 * J.m₂ - 2 * ztom) +
      2 * ztom by omega, Nat.add_mod_right, Nat.mod_eq_of_lt by_omega]
    grind

/-- The left stretch starts where the right stretch ends (the shared vertex is not the top of
`C`). -/
theorem base_left (hv : VNotTop J) :
    (6 + tpos J.whole J.m₁ + rlen J) % (chainModel J.whole).W.n =
      6 + tpos J.whole ztbv := by
  zuero

  zucz
  zuebc
  rw [hn, tpos_second J]
  unfold rlen
  zucjr

  · rw [Nat.mod_eq_of_lt hc, ite_eq_right by_omega, Nat.mod_eq_of_lt by_omega]; ring
  · have hc' : 2 * ztom < tpos J.whole J.m₁ + 2 * J.m₂ := by_omega
    zubek
    rw [show tpos J.whole J.m₁ + 2 * J.m₂ = (tpos J.whole J.m₁ + 2 * J.m₂ -
      2 * ztom) + 2 * (J.m₁ + J.m₂) by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (show tpos J.whole J.m₁ + 2 * J.m₂ - 2 * ztom < 2 * ztom
        by omega)]
    rw [show 6 + tpos J.whole J.m₁ + (2 * J.m₂ + 7) = (6 + (tpos J.whole J.m₁ + 2 * J.m₂ -
        2 * ztom)) + (2 * (J.m₁ + J.m₂) + 7) by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt by_omega]

/-! ## Soundness: a genuine hit is a fused chord -/

/-- **The piece is attached at the arrival position** (model of `C₁`). -/
theorem attach_left_of_arrival {C : Chain} {a : Point} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {τ : ℝ}
    (hτ : 0 < τ) {p : ℕ} {t : ℝ} (hA : Arrival (chainModel C).W ztiu σ p t) :
    SideAttach (chainModel C).W ztxvb p t := by
  zuwq
  zukv
  refine ⟨hp, ht0, ht1, by zvmxe; exact Geometry.right_mem_segment _ _, τ, hτ,
    fun x hx hxw _ => ?_⟩
  zvmxe at hxw
  zueuw
  have hu1' : u < 1 := by
    rcases hu1.lt_or_eq with h | h
    · zubh
    simp_all
  have e : lerp a ztiu u = rayPt ztiu (-σ) (τ * ztgxi) := by
    apply point_ext <;> simp [rayPt, lerp]; ring
  zui
  have h1 : sideLeft (chainModel C).W p t (rayPt ztic (-σ) 1) := by
    simp_all
  have := (sideLeft_rayPt_iff _ p t (-σ) one_pos (show 0 < τ * ztgxi by nlinarith)).1 h1
  simp_all

/-- **The piece is attached at the corresponding position of `C`** (left correspondence, away from
its base and its split vertex). -/
theorem attach_whole_of_arrival (hP : J.P.Simple) {a : Point} {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) {τ : ℝ} (hτ : 0 < τ) {d : ℕ} (hd : d < lL1 J + lL2 J) {t : ℝ}
    (hsec : t = 0 → d ≠ 0 ∧ d ≠ lL1 J)
    (hA : Arrival (chainModel J.left).W ztiu σ
      ztok t) :
    SideAttach (chainModel J.whole).W ztxvb
      ztwkx t := by
  zubwd
  exact (hC.attach_iff hd hsec _).2 ztlga

/-! ## Completeness: a fused chord is a genuine hit -/

/-- **A fused chord attached on the left stretch is a genuine detection hit**: if the direction
`σ` is free for `C` at `a` (not above the top of `C₁`) and the chord `shoot J.whole a σ` is attached
at a position of the left stretch of `C` (away from its base and split vertex), then the shot from
`a` in the model of `C₁` is genuine at the first hit of `C`, and arrives at the corresponding
position. -/
theorem genuine_of_attach (hP : J.P.Simple) {a : Point}
    (ha₁ : a.2 ≤ J.left.top.2) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (hfree : FreeAt J.whole a σ)
    {d : ℕ} (hd : d < lL1 J + lL2 J) {t : ℝ} (hsec : t = 0 → d ≠ 0 ∧ d ≠ lL1 J)
    (hA : SideAttach (chainModel J.whole).W ztxc
      ztwkx t)
    (hend : sidePt (chainModel J.whole).W
      ztwkx t =
        rayPt a σ zton) :
    Genuine J.left a σ zton ∧
      Arrival (chainModel J.left).W ztwqt σ
        ztok t := by
  zubwd
  have hM₁ : WalkAx ztbw := hC.hM₂
  set T := J.whole.hitParam a σ with hT
  have hz' : ztlal := ha₁.trans J.left_top_le
  obtain ⟨hT0, hwD, hdom⟩ := Merge.hit_of_freeAt J.whole hz' hσ hfree
  have hA₁ := (hC.attach_iff hd hsec _).1 hA
  have hpt : sidePt (chainModel J.left).W
      ztok t =
        rayPt a σ T := by
    rw [← hC.sidePt_eq hd t]; omega
  refine ⟨⟨hT0, fun s h0 h1 => dom_left J (hdom s h0 h1) by_simp_all, ?_⟩, ?_⟩
  · zuezz
    zuitk
  · zusl

    have hmem : ztxzu := by
      zudlx

      have e : ztxti := by
        zufqp
      zui
      exact Geometry.lerp_mem_segment _ _ by_positivity
        ztmdf
    have hne : ztxzv := by
      zuq
      have := congrArg Prod.fst h
      zudv
      zubbe
    zuehc
    have hdist : ztxtg := by
      zuhkx
    zuhyy
    have h1 : sideLeft (chainModel J.left).W
        ztok t
        (rayPt (sidePt (chainModel J.left).W
          ztok t) (-σ) s) := by
      grind
    have := (sideLeft_rayPt_iff _ _ t (-σ) hs0 one_pos).1 h1
    grind
end Machine
end Sweep
open Chazelle.Chain (sideCross)
namespace Sweep
section ChainModel
variable (C : Chain)

/-- **A chord along a ray leaving a walk position is attached there**: if the ray from the point of
the position `(p, t)` in direction `τ'` starts in the left sector and along an admissible chord,
the chord is attached at `(p, t)`. -/
theorem sideAttach_of_along (hP : C.P.Simple) {e : Set Point} (he : e ∈ Merge.augChords C)
    {p : ℕ} {t : ℝ} (hp : p < (chainModel C).W.n) (ht : 0 ≤ t) (ht1 : t < 1) {τ' : ℝ}
    (hτ' : τ' = 1 ∨ τ' = -1)
    (hsec : sideLeft (chainModel C).W p t (rayPt ztic τ' 1))
    (hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt ztic τ' s ∈ e) :
    SideAttach (chainModel C).W e p t := by
  zubkf
  set z := sidePt (chainModel C).W p t with hz
  have hzD : ztsnn := hM.trace p hp t ht ht1.le
  have hsec' : ∀ s > 0, sideLeft (chainModel C).W p t (rayPt z τ' s) :=
    fun s hs => (sideLeft_rayPt_iff _ p t τ' one_pos hs).1 hsec
  zuvj
  zubwk
  zubrt
  have hs₁0' : (0 : ℝ) < s₁ := hs₁0
  zufhk
  have hzpt : ztyxx := Prod.ext rfl hzy.symm
  refine ztfwq
  · zukmz
    · have hzl : ztlaz := by
        zubq

        obtain ⟨s, hs, hs'⟩ :=
          (hev.and ztbyk).exists
        have := hs.2.1; zvmxf at this; grind
      have hzr : ztlbk := by
        have := hs₁.2.2; zvmxf at this; linarith
      tauto
    · have hzr : ztlbk := by
        zubq

        obtain ⟨s, hs, hs'⟩ :=
          (hev.and ztbyl).exists
        have := hs.2.2; zvmxf at this; grind
      have hzl : ztlaz := by
        have := hs₁.2.1; zvmxf at this; linarith
      tauto
  · zugpy
    zukmz
    · have hzl : z.1 = l := by
        have h1 : ztlaz := by
          zubq

          obtain ⟨s, hs, hs'⟩ :=
            (hev.and ztbyk).exists
          have := hs.2.1; zvmxf at this; grind
        have h2 : z.1 < r := by
          have := hs₁.2.2; zvmxf at this; linarith
        zucop
        · exact absurd (by zuoth; exact hH.open_mem _ h h2) hzD
        simp_all
      have hxl' : l < x.1 := by
        grind
      have e : ztlyy :=
        point_ext by_simp_all by_simp_all
      grind
    · have hzr : z.1 = r := by
        have h1 : ztlbk := by
          zubq

          obtain ⟨s, hs, hs'⟩ :=
            (hev.and ztbyl).exists
          have := hs.2.2; zvmxf at this; grind
        have h2 : l < z.1 := by
          have := hs₁.2.1; zvmxf at this; linarith
        zucop
        · exact absurd (by zuoth; exact hH.open_mem _ h2 h) hzD
        omega
      have hxr' : x.1 < r := by
        grind
      have e : ztjat :=
        point_ext by_simp_all by_simp_all
      grind
end ChainModel
end Sweep
end
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft sideCross freeIn regionsIn)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd hseg)
open Chazelle.Geometry (lerp point_ext)
open Chazelle.Merge (FreeAt)
open WalkEmbed
namespace Sweep
theorem chord_eq_shoot_of_end (C : Chain) {h : Set Point} (hh : h ∈ Merge.augChords C)
    {w : Point} (hw : w ∈ h) (hwD : w ∉ C.dom) :
    ∃ σ : ℝ, ztdd ∧ FreeAt C w σ ∧ h = Merge.shoot C w σ := by
  obtain ⟨y, l, r, hH, hy, rfl, -, -⟩ := Merge.augChords_spec hh
  zubwk
  obtain ⟨hwy, hwl, hwr⟩ := hw
  have hw' : w = (zthla : Point) := Prod.ext rfl hwy
  have hend : w.1 = l ∨ w.1 = r := by
    rcases hwl.lt_or_eq with h1 | h1
    · rcases hwr.lt_or_eq with h2 | h2
      · exact absurd (by zuofq; exact hH.open_mem _ h1 h2) hwD
      grind
    grind
  have hwy' : w.2 ≤ C.top.2 := by_grind
  rcases hend with hl | hr
  · -- from the left end, to the right
    have hfree : FreeAt C w 1 := by
      zuhut
      rw [show rayPt w 1 s = ((w.1 + s, y) : Point) from
        point_ext by_simp by_tauto]
      zulff
    obtain ⟨hT, hTD, hTdom⟩ := Merge.hit_of_freeAt C hwy' ztp hfree
    have hTeq : C.hitParam w 1 = r - l := by
      rcases lt_trichotomy ztsvw ztbju with h | h | h
      · zumae
        rw [show rayPt w 1 ztsvw = ((w.1 + C.hitParam w 1, y) : Point) from
          point_ext by_simp by_tauto]
        zulfg
      · zubh
      · exfalso
        have := hTdom ztbju by_linarith h
        rw [show rayPt w 1 ztbju = (ztevf : Point) from
          point_ext ztnuy by_tauto] at this
        exact hH.right_not this
    refine ⟨1, Or.inl rfl, hfree, ?_⟩
    zuipz

    zuewp
    constructor
    · zuifq
      refine ⟨(z.1 - l) / ztbju, div_nonneg by_linarith by_linarith,
        (div_le_one by_linarith).2 by_linarith, ?_⟩
      zubjw
      · simp only [Geometry.lerp_fst, rayPt_fst, hl]
        grind
      · zugyy
    · zuczj
      refine ztinn <;> simp [lerp, rayPt, hl] <;> nlinarith
  · -- from the right end, to the left
    have hfree : FreeAt C w (-1) := by
      zuhut
      rw [show rayPt w (-1) s = ((w.1 - s, y) : Point) from
        point_ext zteqe by_tauto]
      zulff
    obtain ⟨hT, hTD, hTdom⟩ := Merge.hit_of_freeAt C hwy' ztbt hfree
    have hTeq : C.hitParam w (-1) = r - l := by
      rcases lt_trichotomy ztowk ztbju with h | h | h
      · zumae
        rw [show rayPt w (-1) ztowk = ((w.1 - C.hitParam w (-1), y) : Point) from
          point_ext zteqe by_tauto]
        zulfg
      · zubh
      · exfalso
        have := hTdom ztbju by_linarith h
        rw [show rayPt w (-1) ztbju = (ztetv : Point) from
          point_ext ztnuy by_tauto] at this
        exact hH.left_not this
    refine ⟨-1, Or.inr rfl, hfree, ?_⟩
    zuipz

    zuewp
    constructor
    · zuifq
      refine ⟨(r - z.1) / ztbju, div_nonneg by_linarith by_linarith,
        (div_le_one by_linarith).2 by_linarith, ?_⟩
      zubjw
      · simp only [Geometry.lerp_fst, rayPt_fst, hr]
        grind
      · zugyy
    · zuczj
      refine ztinn <;> simp [lerp, rayPt, hr] <;> nlinarith
section Machine
variable (J : Merge.Junction)

/-- **The shot origins of the candidate chords**: a candidate chord of `λ` is seen from an
endpoint of an exit chord of `λ` or of a region at a side of the slit of `C₂` along it, or from the shared vertex, or from the top of `C₂`. -/
theorem cand_cases {S₂ : Set ztf} (hS₂ : S₂ ⊆ Merge.augChords J.right) {L : Set Point}
    {h : Set Point} (hh : h ∈ Cand J S₂ L) :
    (∃ c ∈ S₂, ztgnu ∧
      ((FreeAt J.whole ztffp 1 ∧ h = Merge.shoot J.whole ztffp 1) ∨
        (FreeAt J.whole ztffq (-1) ∧ h = Merge.shoot J.whole ztffq (-1)))) ∨
    (∃ σ : ℝ, ztdd ∧ FreeAt J.whole J.shared σ ∧ h = Merge.shoot J.whole J.shared σ) ∨
    (∃ σ : ℝ, ztdd ∧ FreeAt J.whole J.right.top σ ∧
      h = Merge.shoot J.whole J.right.top σ) := by
  obtain ⟨hF, hc⟩ := hh
  have hA : h ∈ Merge.augChords J.whole := F₂plus_subset J hS₂ hF
  have hvD : ztpkm := fun hd =>
    J.whole.not_mem_set_of_mem_dom hd ztffl
  have htD : J.right.top ∉ J.whole.dom := fun hd =>
    J.whole.not_mem_set_of_mem_dom hd ztuzd
  rcases hc with ⟨c, hcS, hhc, htouch⟩ | hv | ht
  · rcases hF with ((⟨c', hc', hfree, rfl⟩ | ⟨c', hc', hfree, rfl⟩) | hsh) | htop
    · zudol
      have := s2_eq_of_sub J hS₂ hcS hc'S hA hhc (by
        obtain ⟨y, l, r, hH, hy, hceq, hl, -⟩ := Merge.augChords_spec ztvua
        zukuu
        exact Merge.shoot_subset_pos J.whole hH.lt (fun hd => hH.right_not
          zteex))
      grind
    · zudol
      have := s2_eq_of_sub J hS₂ hcS hc'S hA hhc (by
        obtain ⟨y, l, r, hH, hy, hceq, -, hr⟩ := Merge.augChords_spec ztvua
        zukvv
        exact Merge.shoot_subset_neg J.whole hH.lt (fun hd => hH.left_not
          zteex))
      grind
    · tauto
    · zucec
      have hv : ztxmm := by
        zubut
      refine Or.inr ztkqi
      · zufab
      · zufaa
  · obtain ⟨σ, hσ, hfree, heq⟩ := chord_eq_shoot_of_end J.whole hA hv hvD
    grind
  · obtain ⟨σ, hσ, hfree, heq⟩ := chord_eq_shoot_of_end J.whole hA ht htD
    grind
end Machine
end Sweep
end
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft sideCross freeIn regionsIn)
open WalkEmbed
namespace Sweep
section Machine
variable (J : Merge.Junction)

/-- **The top of `C` lies in `C₁` when the box of `C` lies inside the left stretch.** -/
theorem top_left_of_box (h : 2 * J.whole.m - tpos J.whole ztbv < 2 * J.m₁) :
    J.right.top.2 ≤ J.left.top.2 := by
  zufz

  zueqr
  have hTl : J.whole.topIdx < J.m₁ := by
    simp only [Merge.Junction.whole_m] at hT h
    unfold tpos bS Chain.sideS at h
    simp only [Merge.Junction.whole_m] at h
    cases hb : J.whole.sideBeta <;> simp only [hb, Bool.false_eq_true, ↓reduceIte] at h
    · zukr
      rw [Nat.mod_eq_sub_mod by_omega,
        Nat.mod_eq_of_lt by_omega] at h
      omega
    · rw [Nat.mod_eq_sub_mod by_omega,
        Nat.mod_eq_of_lt by_omega] at h
      omega
  have e : J.left.top = J.whole.top := by
    zultq
    rw [left_topIdx_eq J hTl]
    rfl
  zui
  exact J.right_top_le

/-- **The positions of the left stretch in the walk of `C₁`**: tour positions, unless the box of `C`
lies inside the left stretch. -/
theorem left_pos_cases {d : ℕ} (hd : d < lL1 J + lL2 J) :
    (∃ i, i < 2 * J.m₁ ∧
      (6 + tpos J.left J.m₁ + dq ztdov ztety d) % (chainModel J.left).W.n = i + 6) ∨
    2 * J.whole.m - tpos J.whole ztbv < 2 * J.m₁ := by
  zuerx
  zucmz
  zufd
  zvmxz at hτ hn₁
  unfold lL1 lL2 lδ dq at *
  by_cases hA : 2 * J.whole.m - tpos J.whole ztbv < 2 * J.m₁
  · omega
  · left
    simp only [ite_eq_right hA] at hd ⊢
    zumns
    by_cases hN : 2 * J.m₁ ≤ 2 * J.left.m - tpos J.left J.m₁
    · simp only [ite_eq_left hN] at hd ⊢
      zvmxz at hN
      have hτ0 : ztsmo := by_omega
      refine ⟨d, by_omega, ?_⟩
      rw [hτ0]
      split_ifs <;> (zvmyc; ring)
    · simp only [ite_eq_right hN] at hd ⊢
      zvmxz at hN hd ⊢
      split_ifs with hdl
      · exact ⟨tpos J.left J.m₁ + d, by_omega, by zvmyc; ring⟩
      · refine ⟨tpos J.left J.m₁ + d - 2 * J.m₁, by_omega, ?_⟩
        rw [show 6 + tpos J.left J.m₁ + zttit = (tpos J.left J.m₁ + d - 2 * J.m₁ + 6) +
          ztgcb by omega, Nat.add_mod_right, Nat.mod_eq_of_lt by_omega]

/-- **A point of `C₂` at a position of the left stretch is the shared vertex.** -/
theorem left_stretch_pt (hP : J.P.Simple) 
    {d : ℕ} (hd : d < lL1 J + lL2 J) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hx : sidePt (chainModel J.whole).W
      ztwkx t ∈ J.right.set) :
    sidePt (chainModel J.whole).W
      ztwkx t = J.shared := by
  zubao
  have hleft : ∀ y, y ∈ J.left.set → y ∈ J.right.set → y = J.shared := by
    zujbw
    have := (Set.ext_iff.1 (J.left_inter_right hP) y).1 by_simp_all
    simp_all
  rw [hC.sidePt_eq hd t] at hx ⊢
  set q := (6 + tpos J.left J.m₁ + dq _ _ d) % (chainModel J.left).W.n with hq
  have hqn : q < (chainModel J.left).W.n := Nat.mod_lt _ hC.n₂_pos
  -- a tour position gives a point of `C₁`
  have htour : ∀ i, i ≤ 2 * J.left.m → (i = 2 * J.left.m → t = 0) → q = i + 6 →
      sidePt (chainModel J.left).W q t = J.shared := by
    intro i hi hit hqi
    rw [hqi] at hx ⊢
    exact hleft _ (J.left.sideWalk_tour_pt_mem J.left.sideBeta hi hit ht0 ht1) hx
  rcases left_pos_cases J hd with ⟨i, hi, hqi⟩ | hA
  · exact htour i (by rw [show J.left.m = J.m₁ from rfl]; omega) (fun h => by
      simp_all) hqi
  · -- the box of `C` in the left stretch: points of the box block of `C₁` are not on `C₂`
    have htop := top_left_of_box J hA
    rw [cm_W] at hx hqn
    have hb := J.right.abs_le_coordBound_of_mem_set hx
    have hR : Jordan.coordBound J.right.P < J.left.radius := by
      rw [FuseMath.radius_of_P J rfl, ← FuseMath.radius_of_P J (C' := J.right) rfl]
      exact J.right.coordBound_lt_radius
    have htopR := J.left.top_snd_lt_radius
    have hx2 := J.right.snd_le_top_of_mem_set hx
    obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := J.left.sidePt_box J.left.sideBeta t
    rcases J.left.sideWalk_pos_cases J.left.sideBeta hqn ht0 with (hp5 | ⟨hq6, htp⟩) | ⟨i, hi, hqi, hit⟩
    · exfalso
      have hq' : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by_omega
      rcases hq' with hq' | hq' | hq' | hq' | hq' | hq' <;> rw [hq'] at hx hb hx2
      · grind
      · zvmwp at hb; simp only at hb; have := (abs_le.1 hb.1).1; linarith
      · zvmxx at hb; simp only at hb; have := (abs_le.1 hb.2).1; linarith
      · zvncq at hb; simp only at hb; have := (abs_le.1 hb.1).2; linarith
      · grind
      · -- down the slit of `C₁`: the point is the top of `C₁`
        rw [h5] at hx hx2 hb
        simp only at hx2 hb
        have ht1' := ht1.le
        have hy : J.left.top.2 + ztca * ztnlu ≤ J.right.top.2 := by
          nlinarith
        have : 0 < ztca * ztnlu := mul_pos by_linarith by_linarith
        linarith
    · exfalso
      rw [hq6] at hx hb hx2
      rw [h6] at hx hb hx2
      simp only at hx2
      -- up the slit of `C₁` above its top, at a height `≤ top(C₂) ≤ top(C₁)`
      have hpos : 0 < t * ztnlu := mul_pos htp by_linarith
      linarith
    · exact htour i hi hit hqi

/-- **The points of `C₂` other than the shared vertex are on the right stretch**: every position of
the walk of `C` whose point is such a point has its offset in `(0, L)`. -/
theorem off_right_pt_of_vnt (hP : J.P.Simple) 
    (hv : VNotTop J) {S₂ : Set ztf} (hS₂ : S₂ ⊆ Merge.augChords J.right)
    (hS₂f : S₂.Finite) {p : ℕ} (hp : p < (chainModel J.whole).W.n) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t < 1) (hx : sidePt (chainModel J.whole).W p t ∈ J.right.set)
    (hxv : sidePt (chainModel J.whole).W p t ≠ J.shared) :
    0 < off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztk ∧
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztk <
        ((rL1 J + rL2 J : ℕ) : ℝ) := by
  zubao
  have hCr := corr_right0 J hP hS₂ hS₂f
  zudbo
  set gL := 6 + tpos J.whole ztbv with hgL
  set g := 6 + tpos J.whole J.m₁ with hg
  have hsum := rlen_add_llen J hv
  have hbase := base_left J hv
  have hrl := rL1_add_rL2 J
  zulkl
  obtain ⟨hpd, -⟩ := hC.decomp hp ht0 ht1
  set d := dOf n gL p with hd
  zufun
  by_cases hdl : d < llen J
  · exfalso
    zuldi
    rw [← hpd] at hx ⊢
    zuhui
  · -- the position is in the right stretch
    have e : p = ztzvv % n := by
      rw [← hpd, hgL, ← hbase, Nat.mod_add_mod, ← hg]
      rw [show g + rlen J + d = ztzvv + n by omega, Nat.add_mod_right]
    have hoff : off (n : ℝ) (g : ℝ) ztk = ((d - llen J : ℕ) : ℝ) + t := by
      zui
      exact off_key hCr.hg by_omega ht0 ht1
    rw [hoff, hrl]
    zujx
    · rcases Nat.eq_zero_or_pos ztlmt with h0 | h0
      · zukml
        · grind
        · exfalso
          zuldi
          rw [e, h0, ← htp, add_zero]
          have := sidePt_off_zero J hP hS₂ hS₂f ztcv le_rfl
            one_pos (by
              rw [show ((g % n : ℕ) : ℝ) + 0 = ((((g + 0) % n : ℕ)) : ℝ) + 0 by simp]
              rw [off_key hCr.hg by_omega le_rfl one_pos]; simp)
          omega
      positivity
    · have hlt : d - llen J < rlen J := by_omega
      have : ((d - llen J : ℕ) : ℝ) + 1 ≤ (rlen J : ℝ) := by exact_mod_cast hlt
      linarith

/-- **The points of `C₂` other than the shared vertex are on the right stretch** (general form;
when the shared vertex is the top of `C`, the box block of `C` lies between the two stretches and
carries no point of `C₂`). -/
theorem off_right_pt (hP : J.P.Simple) 
    {S₂ : Set ztf} (hS₂ : S₂ ⊆ Merge.augChords J.right)
    (hS₂f : S₂.Finite) {p : ℕ} (hp : p < (chainModel J.whole).W.n) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t < 1) (hx : sidePt (chainModel J.whole).W p t ∈ J.right.set)
    (hxv : sidePt (chainModel J.whole).W p t ≠ J.shared) :
    0 < off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztk ∧
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztk <
        ((rL1 J + rL2 J : ℕ) : ℝ) := by
  zuhbs
  · exact off_right_pt_of_vnt J hP hv hS₂ hS₂f hp ht0 ht1 hx hxv
  zumh
  zucz
  zunf
  zufz

  unfold VNotTop at hv
  have hrl : rL1 J + rL2 J = 2 * J.m₂ := by
    zupcm; unfold rlen; grind
  have hT2' : tpos J.whole ztbv = 2 * J.m₂ ∨
      tpos J.whole ztbv = 0 := by
    zuezn
    rcases ztfin
      with h | h
    · left; rw [h, zero_add, Nat.mod_eq_of_lt by_omega]
    simp_all
  have hll : lL1 J + lL2 J = 2 * J.m₁ := by
    zuogn; unfold llen; grind
  -- no box position carries a point of the chain
  have hbox : ¬ (p ≤ 5 ∨ (p = 2 * J.whole.m + 6 ∧ 0 < t)) := fun hb =>
    (J.whole.sideWalk_box_pt J.whole.sideBeta hb ht0 ht1).1 ztuzg
  zufus
  -- the copies of the shared vertex at the walk vertices `6 + τ` and `6 + τ + 2 m₂`
  have hv0 : (chainModel J.whole).W.vtx ztve = J.shared := by
    have := walk_tour J.whole J.m₁ 0 by_omega
    rw [add_zero, Nat.mod_eq_of_lt hg, tourV_right J ztbg, tourV_right_zero] at this
    omega
  have htop6 : (chainModel J.whole).W.vtx 6 = (chainModel J.whole).W.vtx ztjew := by
    rw [cm_W, J.whole.sideWalk_vtx_six, J.whole.sideWalk_vtx_tour _ le_rfl,
      J.whole.sideTour_two_m]
  -- the left stretch carries no point of `C₂` but the shared vertex
  have hleft : ∀ d, d < 2 * J.m₁ →
      p = ztwtl % (chainModel J.whole).W.n → False := by
    zumgo
    zuldi
    rw [hpd] at hx ⊢
    zuhui
  -- the right stretch
  have hright : ∀ d, d < 2 * J.m₂ → p = ztlv % (chainModel J.whole).W.n →
      0 < off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztk ∧
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztk <
        ((rL1 J + rL2 J : ℕ) : ℝ) := by
    zumgo
    rw [hpd, off_key hg by_omega ht0 ht1, hrl]
    have hd' : (d : ℝ) + 1 ≤ ((2 * J.m₂ : ℕ) : ℝ) := by exact_mod_cast hd
    refine ⟨?_, by_linarith⟩
    rcases Nat.eq_zero_or_pos d with rfl | hdp
    · zukml
      · grind
      · exfalso; apply hxv
        rw [hpd, ← htp, Chazelle.Chain.sidePt_zero, add_zero, Nat.mod_eq_of_lt hg]
        omega
    positivity
  have hp6 : ztsaj := by_omega
  rcases ztfin
    with hA | hB
  · -- the right stretch starts at the walk vertex `6`, the box block follows the left stretch
    have hL : tpos J.whole ztbv = 2 * J.m₂ := by
      rw [tpos_second J, hA, zero_add, Nat.mod_eq_of_lt by_omega]
    zukne
    · exfalso
      have ht : ztbhh := by
        grind
      zuldi
      rw [hpe, ht, Chazelle.Chain.sidePt_zero, ← htop6, ← hv0, hA]
    · by_cases hi : p - 6 < 2 * J.m₂
      · exact hright _ hi (by rw [hA, Nat.mod_eq_of_lt by_omega]; omega)
      · exact (hleft (p - 6 - 2 * J.m₂) by_omega
          ztktb).elim
  · -- the left stretch starts at the walk vertex `6`, the box block follows the right stretch
    have hL : tpos J.whole ztbv = 0 := by
      rw [tpos_second J, hB, Nat.mod_self]
    zukne
    · exfalso
      have ht : ztbhh := by
        grind
      zuldi
      have := walk_tour J.whole J.m₁ ztgyh by_omega
      rw [tourV_right J le_rfl, tourV_right_end,
        Nat.mod_eq_of_lt by_grind] at this
      rw [hpe, ht, Chazelle.Chain.sidePt_zero, ← this]
      grind
    · by_cases hi : tpos J.whole J.m₁ ≤ p - 6
      · exact hright (p - 6 - tpos J.whole J.m₁) by_omega
          (by zvmyc; omega)
      · exact (hleft (p - 6) by_omega ztktb).elim
end Machine
end Sweep
end
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft sideCross freeIn regionsIn)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd hseg)
open Chazelle.Geometry (lerp point_ext)
open Chazelle.Merge (FreeAt)
open WalkEmbed
namespace Sweep
section Machine
variable (J : Merge.Junction)

/-- **The stop chords** (precomputed by the RAM, design §9.2): the shared chords, and the chords
seen from an endpoint of a chord of `S₂` that is not on `C₂` (a box-wall endpoint). -/
def StopChord (S₂ : Set ztf) (e : Set Point) : Prop :=
  (∃ σ : ℝ, ztdd ∧ FreeAt J.whole J.shared σ ∧ e = Merge.shoot J.whole J.shared σ) ∨
  (∃ c ∈ S₂, ∃ (a : Point) (σ : ℝ), ztxel ∧
    a ∉ J.right.set ∧ FreeAt J.whole a σ ∧ e = Merge.shoot J.whole a σ)

/-- The origin of a chord seen from a point off the domain is an end of it, off the domain. -/
theorem origin_mem {a : Point} {σ : ℝ} : a ∈ Merge.shoot J.whole a σ :=
  Geometry.left_mem_segment _ _

/-- An endpoint of a chord of `S₂` is off the domain of `C`. -/
theorem end_not_mem_dom {S₂ : Set ztf} (hS₂ : S₂ ⊆ Merge.augChords J.right)
    {c : Set Point} (hc : c ∈ S₂) :
    Merge.lend c ∉ J.whole.dom ∧ Merge.rend c ∉ J.whole.dom := by
  obtain ⟨y, l, r, hH, hy, -, hl, hr⟩ := Merge.augChords_spec ztbac
  zukuv
  exact ⟨fun hd => hH.left_not zteex, fun hd => hH.right_not zteex⟩

/-- **A non-stop chord has an attachment on the open right stretch.** -/
theorem stretch_end (hP : J.P.Simple)
    {S₂ : Set ztf} (hS₂ : S₂ ⊆ Merge.augChords J.right)
    (hS₂f : S₂.Finite) {e : Set Point} (he : e ∈ F₂plus J S₂) (hns : ¬ StopChord J S₂ e) :
    ∃ (pB : ℕ) (tB : ℝ), SideAttach (chainModel J.whole).W e pB tB ∧
      0 < off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztdhv ∧
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztdhv <
        ((rL1 J + rL2 J : ℕ) : ℝ) ∧
      sidePt (chainModel J.whole).W pB tB ∈ J.right.set ∧
      sidePt (chainModel J.whole).W pB tB ≠ J.shared := by
  zugb
  have hA : e ∈ Merge.augChords J.whole := F₂plus_subset J hS₂ he
  have hvD : ztpkm := fun hd =>
    J.whole.not_mem_set_of_mem_dom hd ztffl
  -- an end of `e` on `C₂` other than the shared vertex gives the attachment
  have key : ∀ x, x ∈ e → x ∈ J.right.set → x ≠ J.shared → ∃ (pB : ℕ) (tB : ℝ),
      SideAttach (chainModel J.whole).W e pB tB ∧
      0 < off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztdhv ∧
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztdhv <
        ((rL1 J + rL2 J : ℕ) : ℝ) ∧
      sidePt (chainModel J.whole).W pB tB ∈ J.right.set ∧
      sidePt (chainModel J.whole).W pB tB ≠ J.shared := by
    intro x hxe hx hxv
    have hxD : x ∉ J.whole.dom := fun hd =>
      J.whole.not_mem_set_of_mem_dom hd ztuzg
    obtain ⟨a, b, -, hcab, -, hopen, ⟨⟨pa, ta, hAa, hAa'⟩, -⟩, ⟨⟨pb, tb, hBb, hBb'⟩, -⟩⟩ :=
      hM.ends e hA
    have hxab : x = a ∨ x = b := by
      zudmi
      · simp_all
      · right
        zvmyh at hxe
        exact seg_end hxe hxD hopen hxa
    rcases hxab with rfl | rfl
    · refine ⟨pa, ta, hAa, ?_⟩
      have := off_right_pt J hP hS₂ hS₂f hAa.1 hAa.2.1 hAa.2.2.1 by_simp_all
        by_simp_all
      simp_all
    · refine ⟨pb, tb, hBb, ?_⟩
      have := off_right_pt J hP hS₂ hS₂f hBb.1 hBb.2.1 hBb.2.2.1 by_simp_all
        by_simp_all
      simp_all
  -- a chord through the shared vertex is a shared chord, a stop chord
  have hshared : J.shared ∉ e := by
    intro hv'
    obtain ⟨σ, hσ, hfree, heq⟩ := chord_eq_shoot_of_end J.whole hA hv' hvD
    exact hns ztkqg
  zubjm
  · zudol
    by_cases hr : Merge.lend c' ∈ J.right.set
    · zujvd
    · exact absurd (Or.inr ⟨c', hc'S, _, 1, Or.inl ztrh, hr, hfree, rfl⟩) hns
  · zudol
    by_cases hr : Merge.rend c' ∈ J.right.set
    · zujvd
    · exact absurd (Or.inr ⟨c', hc'S, _, -1, Or.inr ztrh, hr, hfree, rfl⟩) hns
  · tauto
  · zucec
    have hv' : ztxmm := by
      zubut
    have hmem : ztzor := by
      zugxx
    exact key _ hmem J.right.top_mem_set (fun h => hshared (h ▸ hmem))

/-- **Completeness of the detection**: from a valid label `λ` of the region faced at a non-cut
position of the `C₁` part, the next cut key `K` without stop chords carries a chord seen from an
endpoint (on `C₂`, not the shared vertex) of an exit chord of `λ` or of a region at a side of
the slit of `C₂`, or from the top of `C₂`. -/
theorem next_event_origin (hP : J.P.Simple)
    {Q : Polygon} {S₂ : Set ztf}
    (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    (hF : (chainModel J.whole).ChordFamily Q ztbi) {G L : Set Point}
    (hG : G ∈ (chainModel J.whole).regions ztbi)
    (hL : L ∈ (chainModel J.right).regions S₂) (hvalid : Valid J S₂ G L)
    {p₀ : ℕ} {t₀ : ℝ} (hp₀ : p₀ < (chainModel J.whole).W.n) (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (hnc₀ : ¬ (chainModel J.whole).IsCut ztbi zthw)
    (hfG₀ : (chainModel J.whole).Faces p₀ t₀ G)
    (ho₀ : ((rL1 J + rL2 J : ℕ) : ℝ) <
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zthw)
    {pK : ℕ} {tK : ℝ} (hpK : pK < (chainModel J.whole).W.n) (htK0 : 0 ≤ tK) (htK1 : tK < 1)
    (hoK : off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zthw <
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztkm)
    (hgap : ∀ x, (chainModel J.whole).IsCut ztbi x → 0 ≤ x →
      x < (chainModel J.whole).W.n →
      ¬ (off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zthw <
          off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) x ∧
        off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) x <
          off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztkm))
    {e : Set Point} (he : e ∈ F₂plus J S₂) (heK : SideAttach (chainModel J.whole).W e pK tK)
    (hstop : ∀ e' ∈ F₂plus J S₂, SideAttach (chainModel J.whole).W e' pK tK →
      ¬ StopChord J S₂ e') :
    ∃ h ∈ F₂plus J S₂, SideAttach (chainModel J.whole).W h pK tK ∧
      ∃ (a : Point) (σ : ℝ), ztdd ∧ FreeAt J.whole a σ ∧
        h = Merge.shoot J.whole a σ ∧
        ((∃ c ∈ S₂, ztgnu ∧
          ztxel ∧
          a ∈ J.right.set ∧ a ≠ J.shared) ∨ a = J.right.top) := by
  zugb
  have hFs : ztgty := hF.2.1
  have hvD : ztpkm := fun hd =>
    J.whole.not_mem_set_of_mem_dom hd ztffl
  -- the stretch attachment of `e`
  obtain ⟨pB, tB, heB, hB0, hBL, hBr, hBv⟩ :=
    stretch_end J hP hS₂.2.1 hS₂.1 he (hstop e he heK)
  have hLK : ((rL1 J + rL2 J : ℕ) : ℝ) <
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztkm := by_linarith
  have heKB : sidePt (chainModel J.whole).W pK tK ≠ sidePt (chainModel J.whole).W pB tB := by
    zuq
    have := off_right_pt J hP hS₂.2.1 hS₂.1 hpK htK0 htK1 by_grind
      by_grind
    grind
  have hnobr : ∀ e' ∈ F₂plus J S₂, SideAttach (chainModel J.whole).W e' pK tK →
      ∃ (pb : ℕ) (tb : ℝ), SideAttach (chainModel J.whole).W e' pb tb ∧
        off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztbd <
          ((rL1 J + rL2 J : ℕ) : ℝ) := by
    intro e' he' heK'
    obtain ⟨pb, tb, hb, -, hbL, -⟩ :=
      stretch_end J hP hS₂.2.1 hS₂.1 he' (hstop e' he' heK')
    grind
  obtain ⟨h, hh, hhK⟩ := next_event_detected J hP hS₂ hF hG hL hvalid hp₀ ht₀ hnc₀ hfG₀ ho₀
    hpK htK0 htK1 hoK hgap he heK heB heKB hB0 hBL hnobr
  have hhF : h ∈ F₂plus J S₂ := hh.1
  refine ⟨h, hhF, hhK, ?_⟩
  have hns := hstop h hhF hhK
  rcases cand_cases J hS₂.2.1 hh with ⟨c, hc, htouch, hcase⟩ | ⟨σ, hσ, hfree, rfl⟩ |
      ⟨σ, hσ, hfree, rfl⟩
  · rcases hcase with ⟨hfree, rfl⟩ | ⟨hfree, rfl⟩
    · refine ⟨_, 1, Or.inl rfl, hfree, rfl, Or.inl ⟨c, hc, htouch, Or.inl ztrh, ?_, ?_⟩⟩
      · by_contra hr
        exact hns (Or.inr ⟨c, hc, _, 1, Or.inl ztrh, hr, hfree, rfl⟩)
      · intro hlv
        exact hns (Or.inl ⟨1, Or.inl rfl, by_grind, by zupdq⟩)
    · refine ⟨_, -1, Or.inr rfl, hfree, rfl, Or.inl ⟨c, hc, htouch, Or.inr ztrh, ?_, ?_⟩⟩
      · by_contra hr
        exact hns (Or.inr ⟨c, hc, _, -1, Or.inr ztrh, hr, hfree, rfl⟩)
      · intro hlv
        exact hns (Or.inl ⟨-1, Or.inr rfl, by_grind, by zupdq⟩)
  · exact absurd (Or.inl ztbkb) hns
  grind
end Machine
end Sweep
end
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft sideCross freeIn regionsIn)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd hseg)
open Chazelle.Geometry (lerp point_ext)
open Chazelle.Merge (FreeAt)
open WalkEmbed
namespace Sweep
theorem endpoint_attach {M : Model} (hM : WalkAx M) {e : Set Point} (he : e ∈ M.Adm) {x : Point}
    (hx : x ∈ e) (hxD : x ∉ M.D) :
    ∃ (p : ℕ) (t : ℝ), SideAttach M.W e p t ∧ sidePt M.W p t = x := by
  obtain ⟨a, b, -, hcab, -, hopen, ⟨⟨pa, ta, hAa, hAa'⟩, -⟩, ⟨⟨pb, tb, hBb, hBb'⟩, -⟩⟩ := hM.ends e he
  zudmi
  · grind
  · zugdr
    have := seg_end hx hxD hopen hxa
    grind
section Machine
variable (J : Merge.Junction)

/-- **A position of the open right stretch** is `(g + d, t)` with `d < L`, and `d ≠ 0` at a vertex. -/
theorem stretch_decomp (hP : J.P.Simple) {S₂ : Set ztf}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {p : ℕ}
    (hp : p < (chainModel J.whole).W.n) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (h0 : 0 < off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztk)
    (hL : off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztk <
      ((rL1 J + rL2 J : ℕ) : ℝ)) :
    ∃ d, d < rL1 J + rL2 J ∧ ztevv ∧
      p = ztlv % (chainModel J.whole).W.n := by
  zuv
  zucib

  zueye
  refine ⟨d, ?_, fun ht => ?_, hpd.symm⟩
  · zuhdh
    zufc
  · rw [ht, add_zero] at h0
    intro hd; simp_all
end Machine
variable {M : Model}
variable {F : Set (Set Point)} {U : Set Point}
/-- **An arc faces its region just after a key inside it** (or at its start). -/
theorem afterFaces_of_arc {l r : ℝ}
    (harc : M.IsArc F U l r) {p : ℕ} (hp : p < M.W.n) {t : ℝ} (ht0 : 0 ≤ t)
    (hin : ∀ᶠ s in 𝓝[>] (0 : ℝ), sideInArc l r ((p : ℝ) + t + s)) : AfterFaces M p t U := by
  obtain ⟨δ, hδ, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hin
  refine zteze
  have := hsub ztdxi
  exact harc.2.2.2.2.2.2 p ztuf hp by_linarith hs2 by_grind

/-- **An arc faces its region just before its end at a walk vertex.** -/
theorem beforeFaces_of_arc_end {l : ℝ} {p : ℕ}
    (hp : p < M.W.n) (hp1 : 1 ≤ p) (harc : M.IsArc F U l ztcfa) (hlr : l ≠ (p : ℝ) + 0) :
    BeforeFaces M p 0 U := by
  zufzk
  zukho
  refine ⟨min δ 1, lt_min hδ' one_pos, fun h => absurd h ztgkw, fun _ s hs0 hs1 => ?_⟩
  have hs1' : ztlbe := lt_of_lt_of_le hs1 ztff
  have hs2 : ztdrm := lt_of_lt_of_le hs1 ztgh
  have := hsub ⟨hs0, hs1'⟩
  zukyh
  refine harc.2.2.2.2.2.2 ztoq zteb by_omega by_linarith by_linarith ?_
  simp_all
section ChainModel
variable (C : Chain)

/-- **The region of a query ray off the chords**: the ray from the point of the position `(p, t)`
into its left sector, along no chord of the family, starts in a region `U`, faced just after the
position (a non-cut key, or a cut vertex turning counterclockwise from the next walk edge) or just
before it (a cut vertex turning clockwise from the previous walk edge). -/
theorem leave_region (hP : C.P.Simple) {Q : Polygon} {F : Set ztf}
    (hFam : (chainModel C).ChordFamily Q F) {z : Point} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {p : ℕ}
    {t : ℝ} (hp : p < (chainModel C).W.n) (ht : 0 ≤ t) (ht1 : t < 1)
    (hpt : sidePt (chainModel C).W p t = z) (hsec : sideLeft (chainModel C).W p t zthzp)
    (hzR : |z.2| < C.radius)
    (hno : ∀ e ∈ F, ¬ ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt z σ s ∈ e) :
    ∃ U ∈ (chainModel C).regions F, (∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt z σ s ∈ U) ∧
      ((¬ (chainModel C).IsCut F ztk ∧ AfterFaces ztc p t U) ∨
        (t = 0 ∧ 0 < sideCross ((chainModel C).W.vtx ztwkm -
            (chainModel C).W.vtx p) ((σ, 0) : Point) ∧ AfterFaces (chainModel C) p t U) ∨
        (t = 0 ∧ 0 < sideCross (ztwn : Point) ((chainModel C).W.vtx
            ztcrw - (chainModel C).W.vtx p) ∧
          BeforeFaces ztc p t U)) := by
  zubkf
  zuoj
  have hF : F ⊆ (chainModel C).Adm := hFam.2.1
  zukbz
  have hsec' : ztwnr := by
    simp_all
  zugjl
  · rcases leave_cases C hP hFam hσ hp ht ht1 hpt hsec hzR with ⟨e, he, -, hev⟩ | hnc |
        ⟨rfl, hp1, hnot, hcr⟩
    · grind
    · simp_all
    · zudqz
      obtain ⟨rfl, rfl⟩ := Chazelle.Chain.sideKey_inj hAc.2.1 hAc.2.2.1 le_rfl one_pos hkey.symm
      zubou
      zubar
      have hnot' : ∀ c ∈ F, SideAttach (chainModel C).W c p' 0 →
          ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt (sidePt (chainModel C).W p' 0) σ s ∉ c := by
        simp_all
      zukle
      · have hray := ray_mem_region_after hGM hFam hU hp harcU hc hAc hσ hsec' hnot' hcr
        zudum
        refine ⟨U, hU, hray, Or.inr (Or.inl ⟨rfl, hcr, ?_⟩)⟩
        exact afterFaces_of_arc harcU hp le_rfl
          ztnqg
      · have hray := ray_mem_region_before hGM hFam hV hp hp1 harcV hc hAc hσ hsec' hnot' hcr
        zudum
        exact ⟨V, hV, hray, Or.inr (Or.inr ⟨rfl, hcr,
          beforeFaces_of_arc_end hp hp1 harcV (WalkAx.arc_cuts hne harcV).2.2⟩)⟩
  · -- a non-cut key: the arc around it
    have hnc := hcut
    have hkey : ztehd := by
      zuks

      have hp0 : ztidy := by
        zuhdi
        simp_all
      have ht0 : ztbhh := by
        grind
      zultd
      have h0 : ztdxs := by
        zudtj
      have := congrArg Prod.snd ztqqn
      zudbt
      grind
    obtain ⟨U, hU, l, r, harc, hin⟩ := exists_arc_around hGM hFam hkey hnc
    have hray := ray_mem_region_of_arc hGM hFam hU hp ht ht1 harc hin hσ hsec'
    zudum
    exact ⟨U, hU, hray, Or.inl ⟨hnc, afterFaces_of_arc harc hp ht ztkfe⟩⟩
end ChainModel
end Sweep
end
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft sideCross freeIn regionsIn)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd hseg)
open Chazelle.Geometry (lerp point_ext)
open Chazelle.Merge (FreeAt)
namespace Sweep
theorem record_ok (M : Model) (Q : Polygon) {z : Point} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {T : ℝ}
    (hT : 0 < T) {h : ℕ} (hh : (Q.vtx h).2 = z.2) {pz pw lp rp : ℕ}
    (hz : M.pos Q ztgpf = z) (hw : M.pos Q ztgpe = rayPt z σ T)
    (hAz : SideAttach M.W ztxvc pz (M.param Q ztgpf))
    (hAw : SideAttach M.W ztxvc pw (M.param Q ztgpe))
    (hlr : ztkic ∧ ztiua) :
    (recOf ztcvt).toSet M Q = Chazelle.segment z ztxn ∧
      (recOf ztcvt).Attached M Q := by
  have hwpt : rayPt z σ T = ((z.1 + σ * T, z.2) : Point) :=
    point_ext by_simp by_simp
  have hzpt : z = ((z.1, z.2) : Point) := rfl
  zur
  · obtain ⟨rfl, rfl⟩ := hlr.1 rfl
    have hset : (recOf ztcvt).toSet M Q = Chazelle.segment z (rayPt z 1 T) := by
      zufdb
      zubi
      rw [hz, hw, hwpt, hh, FactsChain.hseg_eq_segment by_linarith]
    refine ztrdc
    · zudup
    · zudup
  · obtain ⟨rfl, rfl⟩ := hlr.2 rfl
    have hset : (recOf ztcvt).toSet M Q = Chazelle.segment z (rayPt z (-1) T) := by
      zufdb
      zubi
      rw [hz, hw, hwpt, hh, FactsChain.hseg_eq_segment by_linarith, Geometry.segment_comm]
    refine ztrdc
    · zudup
    · zudup

/-- **`SeesInWhole` from the answer**: the flag is `1` iff the direction is free for `C`, and when it
is, the record is the one of `record_ok` at the first hit of `C`. -/
theorem seesInWhole_of_answer (J : Merge.Junction) (Q : Polygon) (i : ℕ) (q : ℕ × ℕ × ℕ)
    (r : ℕ × ℕ × ℕ × ℕ)
    (hflag : r.1 = 1 ↔ FreeAt J.whole ztxjt
      zthwj)
    (hrec : r.1 = 1 → (recOf r.2).toSet ztbm Q =
        Merge.shoot J.whole ztxjt zthwj ∧
      (recOf r.2).Attached ztbm Q) :
    SeesInWhole J Q i q r :=
  ⟨hflag, hrec⟩
end Sweep
end
namespace FuseAsm
@[expose] public section
open Chazelle.Merge (FreeAt shoot)
theorem param_congr (M : Model) (Q : Polygon) (e : ℕ) {h h' : ℕ}
    (hh : (Q.vtx h).2 = (Q.vtx h').2) : M.param Q ztgov = M.param Q ztcju := by
  zudcl
theorem pos_congr (M : Model) (Q : Polygon) (e : ℕ) {h h' : ℕ}
    (hh : (Q.vtx h).2 = (Q.vtx h').2) : M.pos Q ztgov = M.pos Q ztcju := by
  unfold Model.pos; rw [param_congr M Q e hh]
variable (M : Model) (Q : Polygon) (J : Merge.Junction)
theorem toSet_congr {r r' : CRec} (hh : (Q.vtx r.h).2 = (Q.vtx r'.h).2)
    (hl : r.lp = r'.lp) (hr : r.rp = r'.rp) : r.toSet M Q = r'.toSet M Q := by
  zumqj
  rw [hh, pos_congr M Q r.lp hh, pos_congr M Q r.rp hh, hl, hr]
theorem attached_congr {r r' : CRec}
    (hh : (Q.vtx r.h).2 = (Q.vtx r'.h).2) (hl : r.lp = r'.lp) (hr : r.rp = r'.rp)
    (hA : r.Attached M Q) : r'.Attached M Q := by
  unfold CRec.Attached CRec.lpos CRec.rpos at *
  rw [← toSet_congr M Q hh hl hr, ← hl, ← hr, ← param_congr M Q r.lp hh,
    ← param_congr M Q r.rp hh]
  exact hA

/-- The height of a query agrees with its height code. -/
def HeightOK (J : Merge.Junction) (Q : Polygon) (i : ℕ) (q : ℕ × ℕ × ℕ) : Prop :=
  ((chainModel ztgi).pos Q ztpo).2 = (Q.vtx zteut).2

/-- The triple of an answer, with the height index of its query. -/
def qtrip (p : zte × ztpl) : ℕ × ℕ × ℕ :=
  (p.1.2.1 - 1, p.2.2.2.1, p.2.2.2.2)

/-- The triples of the answers with flag `1`, with the height indices of their queries. -/
def collectQ (L : List zte) (R : List ztpl) : List zte :=
  ((L.zip R).filter (fun p => p.2.1 == 1)).map qtrip
theorem collectQ_append {L : List zte} {R : List ztpl}
    (hlen : L.length = R.length) (q : ℕ × ℕ × ℕ) (r : ℕ × ℕ × ℕ × ℕ) :
    collectQ (L ++ [q]) (R ++ [r]) =
      collectQ L R ++ ztfsr := by
  unfold collectQ
  rw [List.zip_append hlen, List.filter_append, List.map_append]
  by_cases h : r.1 = 1 <;> simp [h, qtrip]
theorem collectQ_length_le (L : List zte) (R : List ztpl) :
    (collectQ L R).length ≤ L.length := by
  unfold collectQ; grind

/-- The chord seen from a query of a reported answer is at the height of the query. -/
theorem qtrip_eq (Q : Polygon) (i : ℕ) {q : ℕ × ℕ × ℕ}
    {r : ℕ × ℕ × ℕ × ℕ} (hs : SeesInWhole J Q i q r) (hH : HeightOK J Q i q) (h1 : r.1 = 1) :
    (recOf ztilw).toSet ztbm Q = (recOf r.2).toSet ztbm Q ∧
      (recOf ztilw).Attached ztbm Q := by
  obtain ⟨-, hrec⟩ := hs
  obtain ⟨hset, hatt⟩ := hrec h1
  have hz := Sweep.origin_mem J (a := (chainModel ztgi).pos Q ztpo)
    (σ := dirOf q.2.2)
  rw [← hset] at hz
  have hy : ((chainModel ztgi).pos Q ztpo).2 = (Q.vtx (recOf r.2).h).2 := hz.1
  have hh : (Q.vtx (recOf r.2).h).2 = (Q.vtx (recOf ztilw).h).2 := by
    rw [← hy]; exact hH
  exact ⟨(toSet_congr _ Q hh rfl rfl).symm, attached_congr _ Q hh rfl rfl hatt⟩

/-- **The chords reported by the sweep**, with the height indices of the queries. -/
theorem collectQ_spec (Q : Polygon) (i : ℕ) (L : List zte)
    (R : List ztpl) (hlen : R.length = L.length)
    (hs : ∀ j, j < L.length → SeesInWhole J Q i ztwzi ztxkj)
    (hq : ∀ q ∈ L, QueryOK J Q i q ∧ HeightOK J Q i q) :
    {d | ∃ t ∈ collectQ L R, d = (recOf t).toSet ztbm Q} =
        shots J (geoQ J Q i L) ∧
      ∀ t ∈ collectQ L R, (recOf t).Attached ztbm Q ∧ t.1 < Q.n := by
  have key : ∀ t ∈ collectQ L R, ∃ j, j < L.length ∧ (R.getD j ztlt).1 = 1 ∧
      t = qtrip ztyow := by
    zucj
    simp only [collectQ, List.mem_map, List.mem_filter, beq_iff_eq] at ht
    obtain ⟨p, ⟨hp, h1⟩, rfl⟩ := ht
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hp
    grind
  have memk : ∀ j, j < L.length → (R.getD j ztlt).1 = 1 →
      qtrip ztyow ∈ collectQ L R := by
    intro j hj h1
    have hjR : j < R.length := by_omega
    simp only [collectQ, List.mem_map, List.mem_filter, beq_iff_eq]
    refine ⟨ztlfe, ztcp, ?_⟩
    · have : (L.zip R)[j]' by_simp_all = ztlfe := by_simp
      grind
    · simp_all
    simp_all
  refine ⟨?_, fun t ht => ?_⟩
  · zufsm
    simp only [shots, geoQ, Set.mem_ofPred_eq]
    constructor
    · zuifv
      zucsx

      obtain ⟨e1, -⟩ := qtrip_eq J Q i zttoj (hq _ hmem).2 h1
      zukd
      obtain ⟨hf, hrec⟩ := hs j hj
      grind
    · rintro ⟨x, ⟨q, hq', rfl⟩, hf, rfl⟩
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hq'
      have hs' := hs j hj
      rw [getD_lt hj] at hs'
      have h1 := hs'.1.2 hf
      refine ⟨_, memk j hj h1, ?_⟩
      obtain ⟨e1, -⟩ := qtrip_eq J Q i hs' (hq _ ztuzm).2 h1
      rw [getD_lt hj, e1, (hs'.2 h1).1]
  · zucsx

    obtain ⟨hQ, hH⟩ := hq _ hmem
    refine ⟨(qtrip_eq J Q i zttoj hH h1).2, ?_⟩
    obtain ⟨-, h1', h2', -⟩ := hQ
    simp only [qtrip]
    omega
