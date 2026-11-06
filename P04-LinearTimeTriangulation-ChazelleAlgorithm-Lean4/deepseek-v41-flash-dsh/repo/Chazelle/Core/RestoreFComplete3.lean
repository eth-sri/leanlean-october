module

public import Chazelle.Golf

public import Chazelle.Core.RestoreFComplete2
public import Chazelle.Core.ShootCutCutterOK

/-!
# WP-E, the search: completeness (part 3)

**A pair run finds a success** (`pair_complete`): the good vertex lies in a closed piece of the
cut of its arc; a kind-0 piece tests it among its first ten vertices, a kind-1 piece at an end or
the junction of its stretches, or its descent reaches it.
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Set Filter Topology
open Chazelle.Chain (sideInArc SideAttach sidePt)
open DownHost ArcT

variable {E : FEnv} {c₀ : Config}

/-- At most seven walk edges are uncounted. -/
theorem uncounted_le (hE : FGood E c₀) : {p | p < E.M.W.n ∧ ¬ E.M.counted p}.ncard ≤ 7 := by
  rcases hE.kind with ⟨C, -, hM⟩ | hM
  · have hn : E.M.W.n = 2 * C.m + 7 := by rw [hM]; exact chainModel_n C
    have hsub : {p | p < E.M.W.n ∧ ¬ E.M.counted p} ⊆
        (([0, 1, 2, 3, 4, 5, 2 * C.m + 6].toFinset : Finset ℕ) : Set ℕ) := by
      rintro p ⟨hp, hc⟩
      rw [hM] at hc
      simp only [chainModel, not_and, not_lt] at hc
      simp only [List.coe_toFinset, List.mem_cons, List.not_mem_nil, or_false,
        mem_ofPred_eq]
      by_cases h6 : 6 ≤ p
      · have := hc h6; omega
      · omega
    calc _ ≤ (([0, 1, 2, 3, 4, 5, 2 * C.m + 6].toFinset : Finset ℕ) : Set ℕ).ncard :=
          Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      _ ≤ 7 := by rw [Set.ncard_coe_finset]; exact List.toFinset_card_le _
  · have : {p | p < E.M.W.n ∧ ¬ E.M.counted p} = ∅ := by
      ext p; simp only [mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro _ h; apply h; rw [hM]; trivial
    rw [this, Set.ncard_empty]; omega

/-- **A closed piece from unwrapped bounds.** -/
theorem closed_of_unwrap {n a x y z : ℝ} (ha : 0 ≤ a ∧ a < n) (hx : 0 ≤ x ∧ x < n)
    (hy : 0 ≤ y ∧ y < n) (hz : 0 ≤ z ∧ z < n) (hxz : unwrapK n a x < unwrapK n a z)
    (h1 : unwrapK n a x ≤ unwrapK n a y) (h2 : unwrapK n a y ≤ unwrapK n a z) :
    ClosedArc x z y := by
  rcases h1.lt_or_eq with h1 | h1
  · rcases h2.lt_or_eq with h2 | h2
    · exact Or.inl ((cyc_unwrap ha hx hz hy hxz).2 ⟨h1, h2⟩)
    · right; right
      Ξ ← wrapK_unwrapK (n := n) (l := a) hy, h2, wrapK_unwrapK hz
  · right; left
    Ξ ← wrapK_unwrapK (n := n) (l := a) hy, ← h1, wrapK_unwrapK hx

theorem dir_bit {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    ∃ σb, σb ≤ 1 ∧ dirOf σb = σ := by
  rcases hσ with rfl | rfl
  · exact ⟨1, le_rfl, ⊚ dirOf⟩
  · exact ⟨0, ⊛, by simp [dirOf]⟩


/-- **A pair run of the good vertex's arcs finds a success.** -/
theorem pair_complete (hE : FGood E c₀) {reg : ℕ → Set Point}
    (hregs : NFRegs E.M (Qof E.P) E.N reg) {X : WPos} {σ T : ℝ} {po : ℕ} {tq : ℝ}
    {ti tj : ℕ} (hG : GoodSet E reg X σ T po tq ti tj) {f : ℕ} (hpd : PairDone E c₀ ti tj f) :
    f = 1 := by
  obtain ⟨c₃, hI₃, hcp, h40, h41, hdone⟩ := hpd
  have hE₃ := hE.rebase hI₃
  have hM := walkAx_of_goodModel hE.hGM
  set L := c₃.nreg 81076 with hLdef
  have hT := tile_of_cut hE hG.hch hG.hti hcp
  have hcp' := hcp
  obtain ⟨hLq, -, hq1, -, -, -, -, hk0w, hk1w, hpos, hkind⟩ := hcp'
  -- the good vertex
  have hX0 := hG.hgc.1
  have hXe := hG.hgc.2.1
  have hXX : X = ⟨X.edge, 0⟩ := by cases X; simp only at hX0 ⊢; rw [hX0]
  have hxk : 0 ≤ (X.edge : ℝ) + 0 ∧ (X.edge : ℝ) + 0 < E.M.W.n := by
    have : (X.edge : ℝ) + 1 ≤ E.M.W.n := by exact_mod_cast hXe
    constructor <;> linarith [(Nat.cast_nonneg X.edge : (0 : ℝ) ≤ X.edge)]
  have hXi := hG.hXi
  unfold aK bK at hXi
  obtain ⟨u1, u2⟩ := (closedArc_unwrap hT.ha hT.hb hxk hT.hab).1 hXi
  obtain ⟨i', hi', hs1, hs2⟩ := tile_cover hT hxk u1 u2
  obtain ⟨-, -, hse, -⟩ := tile_mono hT i' hi'
  have hcl : ClosedArc (psK E c₃.nmem L i') (peK E c₃.nmem L i') ((X.edge : ℝ) + 0) :=
    closed_of_unwrap hT.ha (hT.hs i' hi') hxk (hT.he i' hi') hse hs1 hs2
  rw [add_zero] at hcl
  have hspe : psK E c₃.nmem L i' ≠ peK E c₃.nmem L i' := fun h => by rw [h] at hse; exact lt_irrefl _ hse
  obtain ⟨σb, hσb, hdσ⟩ := dir_bit hG.hgc.2.2.1
  have hGA : GoodAt (E.re c₃) reg X.edge σb := ⟨T, by rw [hdσ, ← hXX]; exact hG.hgc⟩
  have hPD := hdone i' hi'
  have hk : c₃.nmem (L + 1 + 7 * i' + 4) ≤ 1 := hkind i' hi'
  rcases (show c₃.nmem (prOf L i' + 4) = 0 ∨ c₃.nmem (prOf L i' + 4) = 1 by
    show c₃.nmem (L + 1 + 7 * i' + 4) = 0 ∨ c₃.nmem (L + 1 + 7 * i' + 4) = 1; omega) with hk0 | hk1
  · -- a kind-0 piece
    obtain ⟨t, ht, htx⟩ := light_cover (uncounted_le hE) (hpos i' hi').1 (hpos i' hi').2.2.1
      (key_bounds (hpos i' hi').2.1 (hpos i' hi').2.2.2) hspe (hk0w i' hi' hk0) hXe hcl
    have e : (c₃.nmem (prOf L i') + t) % E.M.W.n = X.edge := htx
    exact hPD.1 hk0 reg hregs hG.hch t ht (by
      show VSet E ((c₃.nmem (prOf L i') + t) % E.M.W.n)
      rw [e]; exact hG.hVX) σb hσb (by
      show GoodAt (E.re c₃) reg ((c₃.nmem (prOf L i') + t) % E.M.W.n) σb
      rw [e]; exact hGA)
  · -- a kind-1 piece
    obtain ⟨Hs, Cα, N, γ', hK, J, hV, htest, hst1, hst2⟩ := hPD.2 hk1
    obtain ⟨-, Hs', Cα', N', hCD', -, -, hset', hwt', hPW', -, -⟩ := hk1w i' hi' hk1
    have hCC : Cα' = Cα := ShootCut.chainDesc_unique hCD' hK.hCD
    subst hCC
    obtain ⟨hpw0, hpw3, -, hpwe, -⟩ := hPW'
    set n := E.M.W.n with hndef
    set s := c₃.nmem (L + 1 + 7 * i' + 0) with hsdef
    have hs : s < n := (hpos i' hi').2.2.1
    have hmn := hK.hmn
    have hm1 := Cα'.one_le
    have kS : psK E c₃.nmem L i' = (s : ℝ) := by
      unfold psK; simp only at hpw0; rw [hpw0]; exact key_vtx' _ _ _
    have kE : peK E c₃.nmem L i' = (((s + Cα'.m) % n : ℕ) : ℝ) := by
      unfold peK; simp only at hpw3 hpwe; rw [hpw3, hpwe]; exact key_vtx' _ _ _
    have hwt'' : E.M.arcWt (s : ℝ) (((s + Cα'.m) % n : ℕ) : ℝ) = Cα'.m := by
      rw [← kS, ← kE]; exact hwt'
    have hcnt := counted_of_wt (M := E.M) hs (by omega) hmn hwt''
    rw [kS, kE] at hcl
    obtain ⟨d, hd, hdx⟩ := closed_offset hs hmn (by omega) hXe hcl
    -- the piece's chain
    have hdir : (∀ e, e ≤ Cα'.m → E.M.W.vtx ((s + e) % n) = Cα'.vertex e) ∨
        (∀ e, e ≤ Cα'.m → E.M.W.vtx ((s + e) % n) = Cα'.vertex (Cα'.m - e)) := hK.hdir
    have hinB : ∀ C : Chain, E.M = chainModel C → Cα'.set ⊆ C.set := fun C hMC => by
      have hc := hcnt
      have hdir' := hdir
      rw [hndef] at hdir'
      rw [hMC] at hc hdir'
      exact piece_set_sub hdir' hc
    have hsetD : ∀ x ∈ Cα'.set, x ∉ E.M.D := by
      intro x hx
      rw [← hset'] at hx
      obtain ⟨p, t, hp, ht0, ht1, -, rfl⟩ := hx
      exact hM.trace p hp t ht0 ht1
    have hin : ∀ (k : ℕ) (t : ℝ), 0 ≤ t → t < 1 → 0 < (k : ℝ) + t → (k : ℝ) + t < Cα'.m →
        sideInArc (E.M.key (Qof E.P) (arcOf E.N E.r ti).s) (E.M.key (Qof E.P) (arcOf E.N E.r ti).e)
          ((((s + k) % n : ℕ) : ℝ) + t) := fun k t ht0 ht1 h0 hm => by
      have h1 := off_sideInArc hs hmn ht0 ht1 h0 hm
      rw [← kS, ← kE] at h1
      have hb : 0 ≤ (((s + k) % n : ℕ) : ℝ) + t ∧ (((s + k) % n : ℕ) : ℝ) + t < n := by
        have h2 : ((s + k) % n : ℕ) + 1 ≤ n := Nat.mod_lt _ (by omega)
        have h2' : (((s + k) % n : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast h2
        exact ⟨by positivity, by linarith⟩
      exact tile_inner hT hi' hb h1
    -- the target
    have hAj := arc_isArc hE hregs hG.htj
    have haj : E.M.key (Qof E.P) (arcOf E.N E.r tj).s =
        E.M.key (Qof E.P) ⟨c₃.nreg 81140, c₃.nreg 81141⟩ := by rw [h40, h41]
    have hAOK := hE.arcOK hG.hch hG.htj
    have htc : 0 < c₃.nreg 81141 ∨ c₃.nreg 81021 ≤ c₃.nreg 81140 :=
      far_range hE₃ (far := ⟨c₃.nreg 81140, c₃.nreg 81141⟩) (by show _ < n; rw [h40]; exact hAOK.se)
        (fun C hC => by
          show |(E.M.pos (Qof E.P) ⟨c₃.nreg 81140, c₃.nreg 81141⟩).2| < C.radius
          rw [h40, h41]; exact hAOK.sy C hC)
    have hij := hG.hij
    have hXj := hG.hXj
    simp only [aK, bK] at hij hXj
    -- the good vertex in the stretches
    have hgood : ∀ g dX : ℕ, (g + dX) % n = X.edge →
        GoodCand E.M (Qof E.P) (E.N.F E.M (Qof E.P)) (reg E.r) ⟨(g + dX) % n, 0⟩ σ T ∧
        SideAttach E.M.W (chordOf (E.M.pos (Qof E.P) ⟨(g + dX) % n, 0⟩) σ T) ((g + dX) % n) 0 ∧
        SideAttach E.M.W (chordOf (E.M.pos (Qof E.P) ⟨(g + dX) % n, 0⟩) σ T) po tq ∧
        sidePt E.M.W ((g + dX) % n) 0 ≠ sidePt E.M.W po tq ∧
        ClosedArc (E.M.key (Qof E.P) (arcOf E.N E.r ti).s)
          (E.M.key (Qof E.P) (arcOf E.N E.r ti).e) ((((g + dX) % n : ℕ) : ℝ) + 0) ∧
        CountOK E.M (E.N.F E.M (Qof E.P)) (reg E.r) ((((g + dX) % n : ℕ) : ℝ) + 0)
          ((po : ℝ) + tq) := fun g dX h => by
      rw [h, ← hXX]
      exact ⟨hG.hgc, hG.hXA, hG.hOA, hG.hne, hXi, hG.hcnt⟩
    have hPRs : c₃.nmem (prOf L i') = s := rfl
    rcases Nat.eq_zero_or_pos d with rfl | hd0
    · refine htest reg hregs hG.hch X.edge (Or.inl ?_) hG.hVX σb hσb hGA
      rw [hPRs, ← hdx, Nat.add_zero, Nat.mod_eq_of_lt hs]
    rcases (show d = Cα'.m ∨ d < Cα'.m by omega) with rfl | hdm
    · exact htest reg hregs hG.hch X.edge (Or.inr (Or.inl (by rw [hPRs]; exact hdx.symm)))
        hG.hVX σb hσb hGA
    have htl := WalkEmbed.tpos_lt Cα' J
    by_cases hone : WalkEmbed.tpos Cα' J + Cα'.m ≤ 2 * Cα'.m
    · obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hgood s d hdx
      obtain ⟨regα, Tα, hD⟩ := descGood_mk hE₃ hregs hG.hch (arc_isArc hE hregs hG.hti) hAj hij hK
        hcnt hsetD hinB hin (g := s) (d0 := 0) (g' := 6 + WalkEmbed.tpos Cα' J) (L := Cα'.m)
        (dX := d) (by show s = s % E.M.W.n; rw [Nat.mod_eq_of_lt hs]) (by omega) (by omega) hd0 hdm hσb
        hdσ g1 g2 g3 g4 g5 hXj g6
      exact hst1 hone reg _ _ _ _ d regα Tα hD haj htc
    · obtain ⟨hs1', hs2'⟩ := hst2 (by omega)
      set L₁ := 2 * Cα'.m - WalkEmbed.tpos Cα' J with hL₁
      rcases (show d < L₁ ∨ d = L₁ ∨ L₁ < d by omega) with h1 | h1 | h1
      · obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hgood s d hdx
        obtain ⟨regα, Tα, hD⟩ := descGood_mk hE₃ hregs hG.hch (arc_isArc hE hregs hG.hti) hAj
          hij hK hcnt hsetD hinB hin (g := s) (d0 := 0) (g' := 6 + WalkEmbed.tpos Cα' J) (L := L₁)
          (dX := d) (by show s = s % E.M.W.n; rw [Nat.mod_eq_of_lt hs]) (by omega) (by omega) hd0 h1 hσb
          hdσ g1 g2 g3 g4 g5 hXj g6
        exact hs1' reg _ _ _ _ d regα Tα hD haj htc
      · subst h1
        exact htest reg hregs hG.hch X.edge (Or.inr (Or.inr ⟨by omega, by rw [hPRs]; exact hdx.symm⟩))
          hG.hVX σb hσb hGA
      · have hgx : ((s + L₁) % n + (d - L₁)) % n = X.edge := by
          rw [Nat.mod_add_mod, show s + L₁ + (d - L₁) = s + d by omega, hdx]
        obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hgood _ _ hgx
        obtain ⟨regα, Tα, hD⟩ := descGood_mk hE₃ hregs hG.hch (arc_isArc hE hregs hG.hti) hAj
          hij hK hcnt hsetD hinB hin (g := (s + L₁) % n) (d0 := L₁) (g' := 6) (L := Cα'.m - L₁)
          (dX := d - L₁) rfl (by omega) (by omega) (by omega) (by omega) hσb hdσ g1 g2 g3 g4 g5
          hXj g6
        exact hs2' reg _ _ _ _ (d - L₁) regα Tα hD haj htc


/-- **Completeness of the search**: if the region has more exits than the full maps allow, the
pair runs set the flag. -/
theorem find_complete (hE : FGood E c₀) {f : ℕ}
    (hpd : ∀ i, i < kOf E → ∀ j, j < kOf E → PairDone E c₀ i j f) {reg : ℕ → Set Point}
    (hregs : NFRegs E.M (Qof E.P) E.N reg) (hfull : E.M.FullDegLe (Qof E.P) E.D)
    (hdeg : E.D < E.M.deg (E.N.F E.M (Qof E.P)) (reg E.r)) : f = 1 := by
  obtain ⟨X, σ, T, po, tq, ti, tj, hG⟩ := good_set hE hregs hfull hdeg
  have hk : kOf E = (E.N.region E.r).arcs.length := by unfold kOf; rw [ite_eq_right hG.hch]
  exact pair_complete hE hregs hG (hpd ti (by rw [hk]; exact hG.hti) tj (by rw [hk]; exact hG.htj))

end

end Restore

end Chazelle.Core
