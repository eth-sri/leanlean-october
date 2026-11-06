module

public import Chazelle.Core.RestoreDrvPos

/-!
# WP-E, part 13: the restoration driver — `RestoreSpec` from the splitting step

`restoreSpecLocal_of_find : BuildNFSpec → FindSpec → RestoreSpecLocal`.

`RestoreSpecLocal` is `RestoreSpec` with one more hypothesis on the memory context: its
**capacity is local** (`CapLocal X`: `X.cap` does not change when the memory changes at or above
the bound below which `X` holds).  The driver allocates memory before it calls the oracles, and
the oracle interfaces ask for `γ ≤ X.cap` *at the time of the call*; without locality of `cap`
(which `MemCtx` provides for `holds` but not for `cap`) that precondition cannot be re-established
after any write.  The contexts of the project (`gradeCtx`, built by `MemCtx.ofRaw` with a capacity
read at the handle) are local.

The driver runs `d₀ + 1` rounds (`round_step`); after round `t` the degree is
`≤ max D (d₀ - t)`, so the output has degree `≤ D`.  Cost: `(d₀ + 1)` rounds of at most `Br`
steps, bounded by `κ d₀ D (K + 1) F γ G γ (H γ + ⌈log₂ γ⌉ + ⌈log₂ (K + 1)⌉ + 1)` using
`1 ≤ F γ`, `1 ≤ G γ` (`oracle_pos`).
-/

namespace Chazelle.Core

namespace Restore

open Machine Machine.Stmt Programs

@[expose] public section

/-- **`RestoreSpec` for memory contexts with a local capacity.** -/
def RestoreSpecLocal : Prop :=
  ∃ (mk : Stmt → Stmt → Stmt) (κ cR : ℕ → ℕ → ℕ), ∀ (sh cu : Stmt)
    (Bs Bc : Finset ℕ) (F G H : ℕ → ℕ) (X : MemCtx) (Ok : Polygon → Model → Prop),
    CapLocal X → X.Halves → (∀ P M, Ok P M → OkModel P M) →
    Bs ⊆ oracleBands → Bc ⊆ oracleBands → ShooterOK sh Bs F X Ok → CutterOK cu Bc G H X Ok →
    Meets (mk sh cu) (restoreBands ∪ oracleBands)
      (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧
        X.holds P c.nmem (rd c bRestore 6) (c.nreg ALLOC) ∧
        rd c bRestore 4 ≤ X.cap P c.nmem (rd c bRestore 6) ∧ 4 ≤ rd c bRestore 3 ∧
        ModelDescWF P (c.nreg ALLOC) c.nmem (rd c bRestore 0) ∧
        (c.nmem (rd c bRestore 0) = 0 → ∀ H C,
          ChainDescAt c.nmem (rd c bRestore 0 + 1) (Qof P) H C → HostRegular (Qof P).n H) ∧
        (c.nmem (rd c bRestore 0) = 0 → ∀ H C,
          ChainDescAt c.nmem (rd c bRestore 0 + 1) (Qof P) H C → C.P.Simple) ∧
        ∃ M N, ModelDescAt c.nmem (rd c bRestore 0) (Qof P) M ∧ GoodModel M ∧ Ok P M ∧
          M.FullDegLe (Qof P) (rd c bRestore 3) ∧
          NFWithin c.nmem (rd c bRestore 1) (c.nreg ALLOC) N ∧ IsNF M (Qof P) N ∧
          M.DegLe (N.F M (Qof P)) (rd c bRestore 2) ∧
          M.Semigranular (N.F M (Qof P)) (rd c bRestore 4))
      (fun P c c' => ∀ M N, ModelDescAt c.nmem (rd c bRestore 0) (Qof P) M →
        NFAt c.nmem (rd c bRestore 1) N →
        ∃ N', c.nreg ALLOC ≤ rd c' bRestore 5 ∧
          NFWithin c'.nmem (rd c' bRestore 5) (c'.nreg ALLOC) N' ∧ IsNF M (Qof P) N' ∧
          N.F M (Qof P) ⊆ N'.F M (Qof P) ∧ M.DegLe (N'.F M (Qof P)) (rd c bRestore 3) ∧
          M.Semigranular (N'.F M (Qof P)) (rd c bRestore 4) ∧
          N'.nChords ≤ cR (rd c bRestore 2) (rd c bRestore 3) * (N.nChords + 1))
      (fun _ c => κ (rd c bRestore 2) (rd c bRestore 3) * (c.nmem (rd c bRestore 1) + 1) *
        F (rd c bRestore 4) * G (rd c bRestore 4) *
        (H (rd c bRestore 4) + Nat.clog 2 (rd c bRestore 4) +
          Nat.clog 2 (c.nmem (rd c bRestore 1) + 1) + 1))

/-! ## The round loop -/

/-- **All rounds.** -/
theorem rounds_exec {E : DrvEnv} (hE : DrvGood E) {c : Config} (hI : OutI E 0 c) :
    ∃ c' k, Exec E.P E.W (.whileLtN 80010 80011 (roundBody E.sF E.sB)) c c' k ∧
      OutI E (E.d0 + 1) c' ∧ RF dBands E.A₀ c c' k ∧ k ≤ (E.Br + 2) * (E.d0 + 1) + 2 := by
  obtain ⟨c', k, e, ⟨t, I'⟩, hx, RFl, hk⟩ := whileLtN_frame (P := E.P) (W := E.W)
    (a := 80010) (b := 80011) (body := roundBody E.sF E.sB) (B := dBands) (A₀ := E.A₀)
    (fun c => ∃ t, OutI E t c) (fun c => E.d0 + 1 - c.nreg 80010) E.Br
    (fun c ⟨_, h⟩ => h.wb)
    (fun c ⟨t, I⟩ ht => by
      rw [I.r10, I.r11] at ht
      obtain ⟨c', k, e, I', RF', hk⟩ := round_step hE I ht
      exact ⟨c', k, e, ⟨t + 1, I'⟩, RF', hk, by rw [I.r10, I'.r10]; omega⟩) ⟨0, hI⟩
  have ht : t = E.d0 + 1 := by
    rw [I'.r10, I'.r11] at hx; have := I'.t_le; omega
  subst ht
  refine ⟨c', k, e, I', RFl, ?_⟩
  rw [hI.r10] at hk
  simpa using hk

/-! ## Arithmetic of the cost -/

theorem clog_two_pow_mul (j x : ℕ) : Nat.clog 2 (2 ^ j * x) ≤ j + Nat.clog 2 x := by
  apply Nat.clog_le_of_le_pow
  rw [pow_add]
  exact Nat.mul_le_mul_left _ (Nat.le_pow_clog (by norm_num) x)

/-- The constant of the round bound. -/
def C1 (κf : ℕ → ℕ) (κB d0 D : ℕ) : ℕ :=
  40 + 21 * 2 ^ (d0 + 1) + (κf (d0 + D) + 22) * 2 ^ (d0 + 1) +
    κB * (2 * 2 ^ (d0 + 1) * (d0 + 3) + 1)

/-- The constant of the cost bound. -/
def κRestore (κf : ℕ → ℕ) (κB : ℕ) (d0 D : ℕ) : ℕ :=
  (d0 + 1) * (C1 κf κB d0 D + 14) + d0 + D + 20

set_option maxHeartbeats 4000000 in
/-- **The round bound is linear.** -/
theorem Br_le (E : DrvEnv) (hF : 1 ≤ E.F E.γ) (hG : 1 ≤ E.G E.γ) :
    E.Br ≤ C1 E.κf E.κB E.d0 E.D * (E.K₀ + 1) * (E.F E.γ * E.G E.γ *
      (E.Hc E.γ + Nat.clog 2 E.γ + Nat.clog 2 (E.K₀ + 1) + 1)) := by
  set T := 2 ^ (E.d0 + 1) with hT
  set K1 := E.K₀ + 1 with hK1
  set A := E.F E.γ * E.G E.γ * (E.Hc E.γ + Nat.clog 2 E.γ + Nat.clog 2 K1 + 1) with hA
  set A0 := E.F E.γ * E.G E.γ * (E.Hc E.γ + Nat.clog 2 E.γ + 1) with hA0
  set L := Nat.clog 2 K1
  have hFG : 1 ≤ E.F E.γ * E.G E.γ := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hA1 : 1 ≤ A := by
    rw [hA]; nlinarith
  have hA0A : A0 ≤ A := by
    rw [hA, hA0]; exact Nat.mul_le_mul_left _ (by omega)
  have hLA : L + 1 ≤ A := by
    rw [hA]
    calc L + 1 ≤ 1 * (E.Hc E.γ + Nat.clog 2 E.γ + L + 1) := by omega
      _ ≤ E.F E.γ * E.G E.γ * (E.Hc E.γ + Nat.clog 2 E.γ + L + 1) := Nat.mul_le_mul_right _ hFG
  have hKc : E.Kc = T * K1 := rfl
  have hBf : E.Bf = E.κf (E.d0 + E.D) * A0 + 20 := by
    unfold DrvEnv.Bf costF; rw [hA0]; ring
  have hcl : Nat.clog 2 (2 * E.Kc) ≤ E.d0 + 2 + L := by
    have : 2 * E.Kc = 2 ^ (E.d0 + 2) * K1 := by rw [hKc, hT, pow_succ 2 (E.d0 + 1)]; ring
    rw [this]; exact clog_two_pow_mul _ _
  have hBr : E.Br = 40 + 21 * E.Kc + (E.Bf + 2) * E.Kc +
      E.κB * (2 * E.Kc * (Nat.clog 2 (2 * E.Kc) + 1) + 1) := rfl
  -- the four terms
  have t1 : 40 ≤ 40 * K1 * A := by nlinarith
  have t2 : 21 * E.Kc ≤ 21 * T * K1 * A := by rw [hKc]; nlinarith
  have t3 : (E.Bf + 2) * E.Kc ≤ (E.κf (E.d0 + E.D) + 22) * T * K1 * A := by
    rw [hBf, hKc]
    have h1 : E.κf (E.d0 + E.D) * A0 + 22 ≤ (E.κf (E.d0 + E.D) + 22) * A := by nlinarith
    have h2 := Nat.mul_le_mul_right (T * K1) h1
    nlinarith
  have t4 : 2 * E.Kc * (Nat.clog 2 (2 * E.Kc) + 1) + 1 ≤
      (2 * T * (E.d0 + 3) + 1) * K1 * A := by
    rw [hKc]
    have h1 : 2 * (T * K1) * (Nat.clog 2 (2 * (T * K1)) + 1) ≤
        2 * (T * K1) * (E.d0 + 3 + L) := Nat.mul_le_mul_left _ (by rw [← hKc]; omega)
    have h2 : E.d0 + 3 + L ≤ (E.d0 + 3) * A := by nlinarith
    have h3 : 2 * (T * K1) * (E.d0 + 3 + L) ≤ 2 * (T * K1) * ((E.d0 + 3) * A) :=
      Nat.mul_le_mul_left _ h2
    nlinarith
  have t4' := Nat.mul_le_mul_left E.κB t4
  have hC : C1 E.κf E.κB E.d0 E.D * (E.K₀ + 1) * (E.F E.γ * E.G E.γ *
      (E.Hc E.γ + Nat.clog 2 E.γ + Nat.clog 2 (E.K₀ + 1) + 1)) =
      40 * K1 * A + 21 * T * K1 * A + (E.κf (E.d0 + E.D) + 22) * T * K1 * A +
        E.κB * ((2 * T * (E.d0 + 3) + 1) * K1 * A) := by
    unfold C1; rw [← hT, ← hK1]; ring
  rw [hC, hBr]
  omega

set_option maxHeartbeats 8000000 in
/-- **WP-E: restoring conformality**, from the splitting step (`FindSpec`) and the construction
of normal forms, for memory contexts with a local capacity. -/
theorem restoreSpecLocal_of_find (hB : BuildNFSpec) (hF : FindSpec) : RestoreSpecLocal := by
  obtain ⟨sB, κB, hsB⟩ := Gran.buildOK_of hB
  obtain ⟨mkF, κf, hmkF⟩ := hF
  refine ⟨fun sh cu => restoreStmt (mkF sh cu) sB, κRestore κf κB, fun d0 _ => 2 ^ (d0 + 1), ?_⟩
  intro sh cu Bs Bc F G H X Ok hloc hhalf hOkM hBs hBc hsh hcu P W c hw pre hroom
  obtain ⟨hGE, hWh, hX, hcap, hD4, hwf, hreg, hsimp, M, N, hMD, hGM, hOk, hfull, hNW, hNF, hdeg, hsg⟩ := pre
  beta_reduce at hroom ⊢
  have e0 : rd c bRestore 0 = c.nreg 80000 := rfl
  have e1 : rd c bRestore 1 = c.nreg 80001 := rfl
  have e2 : rd c bRestore 2 = c.nreg 80002 := rfl
  have e3 : rd c bRestore 3 = c.nreg 80003 := rfl
  have e4 : rd c bRestore 4 = c.nreg 80004 := rfl
  have e6 : rd c bRestore 6 = c.nreg 80006 := rfl
  rw [e0] at hwf hMD hreg hsimp
  rw [e1] at hNW hroom
  rw [e2] at hdeg hroom
  rw [e3] at hfull hD4 hroom
  rw [e4] at hsg hcap hroom
  rw [e6] at hX hcap
  rw [e0, e1, e2, e3, e4]
  set MD := c.nreg 80000
  set NFH := c.nreg 80001
  set d0 := c.nreg 80002
  set D := c.nreg 80003
  set γ := c.nreg 80004
  set g := c.nreg 80006
  have hK : c.nmem NFH = N.nChords := hNW.nfAt.1
  rw [hK] at hroom ⊢
  set K := N.nChords with hKd
  have hγ1 : 1 ≤ γ := one_le_gamma hGM hNF.1 hsg
  obtain ⟨hF1, hG1⟩ := oracle_pos hsh hcu hw hGE hWh hX hcap hwf hreg hMD hGM hOk hγ1
    (hw.1 _) (hw.1 _) (hw.1 _)
  -- the driver data
  set E : DrvEnv := ⟨P, W, M, c.nreg ALLOC, c.nmem, MD, d0, D, γ, g, mkF sh cu, sB, κf, κB, F, G,
    H, X, Ok, N.F M (Qof P), K⟩
  have hE : DrvGood E := ⟨hmkF sh cu Bs Bc F G H X Ok oracleBands subset_rfl (by decide) hloc hhalf
    (fun P M h => Or.inl (hOkM P M h))
    hBs hBc hsh hcu, hsB, hGE, hWh, hX,
    fun m hm => by
      show γ ≤ X.cap P m g
      rwa [hloc P c.nmem m g (c.nreg ALLOC) hm hX],
    hwf, hMD, hreg, hsimp, hGM, hOk, hfull⟩
  -- cost bounds
  set A := F γ * G γ * (H γ + Nat.clog 2 γ + Nat.clog 2 (K + 1) + 1) with hAd
  have hBr : E.Br ≤ C1 κf κB d0 D * (K + 1) * A := Br_le E hF1 hG1
  have hcost : κRestore κf κB d0 D * (K + 1) * F γ * G γ *
      (H γ + Nat.clog 2 γ + Nat.clog 2 (K + 1) + 1) = κRestore κf κB d0 D * (K + 1) * A := by
    rw [hAd]; ring
  rw [hcost] at hroom ⊢
  have hK1A : 1 ≤ (K + 1) * A := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hbig : (E.Br + 2) * (E.d0 + 1) + 20 + d0 + D ≤ κRestore κf κB d0 D * (K + 1) * A := by
    have h1 : (E.Br + 2) * (d0 + 1) ≤ (C1 κf κB d0 D * (K + 1) * A + 2) * (d0 + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 : κRestore κf κB d0 D * (K + 1) * A =
        (d0 + 1) * (C1 κf κB d0 D + 14) * ((K + 1) * A) + (d0 + D + 20) * ((K + 1) * A) := by
      unfold κRestore; ring
    have h3 : (C1 κf κB d0 D * (K + 1) * A + 2) * (d0 + 1) ≤
        (d0 + 1) * (C1 κf κB d0 D + 14) * ((K + 1) * A) := by nlinarith
    have h4 : d0 + D + 20 ≤ (d0 + D + 20) * ((K + 1) * A) := Nat.le_mul_of_pos_right _ hK1A
    show (E.Br + 2) * (d0 + 1) + 20 + d0 + D ≤ _
    omega
  -- initialisation
  have hn3 : 3 ≤ P.n := Jordan.simple_three_le hGE.1
  have hW5 : 5 ≤ W := le_trans (by unfold hostWords; omega) hWh
  obtain ⟨c₁, k₁, e₁, hk₁, i20, i21, i22, i23, i24, i12, i10, i11, i19, R₁, rr₁, m₁, rm₁, o₁⟩ :=
    init_exec (P := P) c hw hW5 (by omega) (by omega)
  have w₁ := e₁.wb_right
  have A₁ : c₁.nreg ALLOC = c.nreg ALLOC := R₁ _ (by left; decide) (by decide)
  have hI0 : OutI E 0 c₁ := by
    refine ⟨w₁, R₁ _ (by left; decide) (by decide), R₁ _ (by left; decide) (by decide),
      R₁ _ (by left; decide) (by decide), R₁ _ (by left; decide) (by decide),
      R₁ _ (by left; decide) (by decide), i10, i11, i19, i20, i21, i22, i23, i24, ⟨N, ?_⟩,
      fun a _ => by rw [m₁], by rw [A₁], by omega, ?_⟩
    · refine ⟨by rwa [i12, m₁, A₁], hNF, subset_rfl, ?_, hsg, by show N.nChords + 1 ≤ 2 ^ 0 * (K + 1); simp [hKd], fun h => ?_⟩
      · exact Model.DegLe.mono _ hdeg (by show d0 ≤ max D (d0 - 0); omega)
      · omega
    · rw [A₁]
      show c.nreg ALLOC + (d0 + 1 - 0) * (E.Br + 2) + 3 ≤ W
      have : (d0 + 1 - 0) * (E.Br + 2) = (E.Br + 2) * (E.d0 + 1) := by
        show (d0 + 1 - 0) * (E.Br + 2) = (E.Br + 2) * (d0 + 1); rw [Nat.sub_zero, mul_comm]
      omega
  -- the rounds
  obtain ⟨c₂, k₂, e₂, I₂, RF₂, hk₂⟩ := rounds_exec hE hI0
  obtain ⟨N₂, hcur₂⟩ := I₂.cur
  -- the output
  obtain ⟨c₃, k₃, e₃, hk₃, h05, R₃, rr₃, m₃, rm₃, o₃⟩ := copy1_exec' (P := P) c₂ I₂.wb 80005 80012
  have RF₁ : RF dBands (c.nreg ALLOC) c c₁ k₁ :=
    rf_of_regs (fun r hr => R₁ r (by omega) (by omega)) rr₁ m₁ rm₁ o₁
  have RF₃ : RF dBands (c.nreg ALLOC) c₂ c₃ k₃ :=
    rf_of_regs (fun r hr => R₃ r (by omega)) rr₃ m₃ rm₃ o₃
  have RFall := RF₁.trans (RF₂.trans RF₃)
  refine ⟨c₃, k₁ + (k₂ + k₃), .seq e₁ (.seq e₂ e₃), ?_, ?_, RFall.to_frame⟩
  · show k₁ + (k₂ + k₃) ≤ _
    omega
  · intro M' N' hM' hN'
    have hMM : M = M' := NFLoc.modelDesc_unique hMD hM'
    subst hMM
    have hch := NFLoc.nfAt_chords_eq hNW.nfAt hN'
    have hFeq : N'.F M (Qof P) = N.F M (Qof P) := Gran.F_congr hch
    have hA3 : c₃.nreg ALLOC = c₂.nreg ALLOC := R₃ _ (by decide)
    have hKN' : N'.nChords = K := by
      show N'.chords.length = N.chords.length; rw [hch]
    refine ⟨N₂, ?_, ?_, hcur₂.nf, by rw [hFeq]; exact hcur₂.sub, ?_, hcur₂.sg, ?_⟩
    · show c.nreg ALLOC ≤ c₃.nreg 80005
      rw [h05]; exact hcur₂.fresh (by omega)
    · show NFWithin c₃.nmem (c₃.nreg 80005) (c₃.nreg ALLOC) N₂
      rw [h05, m₃, hA3]; exact hcur₂.nw
    · exact Model.DegLe.mono _ hcur₂.deg (by show max D (d0 - (d0 + 1)) ≤ D; omega)
    · have hs := hcur₂.size
      show N₂.nChords ≤ 2 ^ (d0 + 1) * (N'.nChords + 1)
      rw [hKN']
      have : E.d0 = d0 := rfl
      have : E.K₀ = K := rfl
      simp only [‹E.d0 = d0›, ‹E.K₀ = K›] at hs
      omega

end

end Restore

end Chazelle.Core
