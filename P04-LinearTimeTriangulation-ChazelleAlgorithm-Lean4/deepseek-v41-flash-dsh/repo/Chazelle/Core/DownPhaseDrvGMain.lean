module

public import Chazelle.Golf

public import Chazelle.Core.DownPhaseDrvGInit
public import Chazelle.Core.DownPhaseDrvRRegSpec
public import Chazelle.Core.ShootCutGrade

/-!
# Down-phase driver, region procedure (D5), part 10: the contract

**`DrvG.regionSpec (hM : MergeSpec) (hSC : ShootCutSpec O) (hPc : PieceSpec O) :
DrvR.RegionSpec O`**.  The program `rgS sp (mk sh cu)` (`DownPhaseDrvGProg`) with the piece
procedure of `PieceSpec`, the merge of `MergeSpec` and the oracles of `ShootCutSpec`: the leaf
table (`plS`), the pieces in chain order (connectors and leaves, `lfLoop`, `finCon`) merged one by
one (`mgStep`), at most `120` merges (at most `60` leaves), cost `rgK (lemma41Nat μ + 1)`.
-/

namespace Chazelle.Core

namespace DrvG

open Machine Machine.Stmt Programs BuildRam DrvR

@[expose] public section

/-- The constant of the region procedure. -/
def rgK (κP κM κs : ℕ) : ℕ := 121 * κP + 121 * mcK κM κs + 200000

theorem lfB_def (pc : ℕ) : lfB pc = 2 * pc + 30 := rfl

section exec

variable {O : OracleIface} {P : Polygon} {W : ℕ}


/-- **The region procedure, one run.** -/
theorem rgS_run {sp sM : Stmt} {κP κs : ℕ} {κ : ℕ → ℕ} (hsp : PcMeets O sp κP)
    (hM : L41.MergeMeets sM κ (L41.scF κs) (L41.scG κs) cutGran (gradeCtx O) OkModel)
    (c : Config) (hw : WordsBounded W c)
    (hPre : GoodEnv P ∧ hostWords P.n ≤ W ∧
      (gradeCtx O).holds P c.nmem (c.nreg 219205) (c.nreg ALLOC) ∧
      7 ≤ c.nreg 219202 ∧ c.nreg 219202 ≤ c.nmem (c.nreg 219205) ∧
      c.nreg 219203 = 2 ^ c.nreg 219202 ∧
      2 * gradeGran (c.nreg 219202) ≤ c.nreg 219204 ∧ 128 ≤ c.nreg 219204 ∧
      c.nreg 219204 ≤ 4096 * 2 ^ Cost.ceilBeta (c.nreg 219202) ∧
      c.nreg 219204 + 129 ≤ (gradeCtx O).cap P c.nmem (c.nreg 219205) ∧
      ∃ H : Host, Robust (c.nreg ALLOC) c.nmem (fun m => HostAt m (c.nreg 219200) H) ∧
        c.nreg 219200 + 3 * H.length + 1 ≤ c.nreg ALLOC ∧
        H.length ≤ 20 ∧ HostWF (Qof P).n H ∧ HostRegular (Qof P).n H ∧
        (H.poly (Qof P)).Simple ∧
        c.nreg 219201 = (H.pts (Qof P).n).length ∧ 3 ≤ c.nreg 219201 ∧
        ∀ a ℓ, HostItem.run a ℓ ∈ H → ℓ ≤ 2 * c.nreg 219203)
    (hroom : c.nreg ALLOC + rgK κP (κ 130) κs * (lemma41Nat (c.nreg 219202) + 1) ≤ W) :
    ∃ c' k, Exec P W (rgS sp sM) c c' k ∧
      k ≤ rgK κP (κ 130) κs * (lemma41Nat (c.nreg 219202) + 1) ∧
      ((∀ q, bandOf q = bDownDrv → (q < 218000 ∨ 220000 ≤ q) → c'.nreg q = c.nreg q) ∧
      c.nreg ALLOC ≤ c'.nreg 219210 ∧ c.nreg ALLOC ≤ c'.nreg 219211 ∧
      c.nreg 219204 ≤ c'.nreg 219212 ∧ c'.nreg 219212 ≤ c.nreg 219204 + 128 ∧
      ModelDescWF P (c'.nreg ALLOC) c'.nmem (c'.nreg 219210) ∧
      ∀ (H : Host) (C : Chain), HostAt c.nmem (c.nreg 219200) H → C.P = H.poly (Qof P) →
        C.s = 0 → C.m + 1 = C.P.n →
        Robust (c'.nreg ALLOC) c'.nmem
          (fun m => m (c'.nreg 219210) = 0 ∧
            ChainDescAt m (c'.nreg 219210 + 1) (Qof P) H C ∧
            m (c'.nreg 219210 + 1) = c.nreg 219200) ∧
        ∃ N, NFWithin c'.nmem (c'.nreg 219211) (c'.nreg ALLOC) N ∧
          IsCanonicalNF (chainModel C) (Qof P) N (c'.nreg 219212) regCap) ∧
      Frame drvBands c c' k := by
  obtain ⟨hG, hWn, hX0, hμ7, hμg0, hC, hg0, h128, hg1, hcap0, H, hHA0, hHB0, hHl, hwf, hreg,
    hsimp, hNP, hNP3, hruns⟩ := hPre
  have hAL : ALLOC = 9999 := rfl
  have hqn : (Qof P).n = P.n := shear_n _ _
  have hn3 := hG.1.1
  have hhw : hostWords P.n = 256 * P.n + 16 := rfl
  set μ := c.nreg 219202 with hμ
  set L := lemma41Nat μ with hLdef
  set pc := pcB κP (κ 130) κs L with hpc
  have hrgK : 121 * pc + 5000 ≤ rgK κP (κ 130) κs * (L + 1) := by
    unfold rgK; rw [hpc]; unfold pcB
    have h1 : mcK (κ 130) κs * L ≤ mcK (κ 130) κs * (L + 1) := Nat.mul_le_mul_left _ (by omega)
    nlinarith
  have hHA0' := hHA0.holds
  have hwfP : HostWF P.n H := hqn ▸ hwf
  have hK60 : (hostLeaves P.n (2 ^ μ) 0 H).length ≤ 60 := by
    have := hostLeaves_length_le (n := P.n) (C := 2 ^ μ) Nat.one_le_two_pow H 0
      (fun a ℓ hm => by have := hruns a ℓ hm; rw [hC] at this; exact this)
    omega
  have hptsW : (Host.pts P.n H).length + 2 * P.n + 1 ≤ W := by
    have := Host.pts_length_le hwfP
    have : H.length * P.n ≤ 20 * P.n := Nat.mul_le_mul_right _ hHl
    omega
  -- the planner's arguments
  obtain ⟨c₁, k₁, e₁, hk₁, a00, a02, m₁, f₁, rr₁⟩ := rgInit0_exec (P := P) c hw
  have hw₁ := e₁.wb_right
  have hA₁ : c₁.nreg ALLOC = c.nreg ALLOC := f₁.1 ALLOC (by decide)
  have g₁ : ∀ q, q ≠ 219000 → q ≠ 219002 → c₁.nreg q = c.nreg q := fun q h1 h2 => f₁.1 q (by
    simp only [decide_eq_false_iff_not]; omega)
  -- the leaf table
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, t03, t04, tA, tT, tlow, tK, tB, rr₂, rm₂, ro₂⟩ :=
    plS_exec (C := 2 ^ μ) Nat.one_le_two_pow hn3 c₁ hw₁ (H := H) a00 (by rw [a02, hC])
      (by rw [m₁]; exact hHA0') hwfP (by rw [hA₁]; omega)
      (by rw [hA₁]; have := hrgK; omega) hptsW
  set K := (hostLeaves P.n (2 ^ μ) 0 H).length with hK
  have t9 : c₂.nreg 9999 = c.nreg ALLOC + 3 * K := by have := tA; rw [hA₁] at this; exact this
  have g₂ : ∀ q, (q < 219001 ∨ 219029 < q) → q ≠ 9999 → c₂.nreg q = c₁.nreg q := fun q h1 h2 =>
    tB q (by simp only [Bpl, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega)
  -- the padding
  obtain ⟨c₃, e₃, g₃, rr₃, m₃, rm₃, ro₃⟩ := rgPad_exec (P := P) c₂ hw₂ (by rw [t03, t9]; omega)
    (by omega)
  have hw₃ := e₃.wb_right
  have t9₃ : c₃.nreg 9999 = c.nreg ALLOC + 3 * K := by rw [g₃ _ (by decide) (by decide), t9]
  have hk₃ : 3 * (c₂.nreg 9999 - c₂.nreg 219003) + 4 = 9 * K + 4 := by rw [t03, t9]; omega
  have g₀₃ : ∀ q, (q < 219000 ∨ (219029 < q ∧ q ≠ 219250 ∧ q ≠ 219251)) → q ≠ 9999 →
      c₃.nreg q = c.nreg q := fun q h1 h2 => by
    rw [g₃ q (by omega) (by omega), g₂ q (by omega) h2, g₁ q (by omega) (by omega)]
  have hm₃ : ∀ a, a < c.nreg ALLOC → c₃.nmem a = c.nmem a := fun a ha => by
    rw [m₃, tlow a (by rw [hA₁]; exact ha), m₁]
  -- the constants and the loop state
  obtain ⟨c₄, k₄, e₄, hk₄, mg₄, b100, b101, b103, b104, b107, b230, b231, b220, b221, b222, b223,
      b224, b9, hm₄, f₄, rr₄⟩ := rgInit1_exec (P := P) c₃ hw₃ (HB := c.nreg 219200)
    (NP := c.nreg 219201) (T := c.nreg ALLOC) (Hl := H.length)
    (g₀₃ _ (by omega) (by decide)) (g₀₃ _ (by omega) (by decide)) (by rw [g₃ _ (by decide)
      (by decide), t03, hA₁])
    (by rw [hm₃ _ (by omega)]; exact hHA0'.1) (by rw [t9₃]; have := hrgK; omega)
  have hw₄ := e₄.wb_right
  have g₄ := f₄.1
  have g₀₄ : ∀ q, (q < 219000 ∨ (219029 < q ∧ q < 219100) ∨ (219107 < q ∧ q < 219140) ∨
      (219146 < q ∧ q < 219220) ∨ (219231 < q ∧ q ≠ 219250 ∧ q ≠ 219251)) → q ≠ 9999 →
      c₄.nreg q = c.nreg q := fun q h1 h2 => by
    rw [g₄ q (by simp only [Bi1, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega),
      g₀₃ q (by omega) h2]
  have hA₄ : c₄.nreg ALLOC = c.nreg ALLOC + 3 * K + 3 := by
    show c₄.nreg 9999 = _; rw [b9, t9₃]
  have hT₄ : c₄.nreg 219003 = c.nreg ALLOC := by
    rw [g₄ _ (by decide), g₃ _ (by decide) (by decide), t03, hA₁]
  have hK₄ : c₄.nreg 219004 = K := by
    rw [g₄ _ (by decide), g₃ _ (by decide) (by decide), t04]
  have hm₄' : ∀ a, a < c.nreg ALLOC → c₄.nmem a = c.nmem a := fun a ha => by
    rw [hm₄, hm₃ a ha]
  -- the data of the run
  let R : RData := ⟨H, c.nreg 219200, c.nreg 219201, μ, c.nreg 219204, c.nreg 219205, c₄.nmem,
    c₄.nreg ALLOC, c.nreg ALLOC⟩
  have hleaves : R.leaves P = hostLeaves P.n (2 ^ μ) 0 H := by
    show hostLeaves (Qof P).n (2 ^ μ) 0 H = _; rw [hqn]
  have hglt : c.nreg 219205 < c.nreg ALLOC := gradeRaw_handle_lt (O := O) hX0
  have hF : RFacts O P W R := by
    refine ⟨hG, hWn, (hHA0.transport hm₄').mono (by show c.nreg ALLOC ≤ c₄.nreg ALLOC; omega),
      by show c.nreg 219200 + 3 * H.length + 4 ≤ c₄.nreg ALLOC; omega, hHl, hwf, hreg, hsimp, hNP,
      hNP3,
      fun a ℓ hm => by have := hruns a ℓ hm; rw [hC] at this; exact this, hμ7,
      by show μ ≤ c₄.nmem (c.nreg 219205); rw [hm₄' _ hglt]; exact hμg0, hg0, h128, hg1,
      by show _ ≤ (gradeCtx O).cap P c₄.nmem (c.nreg 219205)
         rw [gradeCtx_capLocal O P c.nmem c₄.nmem _ _ hm₄' hX0]; exact hcap0,
      ((gradeCtx O).local_ P _ _ _ _ (fun a ha => (hm₄' a ha).symm) hX0 |> (gradeCtx O).mono P _ _ _
        _ (by show c.nreg ALLOC ≤ c₄.nreg ALLOC; omega)), ?_, ?_, ?_⟩
    · show ChordListAt c₄.nmem (c.nreg ALLOC) (R.leaves P)
      rw [hleaves, hm₄, m₃, ← hA₁]; exact tT
    · show c.nreg ALLOC + 3 * (R.leaves P).length ≤ c₄.nreg ALLOC
      rw [hleaves, hA₄]; omega
    · have := gradeCtx_cap_le (by omega) hX0
      show c.nreg 219204 + 129 ≤ W; omega
  have hRl : (R.leaves P).length = K := by rw [hleaves]
  have E₄ : REnv R c₄ := ⟨g₀₄ _ (by omega) (by decide), g₀₄ _ (by omega) (by decide),
    g₀₄ _ (by omega) (by decide), g₀₄ _ (by omega) (by decide), g₀₄ _ (by omega) (by decide),
    b230, b231, b223, hT₄, mg₄, b100, b101, b103, by rw [b104, g₀₃ _ (by omega) (by decide)],
    b107, fun a _ => rfl, le_refl _⟩
  have hgap : GapsLe 64 ((R.leaves P).drop 0) 0 (R.NP - 1) := by
    rw [List.drop_zero]
    have := hostLeaves_gaps (n := (Qof P).n) (C := 2 ^ μ) Nat.one_le_two_pow (by omega) hwf hHl
      (degCount_le_one hsimp) (by omega)
    show GapsLe 64 (hostLeaves (Qof P).n (2 ^ μ) 0 H) 0 (c.nreg 219201 - 1)
    rw [hNP]; exact this
  have hKL : K * lfB pc ≤ 60 * lfB pc := Nat.mul_le_mul_right _ hK60
  have I₄ : LInv P W R c.nreg (lfB (pcB κP (κ 130) κs (lemma41Nat R.μ)))
      (pcB κP (κ 130) κs (lemma41Nat R.μ) + 2) 0 c₄ := by
    refine ⟨hw₄, fun q hq hq' => g₀₄ q (by simp only [bandOf, bDownDrv] at hq; omega)
      (by simp only [bandOf, bDownDrv] at hq; omega), b220, by rw [hK₄, hRl], E₄,
      by rw [b224]; rfl, Nat.zero_le _, ?_, 0, R.γ₀, b221, hgap, Or.inl ⟨rfl, rfl, b222⟩⟩
    show c₄.nreg ALLOC + ((R.leaves P).length - 0) * lfB pc + (pc + 2) ≤ W
    rw [hRl, hA₄, Nat.sub_zero]
    rw [lfB_def] at hKL ⊢
    have := hrgK
    omega
  -- the leaf loop and the last connector
  obtain ⟨c₅, k₅, e₅, I₅, hk₅, fr₅⟩ := lfLoop_exec hsp hM hF c₄ I₄
  obtain ⟨c₆, k₆, γf, e₆, hk₆, hw₆, E₆, A₆, hγf, hγf', o₆, fr₆⟩ := finCon_exec hsp hM hF c₅ I₅
  -- the outputs
  obtain ⟨c₇, k₇, e₇, hk₇, z10, z11, z12, m₇, f₇⟩ : ∃ c₇ k₇, Exec P W rgOut c₆ c₇ k₇ ∧ k₇ = 3 ∧
      c₇.nreg 219210 = c₆.nreg 219110 ∧ c₇.nreg 219211 = c₆.nreg 219111 ∧
      c₇.nreg 219212 = c₆.nreg 219113 ∧ c₇.nmem = c₆.nmem ∧
      FrameM (fun q => decide (219210 ≤ q ∧ q ≤ 219212)) c₆ c₇ := by
    obtain ⟨c₇, k₇, e₇, hk₇, z10, z11, z12, m₇⟩ : ∃ c₇ k₇, Exec P W rgOut c₆ c₇ k₇ ∧ k₇ = 3 ∧
        c₇.nreg 219210 = c₆.nreg 219110 ∧ c₇.nreg 219211 = c₆.nreg 219111 ∧
        c₇.nreg 219212 = c₆.nreg 219113 ∧ c₇.nmem = c₆.nmem := by
      have hw := hw₆
      unfold rgOut
      exec_block
      refine ⟨rfl, ?_, ?_, ?_, rfl⟩ <;> config_simp
    exact ⟨c₇, k₇, e₇, hk₇, z10, z11, z12, m₇, exec_frameM e₇ (by decide)⟩
  -- the frames
  have Fr₁ : Frame drvBands c c₁ k₁ := frame_band (fun q hq => by
    simp only [decide_eq_true_eq] at hq; simp only [bandOf, bDownDrv]; omega) f₁ m₁ k₁
  have Fr₂₃ : Frame drvBands c₁ c₃ (k₂ + (3 * (c₂.nreg 9999 - c₂.nreg 219003) + 4)) := by
    refine ⟨fun r hr hrA => ?_, fun r hr => by rw [rr₃, rr₂], fun a ha => ?_,
      fun a ha => by rw [rm₃, rm₂], by rw [ro₃, ro₂], ?_, ?_⟩
    · have hb : bandOf r ≠ bDownDrv := fun h => hr (h ▸ bDownDrv_mem_drvBands)
      simp only [bandOf, bDownDrv] at hb
      rw [g₃ r (by omega) (by omega), g₂ r (by omega) hrA]
    · rw [m₃, tlow a ha]
    · have hA1' : c₁.nreg 9999 = c.nreg 9999 := hA₁
      have t9' : c₃.nreg 9999 = c.nreg 9999 + 3 * K := t9₃
      show c₁.nreg 9999 ≤ c₃.nreg 9999; omega
    · have hA1' : c₁.nreg 9999 = c.nreg 9999 := hA₁
      have t9' : c₃.nreg 9999 = c.nreg 9999 + 3 * K := t9₃
      show c₃.nreg 9999 ≤ c₁.nreg 9999 + _; rw [hk₃]; omega
  have Fr₄ : Frame drvBands c₃ c₄ k₄ := by
    refine ⟨fun r hr hrA => g₄ r ?_, fun r hr => by rw [rr₄], fun a ha => by rw [hm₄],
      fun a ha => by rw [f₄.2.2.1], f₄.2.2.2, ?_, ?_⟩
    · have hb : bandOf r ≠ bDownDrv := fun h => hr (h ▸ bDownDrv_mem_drvBands)
      simp only [bandOf, bDownDrv] at hb
      simp only [Bi1, Bool.or_eq_false_iff, decide_eq_false_iff_not]
      refine ⟨⟨⟨by omega, by omega⟩, by omega⟩, ?_⟩
      intro h; exact hrA h
    · show c₃.nreg 9999 ≤ c₄.nreg 9999; rw [b9]; omega
    · show c₄.nreg 9999 ≤ c₃.nreg 9999 + k₄; rw [b9, hk₄]; omega
  have Fr₇ : Frame drvBands c₆ c₇ k₇ := frame_band (fun q hq => by
    simp only [decide_eq_true_eq] at hq; simp only [bandOf, bDownDrv]; omega) f₇ m₇ k₇
  have Fr := ((((Fr₁.trans Fr₂₃).trans Fr₄).trans fr₅).trans fr₆).trans Fr₇
  simp only [Finset.union_self] at Fr
  -- the cost
  have hk₅' : (lfB (pcB κP (κ 130) κs (lemma41Nat R.μ)) + 2) * (R.leaves P).length ≤
      (lfB pc + 2) * 60 := by rw [hRl]; exact Nat.mul_le_mul_left _ hK60
  have hcost : k₁ + (k₂ + ((3 * (c₂.nreg 9999 - c₂.nreg 219003) + 4) + (k₄ + (k₅ + (k₆ + k₇))))) ≤
      rgK κP (κ 130) κs * (L + 1) := by
    rw [hk₃]
    have e1 : pcB κP (κ 130) κs (lemma41Nat R.μ) = pc := rfl
    have e2 : lfB (pcB κP (κ 130) κs (lemma41Nat R.μ)) = 2 * pc + 30 := rfl
    rw [e2] at hk₅' hk₅
    rw [e1] at hk₆
    have := hrgK
    have := hHl
    omega
  have hA₇ : c₇.nreg ALLOC = c₆.nreg ALLOC := f₇.1 ALLOC (by decide)
  have hNPn : (H.poly (Qof P)).n = c.nreg 219201 := by rw [DownMath.host_poly_n, hNP]
  refine ⟨c₇, _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ e₇))))), hcost,
    ⟨fun q hq hq' => ?_, ?_, ?_, ?_, ?_, ?_, fun H' C hH' hP hs hm => ?_⟩,
    Fr.mono (le_refl _) (by omega)⟩
  · rw [f₇.1 q (by simp only [bandOf, bDownDrv] at hq; simp only [decide_eq_false_iff_not]; omega),
      o₆ q hq hq']
    exact I₅.keep q hq hq'
  · rw [z10]; have := A₆.lo1; show c.nreg ALLOC ≤ _
    have : R.A₁ = c₄.nreg ALLOC := rfl
    omega
  · rw [z11]; have := A₆.lo2; show c.nreg ALLOC ≤ _
    have : R.A₁ = c₄.nreg ALLOC := rfl
    omega
  · rw [z12, A₆.r13]; exact hγf
  · rw [z12, A₆.r13]; have : (R.leaves P).length ≤ 60 := by rw [hRl]; exact hK60
    show γf ≤ R.γ₀ + 128; omega
  · -- the model descriptor
    have hC1 : 1 ≤ c.nreg 219201 - 1 := by omega
    let C : Chain := ⟨H.poly (Qof P), 0, c.nreg 219201 - 1, hC1, by rw [hNPn]; omega⟩
    obtain ⟨hdR, N, hN, hc⟩ := A₆.desc C rfl rfl rfl
    obtain ⟨d0, d1, d2⟩ := hdR.holds
    have hHA6 : HostAt c₆.nmem (c.nreg 219200) H := (E₆.hostAt hF).holds
    refine ⟨by rw [z10, hA₇]; exact A₆.dA, fun _ => ?_⟩
    rw [z10, hA₇, m₇]
    exact DrvR.chainWF_host hHA6 (by omega) hwfP
      (by have := E₆.alloc; have : R.A₁ = c₄.nreg ALLOC := rfl; omega) d2 d1
      (by have := A₆.dA; omega) (by show 0 < (H.poly (Qof P)).n; rw [hNPn]; omega)
  · -- the chain and its normal form
    have hHH : H' = H := NFLoc.hostAt_unique hH' hHA0'
    subst hHH
    have hmC : C.m = c.nreg 219201 - 1 := by rw [hP, hNPn] at hm; omega
    obtain ⟨hdR, N, hN, hc⟩ := A₆.desc C hP hs hmC
    rw [z10, z11, z12, hA₇, m₇, A₆.r13]
    exact ⟨Robust.imp hdR fun _ h => ⟨h.1, h.2.2, h.2.1⟩, N, hN, hc⟩

end exec

/-- **D5: the region procedure.** -/
theorem regionSpec {O : OracleIface} (hM : MergeSpec) (hSC : ShootCutSpec O) (hPc : PieceSpec O) :
    RegionSpec O := by
  obtain ⟨sp, κP, hsp⟩ := (pieceSpec_iff O).1 hPc
  obtain ⟨sh, cu, κs, hsh, hcu⟩ := hSC
  obtain ⟨mk, κ, hmk⟩ := L41.mergeMeets_of hM
  have hMM : L41.MergeMeets (mk sh cu) κ (L41.scF κs) (L41.scG κs) cutGran (gradeCtx O)
      OkModel :=
    hmk sh cu oracleBands oracleBands (L41.scF κs) (L41.scG κs) cutGran (gradeCtx O) OkModel
      (gradeCtx_capLocal O) (ShootCut.gradeCtx_halves O) (fun _ _ h => h) (L41.scF_mono κs)
      (L41.scG_mono κs) L41.cutGran_mono (subset_refl _) (subset_refl _) hsh hcu
  refine ⟨rgS sp (mk sh cu), rgK κP (κ 130) κs, ?_⟩
  intro P W c hw hPre hroom
  exact rgS_run hsp hMM c hw hPre hroom

end

end DrvG

end Chazelle.Core
