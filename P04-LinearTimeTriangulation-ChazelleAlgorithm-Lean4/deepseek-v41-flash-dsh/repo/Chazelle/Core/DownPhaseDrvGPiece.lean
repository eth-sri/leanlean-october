module

public import Chazelle.Golf

public import Chazelle.Core.DownPhaseDrvGProg
public import Chazelle.Core.DownPhaseDrvRPieceSpec

/-!
# Down-phase driver, region procedure (D5), part 4: calling the piece procedure

* `PcMeets O sp κP`: the `Meets` judgement of `PieceSpec O` (`pieceSpec_iff`);
* `frame_band`: a block writing only registers of band `bDownDrv` (and no memory) has the frame of
  that band;
* `pcCall_exec`: the arguments `pcArgs` and the piece procedure `sp` compute the descriptor and
  the canonical normal form of the piece `⟨H.poly Q, s, m⟩` (target `γ`, cap `130`), fresh and
  robust below the new allocator, keeping the registers of band `bDownDrv` outside
  `218000 … 218999`.
-/

namespace Chazelle.Core

namespace DrvG

open Machine Machine.Stmt Programs BuildRam DrvR

@[expose] public section

/-- The judgement of `PieceSpec O`. -/
def PcMeets (O : OracleIface) (sp : Stmt) (κ : ℕ) : Prop :=
  Meets sp drvBands
    (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧
      (gradeCtx O).holds P c.nmem (c.nreg 218008) (c.nreg ALLOC) ∧
      4 ≤ c.nreg 218006 ∧ 1 ≤ c.nreg 218002 ∧ c.nreg 218003 ≤ 1 ∧
      ∃ H : Host, Robust (c.nreg ALLOC) c.nmem (fun m => HostAt m (c.nreg 218000) H) ∧
        c.nreg 218000 + 3 * H.length + 4 ≤ c.nreg ALLOC ∧
        H.length ≤ 64 ∧ HostWF (Qof P).n H ∧ HostRegular (Qof P).n H ∧
        (H.poly (Qof P)).Simple ∧
        c.nreg 218001 + c.nreg 218002 + 1 ≤ (H.pts (Qof P).n).length ∧
        (c.nreg 218003 = 1 →
          c.nreg 218002 ≤ 2 ^ c.nreg 218005 ∧ c.nreg 218005 ≤ c.nmem (c.nreg 218008) ∧
          c.nreg 218004 + c.nreg 218002 + 1 ≤ (Qof P).n ∧
          2 * gradeGran (c.nreg 218005) ≤ c.nreg 218007 ∧
          ∀ k, k ≤ c.nreg 218002 →
            (H.pts (Qof P).n).getD (c.nreg 218001 + k) (.vtx 0) = .vtx (c.nreg 218004 + k)) ∧
        (c.nreg 218003 = 0 → c.nreg 218002 ≤ 64 ∧ 2 * c.nreg 218002 ≤ c.nreg 218007))
    (fun P c c' =>
      (∀ q, bandOf q = bDownDrv → (q < 218000 ∨ 219000 ≤ q) → c'.nreg q = c.nreg q) ∧
      c.nreg ALLOC ≤ c'.nreg 218010 ∧ c.nreg ALLOC ≤ c'.nreg 218011 ∧
      ModelDescWF P (c'.nreg ALLOC) c'.nmem (c'.nreg 218010) ∧
      ∀ (H : Host) (C : Chain), HostAt c.nmem (c.nreg 218000) H → C.P = H.poly (Qof P) →
        C.s = c.nreg 218001 → C.m = c.nreg 218002 →
        Robust (c'.nreg ALLOC) c'.nmem
          (fun m => m (c'.nreg 218010) = 0 ∧
            ChainDescAt m (c'.nreg 218010 + 1) (Qof P) H C ∧
            m (c'.nreg 218010 + 1) = c.nreg 218000) ∧
        ∃ N, NFWithin c'.nmem (c'.nreg 218011) (c'.nreg ALLOC) N ∧
          IsCanonicalNF (chainModel C) (Qof P) N (c.nreg 218007) (c.nreg 218006))
    (fun _ c => κ * (lemma41Nat (c.nreg 218005) + 1))

theorem pieceSpec_iff (O : OracleIface) : PieceSpec O ↔ ∃ sp κ, PcMeets O sp κ := Iff.rfl

/-- **The frame of a register block** of band `bDownDrv`. -/
theorem frame_band {B : ℕ → Bool} (hB : ∀ q, B q = true → bandOf q = bDownDrv) {c c' : Config}
    (hf : FrameM B c c') (hm : c'.nmem = c.nmem) (k : ℕ) : Frame drvBands c c' k := by
  have hA : c'.nreg ALLOC = c.nreg ALLOC := hf.1 ALLOC (by
    cases h : B ALLOC
    · rfl
    · have := hB _ h; simp [bandOf, ALLOC, bDownDrv] at this)
  refine ⟨fun r hr _ => hf.1 r ?_, fun r hr => hf.2.1 r ?_, fun a _ => by rw [hm],
    fun a _ => by rw [hf.2.2.1], hf.2.2.2, by omega, by omega⟩ <;>
  · cases h : B r
    · rfl
    · exact absurd (hB r h ▸ bDownDrv_mem_drvBands) hr

section exec

variable {P : Polygon} {W : ℕ}

/-- The arguments of a piece. -/
theorem pcArgs_exec (d : Config) (hw : WordsBounded W d) (hW : 130 ≤ W) :
    ∃ d' k, Exec P W pcArgs d d' k ∧ k = 9 ∧ d'.nreg 218000 = d.nreg 219200 ∧
      d'.nreg 218001 = d.nreg 219240 ∧ d'.nreg 218002 = d.nreg 219241 ∧
      d'.nreg 218003 = d.nreg 219242 ∧ d'.nreg 218004 = d.nreg 219243 ∧
      d'.nreg 218005 = d.nreg 219202 ∧ d'.nreg 218006 = 130 ∧ d'.nreg 218007 = d.nreg 219204 ∧
      d'.nreg 218008 = d.nreg 219205 ∧ d'.nmem = d.nmem ∧
      FrameM (fun q => decide (218000 ≤ q ∧ q ≤ 218008)) d d' := by
  obtain ⟨d', k, ex, hk, h1, h2, h3, h4, h5, h6, h7, h8, h9, hm⟩ : ∃ d' k,
      Exec P W pcArgs d d' k ∧ k = 9 ∧ d'.nreg 218000 = d.nreg 219200 ∧
      d'.nreg 218001 = d.nreg 219240 ∧ d'.nreg 218002 = d.nreg 219241 ∧
      d'.nreg 218003 = d.nreg 219242 ∧ d'.nreg 218004 = d.nreg 219243 ∧
      d'.nreg 218005 = d.nreg 219202 ∧ d'.nreg 218006 = 130 ∧ d'.nreg 218007 = d.nreg 219204 ∧
      d'.nreg 218008 = d.nreg 219205 ∧ d'.nmem = d.nmem := by
    unfold pcArgs
    exec_block
    · exact hW
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩ <;> config_simp
  exact ⟨d', k, ex, hk, h1, h2, h3, h4, h5, h6, h7, h8, h9, hm, exec_frameM ex (⌖)⟩

/-- **One call of the piece procedure.** -/
theorem pcCall_exec {O : OracleIface} {sp : Stmt} {κP : ℕ} (hsp : PcMeets O sp κP)
    (hG : GoodEnv P) (hWn : hostWords P.n ≤ W) (d : Config) (hw : WordsBounded W d)
    {H : Host} {HB s m kind a μ γ g : ℕ}
    (h00 : d.nreg 219200 = HB) (h40 : d.nreg 219240 = s) (h41 : d.nreg 219241 = m)
    (h42 : d.nreg 219242 = kind) (h43 : d.nreg 219243 = a) (h02 : d.nreg 219202 = μ)
    (h04 : d.nreg 219204 = γ) (h05 : d.nreg 219205 = g)
    (hX : (gradeCtx O).holds P d.nmem g (d.nreg ALLOC))
    (hH : Robust (d.nreg ALLOC) d.nmem (fun mm => HostAt mm HB H))
    (hHB : HB + 3 * H.length + 4 ≤ d.nreg ALLOC) (hHl : H.length ≤ 64)
    (hwf : HostWF (Qof P).n H) (hreg : HostRegular (Qof P).n H) (hsimp : (H.poly (Qof P)).Simple)
    (hsm : s + m + 1 ≤ (H.pts (Qof P).n).length) (hm1 : 1 ≤ m) (hk : kind ≤ 1)
    (hleaf : kind = 1 → m ≤ 2 ^ μ ∧ μ ≤ d.nmem g ∧ a + m + 1 ≤ (Qof P).n ∧
      2 * gradeGran μ ≤ γ ∧
      ∀ k, k ≤ m → (H.pts (Qof P).n).getD (s + k) (.vtx 0) = .vtx (a + k))
    (hcon : kind = 0 → m ≤ 64 ∧ 2 * m ≤ γ)
    (hroom : d.nreg ALLOC + κP * (lemma41Nat μ + 1) ≤ W) :
    ∃ d' k, Exec P W (.seq pcArgs sp) d d' k ∧ k ≤ 9 + κP * (lemma41Nat μ + 1) ∧
      (∀ q, bandOf q = bDownDrv → (q < 218000 ∨ 219000 ≤ q) → d'.nreg q = d.nreg q) ∧
      d.nreg ALLOC ≤ d'.nreg 218010 ∧ d.nreg ALLOC ≤ d'.nreg 218011 ∧
      ModelDescWF P (d'.nreg ALLOC) d'.nmem (d'.nreg 218010) ∧
      (∀ C : Chain, C.P = H.poly (Qof P) → C.s = s → C.m = m →
        Robust (d'.nreg ALLOC) d'.nmem
          (fun mm => mm (d'.nreg 218010) = 0 ∧
            ChainDescAt mm (d'.nreg 218010 + 1) (Qof P) H C ∧ mm (d'.nreg 218010 + 1) = HB) ∧
        ∃ N, NFWithin d'.nmem (d'.nreg 218011) (d'.nreg ALLOC) N ∧
          IsCanonicalNF (chainModel C) (Qof P) N γ 130) ∧
      Frame drvBands d d' k := by
  have hW130 : 130 ≤ W := by have : hostWords P.n = 256 * P.n + 16 := rfl; have := hG.1.1; omega
  obtain ⟨d₁, k₁, e₁, hk₁, a0, a1, a2, a3, a4, a5, a6, a7, a8, m₁, f₁⟩ :=
    pcArgs_exec (P := P) d hw hW130
  have hA₁ : d₁.nreg ALLOC = d.nreg ALLOC := f₁.1 ALLOC (⌖)
  have fr₁ : Frame drvBands d d₁ k₁ := frame_band (fun q hq => by
    simp only [decide_eq_true_eq] at hq; simp only [bandOf, bDownDrv]; omega) f₁ m₁ k₁
  have hHA : HostAt d.nmem HB H := hH.holds
  have hpre : _ := hsp P W d₁ e₁.wb_right ⟨hG, hWn, by rw [a8, h05, m₁, hA₁]; exact hX,
    by rw [a6]; omega, by rw [a2, h41]; exact hm1, by rw [a3, h42]; exact hk, H,
    by rw [a0, h00, m₁, hA₁]; exact hH, by rw [a0, h00, hA₁]; exact hHB, hHl, hwf, hreg, hsimp,
    by rw [a1, a2, h40, h41]; exact hsm,
    fun h1 => by
      rw [a3, h42] at h1
      obtain ⟨b1, b2, b3, b4, b5⟩ := hleaf h1
      Ξ a2, a5, a8, a4, a7, a1, h41, h02, h05, h43, h04, h40, m₁
      exact ⟨b1, b2, b3, b4, b5⟩,
    fun h0 => by
      rw [a3, h42] at h0
      rw [a2, a7, h41, h04]; exact hcon h0⟩ (by beta_reduce; rw [a5, h02, hA₁]; exact hroom)
  obtain ⟨d', k₂, e₂, hk₂, ⟨q1, q2, q3, q4, q5⟩, fr₂⟩ := hpre
  beta_reduce at hk₂
  rw [a5, h02] at hk₂
  refine ⟨d', k₁ + k₂, .seq e₁ e₂, ⋄, fun q hq hq' => ?_, by rw [← hA₁]; exact q2,
    by rw [← hA₁]; exact q3, q4, fun C hP hs hm => ?_, by
      have := fr₁.trans fr₂; rwa [Finset.union_self] at this⟩
  · Ξ q1 q hq hq', f₁.1 q (by simp only [decide_eq_false_iff_not]; omega)
  · obtain ⟨r1, N, r2, r3⟩ := q5 H C (by rw [a0, h00, m₁]; exact hHA) hP (by rw [a1, h40]; exact hs)
      (by rw [a2, h41]; exact hm)
    rw [a7, a6, h04] at r3
    refine ⟨?_, N, r2, r3⟩
    rw [a0, h00] at r1; exact r1

end exec

end

end DrvG

end Chazelle.Core
