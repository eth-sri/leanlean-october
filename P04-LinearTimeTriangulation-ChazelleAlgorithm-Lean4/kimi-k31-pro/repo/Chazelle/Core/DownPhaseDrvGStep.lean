module

public import Chazelle.Core.DownPhaseDrvGEnv
public import Chazelle.Core.GranSize
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.SimpTactics
public import Chazelle.ChainTactics
set_option maxHeartbeats 4000000

/-!
# Down-phase driver, region procedure (D5), part 6: one piece

`pcS_exec`: the piece `⟨H.poly Q, s, m⟩` (arguments in `219240 … 219243`) is computed by the
piece procedure (`pcCall_exec`) and becomes the accumulated chain (`s = 0`, the first piece) or is
merged into the accumulated chain `⟨H.poly Q, 0, s⟩` (`DrvR.mgStep_exec`): the junction `s` is a
run-interior host point (`DownMath.sharedGeneric_run`), the degree cap `130` bounds the full map
of the union (`fullDegLe_host`, at most `20` items), and the merge costs at most
`mcK κM κ · lemma41Nat μ` (`mcost_le`, Lemma 2.3 for the chord counts).
-/

namespace Chazelle.Core

namespace DrvG

open Machine Machine.Stmt Programs BuildRam DrvR

@[expose] public section

theorem exec_seq_inv {P : Polygon} {W : ℕ} {s t : Stmt} {c c' : Config} {k : ℕ}
    (h : Exec P W (.seq s t) c c' k) :
    ∃ c₁ k₁ k₂, Exec P W s c c₁ k₁ ∧ Exec P W t c₁ c' k₂ ∧ k = k₁ + k₂ := by
  cases h with
  | seq e₁ e₂ => exact ⟨_, _, _, e₁, e₂, rfl⟩

/-- The number of points of a host whose runs have at most `2 C` edges. -/
theorem pts_length_le_runs (n C : ℕ) : ∀ H : Host, (∀ a ℓ, HostItem.run a ℓ ∈ H → ℓ ≤ 2 * C) →
    (H.pts n).length ≤ H.length * (2 * C + 1)
  | [], _ => by simp [Host.pts]
  | .pt x :: H, h => by
    rw [DownMath.pts_cons, List.length_append, List.length_cons, Nat.succ_mul]
    have := pts_length_le_runs n C H fun a ℓ hm => h a ℓ (List.mem_cons_of_mem _ hm)
    sio only [HostItem.pts, List.length_singleton]
  | .run a ℓ :: H, h => by
    rw [DownMath.pts_cons, List.length_append, List.length_cons, Nat.succ_mul,
      DownMath.run_pts_length]
    have := pts_length_le_runs n C H fun a ℓ hm => h a ℓ (List.mem_cons_of_mem _ hm)
    have := h a ℓ (List.mem_cons_self ..)
    omega

/-- The chord count of a `γ`-canonical normal form (cap `130`) of a chain (Lemma 2.3). -/
theorem chords_le {C : Chain} (hP : C.P.Simple) {Q : Polygon} {N : NF} {γ : ℕ}
    (hc : IsCanonicalNF (chainModel C) Q N γ 130) :
    N.chords.length * (γ + 1) ≤ 18480 * (2 * C.m + 1) := by
  have h := DownMath.lemma23_chain hP hc.1.1 hc.2.1 hc.2.2.1
  rw [Gran.ncard_F hc.1] at h
  unfold NF.nChords at h
  exact h

/-- The cost bound of one piece. -/
def pcB (κP κM κs L : ℕ) : ℕ := 9 + κP * (L + 1) + 1570 + mcK κM κs * L

section exec

variable {O : OracleIface} {P : Polygon} {W : ℕ} {R : RData}

/-- **One piece**: computed, then merged into the accumulated chain (or becoming it). -/
theorem pcS_exec {sp sM : Stmt} {κP κs : ℕ} {κ : ℕ → ℕ}
    (hsp : PcMeets O sp κP)
    (hM : L41.MergeMeets sM κ (L41.scF κs) (L41.scG κs) cutGran (gradeCtx O) OkModel)
    (hF : RFacts O P W R) (d : Config) (hw : WordsBounded W d) (hE : REnv R d)
    {s m kind a γ : ℕ}
    (h40 : d.nreg 219240 = s) (h41 : d.nreg 219241 = m) (h42 : d.nreg 219242 = kind)
    (h43 : d.nreg 219243 = a)
    (hacc : (d.nreg 219222 = 0 ∧ s = 0 ∧ γ = R.γ₀) ∨ (0 < s ∧ AccOK P R d s γ))
    (hγ : R.γ₀ ≤ γ) (hγ' : γ ≤ R.γ₀ + 127)
    (hm1 : 1 ≤ m) (hsm : s + m + 1 ≤ R.NP) (hk : kind ≤ 1)
    (hleaf : kind = 1 → m ≤ 2 ^ R.μ ∧ a + m + 1 ≤ (Qof P).n ∧
      ∀ k, k ≤ m → (R.H.pts (Qof P).n).getD (s + k) (.vtx 0) = .vtx (a + k))
    (hcon : kind = 0 → m ≤ 64)
    (hjun : 0 < s → ∃ H₁ a' ℓ H₂ k, R.H = H₁ ++ HostItem.run a' ℓ :: H₂ ∧ 1 ≤ k ∧ k < ℓ ∧
      s = (H₁.pts (Qof P).n).length + k)
    (hroom : d.nreg ALLOC + pcB κP (κ 130) κs (lemma41Nat R.μ) ≤ W) :
    ∃ d' k, Exec P W (pcS sp sM) d d' k ∧ k ≤ pcB κP (κ 130) κs (lemma41Nat R.μ) ∧
      REnv R d' ∧ AccOK P R d' (s + m) (if s = 0 then R.γ₀ else γ + 1) ∧
      (∀ q, bandOf q = bDownDrv →
        (q < 218000 ∨ (219000 ≤ q ∧ q < 219110) ∨ (219139 < q ∧ q ≠ 219222)) →
        d'.nreg q = d.nreg q) ∧
      Frame drvBands d d' k := by
  have hQn : (Qof P).n = P.n := shear_n _ _
  have hn3  := hF.hG.1.1
  have hNPn : (R.H.poly (Qof P)).n = R.NP := by rw [DownMath.host_poly_n, hF.hNP]
  have hW1 : 1579 ≤ W := by ufo pcB at hroom
  -- the piece
  obtain ⟨d₁, k₁, e₁, hk₁, q1, q2, q3, q4, q5, fr₁⟩ := pcCall_exec (P := P) hsp hF.hG hF.hWn d hw
    (H := R.H) hE.r200 h40 h41 h42 h43 hE.r202 hE.r204 hE.r205 (hE.holds hF) (hE.hostAt hF)
    (by have := hF.hHB; have := hE.alloc; omega) (by have := hF.hHl; omega) hF.hwf hF.hreg
    hF.hsimp (by rwx [← hF.hNP]) hm1 hk
    (fun h1 => by
      obtain ⟨b1, b2, b3⟩ := hleaf h1
      exact ⟨b1, by rw [hE.grades hF]; exact hF.hμg, b2, hF.hg0, b3⟩)
    (fun h0 => ⟨hcon h0, by have := hcon h0; have := hF.h128; omega⟩)
    (by ufo pcB at hroom)
  obtain ⟨d₀, k₀, k₀', e₀, e₀', hk₀⟩ := exec_seq_inv e₁
  have keep1 : ∀ q ∈ envRegs, d₁.nreg q = d.nreg q := by
    intro q hq
    obtain ⟨b1, b2, -, -⟩ := envRegs_band q hq
    exact q1 q b1 (by omega)
  have E₁ : REnv R d₁ := hE.keep keep1
    (fun a ha => fr₁.2.2.1 a (by have := hE.alloc; omega)) fr₁.2.2.2.2.2.1
  have hw₁ := e₁.wb_right
  have r22 : d₁.nreg 219222 = d.nreg 219222 := q1 _ (by simp [bandOf, bDownDrv]) (by omega)
  have r41 : d₁.nreg 219241 = m := by rw [q1 _ (by simp [bandOf, bDownDrv]) (by omega), h41]
  rcases hacc with ⟨f0, hs0, hγ0⟩ | ⟨hs, A⟩
  · -- the first piece
    subst hs0 hγ0
    obtain ⟨d₂, k₂, e₂, hk₂, v10, v11, v12, v13, v22, m₂, g₂⟩ : ∃ d₂ k₂, Exec P W pcFirst d₁ d₂ k₂ ∧
        k₂ = 5 ∧ d₂.nreg 219110 = d₁.nreg 218010 ∧ d₂.nreg 219111 = d₁.nreg 218011 ∧
        d₂.nreg 219112 = m ∧ d₂.nreg 219113 = R.γ₀ ∧ d₂.nreg 219222 = 1 ∧ d₂.nmem = d₁.nmem ∧
        FrameM (fun q => decide (219110 ≤ q ∧ q ≤ 219113) || decide (q = 219222)) d₁ d₂ := by
      obtain ⟨d₂, k₂, e₂, hk₂, v10, v11, v12, v13, v22, m₂⟩ : ∃ d₂ k₂,
          Exec P W pcFirst d₁ d₂ k₂ ∧ k₂ = 5 ∧ d₂.nreg 219110 = d₁.nreg 218010 ∧
          d₂.nreg 219111 = d₁.nreg 218011 ∧ d₂.nreg 219112 = m ∧ d₂.nreg 219113 = R.γ₀ ∧
          d₂.nreg 219222 = 1 ∧ d₂.nmem = d₁.nmem := by
        unfold pcFirst
        exec_block
        · omega
        refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, rfl⟩ <;> config_simp
        · exact r41
        · exact E₁.r204
      exact ⟨d₂, k₂, e₂, hk₂, v10, v11, v12, v13, v22, m₂, exec_frameM e₂ (by decide)⟩
    have fr₂ : Frame drvBands d₁ d₂ k₂ := frame_band (fun q hq => by
      simp [Bool.or_eq_true, decide_eq_true_eq] at hq; sio only [bandOf, bDownDrv])
      g₂ m₂ k₂
    have hA₂ : d₂.nreg ALLOC = d₁.nreg ALLOC := fr₂.2.2.2.2.2.1.antisymm' (by
      have := fr₂.2.2.2.2.2.2; have := g₂.1 ALLOC (by decide); omega)
    refine ⟨d₂, k₀ + (k₀' + (k₂ + 1)), .seq e₀ (.seq e₀' (.ifLtN_true (by
      rwo [r22, f0, E₁.r230]) e₂)), by ufo pcB, E₁.keep (fun q hq => g₂.1 q (by
      obtain ⟨-, -, b3, b4⟩ := envRegs_band q hq
      sio only [Bool.or_eq_false_iff, decide_eq_false_iff_not]))
      (fun a ha => by rw [m₂]) (by omega), ?_, fun q hq hq' => ?_, ?_⟩
    · simp [↓reduceIte, Nat.zero_add]
      refine ⟨v22, v12, v13, by rw [v10, hA₂]; exact q4.1, by rw [v10]; have := hE.alloc; omega,
        by rw [v11]; have := hE.alloc; omega, fun C hP hs hm => ?_⟩
      obtain ⟨r1, N, r2, r3⟩ := q5 C hP hs hm
      rw [v10, v11, hA₂, m₂]
      exact ⟨Robust.imp r1 fun _ h => ⟨h.1, h.2.2, h.2.1⟩, N, r2, r3⟩
    · rw [g₂.1 q (by sio only [Bool.or_eq_false_iff, decide_eq_false_iff_not])]
      exact q1 q hq (by omega)
    · have := fr₁.trans fr₂
      rw [Finset.union_self] at this
      exact this.mono (le_refl _) (by omega)
  · -- a later piece: the merge
    have r22' : d₁.nreg 219222 = 1 := by rw [r22, A.r22]
    obtain ⟨d₂, k₂, e₂, hk₂, v14, v15, v16, m₂, g₂⟩ : ∃ d₂ k₂, Exec P W
        (block [.copyN 219114 218010, .copyN 219115 218011, .copyN 219116 219241]) d₁ d₂ k₂ ∧
        k₂ = 3 ∧ d₂.nreg 219114 = d₁.nreg 218010 ∧ d₂.nreg 219115 = d₁.nreg 218011 ∧
        d₂.nreg 219116 = m ∧ d₂.nmem = d₁.nmem ∧
        FrameM (fun q => decide (219114 ≤ q ∧ q ≤ 219116)) d₁ d₂ := by
      obtain ⟨d₂, k₂, e₂, hk₂, v14, v15, v16, m₂⟩ : ∃ d₂ k₂, Exec P W
          (block [.copyN 219114 218010, .copyN 219115 218011, .copyN 219116 219241]) d₁ d₂ k₂ ∧
          k₂ = 3 ∧ d₂.nreg 219114 = d₁.nreg 218010 ∧ d₂.nreg 219115 = d₁.nreg 218011 ∧
          d₂.nreg 219116 = m ∧ d₂.nmem = d₁.nmem := by
        exec_block
        refine ⟨rfl, ?_, ?_, ?_, rfl⟩ <;> config_simp
        exact r41
      exact ⟨d₂, k₂, e₂, hk₂, v14, v15, v16, m₂, exec_frameM e₂ (by decide)⟩
    have fr₂ : Frame drvBands d₁ d₂ k₂ := frame_band (fun q hq => by
      simp [decide_eq_true_eq] at hq; sio only [bandOf, bDownDrv]) g₂ m₂ k₂
    have hA₂ : d₂.nreg ALLOC = d₁.nreg ALLOC := g₂.1 ALLOC (by decide)
    have E₂ : REnv R d₂ := E₁.keep (fun q hq => g₂.1 q (by
      obtain ⟨-, -, b3, -⟩ := envRegs_band q hq
      sio only [decide_eq_false_iff_not])) (fun a ha => by rw [m₂]) (by omega)
    have A₂ : AccOK P R d₂ s γ := (A.keep fr₁ fun q hq => q1 q (by
      rcases hq with h | h | h | h | h <;> subst h <;> simp [bandOf, bDownDrv])
      (by omega)).keep fr₂ fun q hq => g₂.1 q (by
        sio only [decide_eq_false_iff_not])
    -- the two chains
    let C1 : Chain := ⟨R.H.poly (Qof P), 0, s, hs, by rwo [hNPn]⟩
    let C2 : Chain := ⟨R.H.poly (Qof P), s, m, hm1, by rwo [hNPn]⟩
    have hlen : C1.m + C2.m + 1 ≤ C1.P.n := by
      show s + m + 1 ≤ (R.H.poly (Qof P)).n; rwx [hNPn]
    obtain ⟨hd1R, N1, hN1, hc1⟩ := A₂.desc C1 rfl rfl rfl
    obtain ⟨hd2R, N2, hN2, hc2⟩ := q5 C2 rfl rfl rfl
    -- the junction and the degree
    have hDH : DistinctHeights (Qof P) := (goodShear_epsOf hF.hG.2).2.1
    have hgen : SharedGeneric (L41.jOf C1 C2 hlen) := by
      obtain ⟨H₁, a', ℓ, H₂, k, eH, hk1, hkl, hsk⟩ := hjun hs
      refine DownMath.sharedGeneric_run (by rwo [hQn]) hDH (H₁ := H₁) (H₂ := H₂) (a := a')
        (ℓ := ℓ) (k := k) ?_ hk1 hkl ?_
      · show R.H.poly (Qof P) = _; rw [eH]
      · show (0 + s) % (R.H.poly (Qof P)).n = _
        rwo [hNPn, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
    have hfd : (chainModel (L41.jOf C1 C2 hlen).whole).FullDegLe (Qof P) 130 := by
      have h1 := fullDegLe_host (C := (L41.jOf C1 C2 hlen).whole) (t := R.H.length) hF.hsimp
        (fun y => host_ncard_le (Qof P) hDH R.H y) (Qof P)
      exact fullDegLe_mono h1 (by have := hF.hHl; omega)
    -- the cost of the merge
    have hx := chords_le hF.hsimp hc1
    have hy := chords_le hF.hsimp hc2
    have hMb : s + m ≤ 20 * (2 * 2 ^ R.μ + 1) := by
      have h1 := pts_length_le_runs (Qof P).n (2 ^ R.μ) R.H hF.hruns
      have h2 : R.H.length * (2 * 2 ^ R.μ + 1) ≤ 20 * (2 * 2 ^ R.μ + 1) :=
        Nat.mul_le_mul_right _ hF.hHl
      have := hF.hNP
      omega
    have hmc := mcost_le (κ 130) κs (x := N1.chords.length) (y := N2.chords.length) hF.hμ7 hF.hg0
      hF.hg1 (show γ ≤ R.γ₀ + 128 by omega) hMb
      (by
        have h1 : N1.chords.length * (R.γ₀ + 1) ≤ N1.chords.length * (γ + 1) :=
          Nat.mul_le_mul_left _ (by omega)
        have h2 : 18480 * (2 * s + 1) ≤ 18480 * (2 * (s + m) + 1) := by omega
        exact h1.trans (hx.trans h2))
      (by
        have h2 : 18480 * (2 * m + 1) ≤ 18480 * (2 * (s + m) + 1) := by omega
        exact hy.trans h2)
    have hmc' : mgCostV κ (L41.scF κs) (L41.scG κs) cutGran 130 N1.chords.length
        N2.chords.length γ (s + m) ≤ mcK (κ 130) κs * lemma41Nat R.μ := hmc
    have hγW : R.γ₀ ≤ W := by have := hw.1 219204; rw [hE.r204] at this; exact this
    -- the merge step
    obtain ⟨d₃, k₃, e₃, hk₃, w10, w11, w12, w13, wA, wR, -, ⟨N, wN, wc⟩, wq, fr₃⟩ :=
      mgStep_exec (P := P) (W := W) hM (gradeCtx_capLocal O) hF.hG hF.hWn d₂ e₂.wb_right E₂.mg
        (H := R.H) (D := 130) (g := R.g) (γ := γ) (ma := s) (mp := m) (C1 := C1) (C2 := C2)
        (N1 := N1) (N2 := N2) (γ1 := γ) (γ2 := R.γ₀)
        E₂.r100 E₂.r101 E₂.r103 E₂.r104 E₂.r107 A₂.r12 A₂.r13 v16 (E₂.hostAt hF)
        (by have := hF.hHl; omega) (hQn ▸ hF.hwf) hF.hreg hF.hsimp
        (by have := hF.hHB; have := E₂.alloc; omega) (by rw [← hQn]; exact hF.hNP)
        (Robust.imp hd1R fun _ h => ⟨h.2.1, h.2.2⟩)
        (by rw [v14, hA₂, m₂]; exact Robust.imp hd2R fun _ h => ⟨h.2.2, h.2.1⟩)
        A₂.dA (by rw [v14, hA₂]; exact q4.1) rfl rfl rfl rfl hlen hN1
        (by rwx [v15, hA₂, m₂]) hc1 hc2 (le_refl _) hγ hgen hfd (by norm_num)
        (E₂.holds hF) (by rw [E₂.cap hF]; have := hF.hcap; ufo fuseLoss)
        (by have := hF.hγW; omega)
        (by
          have := fr₁.2.2.2.2.2.2
          ruo [hA₂] pcB at hroom)
    refine ⟨d₃, k₀ + (k₀' + ((k₂ + k₃) + 2)), .seq e₀ (.seq e₀' (.ifLtN_false (by
      rwo [r22', E₁.r230]) (.seq e₂ e₃))), by have := hF.hHl; ufo pcB,
      E₂.keep (fun q hq => wq q (envRegs_band q hq).1 (by
        obtain ⟨-, -, b3, -⟩ := envRegs_band q hq; omega)) (fun a ha => fr₃.2.2.1 a (by
          have := E₂.alloc; omega)) fr₃.2.2.2.2.2.1, ?_, fun q hq hq' => ?_, ?_⟩
    · rw [ite_eq_right (by omega)]
      refine ⟨by rw [wq _ (by simp [bandOf, bDownDrv]) (by omega), A₂.r22], w12, w13,
        by rw [w10]; exact wA, by rw [w10]; have := E₂.alloc; omega,
        by have := E₂.alloc; omega, fun C hP hs' hm' => ?_⟩
      have hC : C = (L41.jOf C1 C2 hlen).whole := L41.chain_eq hP hs' hm'
      subst hC
      rw [w10]
      exact ⟨wR, N, wN, wc⟩
    · rw [wq q hq (by omega), g₂.1 q (by sio only [decide_eq_false_iff_not])]
      exact q1 q hq (by omega)
    · have := (fr₁.trans fr₂).trans (fr₃.mono mgBands_subset (le_refl _))
      rw [Finset.union_self, Finset.union_self] at this
      exact this.mono (le_refl _) (by omega)

end exec

end

end DrvG

end Chazelle.Core
