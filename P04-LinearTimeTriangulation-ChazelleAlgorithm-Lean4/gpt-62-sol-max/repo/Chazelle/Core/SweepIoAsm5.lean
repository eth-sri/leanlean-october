module

public import Chazelle.Core.SweepIoAsm4

/-!
# The sweep RAM (WP-D), the assembly (piece I), part 5: `asmGoal`

**`asmGoal : AsmGoal`**: `SweepSpecH` from stages 2/3 (`SweepEvSpec`), a side-0 initialisation
(`InitSpec`) and the query loop (`LoopSpec`), with the program `asmProg` and the constant
`asmK κE κ0 κL D = κE D + 238 κ0 D + 10 κL D + 1000`.
-/

namespace Chazelle.Core

namespace SweepIo

open Machine Machine.Stmt Programs SweepRam SweepPrim Sweep

@[expose] public section

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 40000 in
/-- **The assembly of the sweep.** -/
theorem asmGoal : AsmGoal := by
  intro hEv init0 Aux κ0 hInit hLoop
  obtain ⟨evMk, κE, hEv⟩ := hEv
  obtain ⟨loopS, κL, hL⟩ := hLoop
  refine ⟨fun sh => asmProg (evMk sh) init0 (loopS sh), asmK κE κ0 κL, ?_⟩
  intro sh Bs F X Ok hXl hBs hsh P W c hw hpre hroom
  obtain ⟨hG, hWh, hX, hcap, h7, hJWF, H, J, N₁, N₂, L, hJ, hP, hOk₁, hOk₂, hNW₁, hNW₂, hNF₁,
    hNF₂, hdeg₁, hdeg₂, hsg₁, hsg₂, hLn, hLm, hLat, hq, hend, hht⟩ := hpre
  beta_reduce at hroom
  -- abbreviations
  have hK₁ : c.nmem (rd c bSweep 3) = N₁.nChords := hNW₁.nfAt.1
  have hK₂ : c.nmem (rd c bSweep 4) = N₂.nChords := hNW₂.nfAt.1
  obtain ⟨b3, -⟩ := Restore.nf_bounds hNW₁
  obtain ⟨b4, -⟩ := Restore.nf_bounds hNW₂
  set A₀ := c.nreg ALLOC with hA₀
  set n₁ := N₁.nChords + N₂.nChords + 1 with hn₁
  set nT := n₁ + L.length with hnT
  set f := F (rd c bSweep 5) with hf
  set D := rd c bSweep 6 with hD
  set Λ := Nat.clog 2 nT with hΛ
  have eT : c.nmem (rd c bSweep 3) + c.nmem (rd c bSweep 4) + rd c bSweep 9 + 1 = nT := by
    rw [hK₁, hK₂, hLn]; omega
  rw [eT] at hroom
  have hroomK : A₀ + (κE D + 238 * κ0 D + 10 * κL D + 1000) * nT * (f + Λ + 1) ≤ W := hroom
  clear hroom
  have hl₁ : Nat.clog 2 n₁ ≤ Λ := clog_mono (by omega)
  have hbig : 1000 * nT ≤ (κE D + 238 * κ0 D + 10 * κL D + 1000) * nT * (f + Λ + 1) := by
    have h1 : 1000 * nT * 1 ≤ (κE D + 238 * κ0 D + 10 * κL D + 1000) * nT * (f + Λ + 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul_right _ (by omega)) (by omega)
    omega
  have b3' : c.nreg (sw 3) + 7 < A₀ := b3
  have b4' : c.nreg (sw 4) + 7 < A₀ := b4
  have hK₁' : c.nmem (c.nreg (sw 3)) = N₁.nChords := hK₁
  have hK₂' : c.nmem (c.nreg (sw 4)) = N₂.nChords := hK₂
  have hLm' : c.nreg (sw 8) + 3 * L.length ≤ A₀ := hLm
  have hWm : 2 * J.whole.m + 7 ≤ W := by
    have := MergeAsm.chain_m_le hJWF.2.2.1 hJ.2.2
    unfold hostWords at hWh; omega
  have hnar₁ := SweepEv.arcsTask J.left (Qof P) N₁ hP hNF₁
  -- 1. save the side
  obtain ⟨c₁, k₁, e₁, hk₁, p99, p7, pr, pm, prr, prm, po⟩ := preS_exec (P := P) c hw
  have p : ∀ j, j ≠ 99 → j ≠ 7 → c₁.nreg (sw j) = c.nreg (sw j) := fun j h1 h2 =>
    pr _ (by unfold sw; omega) (by unfold sw; omega)
  have pA : c₁.nreg ALLOC = A₀ := pr _ (by unfold sw ALLOC; omega) (by unfold sw ALLOC; omega)
  -- 2. stage 0
  obtain ⟨c₂, k₂, e₂, hk₂, hSt0, hF₂⟩ := initS_exec (P := P) c₁ e₁.wb_right (H := H) (J := J)
    (by rw [p7]; omega)
    (by rw [pm, p 0 (by omega) (by omega), p 1 (by omega) (by omega), p 2 (by omega) (by omega)]
        exact hJ)
    (by rw [pm, pA, p 0 (by omega) (by omega), p 1 (by omega) (by omega),
        p 2 (by omega) (by omega)]; exact hJWF)
    hWm (by rw [pA]; omega)
  have h99₂ : c₂.nreg (sw 99) = rd c bSweep 7 := (initS_keep99 e₂).trans p99
  have hSt0S₂ : SweepEv.St0S P c₂ H J := SweepEv.st0S_of_st0 hSt0 p7
  obtain ⟨s90, s91, -, -, slo, sA, sJ, sJWF, -, sw20, -, sw21, -⟩ := hSt0
  have e2 : ∀ j, j < 20 → j ≠ 7 → c₂.nreg (sw j) = c.nreg (sw j) := fun j hj h =>
    (slo j hj).trans (p j (by omega) h)
  have A2 : c₂.nreg ALLOC = A₀ + 12 := by rw [sA, pA]
  have m2 : ∀ a, a < A₀ → c₂.nmem a = c.nmem a := fun a ha =>
    (hF₂.2.2.1 a (by rw [pA]; exact ha)).trans (by rw [pm])
  -- 3. stages 2/3
  have r2 : ∀ j, j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 10 → rd c₂ bSweep j = rd c bSweep j :=
    fun j hj => e2 j (by omega) (by omega)
  have hPre₂ : SweepEv.Pre X Ok P W c₂ := by
    refine ⟨hG, hWh, ?_, ?_, sJWF, H, J, N₁, N₂, sJ, hP, hOk₁, hOk₂, ?_, ?_, hNF₁, hNF₂, ?_, ?_,
      ?_, ?_, hSt0S₂⟩
    · rw [r2 10 (by simp)]
      exact X.mono _ _ _ _ _ (by omega) (X.local_ _ _ _ _ _ (fun a ha => (m2 a ha).symm) hX)
    · rw [r2 5 (by simp), r2 10 (by simp), hXl _ _ _ _ _ m2 hX]; exact hcap
    · rw [r2 3 (by simp)]; exact (Robust.transport hNW₁ m2).mono (by omega)
    · rw [r2 4 (by simp)]; exact (Robust.transport hNW₂ m2).mono (by omega)
    · rw [r2 6 (by simp)]; exact hdeg₁
    · rw [r2 6 (by simp)]; exact hdeg₂
    · rw [r2 5 (by simp)]; exact hsg₁
    · rw [r2 5 (by simp)]; exact hsg₂
  have eK2 : c₂.nmem (rd c₂ bSweep 3) + c₂.nmem (rd c₂ bSweep 4) + 1 = n₁ := by
    rw [r2 3 (by simp), r2 4 (by simp), m2 _ (by omega), m2 _ (by omega), hK₁, hK₂]
  have hc3 : SweepEv.cost κE F P c₂ = κE D * n₁ * (f + Nat.clog 2 n₁ + 1) := by
    unfold SweepEv.cost
    rw [eK2, r2 6 (by simp), r2 5 (by simp)]
  have room3 := asm_cost (κE := κE D) (κ0 := κ0 D) (κL := κL D) (f := f) (Λ := Λ)
    (l₁ := Nat.clog 2 n₁) (n₁ := n₁) (nT := nT) (K₁ := N₁.nChords) (K₂ := N₂.nChords)
    (Lq := L.length) (S := 0) (Lg := 0) (TLR := 0) (A₁ := 0) (k₂ := 220)
    (k₃ := κE D * n₁ * (f + Nat.clog 2 n₁ + 1)) (k₄ := 0) (k₅ := 0) (k₇ := 0) rfl rfl hl₁
    (by omega) (by omega) (by omega) (by omega) le_rfl le_rfl (by omega) (Nat.zero_le _)
    (Nat.zero_le _)
  obtain ⟨c₃, k₃, e₃, hk₃, hPost, hF₃⟩ := hEv sh Bs F X Ok hXl hBs hsh P W c₂ e₂.wb_right hPre₂
    (by rw [hc3, A2]; omega)
  rw [hc3] at hk₃
  obtain ⟨keep, -, b200', -, b300', -, b302', hS16, hL16, hOut⟩ := hPost
  rw [eK2] at hS16 hL16
  rw [show c₂.nmem (rd c₂ bSweep 4) = N₂.nChords by rw [r2 4 (by simp), m2 _ (by omega), hK₂]]
    at b302'
  have m3 : ∀ a, a < A₀ → c₃.nmem a = c.nmem a := fun a ha =>
    (hF₃.2.2.1 a (by omega)).trans (m2 a ha)
  have A3 := hF₃.2.2.2.2.2.1
  have A3' := hF₃.2.2.2.2.2.2
  have hOut₃ : SweepEv.Out P J N₂ c₃ := hOut H J N₂ sJ
    (by rw [r2 4 (by simp)]; exact NFWithin.nfAt (Robust.transport hNW₂ m2)) hNF₂
  have hSt0S₃ : SweepEv.St0S P c₃ H J :=
    st0S_transport hSt0S₂ (fun j hj _ => keep j (by omega)) hF₃.2.2.1 A3
  have e3 : ∀ j, j < 20 → j ≠ 7 → c₃.nreg (sw j) = c.nreg (sw j) := fun j hj h =>
    (keep j (by omega)).trans (e2 j hj h)
  -- 4. the initialisation of the answers
  have room4 := asm_cost (κE := κE D) (κ0 := κ0 D) (κL := κL D) (f := f) (Λ := Λ)
    (l₁ := Nat.clog 2 n₁) (n₁ := n₁) (nT := nT) (K₁ := N₁.nChords) (K₂ := N₂.nChords)
    (Lq := L.length) (S := 0) (Lg := 0) (TLR := 0) (A₁ := 0) (k₂ := k₂) (k₃ := k₃)
    (k₄ := 100 + 6 * (Nat.clog 2 n₁ + 6)) (k₅ := 0) (k₇ := 0) rfl rfl hl₁
    (by omega) (by omega) (by omega) (by omega) hk₂ hk₃ le_rfl (Nat.zero_le _) (Nat.zero_le _)
  have hF2A := hF₂.2.2.2.2.2.2
  obtain ⟨c₄, k₄, e₄, hk₄, hF₄, hCs, hside, z30, z31, z0, zq, z6, zl, tb, ta, t64, tle, ttab, m4,
    r4⟩ := ansInit_exec (P := P) c₃ e₃.wb_right (n := n₁)
      (by rw [keep 90 (by omega), s90]) (by rw [keep 91 (by omega), s91])
      (by rw [keep 20 (by omega)]; have := sw20.1; omega)
      (by rw [keep 21 (by omega)]; have := sw21.1; omega)
      (by rw [e3 3 (by omega) (by omega)]; omega) (by rw [e3 4 (by omega) (by omega)]; omega)
      (by rw [e3 3 (by omega) (by omega), e3 4 (by omega) (by omega), m3 _ (by omega),
        m3 _ (by omega), hK₁', hK₂'])
      (by rw [pA] at hF2A; omega) (by omega)
  have hAE₄ : AEnv P W X Ok J H N₁ N₂ A₀ c₄ :=
    asm_aenv hXl hG hWh hX hcap hP hOk₁ hOk₂ hNW₁ hNW₂ hNF₁ hNF₂ hdeg₁ hdeg₂ hsg₁ hsg₂ hWm
      hSt0S₃ hOut₃ b200' b300' b302' hS16 hL16 (fun j hj => e3 j (by omega) (by omega)) m3 (by omega)
      hCs z30 z31 z0 zq z6 zl tb ta t64 ttab m4 r4
  have e4 : ∀ j, j < 20 → j ≠ 7 → c₄.nreg (sw j) = c.nreg (sw j) := fun j hj h =>
    (r4 j (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (Or.inl (by omega))).trans (e3 j hj h)
  have e4r : ∀ j, (j = 201 ∨ j = 301) → c₄.nreg (sw j) = c₃.nreg (sw j) := fun j hj =>
    r4 j (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (Or.inl (by omega))
  -- 5. the side-0 initialisation
  have hc5 : κ0 (c₄.nreg (sw 6)) * (rd c₄ bSweep 201 + rd c₄ bSweep 301 + 2 * N₂.nChords + 1) *
      (c₄.nreg TLR + 1) = κ0 D * (rd c₃ bSweep 201 + rd c₃ bSweep 301 + 2 * N₂.nChords + 1) *
      (c₄.nreg TLR + 1) := by
    rw [e4 6 (by omega) (by omega), show rd c₄ bSweep 201 = rd c₃ bSweep 201 from e4r 201 (by simp),
      show rd c₄ bSweep 301 = rd c₃ bSweep 301 from e4r 301 (by simp)]
    rfl
  have room5 := asm_cost (κE := κE D) (κ0 := κ0 D) (κL := κL D) (f := f) (Λ := Λ)
    (l₁ := Nat.clog 2 n₁) (n₁ := n₁) (nT := nT) (K₁ := N₁.nChords) (K₂ := N₂.nChords)
    (Lq := L.length) (S := rd c₃ bSweep 201) (Lg := rd c₃ bSweep 301) (TLR := c₄.nreg TLR)
    (A₁ := 0) (k₂ := k₂) (k₃ := k₃) (k₄ := k₄)
    (k₅ := κ0 D * (rd c₃ bSweep 201 + rd c₃ bSweep 301 + 2 * N₂.nChords + 1) * (c₄.nreg TLR + 1))
    (k₇ := 0) rfl rfl hl₁ hS16 hL16 tle (by omega) hk₂ hk₃ hk₄ le_rfl (Nat.zero_le _)
  have hF3A := hF₃.2.2.2.2.2.2
  have hF4A := hF₄.2.2.2.2.2.2
  obtain ⟨c₅, k₅, e₅, hk₅, hF₅, hr₅, hAux₅⟩ := hInit.1 P W X Ok J H N₁ N₂ A₀ c₄ e₄.wb_right hAE₄
    (by rw [hc5]; rw [pA] at hF2A; omega)
  rw [hc5] at hk₅
  have hAE₅ : AEnv P W X Ok J H N₁ N₂ A₀ c₅ :=
    aenv_transport hXl hAE₄ (fun j hj _ hj' => hr₅ j hj hj') hF₅.2.2.1 hF₅.2.2.2.2.2.1
  -- 6. the result base
  set c₆ : Config := { c₅ with nreg := upd c₅.nreg (sw 11) (c₅.nreg ALLOC) } with hc₆
  have e₆ : Exec P W (.instr (.copyN (sw 11) ALLOC)) c₅ c₆ 1 := Exec.copyN e₅.wb_right (sw 11) ALLOC
  have r6 : ∀ r, r ≠ sw 11 → c₆.nreg r = c₅.nreg r := fun r hr => upd_other _ _ _ hr
  have A6 : c₆.nreg ALLOC = c₅.nreg ALLOC := r6 _ (by unfold sw ALLOC; omega)
  have hAE₆ : AEnv P W X Ok J H N₁ N₂ A₀ c₆ :=
    aenv_transport hXl hAE₅ (fun j hj h11 _ => r6 _ (by unfold sw; omega)) (fun _ _ => rfl)
      (by rw [A6])
  have e6 : ∀ j, j < 20 → j ≠ 7 → j ≠ 11 → c₆.nreg (sw j) = c.nreg (sw j) := fun j hj h h' => by
    rw [r6 _ (by unfold sw; omega), hr₅ j (by omega) (Or.inl (by omega)), e4 j hj h]
  have A5 := hF₅.2.2.2.2.2.1
  have A5' := hF₅.2.2.2.2.2.2
  have m6 : ∀ a, a < A₀ → c₆.nmem a = c.nmem a := fun a ha => by
    show c₅.nmem a = c.nmem a
    rw [hF₅.2.2.1 a (by omega), m4 a (by omega), m3 a ha]
  have hTL6 : c₆.nreg TLR = c₄.nreg TLR := by
    rw [r6 _ (by unfold TLR sw; omega)]; exact hr₅ 601 (by omega) (Or.inl (by omega))
  have hAB : ABase P W X Ok Aux J H N₁ N₂ A₀ L (rd c bSweep 7) c₆ := by
    refine
      { hw := e₆.wb_right
        hA := hAE₆
        hi := h7
        hside := ?_
        hAux := fun _ => hInit.2 P J N₂ c₅ _ hAux₅
        hLn := by rw [e6 9 (by omega) (by omega) (by omega)]; exact hLn
        hLm := by rw [e6 8 (by omega) (by omega) (by omega), A6]; omega
        hLat := by
          rw [e6 8 (by omega) (by omega) (by omega)]; exact chordList_keep hLat hLm m6
        hq := hq
        hht := hht
        hend := hend
        hres := by rw [A6]; simp [c₆, upd]
        hTLR := by rw [hTL6]; omega }
    rw [r6 _ (by unfold sSide sw; omega), show sSide = sw 98 from rfl,
      hr₅ 98 (by omega) (Or.inl (by omega)), show sw 98 = sSide from rfl, hside,
      keep 99 (by omega), h99₂]
  -- 7. the loop
  have hlc : loopCost κL F c₆ N₁ L = κL D * (L.length + 1) * (f + c₄.nreg TLR + 1) +
      κL D * (N₁.arcs.length + 1) * (f + 1) := by
    unfold loopCost
    rw [hTL6, e6 6 (by omega) (by omega) (by omega), e6 5 (by omega) (by omega) (by omega)]
    rfl
  have room7 := asm_cost (κE := κE D) (κ0 := κ0 D) (κL := κL D) (f := f) (Λ := Λ)
    (l₁ := Nat.clog 2 n₁) (n₁ := n₁) (nT := nT) (K₁ := N₁.nChords) (K₂ := N₂.nChords)
    (Lq := L.length) (S := rd c₃ bSweep 201) (Lg := rd c₃ bSweep 301) (TLR := c₄.nreg TLR)
    (A₁ := N₁.arcs.length) (k₂ := k₂) (k₃ := k₃) (k₄ := k₄) (k₅ := k₅)
    (k₇ := κL D * (L.length + 1) * (f + c₄.nreg TLR + 1) +
      κL D * (N₁.arcs.length + 1) * (f + 1)) rfl rfl hl₁ hS16 hL16 tle hnar₁ hk₂ hk₃ hk₄ hk₅
    le_rfl
  obtain ⟨c₇, k₇, e₇, hk₇, hI₇, hfr₇, R, hRl, hR11, hRat, hSees⟩ :=
    hL sh Bs F X Ok hsh hBs hXl P W c₆ J H N₁ N₂ A₀ L (rd c bSweep 7) hAB
      (by rw [hlc, A6]; rw [pA] at hF2A; omega)
  rw [hlc] at hk₇
  have final := asm_cost (κE := κE D) (κ0 := κ0 D) (κL := κL D) (f := f) (Λ := Λ)
    (l₁ := Nat.clog 2 n₁) (n₁ := n₁) (nT := nT) (K₁ := N₁.nChords) (K₂ := N₂.nChords)
    (Lq := L.length) (S := rd c₃ bSweep 201) (Lg := rd c₃ bSweep 301) (TLR := c₄.nreg TLR)
    (A₁ := N₁.arcs.length) (k₂ := k₂) (k₃ := k₃) (k₄ := k₄) (k₅ := k₅) (k₇ := k₇) rfl rfl hl₁
    hS16 hL16 tle hnar₁ hk₂ hk₃ hk₄ hk₅ hk₇
  have A7 := hfr₇.2.2.2.1
  have A7' := hfr₇.2.2.2.2
  have h11 : c₇.nreg (sw 11) = c₆.nreg (sw 11) := hI₇.hin _ (by unfold IFix sw; omega)
  have v11 : c₆.nreg (sw 11) = c₅.nreg ALLOC := by simp [c₆, upd]
  refine ⟨c₇, k₁ + (k₂ + (k₃ + (k₄ + (k₅ + (1 + k₇))))),
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ e₇))))), ?_, ?_, ?_⟩
  · -- the cost
    beta_reduce
    rw [eT, hk₁]
    unfold asmK
    exact final
  · -- the postcondition
    intro H' J' L' hJ' hL9 hL8
    obtain rfl := junction_unique hJ hJ'
    obtain rfl := BuildNF.chordListAt_unique hLat hL8 (by rw [← hLn, hL9])
    refine ⟨R, ?_, ?_, hRl, ?_, hSees⟩
    · show A₀ ≤ c₇.nreg (sw 11)
      rw [h11, v11]; omega
    · show c₇.nreg (sw 11) + 4 * L.length ≤ c₇.nreg ALLOC
      rw [h11]; exact hR11
    · show ResultListAt c₇.nmem (c₇.nreg (sw 11)) R
      rw [h11]; exact hRat
  · -- the frame
    refine ⟨fun r hr hra => ?_, fun r hr => ?_, fun a ha => ?_, fun a ha => ?_, ?_, ?_, ?_⟩
    · rw [hfr₇.1 r hr hra, r6 r (sw_band hr 11 (by omega)), hF₅.1 r hr hra, hF₄.1 r hr hra,
        hF₃.1 r hr hra, hF₂.1 r (bands_sub hr) hra, pr r (sw_band hr 99 (by omega))
        (sw_band hr 7 (by omega))]
    · rw [hfr₇.2.1 r hr]
      show c₅.rreg r = c.rreg r
      rw [hF₅.2.1 r hr, hF₄.2.1 r hr, hF₃.2.1 r hr, hF₂.2.1 r (bands_sub hr), prr]
    · rw [hI₇.hm a (by rw [A6]; omega), m6 a ha]
    · rw [hI₇.hrm a (by rw [A6]; omega)]
      show c₅.rmem a = c.rmem a
      rw [hF₅.2.2.2.1 a (by omega), hF₄.2.2.2.1 a (by omega), hF₃.2.2.2.1 a (by omega),
        hF₂.2.2.2.1 a (by rw [pA]; exact ha), prm]
    · rw [hfr₇.2.2.1]
      show c₅.output = c.output
      rw [hF₅.2.2.2.2.1, hF₄.2.2.2.2.1, hF₃.2.2.2.2.1, hF₂.2.2.2.2.1, po]
    · omega
    · rw [pA] at hF2A; omega

end

end SweepIo

end Chazelle.Core
