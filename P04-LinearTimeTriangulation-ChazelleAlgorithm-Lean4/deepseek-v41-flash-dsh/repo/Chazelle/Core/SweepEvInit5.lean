module

public import Chazelle.Golf

public import Chazelle.Core.SweepEvInit4
public import Chazelle.Core.SweepEvWinArcs

/-!
# The sweep (WP-D), stages 2–3: the initialisation, part 5 (the environment; task I)

From the precondition `Pre` the initialisation `initE` reaches a configuration `c₀` with the
environment `EvEnv` of the run steps, for every `H J N₁ N₂` of the precondition (`PreAt`):
`evEnv_of_init`.  **`initTask : InitTask`** (constant `κI = 40000`).

Transport lemmas: `modelDescAt_keep'` (both kinds of model descriptors), `st0S_keep` (the stage-0
state survives a step keeping `sw 0 … 99` and the memory below the allocator).
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep

@[expose] public section

/-! ## Transport -/

/-- **A well-formed model descriptor** survives a change of the memory at or above its bound. -/
theorem modelDescAt_keep' {P : Polygon} {m m' : ℕ → ℕ} {D E E' : ℕ} {M : Model}
    (hwf : ModelDescWF P E m D) (hMD : ModelDescAt m D (Qof P) M)
    (he : ∀ a, a < E → m' a = m a) (hE : E ≤ E') :
    ModelDescAt m' D (Qof P) M ∧ ModelDescWF P E' m' D := by
  rcases hMD with ⟨h0, H, C, hC, rfl⟩ | ⟨h1, hbit, rfl⟩
  · obtain ⟨w', h0', hC'⟩ := ShotList.modelDesc_keep hwf h0 hC he hE
    exact ⟨Or.inl ⟨h0', H, C, hC', rfl⟩, w'⟩
  · have hD := hwf.1
    have e0 : m' D = m D := he _ (by omega)
    have e1 : m' (D + 1) = m (D + 1) := he _ (by omega)
    exact ⟨Or.inr ⟨by rw [e0, h1], by rw [e1]; exact hbit, rfl⟩,
      ⟨by omega, fun h => by rw [e0, h1] at h; exact absurd h (by norm_num)⟩⟩

/-- Junction descriptors survive a change of the memory at or above the allocator. -/
theorem junction_keep {P : Polygon} {m m' : ℕ → ℕ} {E E' b0 b1 b2 : ℕ} {H : Host}
    {J : Merge.Junction} (hJ : JunctionAt m b0 b1 b2 (Qof P) H J) (hJW : JunctionWF P E m b0 b1 b2)
    (he : ∀ a, a < E → m' a = m a) (hE : E ≤ E') :
    JunctionAt m' b0 b1 b2 (Qof P) H J ∧ JunctionWF P E' m' b0 b1 b2 := by
  obtain ⟨l0, l1⟩ := chainDesc_keep hJW.1 hJ.1 he hE
  obtain ⟨r0, r1⟩ := chainDesc_keep hJW.2.1 hJ.2.1 he hE
  obtain ⟨w0, w1⟩ := chainDesc_keep hJW.2.2.1 hJ.2.2 he hE
  refine ⟨⟨l0, r0, w0⟩, l1, r1, w1, fun H' hH' => ?_⟩
  have := NFLoc.hostAt_unique w0.1 hH'
  subst this
  exact hJW.2.2.2 H hJ.2.2.1

/-- **The stage-0 state** survives a step keeping `sw 0 … 99` and the memory below the
allocator, and not lowering the allocator. -/
theorem st0S_keep {P : Polygon} {c c' : Config} {H : Host} {J : Merge.Junction}
    (h : St0S P c H J) (hr : ∀ j, j < 100 → c'.nreg (sw j) = c.nreg (sw j))
    (hm : ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) (hA : c.nreg ALLOC ≤ c'.nreg ALLOC) :
    St0S P c' H J := by
  obtain ⟨h90, h91, h92, h93, hJ, hJW, d20, w20, d21, w21, h23, h24, hR, hL, h33, h34, h35, md30,
    mw30, md31, mw31⟩ := h
  have r := hr
  obtain ⟨hJ', hJW'⟩ := junction_keep hJ hJW hm hA
  obtain ⟨d20', w20'⟩ := chainDesc_keep w20 d20 hm hA
  obtain ⟨d21', w21'⟩ := chainDesc_keep w21 d21 hm hA
  obtain ⟨m30, mw30'⟩ := modelDescAt_keep' mw30 md30 hm hA
  obtain ⟨m31, mw31'⟩ := modelDescAt_keep' mw31 md31 hm hA
  refine ⟨by rw [r 90 (⊛)]; exact h90, by rw [r 91 (⊛)]; exact h91,
    by rw [r 92 (⊛)]; exact h92, by rw [r 93 (⊛)]; exact h93,
    by rw [r 0 (⊛), r 1 (⊛), r 2 (⊛)]; exact hJ',
    by rw [r 0 (⊛), r 1 (⊛), r 2 (⊛)]; exact hJW',
    by rw [r 20 (⊛)]; exact d20', by rw [r 20 (⊛)]; exact w20',
    by rw [r 21 (⊛)]; exact d21', by rw [r 21 (⊛)]; exact w21',
    by rw [r 23 (⊛), r 3 (⊛)]; exact h23,
    by rw [r 24 (⊛), r 4 (⊛)]; exact h24,
    fun k hk => by rw [r (40 + k) (⋄)]; exact hR k hk,
    fun k hk => by rw [r (45 + k) (⋄)]; exact hL k hk,
    by rw [r 33 (⊛)]; exact h33, by rw [r 34 (⊛)]; exact h34,
    by rw [r 35 (⊛)]; exact h35, by rw [r 30 (⊛)]; exact m30,
    by rw [r 30 (⊛)]; exact mw30', by rw [r 31 (⊛)]; exact m31,
    by rw [r 31 (⊛)]; exact mw31'⟩

/-! ## Arithmetic -/

theorem clog_four_mul (x : ℕ) : Nat.clog 2 (4 * x) ≤ Nat.clog 2 x + 2 := by
  Ξ Nat.clog_le_iff_le_pow (⊛), pow_add
  have := Nat.le_pow_clog (by norm_num : 1 < 2) x
  norm_num; omega

theorem clog_le_self' (x : ℕ) : Nat.clog 2 x ≤ x := by
  rw [Nat.clog_le_iff_le_pow (⊛)]; exact Nat.lt_two_pow_self.le

/-! ## The environment -/

/-- The constant of the initialisation. -/
def κI : ℕ := 40000


/-- **The environment after the initialisation.** -/
theorem evEnv_of_init {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx}
    {Ok : Polygon → Model → Prop} {J₀ : Merge.Junction} (hXl : X.CapLocal) (hBs : Bs ⊆ oracleBands)
    (hsh : ShooterOK sh Bs F X Ok) {P : Polygon} {W : ℕ} {c c₀ : Config} {k : ℕ}
    (hpre : Pre X Ok P W c) (fr : Frame ioBands c c₀ k) (R : InitRes P J₀ c c₀)
    (hk : k ≤ 31100 + 6 * Nat.clog 2 (c.nmem (c.nreg (sw 3) + 1) + c.nmem (c.nreg (sw 4) + 1) + 1))
    (hroom : c.nreg ALLOC + κI * (c.nmem (rd c bSweep 3) + c.nmem (rd c bSweep 4) + 1) ≤ W)
    {H : Host} {J : Merge.Junction} {N₁ N₂ : NF} (hJ₀ : J = J₀)
    (hpa : PreAt X Ok P c H J N₁ N₂) : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂ := by
  subst hJ₀
  obtain ⟨hG, hWh, hX, hcap, -, -⟩ := hpre
  obtain ⟨hJ, hP, hOk1, hOk2, hNW1, hNW2, hNF1, hNF2, hdeg1, hdeg2, hsg1, hsg2, hst⟩ := hpa
  have hst' := hst
  obtain ⟨-, -, -, -, -, hJW, d20, w20, d21, w21, -⟩ := hst'
  have hm := R.mem
  have hA := fr.2.2.2.2.2.1
  have hAk := fr.2.2.2.2.2.2
  have kp : ∀ j, j < 600 → c₀.nreg (sw j) = c.nreg (sw j) := fun j hj =>
    R.keep _ (not_oracle_sw (by unfold sw; omega) (by unfold sw; omega)) (by unfold sw ALLOC; omega)
      (by unfold sw; omega)
  -- the normal forms
  have nN1 := hNW1.nfAt
  have nN2 := hNW2.nfAt
  have hK1 : c.nmem (rd c bSweep 3) = N₁.nChords := nN1.1
  have hK2 : c.nmem (rd c bSweep 4) = N₂.nChords := nN2.1
  have ha1 : c.nmem (c.nreg (sw 3) + 1) = N₁.arcs.length := nN1.2.1
  have ha2 : c.nmem (c.nreg (sw 4) + 1) = N₂.arcs.length := nN2.2.1
  have hA1 := arcsTask J.left (Qof P) N₁ hP hNF1
  have hA2 := arcsTask J.right (Qof P) N₂ hP hNF2
  Ξ' hK1, hK2 at hroom
  Ξ' ha1, ha2 at hk
  have hL := R.hTLR
  Ξ' ha1, ha2 at hL
  have hpow : N₁.arcs.length + N₂.arcs.length + 1 ≤ 2 ^ c₀.nreg TLR := by
    rw [hL]; exact Nat.le_pow_clog (⊛) _
  have hLle := clog_le_self' (N₁.arcs.length + N₂.arcs.length + 1)
  have hMD := R.hA
  have hTB := R.hTBR
  have hAl := R.hAl
  -- the descriptor of `C₁`
  have k20 : c₀.nreg (sw 20) = c.nreg (sw 20) := kp 20 (⊛)
  obtain ⟨hmd, hmwf, hCD⟩ := modelDesc_of_copy (E' := c₀.nreg ALLOC) w20 d20 hMD hm R.md0
    (fun j hj => R.mdc j hj) (⋄)
  have ctx20 := chainCtx_of (W := W) hG hWh hP hJ hJW d20 w20
  have ctx21 := chainCtx_of (W := W) hG hWh hP hJ hJW d21 w21
  have ctxW := chainCtx_of (W := W) (d := sw 2) hG hWh hP hJ hJW hJ.2.2 hJW.2.2.1
  have hWn : 2 * (chainModel J.whole).W.n ≤ W := walk_two_le hJW.2.2.1 hJ.2.2 hWh
  have e10 := kp 10 (⊛)
  have e5 := kp 5 (⊛)
  have e6 := kp 6 (⊛)
  have e3 := kp 3 (⊛)
  have e4 := kp 4 (⊛)
  refine ⟨hsh, hBs, hXl, hG, hWh, hP, ?_, ?_, hOk1, hNF1, ?_, ?_, hNF2, ?_, hmd, hmwf, R.md0,
    R.hcd, ?_, ?_, ?_, R.hK, R.hO, R.hM, R.hgw, ?_, ?_, hWn, ?_, ?_, hOk2, ?_, ?_, ?_, R.htab,
    ⋄, ⋄, ⋄, ?_, ?_, ?_, R.hTA⟩
  · rw [e10]; exact X.mono _ _ _ _ _ hA (X.local_ P c.nmem c₀.nmem _ _ (fun a ha => (hm a ha).symm) hX)
  · have hc := hXl P c.nmem c₀.nmem _ _ hm hX
    Ξ e10, e5
    exact hcap.trans_eq hc.symm
  · rw [e5]; exact hsg1
  · rw [e3]; exact (hNW1.transport hm).mono hA
  · rw [e4]; exact (hNW2.transport hm).mono hA
  · obtain ⟨g1, g2, -, ⟨H', hd', hreg⟩, g5, g6⟩ := ctx20
    refine ⟨g1, g2, ?_, ⟨H, ?_, ?_⟩, g5, g6⟩
    · rw [R.hcd]; exact hmwf.2 R.md0
    · rw [R.hcd]; exact hCD
    · exact hJW.2.2.2 H hJ.2.2.1
  · exact ctx21.transport (kp 21 (⊛)) hm hA
  · exact ctxW.transport (kp 2 (⊛)) hm hA
  · Ξ R.hTA
  · rw [R.hTA]; have := Nat.mul_le_mul_left κI (le_refl (N₁.nChords + N₂.nChords + 1))
    unfold κI at hroom; omega
  · refine ⟨H, ?_, st0S_keep hst (fun j hj => kp j (⋄)) hm hA⟩
    Ξ kp 0 (⊛), kp 1 (⊛), kp 2 (⊛)
    exact (junction_keep hJ hJW hm hA).1
  · Ξ kp 0 (⊛), kp 1 (⊛), kp 2 (⊛)
    exact (junction_keep hJ hJW hm hA).2
  · rw [e5]; exact hsg2
  · rw [e6]; exact hdeg1
  · rw [e6]; exact hdeg2
  · rw [e3]; exact (hNW1.transport hm).mono (⋄)
  · rw [e4]; exact (hNW2.transport hm).mono (⋄)
  · Ξ hL
    calc Nat.clog 2 (N₁.arcs.length + N₂.arcs.length + 1)
        ≤ Nat.clog 2 (4 * (N₁.nChords + N₂.nChords + 1)) :=
          Nat.clog_mono_right _ (by unfold NF.nChords at *; omega)
      _ ≤ Nat.clog 2 (N₁.nChords + N₂.nChords + 1) + 2 := clog_four_mul _
      _ ≤ _ := ⋄

/-! ## Task I -/

theorem InitRes.keep200 {P : Polygon} {J : Merge.Junction} {c c₀ : Config}
    (R : InitRes P J c c₀) : ∀ j, j < 200 → c₀.nreg (sw j) = c.nreg (sw j) := fun j hj => by
  have h1 : 240000 ≤ sw j := by unfold sw; omega
  have h2 : sw j < 250000 := by unfold sw; omega
  exact R.keep (sw j) (not_oracle_sw h1 h2) (by unfold sw ALLOC; omega) (Or.inl (by
    unfold sw; omega))


/-- **Task I: the initialisation** (`initE`, constant `κI = 40000`). -/
theorem initTask : InitTask := by
  refine ⟨initE, κI, fun sh Bs F X Ok hXl hBs hsh P W c hw hpre hroom => ?_⟩
  have hpre' := hpre
  obtain ⟨hG, hWh, -, -, -, H₀, J₀, N₁₀, N₂₀, hJ₀, hP₀, -, -, hNW1, hNW2, hNF1, hNF2, -, -, -, -,
    hst⟩ := hpre'
  have nN1 := hNW1.nfAt
  have nN2 := hNW2.nfAt
  have hA1 := arcsTask J₀.left (Qof P) N₁₀ hP₀ hNF1
  have hA2 := arcsTask J₀.right (Qof P) N₂₀ hP₀ hNF2
  have hK1 := nN1.1
  have hK2 := nN2.1
  have ha1 : c.nmem (c.nreg (sw 3) + 1) = N₁₀.arcs.length := nN1.2.1
  have ha2 : c.nmem (c.nreg (sw 4) + 1) = N₂₀.arcs.length := nN2.2.1
  have h3 : c.nreg (sw 3) + 1 < c.nreg ALLOC := nfWithin_lt' hNW1
  have h4 : c.nreg (sw 4) + 1 < c.nreg ALLOC := nfWithin_lt' hNW2
  have hroom' := hroom
  Ξ' hK1, hK2 at hroom'
  unfold κI at hroom'
  obtain ⟨c₀, k, ex, hk, fr, R⟩ := initE_exec hw hst hG hWh hP₀ h3 h4 (by
    rw [ha1, ha2]; unfold NF.nChords at *; omega)
  have hk' := hk
  Ξ' ha1, ha2 at hk'
  have hcl := clog_le_self' (N₁₀.arcs.length + N₂₀.arcs.length + 1)
  refine ⟨c₀, k, ex, ?_, fr, ex.wb_right, R.keep200, fun H J N₁ N₂ hpa => ?_⟩
  · rw [hK1, hK2]; unfold κI NF.nChords at *; omega
  · exact evEnv_of_init hXl hBs hsh hpre fr R hk hroom (junction_unique hpa.1 hJ₀) hpa

end

end SweepEv

end Chazelle.Core
