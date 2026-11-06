module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.RestoreTKey
public import Chazelle.Core.RestoreDrvProg

/-!
# WP-E, the candidate test on the RAM, part 3: the run invariant

A run of the candidate test starts in a configuration `c₀` satisfying the precondition of
`TestOK`; its fixed data (the model `M` of the descriptor, a chain model or the interior model,
the normal form `N`, …) are collected in `TGood`.  Every intermediate configuration `c`
satisfies `TInv`: the inputs (band `bRestore` below `83010`) are unchanged; the constants are in
place (`83020`: the chain descriptor address `MD + 1`, `83021`: the model header, `83022`: `0`,
`83023`: `1`); the allocator has not decreased and the memory below the initial allocator is
unchanged.

* `chainDesc_agree`, `chainWF_agree`: a chain descriptor survives changes of the memory at or
  above its bound.
* `TInv.modelDesc`, `TInv.chain`, `TInv.nfAt`: the descriptors stay readable.
* `TInv.prim`: a primitive call (a `Frame primBands` step) is a step of the run (`TStep`).
* `TInv.regs`: a register step inside band `bRestore` from `83010` on, off the constants,
  keeps `TInv`.
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Machine Machine.Stmt Programs SweepPrim WalkEmbed

/-! ## Descriptors survive changes above their bound -/

section
variable {m m' : ℕ → ℕ}
theorem hostAt_agree_r {B E : ℕ} {H : Host} (h : HostAt m B H)
    (hE : B + 3 * H.length + 4 ≤ E) (hm : ∀ a, a < E → m' a = m a) : HostAt m' B H := by
  refine ⟨by rw [hm _ (by omega)]; exact h.1, fun i hi => ?_⟩
  have hh := h.2 i hi
  ram_grind

theorem chainDesc_agree {bw E : ℕ} {Q : Polygon} {H : Host} {C : Chain}
    (hC : ChainDescAt m bw Q H C) (hb : bw + 5 ≤ E) (hE : m bw + 3 * H.length + 4 ≤ E)
    (he : ∀ a, a < E → m' a = m a) : ChainDescAt m' bw Q H C := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hC
  refine ⟨?_, h1, by grind, by grind,
    by grind, by ram_all⟩
  rw [he _ (by omega)]
  exact hostAt_agree_r h0 hE he


end

theorem chainWF_agree {P : Polygon} {m m' : ℕ → ℕ} {bw E E' : ℕ} {H : Host} {C : Chain}
    (hwf : ChainWF P E m bw) (hC : ChainDescAt m bw (Qof P) H C)
    (he : ∀ a, a < E → m' a = m a) (hEE : E ≤ E') : ChainWF P E' m' bw := by
  obtain ⟨hl, hHW, hEb, hs⟩ := hwf.2 H C hC
  have hb := hwf.1
  refine ⟨by omega, fun H' C' hC' => ?_⟩
  have c0 : m' bw = m bw := he _ (by omega)
  have hH' : HostAt m' (m bw) H := hostAt_agree_r hC.1 hEb he
  have hHH : H' = H := NFLoc.hostAt_unique (by rw [← c0]; exact hC'.1) hH'
  ram_grind

/-! ## The fixed data of a run -/

/-- **The fixed data of a run of the candidate test** from `c₀` (model `M`, normal form `N`). -/
structure TGood (P : Polygon) (W : ℕ) (M : Model) (N : NF) (c₀ : Config) : Prop where
  hG : GoodEnv P
  hW : hostWords P.n ≤ W
  hMD : ModelDescAt c₀.nmem (c₀.nreg 83000) (Qof P) M
  hwfMD : ModelDescWF P (c₀.nreg ALLOC) c₀.nmem (c₀.nreg 83000)
  hreg : c₀.nmem (c₀.nreg 83000) = 0 → ∀ H C, ChainDescAt c₀.nmem (c₀.nreg 83000 + 1) (Qof P) H C →
    HostRegular (Qof P).n H
  hsimp : c₀.nmem (c₀.nreg 83000) = 0 → ∀ H C,
    ChainDescAt c₀.nmem (c₀.nreg 83000 + 1) (Qof P) H C → C.P.Simple
  hkind : OkModel P M ∨ M = interiorModel (Qof P)
  hGM : GoodModel M
  hWm : ∀ C : Chain, M = chainModel C → 2 * C.m + 7 ≤ W
  hN : NFWithin c₀.nmem (c₀.nreg 83001) (c₀.nreg ALLOC) N
  hNF : IsNF M (Qof P) N
  hr : c₀.nreg 83002 < N.nRegions
  hxe : c₀.nreg 83005 < M.W.n
  hxp : ProperPos M (Qof P) P.n ⟨c₀.nreg 83005, c₀.nreg 83006⟩
  hxc : c₀.nreg 83006 = 0 ∨ 0 < M.param (Qof P) ⟨c₀.nreg 83005, c₀.nreg 83006⟩
  hxC : ∀ C : Chain, M = chainModel C → M.pos (Qof P) ⟨c₀.nreg 83005, c₀.nreg 83006⟩ ∈ C.set
  hh : c₀.nreg 83007 < P.n
  hy : ((Qof P).vtx (c₀.nreg 83007)).2 = (M.pos (Qof P) ⟨c₀.nreg 83005, c₀.nreg 83006⟩).2
  hσ : c₀.nreg 83008 ≤ 1

/-- **The run invariant** relative to the start `c₀`. -/
structure TInv (W : ℕ) (c₀ c : Config) : Prop where
  hw : WordsBounded W c
  hin : ∀ q, 80000 ≤ q → q < 83010 → c.nreg q = c₀.nreg q
  hA : c₀.nreg ALLOC ≤ c.nreg ALLOC
  hm : ∀ a, a < c₀.nreg ALLOC → c.nmem a = c₀.nmem a
  h20 : c.nreg 83020 = c₀.nreg 83000 + 1
  h21 : c.nreg 83021 = c₀.nmem (c₀.nreg 83000)
  h22 : c.nreg 83022 = 0
  h23 : c.nreg 83023 = 1

/-- **One step of a run**: the invariant after it, the relative frame, band `bRestore`
unchanged. -/
def TStep (W : ℕ) (c₀ c c' : Config) (k : ℕ) : Prop :=
  TInv W c₀ c' ∧ RF dBands (c₀.nreg ALLOC) c c' k ∧
    ∀ q, 80000 ≤ q → q < 90000 → c'.nreg q = c.nreg q

variable {P : Polygon} {W : ℕ} {M : Model} {N : NF} {c₀ c : Config}

section
variable (hE : TGood P W M N c₀) (hI : TInv W c₀ c)
include hE hI
/-- The model descriptor, at any configuration of the run. -/
theorem TInv.modelDesc :
    ModelDescAt c.nmem (c.nreg 83000) (Qof P) M ∧
      ModelDescWF P (c.nreg ALLOC) c.nmem (c.nreg 83000) := by
  have h0 := hI.hin 83000 (by norm_num) (by norm_num)
  have hA6 := hE.hwfMD.1
  rcases hE.hMD with ⟨hz, H, C, hC, hM⟩ | ⟨h1, hbit, hM⟩
  · have hcw : ChainWF P (c₀.nreg ALLOC) c₀.nmem (c₀.nreg 83000 + 1) := hE.hwfMD.2 hz
    obtain ⟨-, -, hEb, -⟩ := hcw.2 H C hC
    have hC' := chainDesc_agree hC hcw.1 hEb hI.hm
    have hz' : c.nmem (c₀.nreg 83000) = 0 := by ram_grind
    rw [h0]
    exact ⟨Or.inl ⟨hz', H, C, hC', hM⟩, by ram_grind,
      fun _ => chainWF_agree hcw hC hI.hm hI.hA⟩
  ram_grind

/-- **The chain descriptor of a chain model**, at any configuration of the run. -/
theorem TInv.chain {C : Chain}
    (hM : M = chainModel C) :
    ∃ H C', ChainDescAt c.nmem (c.nreg 83020) (Qof P) H C' ∧ M = chainModel C' ∧
      ChainWF P (c.nreg ALLOC) c.nmem (c.nreg 83020) := by
  obtain ⟨hMD, hwf⟩ := hI.modelDesc hE
  obtain ⟨hz, H, C', hC, hM'⟩ := chainDesc_of hMD hM
  rw [hI.h20, ← hI.hin 83000 (by norm_num) (by norm_num)]
  ram_grind

theorem TInv.nfWithin :
    NFWithin c.nmem (c.nreg 83001) (c₀.nreg ALLOC) N := by
  rw [hI.hin 83001 (by norm_num) (by norm_num)]
  exact hE.hN.transport hI.hm


end

/-- The primitive bands are bands of the test. -/
theorem primBands_sub : primBands ⊆ dBands := by decide

/-- **A primitive step keeps the invariant** and band `bRestore`. -/
theorem TInv.prim {c' : Config} {k : ℕ} (hI : TInv W c₀ c) (hw : WordsBounded W c')
    (hf : Frame primBands c c' k) : TStep W c₀ c c' k := by
  have h8 : ∀ q, 80000 ≤ q → q < 90000 → c'.nreg q = c.nreg q := fun q h1 h2 =>
    hf.1 q (by
      simp_all [primBands, bRestore, bSign, bLocate] <;> omega_nf) (by omega_nf)
  refine ⟨⟨hw, fun q h1 h2 => (h8 q h1 (by omega)).trans (hI.hin q h1 h2),
    hI.hA.trans hf.2.2.2.2.2.1, fun a ha => (hf.2.2.1 a (by ram_grind)).trans
      (hI.hm a ha), by ram_grind,
    by ram_grind,
    by ram_grind,
    by ram_grind⟩,
    (RF.of_frame hf hI.hA).mono primBands_sub le_rfl, h8⟩

theorem TStep.trans {c₁ c₂ : Config} {k₁ k₂ : ℕ} (h₁ : TStep W c₀ c c₁ k₁)
    (h₂ : TStep W c₀ c₁ c₂ k₂) : TStep W c₀ c c₂ (k₁ + k₂) :=
  ⟨h₂.1, h₁.2.1.trans h₂.2.1, fun q h1 h2 => (h₂.2.2 q h1 h2).trans (h₁.2.2 q h1 h2)⟩

theorem TStep.mono {c' : Config} {k k' : ℕ} (h : TStep W c₀ c c' k) (hk : k ≤ k') :
    TStep W c₀ c c' k' :=
  ⟨h.1, h.2.1.mono subset_rfl hk, h.2.2⟩

/-- **A step writing only registers of the primitive bands.** -/
theorem TInv.stepB {B : ℕ → Bool} {c' : Config} (hI : TInv W c₀ c) (hw : WordsBounded W c')
    (hf : SignK.FrameB B c c') (hB : ∀ r, B r = true → bandOf r ∈ primBands ∧ r ≠ ALLOC)
    (k : ℕ) : TStep W c₀ c c' k :=
  hI.prim hw (NFLoc.frame_of_frameB hf hB k)

/-- **A register step inside band `bRestore` from `83010` on keeps the invariant.** -/
theorem TInv.regs {c' : Config} {k : ℕ} (hI : TInv W c₀ c) (hw : WordsBounded W c')
    (hr : ∀ r, (r < 83010 ∨ 90000 ≤ r ∨ (83020 ≤ r ∧ r < 83024)) → c'.nreg r = c.nreg r)
    (hrr : c'.rreg = c.rreg) (hm : c'.nmem = c.nmem) (hrm : c'.rmem = c.rmem)
    (ho : c'.output = c.output) : TInv W c₀ c' ∧ RF dBands (c₀.nreg ALLOC) c c' k := by
  have hA : c'.nreg ALLOC = c.nreg ALLOC := hr ALLOC (by omega_nf)
  refine ⟨⟨hw, fun q h1 h2 => (hr q (by omega)).trans (hI.hin q h1 h2), by ram_grind,
    fun a ha => by ram_grind, by ram_grind,
    by ram_grind, by ram_grind,
    by ram_grind⟩,
    rf_of_regs (fun r hr' => hr r (by omega)) hrr hm hrm ho⟩

end

end Restore

end Chazelle.Core
