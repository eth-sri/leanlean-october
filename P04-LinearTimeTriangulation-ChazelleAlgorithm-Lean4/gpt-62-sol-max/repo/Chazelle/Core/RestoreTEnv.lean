module

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

abbrev chainDesc_agree := @ChainDescAt.agree

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
  hm : MemEqBelow (c₀.nreg ALLOC) c.nmem c₀.nmem
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
  ram_rw [hI.hin 83000]
  exact hE.hwfMD.transport hE.hMD hI.hm hI.hA

/-- **The chain descriptor of a chain model**, at any configuration of the run. -/
theorem TInv.chain {C : Chain}
    (hM : M = chainModel C) :
    ∃ H C', ChainDescAt c.nmem (c.nreg 83020) (Qof P) H C' ∧ M = chainModel C' ∧
      ChainWF P (c.nreg ALLOC) c.nmem (c.nreg 83020) := by
  obtain ⟨hMD, hwf⟩ := hI.modelDesc hE
  obtain ⟨hz, H, C', hC, hM'⟩ := chainDesc_of hMD hM
  ram_rw [hI.h20, ← hI.hin 83000]
  exact ⟨H, C', hC, hM', hwf.2 hz⟩

theorem TInv.nfWithin :
    NFWithin c.nmem (c.nreg 83001) (c₀.nreg ALLOC) N := by
  ram_rw [hI.hin 83001]
  exact hE.hN.transport hI.hm

end

/-- The primitive bands are bands of the test. -/
theorem primBands_sub : primBands ⊆ dBands := by decide

/-- **A primitive step keeps the invariant** and band `bRestore`. -/
theorem TInv.prim {c' : Config} {k : ℕ} (hI : TInv W c₀ c) (hw : WordsBounded W c')
    (hf : Frame primBands c c' k) : TStep W c₀ c c' k := by
  have h8 := fun q h1 h2 =>
    hf.1 q (by
      rw [band8 h1 h2]
      simp [primBands, bRestore, bSign, bLocate]) (by unfold ALLOC; omega)
  refine ⟨⟨hw, fun q h1 h2 => (h8 q h1 (by omega)).trans (hI.hin q h1 h2),
    hI.hA.trans hf.2.2.2.2.2.1, fun a ha => (hf.2.2.1 a (by have := hI.hA; omega)).trans
      (hI.hm a ha), by ram_rw [h8]; exact hI.h20,
    by ram_rw [h8]; exact hI.h21,
    by ram_rw [h8]; exact hI.h22,
    by ram_rw [h8]; exact hI.h23⟩,
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
  have hA := hr ALLOC (by unfold ALLOC; omega)
  refine ⟨⟨hw, fun q h1 h2 => (hr q (by omega)).trans (hI.hin q h1 h2), by rw [hA]; exact hI.hA,
    fun a ha => by rw [hm]; exact hI.hm a ha, by ram_rw [hr]; exact hI.h20,
    by ram_rw [hr]; exact hI.h21, by ram_rw [hr]; exact hI.h22,
    by ram_rw [hr]; exact hI.h23⟩,
    rf_of_regs (fun r hr' => hr r (by omega)) hrr hm hrm ho⟩

end

end Restore

end Chazelle.Core
