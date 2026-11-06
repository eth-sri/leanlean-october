module

public import Chazelle.Core.MergeAsmDesc
public import Chazelle.Core.MergeAsmCost
public import Chazelle.Core.RestoreDrvPos

/-!
# WP-F merge assembly, part 6: Lemma 3.5 — `mergeSpec_of`

`mergeSpec_of : FuseSpec → RestoreSpec → GranularizeSpec → MergeSpec`.

The merge (`mergeMk`) fuses the two canonical normal forms (weights `≤ γ₀` by monotonicity, degree
`≤ D`), builds a model descriptor of the whole chain at the allocator, computes the degree `d₀`
of the fused map (the largest exit list, `≤ capF D`), restores conformality with the weight bound
`γ_R = min (γ₀ + 1) (2 m + 7)` (every weight is at most the size of the model, so the fused map is
`γ_R`-semigranular; this keeps restoration's `⌈log₂ γ⌉` below `⌈log₂ (m + 1)⌉ + 3`, finding F-G1),
then enforces granularity `γ ≥ γ₀ + 1` with degree cap `D`.

Costs (`MergeAsmCost`): Lemma 2.3 gives `K₁ + K₂ + 1 ≤ β (m + 1)`; the oracle cost functions are
monotone (finding F-G2) and positive (`Restore.oracle_pos`, on a configuration holding the model
descriptor); restoration's output has `≤ cR d₀ D (K + 1)` chords (finding F-G3).
-/

namespace Chazelle.Core

namespace MergeAsm

open Machine Machine.Stmt Programs SignK

@[expose] public section

/-! ## Frames and contexts -/

/-- The bands of the merge. -/
def MB : Finset ℕ := mergeBands ∪ oracleBands

theorem frame_band {b : ℕ} {c c' : Config} (h : FrameB (inBand b) c c') (hb : b ∈ MB)
    (hb0 : b ≠ 0) (k : ℕ) : Frame MB c c' k :=
  NFLoc.frame_of_frameB h (fun r hr => by
    simp only [inBand, decide_eq_true_eq] at hr
    refine ⟨hr ▸ hb, fun h => ?_⟩
    rw [h] at hr; exact hb0 (hr.symm.trans bandOf_alloc)) k

theorem ftr {c c₁ c₂ : Config} {k₁ k₂ : ℕ} (h₁ : Frame MB c c₁ k₁)
    (h₂ : Frame MB c₁ c₂ k₂) : Frame MB c c₂ (k₁ + k₂) :=
  (h₁.trans h₂).mono (by simp) le_rfl

theorem holds_frame {X : MemCtx} {P : Polygon} {g : ℕ} {B : Finset ℕ} {c c' : Config} {k : ℕ}
    (hX : X.holds P c.nmem g (c.nreg ALLOC)) (hf : Frame B c c' k) :
    X.holds P c'.nmem g (c'.nreg ALLOC) :=
  X.mono _ _ _ _ _ hf.2.2.2.2.2.1 (X.local_ _ _ _ _ _ (fun a ha => (hf.2.2.1 a ha).symm) hX)

theorem cap_frame {X : MemCtx} (hloc : X.CapLocal) {P : Polygon} {g : ℕ} {B : Finset ℕ}
    {c c' : Config} {k : ℕ} (hX : X.holds P c.nmem g (c.nreg ALLOC)) (hf : Frame B c c' k) :
    X.cap P c'.nmem g = X.cap P c.nmem g :=
  hloc P c.nmem c'.nmem g _ (fun a ha => hf.2.2.1 a ha) hX

/-- The frame of the descriptor copy. -/
theorem descS_frame {c c' : Config} {A : ℕ} (hA : c.nreg ALLOC = A) (hA' : c'.nreg ALLOC = A + 6)
    (hm : ∀ a, (a < A ∨ A + 6 ≤ a) → c'.nmem a = c.nmem a)
    (hr : ∀ r, (r < 100010 ∨ 100022 ≤ r) → r ≠ ALLOC → c'.nreg r = c.nreg r)
    (hrr : c'.rreg = c.rreg) (hrm : c'.rmem = c.rmem) (ho : c'.output = c.output) :
    Frame MB c c' 27 := by
  refine ⟨fun r hb hra => hr r ?_ hra, fun r _ => by rw [hrr], fun a ha => hm a (by omega),
    fun a _ => by rw [hrm], ho, by omega, by omega⟩
  by_contra h
  push Not at h
  apply hb
  have : bandOf r = bMerge := by unfold bandOf bMerge; omega
  rw [this]; decide

/-! ## The constant -/

/-- The largest value of `f` on `0 … n`. -/
def supTo (f : ℕ → ℕ) (n : ℕ) : ℕ := (Finset.range (n + 1)).sup f

theorem le_supTo {f : ℕ → ℕ} {n d : ℕ} (h : d ≤ n) : f d ≤ supTo f n :=
  Finset.le_sup (f := f) (Finset.mem_range.2 (by omega))

/-- The constant of Lemma 2.3 in the form `K₁ + K₂ + 1 ≤ β (m + 1)`. -/
def βf (c23 : ℕ → ℕ) (D : ℕ) : ℕ := 16 * c23 D + 1

/-- **The constant of the merge.** -/
def κM (κF capF : ℕ → ℕ) (κR cR : ℕ → ℕ → ℕ) (κG c23 : ℕ → ℕ) (D : ℕ) : ℕ :=
  κF D * (βf c23 D + 2) + 8 * (βf c23 D + 7) * supTo (fun d => κR d D) (capF D) +
    κG D * (8 * supTo (fun d => cR d D) (capF D) *
      (8 * supTo (fun d => cR d D) (capF D) * βf c23 D + 1) + 1) + 123

/-! ## Oracle positivity -/

/-- The configuration `c` with a model descriptor of the chain at `bw` written at the allocator
(used only to apply `Restore.oracle_pos`). -/
def withDesc (c : Config) (bw : ℕ) : Config :=
  { c with
    nreg := upd c.nreg ALLOC (c.nreg ALLOC + 6)
    nmem := fun a => if a = c.nreg ALLOC then 0
      else if c.nreg ALLOC < a ∧ a < c.nreg ALLOC + 6 then c.nmem (bw + (a - c.nreg ALLOC - 1))
      else c.nmem a }

theorem oracle_pos_merge {sh cu : Stmt} {Bs Bc : Finset ℕ} {F G H : ℕ → ℕ} {X : MemCtx}
    {Ok : Polygon → Model → Prop} (hloc : X.CapLocal) (hsh : ShooterOK sh Bs F X Ok)
    (hcu : CutterOK cu Bc G H X Ok) {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c)
    (hG : GoodEnv P) (hWh : hostWords P.n ≤ W) {g γ bw : ℕ}
    (hX : X.holds P c.nmem g (c.nreg ALLOC)) (hcap : γ ≤ X.cap P c.nmem g) (hγ : 1 ≤ γ)
    (hγW : γ ≤ W + 6) (hgW : g ≤ W) {Hs : Host} {C : Chain}
    (hwf : ChainWF P (c.nreg ALLOC) c.nmem bw) (hC : ChainDescAt c.nmem bw (Qof P) Hs C)
    (hP : C.P.Simple) (hOk : Ok P (chainModel C)) (hreg : HostRegular (Qof P).n Hs) :
    1 ≤ F γ ∧ 1 ≤ G γ := by
  obtain ⟨A, hAd⟩ : ∃ A, c.nreg ALLOC = A := ⟨_, rfl⟩
  rw [hAd] at hwf hX
  set ĉ := withDesc c bw
  have hA : ĉ.nreg ALLOC = A + 6 := by simp [ĉ, withDesc, hAd]
  have hAW : A ≤ W := hAd ▸ hw.1 ALLOC
  have hmem : ∀ a, ĉ.nmem a = if a = A then 0 else if A < a ∧ a < A + 6 then
      c.nmem (bw + (a - A - 1)) else c.nmem a := fun a => by simp only [ĉ, withDesc, hAd]
  have he : ∀ a, a < A → ĉ.nmem a = c.nmem a := fun a ha => by
    rw [hmem, ite_eq_right (by omega), ite_eq_right (by omega)]
  have hbA := hwf.1
  have hw' : WordsBounded (W + 6) ĉ := by
    refine ⟨fun r => ?_, fun a => ?_⟩
    · simp only [ĉ, withDesc]
      by_cases hr : r = ALLOC
      · subst hr; simp only [upd_same]; omega
      · simp only [upd_other _ _ _ hr]; have := hw.1 r; omega
    · rw [hmem]
      split_ifs
      · omega
      · have := hw.2 (bw + (a - A - 1)); omega
      · have := hw.2 a; omega
  have h0 : ĉ.nmem A = 0 := by rw [hmem, ite_eq_left rfl]
  have hc : ∀ j, j < 5 → ĉ.nmem (A + 1 + j) = c.nmem (bw + j) := fun j hj => by
    rw [hmem, ite_eq_right (by omega), ite_eq_left (by omega), show A + 1 + j - A - 1 = j by omega]
  obtain ⟨hMD, hMWF⟩ := modelDesc_copy hwf hC le_rfl he h0 hc (E' := A + 6) le_rfl
  have hCd : ChainDescAt ĉ.nmem (A + 1) (Qof P) Hs C := by
    obtain ⟨-, -, hEb, -⟩ := hwf.2 Hs C hC
    exact chainDescAt_copy hC hEb he hc
  have hreg' : ĉ.nmem A = 0 → ∀ H' C', ChainDescAt ĉ.nmem (A + 1) (Qof P) H' C' →
      HostRegular (Qof P).n H' := fun _ H' C' h' => by
    rw [NFLoc.hostAt_unique h'.1 hCd.1]; exact hreg
  have hX' : X.holds P ĉ.nmem g (ĉ.nreg ALLOC) := by
    rw [hA]
    exact X.mono _ _ _ _ _ (by omega) (X.local_ _ _ _ _ _ (fun a ha => (he a ha).symm) hX)
  have hcap' : γ ≤ X.cap P ĉ.nmem g := by
    rw [hloc P c.nmem ĉ.nmem g _ he hX]; exact hcap
  exact Restore.oracle_pos hsh hcu hw' hG (by omega) hX' hcap' (by rw [hA]; exact hMWF) hreg' hMD
    (Or.inl ⟨C, hP, rfl⟩) hOk hγ (by omega) hγW (by omega)

end

end MergeAsm

end Chazelle.Core
