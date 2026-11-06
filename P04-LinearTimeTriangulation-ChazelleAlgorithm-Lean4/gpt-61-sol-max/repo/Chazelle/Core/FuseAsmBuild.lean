module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.FuseAsmCollStage

/-!
# WP-F fusion assembly, part 25: the normal form of the fused chord list

`bldStage sB`: a model descriptor of the whole chain at the allocator (`descF`), then `BuildNF`
(`sB`) on it with the chord list at `70242` (length `70219`), and the handle of the result in
`70007` (`bldStage_exec`).
-/

namespace Chazelle.Core

namespace FuseAsm

open Machine Machine.Stmt Programs SignK MergeAsm

@[expose] public section

/-- The precondition of `BuildNF`. -/
def BPre (P : Polygon) (W : ℕ) (c : Config) : Prop :=
  GoodEnv P ∧ hostWords P.n ≤ W ∧
    ModelDescWF P (c.nreg ALLOC) c.nmem (rd c bBuild 0) ∧
    ∃ M L, ModelDescAt c.nmem (rd c bBuild 0) (Qof P) M ∧
    GoodModel M ∧ rd c bBuild 2 = L.length ∧ rd c bBuild 1 + 3 * L.length ≤ c.nreg ALLOC ∧
    ChordListAt c.nmem (rd c bBuild 1) L ∧ ChordTriplesOK M (Qof P) L

/-- The postcondition of `BuildNF`. -/
def BPost (P : Polygon) (c c' : Config) : Prop :=
  ∀ M L, ModelDescAt c.nmem (rd c bBuild 0) (Qof P) M →
    rd c bBuild 2 = L.length → ChordListAt c.nmem (rd c bBuild 1) L →
      ∃ N, c.nreg ALLOC ≤ rd c' bBuild 3 ∧ NFWithin c'.nmem (rd c' bBuild 3) (c'.nreg ALLOC) N ∧
        IsNF M (Qof P) N ∧ N.chords.map (fun r => (r.h, r.lp, r.rp)) = L ∧ N.dec = []

/-- The cost of `BuildNF`. -/
def BCost (κ : ℕ) (_ : Polygon) (c : Config) : ℕ :=
  κ * (rd c bBuild 2 * (Nat.clog 2 (rd c bBuild 2) + 1) + 1)

theorem build_meets (hB : BuildNFSpec) :
    ∃ (s : Stmt) (κ : ℕ), Meets s {bBuild, bSort, bSign} BPre BPost (BCost κ) := hB

/-- A model descriptor of the whole chain at the allocator. -/
def descF : Stmt := block [.constN 70165 1, .constN 70166 5, .copyN 70160 ALLOC,
  .constN 70161 0, .storeN 70160 70161, .copyN 70162 70002, .addN 70163 70160 70165,
  .loadN 70164 70162, .storeN 70163 70164, .addN 70162 70162 70165,
  .addN 70163 70163 70165,
  .loadN 70164 70162, .storeN 70163 70164, .addN 70162 70162 70165,
  .addN 70163 70163 70165,
  .loadN 70164 70162, .storeN 70163 70164, .addN 70162 70162 70165,
  .addN 70163 70163 70165,
  .loadN 70164 70162, .storeN 70163 70164, .addN 70162 70162 70165,
  .addN 70163 70163 70165,
  .loadN 70164 70162, .storeN 70163 70164,
  .constN 70167 6, .addN ALLOC ALLOC 70167]

theorem descF_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) {A bw : ℕ}
    (hA : c.nreg ALLOC = A) (hbw : c.nreg 70002 = bw) (hbA : bw + 5 ≤ A) (hAW : A + 6 ≤ W) :
    ∃ c' k, Exec P W descF c c' k ∧ k = 27 ∧ c'.nreg 70160 = A ∧ c'.nreg ALLOC = A + 6 ∧
      c'.nmem A = 0 ∧ (∀ j, j < 5 → c'.nmem (A + 1 + j) = c.nmem (bw + j)) ∧
      (∀ a, (a < A ∨ A + 6 ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 70160 ∨ 70167 < r) → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold descF
  have hA' : c.nreg 9999 = A := hA
  exec_block
  all_goals try omega
  all_goals try (simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, hA', hbw, ALLOC]; omega)
  refine ⟨rfl, ?_, ?_, ?_, fun j hj => ?_, fun a ha => ?_, fun r h1 h2 => ?_, rfl, rfl,
    rfl⟩
  · omega_nf
  · omega_nf
  · grind [Machine.upd_same, Machine.upd_other, ALLOC]
  · interval_cases j <;>
      grind [Machine.upd_same, Machine.upd_other, ALLOC, add_zero]
  · grind [Machine.upd_other, ALLOC]
  · have h2' : r ≠ 9999 := h2
    simp (disch := omega) only [Machine.upd_other]

/-- The arguments of `BuildNF`. -/
def bldSet : Stmt := block [.copyN 40000 70160, .copyN 40001 70242, .copyN 40002 70219]

/-- The output handle. -/
def bldOut : Stmt := block [.copyN 70007 40003]

/-- **The normal form of the fused chord list.** -/
def bldStage (sB : Stmt) : Stmt := .seq descF (.seq bldSet (.seq sB bldOut))

set_option maxHeartbeats 8000000 in
theorem bldStage_exec {sB : Stmt} {κB : ℕ}
    (hB : Meets sB {bBuild, bSort, bSign} BPre BPost (BCost κB)) {P : Polygon} {W : ℕ}
    (c : Config) (hw : WordsBounded W c) (hG : GoodEnv P) (hHW : hostWords P.n ≤ W)
    {J : Merge.Junction} {H : Host} (hwf : ChainWF P (c.nreg ALLOC) c.nmem (c.nreg 70002))
    (hC : ChainDescAt c.nmem (c.nreg 70002) (Qof P) H J.whole) (hP : J.P.Simple)
    {D : List (ℕ × ℕ × ℕ)} (h42 : ChordListAt c.nmem (c.nreg 70242) D)
    (h19 : c.nreg 70219 = D.length) (hD : c.nreg 70242 + 3 * D.length ≤ c.nreg ALLOC)
    (hok : ChordTriplesOK (chainModel J.whole) (Qof P) D)
    (hroom : c.nreg ALLOC + 40 + κB * (D.length * (Nat.clog 2 D.length + 1) + 1) ≤ W) :
    ∃ c' k N, Exec P W (bldStage sB) c c' k ∧
      k ≤ 40 + κB * (D.length * (Nat.clog 2 D.length + 1) + 1) ∧
      c.nreg ALLOC ≤ c'.nreg 70007 ∧ NFWithin c'.nmem (c'.nreg 70007) (c'.nreg ALLOC) N ∧
      IsNF (chainModel J.whole) (Qof P) N ∧ N.chords.map (fun r => (r.h, r.lp, r.rp)) = D ∧
      Frame FB c c' k ∧
      (∀ r, bandOf r = bFuse → r ≠ 70007 → (r < 70160 ∨ 70167 < r) → c'.nreg r = c.nreg r) := by
  obtain ⟨A, hA⟩ : ∃ x, c.nreg ALLOC = x := ⟨_, rfl⟩
  obtain ⟨bw, hbw⟩ : ∃ x, c.nreg 70002 = x := ⟨_, rfl⟩
  rw [hbw] at hwf hC
  have h5 := hwf.1
  obtain ⟨c₁, k₁, e₁, hk₁, v60, a₁, m0, mc, mo, r₁, rr₁, rm₁, o₁⟩ :=
    descF_exec (P := P) c hw hA hbw (by omega) (by omega)
  have w₁ := e₁.wb_right
  have he : ∀ a, a < A → c₁.nmem a = c.nmem a := fun a ha => mo a (Or.inl ha)
  obtain ⟨hMD, hMWF⟩ := modelDesc_copy (E := A) (E' := c₁.nreg ALLOC) (A := A)
    (by omega_nf) hC le_rfl he m0 mc (by rw [a₁])
  have r42 : c₁.nreg 70242 = c.nreg 70242 := r₁ _ (Or.inr (by norm_num)) (by decide)
  have r19 : c₁.nreg 70219 = D.length := by ram_grind
  obtain ⟨c₂, k₂, e₂, hk₂, q0, q1, q2, qr, qm, qrr, qrm, qo⟩ : ∃ c₂ k₂, Exec P W bldSet c₁ c₂ k₂ ∧
      k₂ = 3 ∧ c₂.nreg 40000 = A ∧ c₂.nreg 40001 = c.nreg 70242 ∧ c₂.nreg 40002 = D.length ∧
      (∀ r, (r < 40000 ∨ 40002 < r) → c₂.nreg r = c₁.nreg r) ∧ c₂.nmem = c₁.nmem ∧
      c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
    unfold bldSet
    exec_block
    grind [Machine.upd_same, Machine.upd_other]
  have w₂ := e₂.wb_right
  have a₂ : c₂.nreg ALLOC = A + 6 := by ram_grind
  have hL₂ : ChordListAt c₂.nmem (c.nreg 70242) D :=
    chordList_agree (E := A) h42 (by omega) (fun a ha => by ram_grind)
  have hpre : BPre P W c₂ := by
    unfold BPre
    refine ⟨hG, hHW, ?_, chainModel J.whole, D, ?_, Or.inl ⟨J.whole, hP, rfl⟩, q2, ?_, ?_, hok⟩
    · omega_nf
    · omega_nf
    · show c₂.nreg 40001 + 3 * D.length ≤ c₂.nreg ALLOC
      omega
    · omega_nf
  have hcost : BCost κB P c₂ = κB * (D.length * (Nat.clog 2 D.length + 1) + 1) := by
    show κB * (c₂.nreg 40002 * (Nat.clog 2 (c₂.nreg 40002) + 1) + 1) = _; rw [q2]
  obtain ⟨c₃, k₃, e₃, hk₃, post, F₃⟩ := hB P W c₂ w₂ hpre (by omega)
  rw [hcost] at hk₃
  obtain ⟨N, hN1, hN2, hN3, hN4, -⟩ := post (chainModel J.whole) D
    (by omega_nf) q2 (by omega_nf)
  have w₃ := e₃.wb_right
  obtain ⟨c₄, k₄, e₄, hk₄, t7, tr, tm, trr, trm, tou⟩ : ∃ c₄ k₄, Exec P W bldOut c₃ c₄ k₄ ∧
      k₄ = 1 ∧ c₄.nreg 70007 = c₃.nreg 40003 ∧ (∀ r, r ≠ 70007 → c₄.nreg r = c₃.nreg r) ∧
      c₄.nmem = c₃.nmem ∧ c₄.rreg = c₃.rreg ∧ c₄.rmem = c₃.rmem ∧ c₄.output = c₃.output := by
    unfold bldOut
    exec_block
    ram_simp
  have ex : Exec P W (bldStage sB) c c₄ (k₁ + (k₂ + (k₃ + k₄))) := .seq e₁ (.seq e₂ (.seq e₃ e₄))
  have F₁ : Frame FB c c₁ k₁ := ⟨fun r hr ha => r₁ r (by
      have : bandOf r ≠ bFuse := fun h => hr (h ▸ band7)
      grind [bandOf, bFuse]) ha, fun r _ => by rw [rr₁], fun a ha => mo a (Or.inl
      (by omega)), fun a _ => by rw [rm₁], o₁, by omega,
      by omega⟩
  have F₂ : Frame FB c₁ c₂ k₂ := ⟨fun r hr ha => qr r (by
      have : bandOf r ≠ bBuild := fun h => hr (by rw [h]; decide)
      grind [bandOf, bBuild]), fun r _ => by rw [qrr], fun a _ => by rw [qm],
      fun a _ => by rw [qrm], qo, by rw [a₂, a₁], by omega⟩
  have F₄ : Frame FB c₃ c₄ k₄ := ⟨fun r hr ha => tr r (fun h => hr (by rw [h]; exact band7)),
    fun r _ => by rw [trr], fun a _ => by rw [tm], fun a _ => by rw [trm], tou,
    by rw [tr _ (by decide)], by rw [tr _ (by decide)]; omega⟩
  have Ft : Frame FB c c₄ (k₁ + (k₂ + (k₃ + k₄))) :=
    ftrF F₁ (ftrF F₂ (ftrF (F₃.mono (by decide) le_rfl) F₄))
  refine ⟨c₄, _, N, ex, by omega, ?_, ?_, hN3, hN4, Ft, fun r h1 h2 h3 => ?_⟩
  · have e3 : rd c₃ bBuild 3 = c₃.nreg 40003 := rfl
    omega
  · rw [t7, tr _ (by decide), tm]; exact hN2
  · have hb3 : bandOf r ∉ ({bBuild, bSort, bSign} : Finset ℕ) := by rw [h1]; decide
    have hA' : r ≠ ALLOC := by intro h; rw [h] at h1; exact absurd h1 (by decide)
    rw [tr r h2, F₃.1 r hb3 hA', qr r (by grind [bandOf, bFuse]), r₁ r h3 hA']

end

end FuseAsm

end Chazelle.Core
