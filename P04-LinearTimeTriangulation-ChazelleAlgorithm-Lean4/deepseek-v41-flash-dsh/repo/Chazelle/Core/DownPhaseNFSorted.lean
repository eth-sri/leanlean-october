module

public import Chazelle.Golf

public import Chazelle.Core.NFBuildMain

/-!
# Down phase, L1: the normal-form build over presorted events (`BuildNFSortedSpec`)

`BuildNFSpec` sorts the `2K` event codes (`K ⌈log₂ K⌉` steps).  The down phase keeps the event
order sorted by splicing, so it needs the build without the sort: `sortedStmt` runs the record
part of phase A (`setupA`, `recLoop`), points phase B's event pointer `r30005` at the caller's
event list (register `bBuild 4`), and runs phase B unchanged (`phaseB_exec`).  Cost `κ (K + 1)`.

* `phaseAS_exec`: the records;
* **`buildNFSorted : BuildNFSortedSpec`**: the normal form `buildNF M Q L E` of the given sorted
  ordering `E`, with `IsNF`, the chord list and no decomposition (`BuildNF.isNF_goodModel`).

Design: `docs/design-downphase-nf.md` §2.
-/

namespace Chazelle.Core

@[expose] public section

open Machine Machine.Stmt Programs SignK NFLoc SortL
open BuildNF (codeLe)

/-- **L1: the normal-form build over presorted events.**  Inputs as in `BuildNFSpec` (model
descriptor `bBuild 0`, chord list `bBuild 1`, length `bBuild 2`) and the event list at
`bBuild 4`: a permutation `E` of the `2K` event codes sorted by `codeLe`, below the allocator.
Output (`bBuild 3`): a fresh handle of the normal form `buildNF M Q L E` of that very ordering,
which is a normal form with the given chords and no decomposition.  Cost `κ (K + 1)`. -/
def BuildNFSortedSpec : Prop :=
  ∃ (s : Stmt) (κ : ℕ), Meets s {bBuild, bSort, bSign}
    (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧
      ModelDescWF P (c.nreg ALLOC) c.nmem (rd c bBuild 0) ∧
      ∃ M L E, ModelDescAt c.nmem (rd c bBuild 0) (Qof P) M ∧
      GoodModel M ∧ rd c bBuild 2 = L.length ∧ rd c bBuild 1 + 3 * L.length ≤ c.nreg ALLOC ∧
      ChordListAt c.nmem (rd c bBuild 1) L ∧ ChordTriplesOK M (Qof P) L ∧
      rd c bBuild 4 + 2 * L.length ≤ c.nreg ALLOC ∧
      seg c.nmem (rd c bBuild 4) (2 * L.length) = E ∧
      E.Perm (List.range (2 * L.length)) ∧ E.Pairwise (codeLe M (Qof P) L))
    (fun P c c' => ∀ M L, ModelDescAt c.nmem (rd c bBuild 0) (Qof P) M →
      rd c bBuild 2 = L.length → ChordListAt c.nmem (rd c bBuild 1) L →
        c.nreg ALLOC ≤ rd c' bBuild 3 ∧
        NFWithin c'.nmem (rd c' bBuild 3) (c'.nreg ALLOC)
          (BuildNF.buildNF M (Qof P) L (seg c.nmem (rd c bBuild 4) (2 * L.length))) ∧
        IsNF M (Qof P) (BuildNF.buildNF M (Qof P) L (seg c.nmem (rd c bBuild 4) (2 * L.length))) ∧
        (BuildNF.buildNF M (Qof P) L (seg c.nmem (rd c bBuild 4) (2 * L.length))).chords.map
          (fun r => (r.h, r.lp, r.rp)) = L ∧
        (BuildNF.buildNF M (Qof P) L (seg c.nmem (rd c bBuild 4) (2 * L.length))).dec = [])
    (fun _ c => κ * (rd c bBuild 2 + 1))

namespace DownNF

open BuildRam

/-- The record part of phase A, then the event pointer. -/
def phaseAS : Stmt := .seq setupA (.seq recLoop (.instr (.copyN 30005 40004)))

/-- **The procedure of `BuildNFSortedSpec`.** -/
def sortedStmt : Stmt :=
  .seq (.instr (.constN 43250 0)) (.ifLtN 43250 40002 (.seq phaseAS phaseB) zeroCase)

/-- The constant of the cost bound. -/
def κSorted : ℕ := 24000

section exec

variable {P : Polygon} {W : ℕ}


/-- **The records and the event pointer.** -/
theorem phaseAS_exec (hWn : hostWords P.n ≤ W) (c : Config)
    (hw : WordsBounded W c) {M : Model} {L : List (ℕ × ℕ × ℕ)} {D B SE : ℕ}
    (hL : ChordTriplesOK M (Qof P) L) (hCL : ChordListAt c.nmem B L)
    (hB : B + 3 * L.length ≤ c.nreg ALLOC) (hD : c.nreg 40000 = D) (hB' : c.nreg 40001 = B)
    (hK : c.nreg 40002 = L.length) (hSE : c.nreg 40004 = SE)
    (hroom : c.nreg ALLOC + 32 * L.length + 22 ≤ W) :
    ∃ c' k, Exec P W phaseAS c c' k ∧ k ≤ 32 * L.length + 18 ∧ WordsBounded W c' ∧
      Frame {bBuild, bSort, bSign} c c' k ∧
      c'.nreg 40000 = D ∧ c'.nreg 42000 = c.nreg ALLOC ∧ c'.nreg 42001 = 2 * L.length ∧
      c'.nreg 43001 = B ∧ c'.nreg 43002 = L.length ∧ c'.nreg 43010 = 0 ∧ c'.nreg 43011 = 1 ∧
      RecsAt c'.nmem (c.nreg ALLOC) L ∧ c'.nreg 30005 = SE ∧
      c'.nreg ALLOC = c.nreg ALLOC + 10 * L.length := by
  set A₀ := c.nreg ALLOC with hA₀
  set K := L.length with hKdef
  have hA : c.nreg 9999 = A₀ := rfl
  have hWn' : P.n + 3 ≤ W := by unfold hostWords at hWn; omega
  -- setup
  obtain ⟨c₁, k₁, x₁, hk₁, v₁⟩ := setupA_exec (P := P) c hw hB' hK hA (by omega) (by omega)
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, fr₁, rr₁, m₁, rm₁, out₁⟩ := v₁
  have w₁ := x₁.wb_right
  -- the record loop
  have hI₁ : RecInv c.nmem L B A₀ (A₀ + 8 * K) c₁ c₁ :=
    { i_le := by rw [r9]; omega, rK := r2, r0 := r3, r1 := r4, a21 := by rw [r10, r9]; omega,
      a22 := by rw [r11, r9]; omega, a23 := by rw [r12, r9]; omega, a24 := by rw [r13, r9],
      fr := fun _ _ => rfl, rr := rfl, rm := rfl, out := rfl,
      mem := fun a => by rw [m₁, r9]; unfold recMem; rw [ite_eq_right (by omega), ite_eq_right (by omega)] }
  have hhW : ∀ x ∈ L, x.1 + 1 ≤ W := fun x hx => by
    have := hL.2.2.2 x hx
    have hn : (Qof P).n = P.n := shear_n _ _
    omega
  obtain ⟨c₂, k₂, x₂, hk₂, hk₂', w₂, I₂, i₂⟩ :=
    recLoop_exec (P := P) hCL hB rfl (by omega) hhW w₁ hI₁ r9
  -- the event pointer
  obtain ⟨c₃, x₃, n₃, m₃, rr₃, rm₃, out₃⟩ := SortR.copyN_char (P := P) w₂ 30005 40004
  have e₃ : ∀ r, r ≠ 30005 → c₃.nreg r = c₂.nreg r := fun r hr => by rw [n₃]; simp [upd, hr]
  have s₃ : c₃.nreg 30005 = c₂.nreg 40004 := by rw [n₃]; simp [upd]
  -- registers untouched by the setup and the loop
  have hc₂ : ∀ r, r < 43020 → r ≠ 43001 → r ≠ 43002 → r ≠ 43010 → r ≠ 43011 → r ≠ 42001 →
      r ≠ 42000 → r ≠ 9999 → c₂.nreg r = c.nreg r := fun r h0 h1 h2 h3 h4 h5 h6 h9 => by
    rw [I₂.fr r (Or.inl h0)]
    exact fr₁ r h1 h2 h3 h4 h5 h6 (by omega) (by omega) h9 (by omega) (by omega) (by omega)
      (by omega) (by omega)
  have X : Exec P W phaseAS c c₃ (k₁ + (k₂ + 1)) := .seq x₁ (.seq x₂ x₃)
  have hA₃ : c₃.nreg 9999 = A₀ + 10 * K := by
    rw [e₃ _ (by norm_num), I₂.fr _ (Or.inl (by norm_num)), r8]
  refine ⟨c₃, _, X, by omega, x₃.wb_right, ⟨fun r hr hra => ?_, fun r hr => ?_,
    fun a ha => ?_, fun a ha => ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hA₃⟩
  · obtain ⟨-, hr'⟩ := band_out hr
    have hra' : r ≠ 9999 := hra
    rw [e₃ r (by omega), I₂.fr _ (by omega)]
    exact fr₁ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) hra' (by omega) (by omega) (by omega) (by omega) (by omega)
  · rw [rr₃, I₂.rr, rr₁]
  · have ha' : a < A₀ := ha
    rw [m₃, I₂.mem, i₂]; unfold recMem; rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  · rw [rm₃, I₂.rm, rm₁]
  · rw [out₃, I₂.out, out₁]
  · show A₀ ≤ c₃.nreg 9999; omega
  · show c₃.nreg 9999 ≤ A₀ + _; omega
  · rw [e₃ _ (by norm_num), hc₂ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num), hD]
  · rw [e₃ _ (by norm_num), I₂.fr _ (Or.inl (by norm_num)), r6]
  · rw [e₃ _ (by norm_num), I₂.fr _ (Or.inl (by norm_num)), r5]
  · rw [e₃ _ (by norm_num), I₂.fr _ (Or.inl (by norm_num)), r1]
  · rw [e₃ _ (by norm_num), I₂.rK]
  · rw [e₃ _ (by norm_num), I₂.r0]
  · rw [e₃ _ (by norm_num), I₂.r1]
  · refine recsAt_of fun q hq => ?_
    rw [m₃, I₂.mem, i₂]; unfold recMem; rw [ite_eq_left (by omega), show A₀ + q - A₀ = q by omega]
  · rw [s₃, hc₂ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num), hSE]


/-- **L1: `BuildNFSortedSpec`.** -/
theorem buildNFSorted : BuildNFSortedSpec := by
  refine ⟨sortedStmt, κSorted, ?_⟩
  intro P W c hw hpre hcost
  obtain ⟨hG, hWn, hwf, M, L, E, hM, hgood, hlen, hBL, hCL, hok, hSEL, hE, hperm, hsort⟩ := hpre
  simp only [rd, bandReg, bBuild] at hwf hM hlen hBL hCL hSEL hE ⊢
  norm_num at hwf hM hlen hBL hCL hSEL hE ⊢
  set K := L.length with hKdef
  set A₀ := c.nreg ALLOC with hA₀
  set SE := c.nreg 40004 with hSEdef
  have hA : c.nreg 9999 = A₀ := rfl
  have hcost' : A₀ + κSorted * (K + 1) ≤ W := by
    have h := hcost
    beta_reduce at h
    simp only [rd, bandReg, bBuild, Nat.reduceMul, Nat.reduceAdd] at h
    rw [hlen] at h
    exact h
  unfold κSorted at hcost'
  have hNF := BuildNF.isNF_goodModel hgood hok hperm hsort
  -- the first instruction
  have x₀ := Exec.constN (P := P) hw 43250 0 (Nat.zero_le _)
  set c₀ : Config := { c with nreg := upd c.nreg 43250 0 } with hc₀
  have w₀ := x₀.wb_right
  have g₀ : ∀ r, r ≠ 43250 → c₀.nreg r = c.nreg r := fun r hr => by rw [hc₀]; simp [hr]
  by_cases hK : 0 < K
  · -- records
    have t₀ : c₀.nreg 43250 < c₀.nreg 40002 := by
      rw [g₀ 40002 (by norm_num), hlen, hc₀]; simp; exact hK
    have hc0A : c₀.nreg ALLOC = A₀ := g₀ 9999 (by norm_num)
    obtain ⟨c₁, k₁, x₁, hk₁, w₁, F₁, d1, d2, d3, d4, d5, d6, d7, hrec, hSE₁, hH₁⟩ :=
      phaseAS_exec (P := P) hWn c₀ w₀ (M := M) (L := L) (D := c.nreg 40000)
        (B := c.nreg 40001) (SE := SE) hok hCL (by rw [hc0A]; exact hBL) (g₀ _ (by norm_num))
        (g₀ _ (by norm_num)) (by rw [g₀ _ (by norm_num), hlen]) (g₀ _ (by norm_num))
        (by rw [hc0A]; omega)
    rw [hc0A] at d2 hrec hH₁
    have hm₀ : c₀.nmem = c.nmem := by rw [hc₀]
    set H := c₁.nreg 9999 with hHdef
    have hHv : H = A₀ + 10 * K := hH₁
    have hlow₁ : ∀ a, a < A₀ → c₁.nmem a = c.nmem a := fun a ha => by
      rw [F₁.2.2.1 a (by rw [hc0A]; exact ha), hm₀]
    have hk₁' : 10 * K ≤ k₁ := by
      have := F₁.2.2.2.2.2.2; rw [hc0A] at this; change H ≤ A₀ + k₁ at this; omega
    obtain ⟨hM₁, hwf₁⟩ := desc_agree hwf hM hlow₁
    have hElen : E.length = 2 * K := by rw [hperm.length_eq, List.length_range]
    have hI : BuildNF.Input M (Qof P) L E :=
      ⟨walkAx_of_goodModel hgood, hok, hperm,
        BuildNF.sorted_of_codeLe (walkAx_of_goodModel hgood) hok hperm hsort⟩
    have hCL₁ : ChordListAt c₁.nmem (c.nreg 40001) L := fun i hi => by
      obtain ⟨a1, a2, a3⟩ := hCL i hi
      exact ⟨by rw [hlow₁ _ (by omega), a1], by rw [hlow₁ _ (by omega), a2],
        by rw [hlow₁ _ (by omega), a3]⟩
    obtain ⟨c₂, k₂, x₂, hk₂, hk₂', w₂, F₂, h40003, h9999, hlow, hNFW⟩ := phaseB_exec (P := P) hG
      hWn c₁ w₁ (M := M) (L := L) (E := E) (D := c.nreg 40000) (T := A₀) (SE := SE)
      (B := c.nreg 40001) (H := H) hI hK d1 d2 d3 d4 d5 d6 d7 hSE₁ rfl
      (modelDescWF_mono hwf₁ (by omega)) hM₁ hrec (by omega) hCL₁ (by omega)
      (fun j hj => by
        rw [hlow₁ _ (by omega)]
        exact seg_getD hE (by omega))
      (by omega) (by unfold sizeB; omega)
    have X : Exec P W sortedStmt c c₂ (1 + (k₁ + k₂ + 1)) :=
      .seq x₀ (.ifLtN_true t₀ (.seq x₁ x₂))
    refine ⟨c₂, _, X, ?_, fun M' L' hM' hlen' hL' => ?_, ?_⟩
    · rw [hlen]; unfold κSorted; omega
    · obtain rfl := NFLoc.modelDesc_unique hM hM'
      obtain rfl := BuildNF.chordListAt_unique hCL hL' (hlen.symm.trans hlen')
      rw [hE]
      exact ⟨by rw [h40003]; omega, by rw [h40003]; exact hNFW, hNF⟩
    · refine ⟨fun r hr hra => ?_, fun r hr => ?_, fun a ha => ?_, fun a ha => ?_, ?_, ?_, ?_⟩
      · rw [F₂.1 r (BphaseB_false hr hra), F₁.1 r hr hra, g₀ r (by
          intro h; subst h; simp [bandOf, bSort, bSign] at hr)]
      · rw [exec_frameM2 x₂ wrM2_phaseB r (BRb_false hr), F₁.2.1 r hr]
      · rw [hlow a (by omega), hlow₁ a ha]
      · rw [F₂.2.2.1, F₁.2.2.2.1 a (by rw [hc0A]; exact ha)]
      · rw [F₂.2.2.2, F₁.2.2.2.2.1]
      · show A₀ ≤ c₂.nreg 9999; rw [h9999]; omega
      · show c₂.nreg 9999 ≤ A₀ + _; rw [h9999]; unfold sizeB at hk₂' ⊢; omega
  · -- `K = 0`
    have hK0 : K = 0 := by omega
    have t₀ : ¬ c₀.nreg 43250 < c₀.nreg 40002 := by
      rw [g₀ 40002 (by norm_num), hlen, hc₀]; simp; omega
    obtain ⟨c', k, x, hk, hk', w', F', h40003, h9999, hlow, hNFW⟩ := zeroCase_exec (P := P) hWn
      c₀ w₀ (M := M) (L := L) (E := E) (D := c.nreg 40000) (H := A₀) hK0
      (g₀ _ (by norm_num)) (by rw [g₀ 9999 (by norm_num)]; rfl) hwf hM (by omega)
    have X : Exec P W sortedStmt c c' (1 + (k + 2)) := .seq x₀ (.ifLtN_false t₀ x)
    refine ⟨c', _, X, by rw [hlen, hK0]; unfold κSorted; omega, fun M' L' hM' hlen' hL' => ?_, ?_⟩
    · obtain rfl := NFLoc.modelDesc_unique hM hM'
      obtain rfl := BuildNF.chordListAt_unique hCL hL' (hlen.symm.trans hlen')
      rw [hE]
      exact ⟨by rw [h40003], by rw [h40003]; exact hNFW, hNF⟩
    · have F₀ : FrameM BphaseB c c₀ := exec_frameM x₀ (by decide)
      have R' : ∀ r, BRb r = false → c'.rreg r = c.rreg r := fun r hr =>
        (exec_frameM2 x wrM2_zeroCase r hr).trans (by rw [hc₀])
      refine frame_of_frameM (F₀.trans F') R' (fun a ha => by rw [hlow a ha]) ?_ ?_
      · show A₀ ≤ c'.nreg 9999; rw [h9999]; omega
      · show c'.nreg 9999 ≤ A₀ + _; rw [h9999]; omega

end exec

end DownNF

/-- **L1: `BuildNFSortedSpec`** (the procedure `DownNF.sortedStmt`). -/
theorem buildNFSorted : BuildNFSortedSpec := DownNF.buildNFSorted

end

end Chazelle.Core
