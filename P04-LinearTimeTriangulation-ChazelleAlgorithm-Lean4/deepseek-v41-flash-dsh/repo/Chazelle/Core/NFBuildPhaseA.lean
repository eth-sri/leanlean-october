module

public import Chazelle.Golf

public import Chazelle.Core.NFBuildInit
public import Chazelle.Core.SortRam

/-!
# WP-C (BuildNF), RAM part 5: records and the sort of the event codes

`phaseA` saves the inputs (`r43001 = B`, `r43002 = K`), allocates the record table
`T = ALLOC` (`8K` words) and the code list `S₀ = T + 8K` (`2K` words), fills them (`recLoop`), and
sorts the codes with `SortR.sortStmt evCmp` (`phaseA_exec`): the sorted codes `E` lie at
`r30005`, a permutation of `range (2K)` sorted by `codeLe`.
-/

namespace Chazelle.Core

namespace BuildRam

open Machine Machine.Stmt Programs SignK SortL
open BuildNF (codeLe)

@[expose] public section

/-- The setup: inputs, constants, allocation of the records and the code list. -/
def setupA : Stmt :=
  block [.copyN 43001 40001, .copyN 43002 40002, .constN 43010 0, .constN 43011 1,
    .addN 42001 43002 43002, .copyN 42000 9999, .addN 43030 42001 42001,
    .addN 43030 43030 43030, .addN 43031 42000 43030, .addN 9999 43031 42001,
    .constN 43020 0, .copyN 43021 43001, .copyN 43022 42000, .copyN 43023 43031,
    .constN 43024 0]

/-- **Phase A**: records, code list, sort. -/
def phaseA : Stmt :=
  .seq setupA (.seq recLoop (.seq (block [.copyN 30003 43031, .copyN 30004 42001])
    (SortR.sortStmt evCmp)))

/-- The cost bound of phase A. -/
def costA (K : ℕ) : ℕ := 32 * K + 22 + SortR.sortCost 11010 (2 * K)

theorem modelDescWF_mono {P : Polygon} {E E' : ℕ} {m : ℕ → ℕ} {D : ℕ}
    (h : ModelDescWF P E m D) (hE : E ≤ E') : ModelDescWF P E' m D :=
  ⟨by have := h.1; omega, fun h0 => (h.2 h0).mono hE⟩

theorem seg_range {m : ℕ → ℕ} {a n : ℕ} (h : ∀ i, i < n → m (a + i) = i) :
    seg m a n = List.range n := by
  unfold seg
  conv_rhs => rw [← List.map_id (List.range n)]
  exact List.map_congr_left fun i hi => h i (List.mem_range.1 hi)

section exec

variable {P : Polygon} {W : ℕ}

/-- A band outside `{bBuild, bSort, bSign}`. -/
theorem band_out {r : ℕ} (hr : bandOf r ∉ ({bBuild, bSort, bSign} : Finset ℕ)) :
    bandOf r ∉ insert bSort ({bSign, bBuild} : Finset ℕ) ∧
      (r < 10000 ∨ (20000 ≤ r ∧ r < 30000) ∨ 50000 ≤ r) := by
  ϴ' Finset.mem_insert, Finset.mem_singleton, bandOf, bBuild, bSort, bSign at hr ⊢
  omega

/-- The setup of phase A. -/
theorem setupA_exec (c : Config) (hw : WordsBounded W c) {B K A₀ : ℕ} (hB' : c.nreg 40001 = B)
    (hK : c.nreg 40002 = K) (hA : c.nreg 9999 = A₀) (hroom : A₀ + 10 * K ≤ W) (hW1 : 1 ≤ W) :
    ∃ c₁ k₁, Exec P W setupA c c₁ k₁ ∧ k₁ = 15 ∧
    (c₁.nreg 43001 = B ∧ c₁.nreg 43002 = K ∧ c₁.nreg 43010 = 0 ∧ c₁.nreg 43011 = 1 ∧
      c₁.nreg 42001 = 2 * K ∧ c₁.nreg 42000 = A₀ ∧ c₁.nreg 43031 = A₀ + 8 * K ∧
      c₁.nreg 9999 = A₀ + 10 * K ∧ c₁.nreg 43020 = 0 ∧ c₁.nreg 43021 = B ∧
      c₁.nreg 43022 = A₀ ∧ c₁.nreg 43023 = A₀ + 8 * K ∧ c₁.nreg 43024 = 0 ∧
      (∀ r, r ≠ 43001 → r ≠ 43002 → r ≠ 43010 → r ≠ 43011 → r ≠ 42001 → r ≠ 42000 →
        r ≠ 43030 → r ≠ 43031 → r ≠ 9999 → r ≠ 43020 → r ≠ 43021 → r ≠ 43022 → r ≠ 43023 →
        r ≠ 43024 → c₁.nreg r = c.nreg r) ∧
      c₁.rreg = c.rreg ∧ c₁.nmem = c.nmem ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output)  := by
  unfold setupA
  exec_block
  all_goals first
    | (config_simp; simp (config := { failIfUnchanged := false }) only [hK, hA, hB']; omega)
    | skip
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 h5 h6 h7 h8 h9
    h10 h11 h12 h13 h14 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals (config_simp <;> (try simp only [hK, hA, hB']) <;>
    (try simp (disch := omega) only [upd_other]) <;> omega)

set_option maxHeartbeats 1000000 in
/-- **Phase A.** -/
theorem phaseA_exec (hG : GoodEnv P) (hWn : hostWords P.n ≤ W) (c : Config)
    (hw : WordsBounded W c) {M : Model} {L : List (ℕ × ℕ × ℕ)} {D B : ℕ}
    (hwf : ModelDescWF P (c.nreg ALLOC) c.nmem D) (hM : ModelDescAt c.nmem D (Qof P) M)
    (hL : ChordTriplesOK M (Qof P) L) (hCL : ChordListAt c.nmem B L)
    (hB : B + 3 * L.length ≤ c.nreg ALLOC) (hD : c.nreg 40000 = D) (hB' : c.nreg 40001 = B)
    (hK : c.nreg 40002 = L.length) (hroom : c.nreg ALLOC + costA L.length ≤ W) :
    ∃ c' k, Exec P W phaseA c c' k ∧ k ≤ costA L.length ∧ WordsBounded W c' ∧
      Frame {bBuild, bSort, bSign} c c' k ∧
      c'.nreg 40000 = D ∧ c'.nreg 42000 = c.nreg ALLOC ∧ c'.nreg 42001 = 2 * L.length ∧
      c'.nreg 43001 = B ∧ c'.nreg 43002 = L.length ∧ c'.nreg 43010 = 0 ∧ c'.nreg 43011 = 1 ∧
      RecsAt c'.nmem (c.nreg ALLOC) L ∧
      c.nreg ALLOC + 10 * L.length ≤ c'.nreg 30005 ∧
      c'.nreg 30005 + 2 * L.length ≤ c'.nreg ALLOC ∧
      ∃ E, seg c'.nmem (c'.nreg 30005) (2 * L.length) = E ∧
        E.Perm (List.range (2 * L.length)) ∧ E.Pairwise (codeLe M (Qof P) L) := by
  set A₀ := c.nreg ALLOC with hA₀
  set K := L.length with hKdef
  have hA : c.nreg 9999 = A₀ := rfl
  have hWn' : P.n + 3 ≤ W := by unfold hostWords at hWn; omega
  have hsc := SortR.sortCost_room 11010 (2 * K)
  have hroom' : A₀ + 32 * K + 22 + SortR.sortCost 11010 (2 * K) ≤ W := by
    unfold costA at hroom; omega
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
  obtain ⟨c₂, k₂, x₂, hk₂, hk₂', w₂, I₂, i₂⟩ := recLoop_exec (P := P) hCL hB rfl (by omega) hhW w₁ hI₁ r9
  -- the sort's inputs
  have hA₂ : c₂.nreg 9999 = A₀ + 10 * K := by rw [I₂.fr _ (Or.inl (by norm_num)), r8]
  have hS₂ : c₂.nreg 43031 = A₀ + 8 * K := by rw [I₂.fr _ (Or.inr (by norm_num)), r7]
  have hN₂ : c₂.nreg 42001 = 2 * K := by rw [I₂.fr _ (Or.inl (by norm_num)), r5]
  obtain ⟨c₃, k₃, x₃, hk₃, v30003, v30004, g₃, mm₃, rr₃, rm₃, out₃⟩ : ∃ c₃ k₃,
      Exec P W (block [.copyN 30003 43031, .copyN 30004 42001]) c₂ c₃ k₃ ∧ k₃ = 2 ∧
      c₃.nreg 30003 = A₀ + 8 * K ∧ c₃.nreg 30004 = 2 * K ∧
      (∀ r, r ≠ 30003 → r ≠ 30004 → c₃.nreg r = c₂.nreg r) ∧ c₃.nmem = c₂.nmem ∧
      c₃.rreg = c₂.rreg ∧ c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    have y1 := Exec.copyN (P := P) w₂ 30003 43031
    have y2 := Exec.copyN (P := P) y1.wb_right 30004 42001
    refine ⟨_, _, .seq y1 (.seq y2 (.skip y2.wb_right)), rfl, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl,
      rfl, rfl⟩
    · simp [hS₂]
    · simp [hN₂]
    · simp [h1, h2]
  have w₃ := x₃.wb_right
  have hA₃ : c₃.nreg 9999 = A₀ + 10 * K := by rw [g₃ _ (by norm_num) (by norm_num), hA₂]
  -- memory at the sort
  have mem₃ : ∀ a, c₃.nmem a = recMem c.nmem L A₀ (A₀ + 8 * K) K a := fun a => by
    rw [mm₃, I₂.mem, i₂]
  have hbelow : ∀ a, a < A₀ → c₃.nmem a = c.nmem a := fun a ha => by
    rw [mem₃]; unfold recMem; rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  have hrecs : RecsAt c₃.nmem A₀ L := recsAt_of fun q hq => by
    rw [mem₃]; unfold recMem; rw [ite_eq_left (by omega), show A₀ + q - A₀ = q by omega]
  have hlist : seg c₃.nmem (A₀ + 8 * K) (2 * K) = List.range (2 * K) := seg_range fun i hi => by
    rw [mem₃]; unfold recMem; rw [ite_eq_right (by omega), ite_eq_left (by omega)]; omega
  obtain ⟨hM₃, hwf₃⟩ := desc_agree hwf hM (m' := c₃.nmem) fun a ha => hbelow a ha
  have hwf₃' : ModelDescWF P (A₀ + 10 * K) c₃.nmem D := modelDescWF_mono hwf₃ (by omega)
  have hD₃ : c₃.nreg 40000 = D := by
    rw [g₃ _ (by norm_num) (by norm_num), I₂.fr _ (Or.inl (by norm_num)),
      fr₁ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num), hD]
  have hT₃ : c₃.nreg 42000 = A₀ := by
    rw [g₃ _ (by norm_num) (by norm_num), I₂.fr _ (Or.inl (by norm_num)), r6]
  have hN₃ : c₃.nreg 42001 = 2 * K := by rw [g₃ _ (by norm_num) (by norm_num), hN₂]
  -- the sort
  have hcmp := evCmp_ok (P := P) (W := W) hG hWn (A₀ := A₀ + 10 * K) (by omega) hwf₃' hM₃ hL
    hrecs (by omega) c₃.nreg
  have hJ₃ : EvJ c₃.nmem (A₀ + 10 * K) D A₀ (2 * K) c₃.nreg c₃ :=
    ⟨hD₃, hT₃, hN₃, fun _ _ => rfl, fun _ _ _ => rfl⟩
  have hJs : SortR.JStable (EvJ c₃.nmem (A₀ + 10 * K) D A₀ (2 * K) c₃.nreg) (c₃.nreg ALLOC) := by
    rw [show ALLOC = 9999 from rfl, hA₃]; exact evJ_stable _ _ _ _ _ _
  obtain ⟨c₄, k₄, x₄, hk₄, J₄, F₄, e₄, e₄', E, hE, hperm, hsort⟩ :=
    SortR.sortStmt_exec (P := P) (W := W) hcmp (by decide)
      (fun a b d h1 h2 => evLeB_trans M (Qof P) L _ a b d h1 h2)
      (fun a b => evLeB_total M (Qof P) L _ a b) w₃ hJ₃ hJs (List.range (2 * K))
      (by rw [List.length_range, v30003]; exact hlist) (by rw [List.length_range, v30004])
      (by rw [List.length_range, show ALLOC = 9999 from rfl, hA₃, v30003]; omega)
      (by rw [List.length_range, show ALLOC = 9999 from rfl, hA₃]; omega)
  rw [List.length_range] at hk₄ e₄' hE
  obtain ⟨j1, j2, j3, j4, j5⟩ := J₄
  have X : Exec P W phaseA c c₄ (k₁ + (k₂ + (k₃ + k₄))) := .seq x₁ (.seq x₂ (.seq x₃ x₄))
  obtain ⟨F1, F2, F3, F4, F5, F6, F7⟩ := F₄
  have hA₄ : A₀ + 10 * K ≤ c₄.nreg 9999 := by
    rw [show ALLOC = 9999 from rfl, hA₃] at F6; exact F6
  have hA₄' : c₄.nreg 9999 ≤ A₀ + 10 * K + k₄ := by
    rw [show ALLOC = 9999 from rfl, hA₃] at F7; exact F7
  rw [show ALLOC = 9999 from rfl, hA₃] at F3 F4
  refine ⟨c₄, _, X, by unfold costA; omega, x₄.wb_right, ⟨fun r hr hra => ?_, fun r hr => ?_,
    fun a ha => ?_, fun a ha => ?_, ?_, ?_, ?_⟩, j1, j2, j3, ?_, ?_, ?_, ?_,
    fun c hc => ?_, ?_, e₄', E, hE, hperm, ?_⟩
  · -- registers outside the bands
    obtain ⟨hr3, hr'⟩ := band_out hr
    have hra' : r ≠ 9999 := hra
    rw [F1 r hr3 hra, g₃ _ (by omega) (by omega), I₂.fr _ (by omega)]
    exact fr₁ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) hra' (by omega) (by omega) (by omega) (by omega) (by omega)
  · rw [F2 r (band_out hr).1, rr₃, I₂.rr, rr₁]
  · have ha' : a < A₀ := ha
    rw [F3 a (lt_of_lt_of_le ha' (Nat.le_add_right _ _))]
    exact hbelow a ha'
  · have ha' : a < A₀ := ha
    rw [F4 a (lt_of_lt_of_le ha' (Nat.le_add_right _ _)), rm₃, I₂.rm, rm₁]
  · rw [F5, out₃, I₂.out, out₁]
  · show A₀ ≤ c₄.nreg 9999; omega
  · show c₄.nreg 9999 ≤ A₀ + _; omega
  · rw [j5 _ (by norm_num) (by norm_num), g₃ _ (by norm_num) (by norm_num),
      I₂.fr _ (Or.inl (by norm_num)), r1]
  · rw [j5 _ (by norm_num) (by norm_num), g₃ _ (by norm_num) (by norm_num), I₂.rK]
  · rw [j5 _ (by norm_num) (by norm_num), g₃ _ (by norm_num) (by norm_num), I₂.r0]
  · rw [j5 _ (by norm_num) (by norm_num), g₃ _ (by norm_num) (by norm_num), I₂.r1]
  · obtain ⟨a1, a2, a3, a4⟩ := hrecs c hc
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [j4 _ (by omega)] <;> assumption
  · rw [show ALLOC = 9999 from rfl, hA₃] at e₄; omega
  · have hnd : E.Nodup := hperm.nodup_iff.2 List.nodup_range
    refine (hsort.and hnd).imp_of_mem fun {a b} ha hb hab => ?_
    have ha' := List.mem_range.1 (hperm.mem_iff.1 ha)
    have hb' := List.mem_range.1 (hperm.mem_iff.1 hb)
    have := hab.1
    unfold evLeB at this
    rw [ite_eq_left ha', ite_eq_left hb'] at this
    exact @of_decide_eq_true _ (Classical.propDecidable _) this

end exec

end

end BuildRam

end Chazelle.Core
