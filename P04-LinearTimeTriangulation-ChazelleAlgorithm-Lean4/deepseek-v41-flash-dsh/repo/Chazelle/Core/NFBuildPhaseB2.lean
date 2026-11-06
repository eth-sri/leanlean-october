module

public import Chazelle.Golf

public import Chazelle.Golf

public import Chazelle.Core.NFBuildPhaseB1

/-!
# WP-C (BuildNF), RAM part 23: the region phase

`regPhase_exec`: from the tables of the main pass (chord table at `CT`, arc table at `AT`,
weights at `WT`), the region phase (counts, records, lists, sequence table, header) writes the
normal form `buildNF M Q L E` at `H`.
-/

namespace Chazelle.Core

namespace BuildRam

open Machine Machine.Stmt Programs SignK NFLoc
open BuildNF (cf af chordRec arcRec gapStarts keyA wA upC dnC)

@[expose] public section

/-- The region phase. -/
def regPhase : Stmt :=
  .seq (.instr (.constN 43201 0)) (.seq zeroLoop (.seq (.instr (.constN 43201 0))
    (.seq arcCntLoop (.seq (.instr (.constN 43201 0)) (.seq chCntLoop
      (.seq (block [.constN 43201 0, .constN 43210 0]) (.seq regRecLoop
        (.seq (.instr (.constN 43201 0)) (.seq arcFillLoop (.seq (.instr (.constN 43201 0))
          (.seq chFillLoop (.seq (.instr (.constN 43201 0)) (.seq seqLoop hdrB)))))))))))))

/-- The registers the region phase writes. -/
def BregPhase (r : ℕ) : Bool :=
  decide (43201 ≤ r ∧ r < 43232) || decide (r = 40003)

theorem wr_regPhase : wrM BregPhase regPhase = true := by
  have h1 := wrM_mono (B' := BregPhase) (fun r hr => by
    ϴ' decide_eq_true_eq at hr; simp only [BregPhase, Bool.or_eq_true,
      decide_eq_true_eq]; omega) wr_zeroLoop
  have h2 := wrM_mono (B' := BregPhase) (fun r hr => by
    ϴ' decide_eq_true_eq at hr; simp only [BregPhase, Bool.or_eq_true,
      decide_eq_true_eq]; omega) wr_arcCntLoop
  have h3 := wrM_mono (B' := BregPhase) (fun r hr => by
    ϴ' decide_eq_true_eq at hr; simp only [BregPhase, Bool.or_eq_true,
      decide_eq_true_eq]; omega) wr_chCntLoop
  have h4 := wrM_mono (B' := BregPhase) (fun r hr => by
    ϴ' BregRec, Bool.or_eq_true, decide_eq_true_eq at hr
    simp only [BregPhase, Bool.or_eq_true, decide_eq_true_eq]; omega) wr_regRecLoop
  have h5 := wrM_mono (B' := BregPhase) (fun r hr => by
    ϴ' decide_eq_true_eq at hr; simp only [BregPhase, Bool.or_eq_true,
      decide_eq_true_eq]; omega) wr_arcFillLoop
  have h6 := wrM_mono (B' := BregPhase) (fun r hr => by
    ϴ' decide_eq_true_eq at hr; simp only [BregPhase, Bool.or_eq_true,
      decide_eq_true_eq]; omega) wr_chFillLoop
  have h7 := wrM_mono (B' := BregPhase) (fun r hr => by
    ϴ' decide_eq_true_eq at hr; simp only [BregPhase, Bool.or_eq_true,
      decide_eq_true_eq]; omega) wr_seqLoop
  have h8 := wrM_mono (B' := BregPhase) (fun r hr => by
    ϴ' decide_eq_true_eq at hr; simp only [BregPhase, Bool.or_eq_true,
      decide_eq_true_eq]; omega) wr_hdrB
  ϴ regPhase, wrM, block, h1, h2, h3, h4, h5, h6, h7, h8, Bool.and_true, Bool.true_and
  decide

section exec

variable {P : Polygon} {W : ℕ}


/-- **The region phase.** -/
theorem regPhase_exec (d : Config) (hw : WordsBounded W d) {D T B H lo hd kd K A : ℕ}
    (C : BConst D T K B H lo hd kd d) (hA : d.nreg 43102 = A) (hAle : A ≤ 2 * K)
    {keyF uF vF wF : ℕ → ℕ}
    (hkey : ∀ j, j < A → d.nmem (H + 12 + 5 * K + 5 * j) = keyF j)
    (hkR : ∀ j, j < A → keyF j < K + 1)
    (hwt : ∀ j, j < A → d.nmem (H + 17 + 28 * K + j) = wF j)
    (hu : ∀ i, i < K → d.nmem (H + 12 + 5 * i + 3) = uF i)
    (hv : ∀ i, i < K → d.nmem (H + 12 + 5 * i + 4) = vF i)
    (huR : ∀ i, i < K → uF i < K + 1) (hvR : ∀ i, i < K → vF i < K + 1)
    (hroom : H + sizeB K ≤ W) :
    ∃ d' k, Exec P W regPhase d d' k ∧ k ≤ 200 * K + 150 ∧ 26 * (K + 1) ≤ k ∧
      WordsBounded W d' ∧ FrameM BregPhase d d' ∧ d'.nreg 40003 = H ∧
      (∀ f, f < 12 → d'.nmem (H + f) = hdrW K A (K + 1) (H + 12) (H + 12 + 5 * K)
        (H + 12 + 15 * K) (H + 17 + 20 * K) (H + 17 + 22 * K) H f) ∧
      (∀ a, (a < H ∨ (H + 12 ≤ a ∧ a < H + 12 + 15 * K)) → d'.nmem a = d.nmem a) ∧
      (∀ r, r < K + 1 → ∀ f, f < 5 → d'.nmem (H + 12 + 15 * K + 5 * r + f) =
        rtv (cntF keyF A) (cnt2F uF vF K) (wmaxF keyF wF A) (5 * r + f)) ∧
      (∀ r, r < K + 1 → ∀ t, t < cntF keyF A r →
        d'.nmem (H + 17 + 22 * K + offF (cntF keyF A) (cnt2F uF vF K) r + t) =
          (lstF keyF A r).getD t 0) ∧
      (∀ r, r < K + 1 → ∀ t, t < cnt2F uF vF K r →
        d'.nmem (H + 17 + 22 * K + (offF (cntF keyF A) (cnt2F uF vF K) r + cntF keyF A r) + t) =
          (lst2F uF vF K r).getD t 0) ∧
      (∀ j, j < A → d'.nmem (H + 17 + 20 * K + j) = j) := by
  set m₃ := d.nmem with hm₃
  have hS := hroom; unfold sizeB at hS
  have hW1 : 1 ≤ W := ⋄
  -- the memory functions
  have ckey : cntF (fun j => m₃ (H + 12 + 5 * K + 5 * j)) A = cntF keyF A := cntF_congr hkey
  have cwmax : wmaxF (fun j => m₃ (H + 12 + 5 * K + 5 * j)) (fun j => m₃ (H + 17 + 28 * K + j)) A =
      wmaxF keyF wF A := wmaxF_congr hkey hwt
  have cc2 : cnt2F (fun i => m₃ (H + 12 + 5 * i + 3)) (fun i => m₃ (H + 12 + 5 * i + 4)) K =
      cnt2F uF vF K := cnt2F_congr hu hv
  have hkR' : ∀ j, j < A → m₃ (H + 12 + 5 * K + 5 * j) < K + 1 := fun j hj => by
    rw [hkey j hj]; exact hkR j hj
  -- 0/1. zero the arrays
  have z0 := Exec.constN (P := P) hw 43201 0 (Nat.zero_le _)
  set e₀ : Config := { d with nreg := upd d.nreg 43201 0 } with he₀
  have C₀ : BConst D T K B H lo hd kd e₀ := C.frame (Bw := fun r => decide (r = 43201))
    (exec_frameM z0 (⌖)) (⌖)
  obtain ⟨e₁, k₁, x₁, hk₁, w₁, f₁, m₁⟩ := zeroLoop_exec (P := P) e₀ z0.wb_right (m₀ := m₃)
    (CA := H + 17 + 30 * K) (R := K + 1) (fA := fun r => m₃ (H + 17 + 30 * K + r))
    (fC := fun r => m₃ (H + 17 + 30 * K + (K + 1) + r))
    (fW := fun r => m₃ (H + 17 + 30 * K + 2 * (K + 1) + r)) C₀.rCA C₀.rR C₀.r0 C₀.r1
    (by rw [he₀]; simp) (⋄) (by rw [he₀]; exact (regMem_self _ _ _).symm)
  have C₁ := C₀.frame f₁ (⌖)
  -- 2. arc counts
  have z2 := Exec.constN (P := P) w₁ 43201 0 (Nat.zero_le _)
  set e₂ : Config := { e₁ with nreg := upd e₁.nreg 43201 0 } with he₂
  have C₂ : BConst D T K B H lo hd kd e₂ := C₁.frame (Bw := fun r => decide (r = 43201))
    (exec_frameM z2 (⌖)) (⌖)
  have hA₂ : e₂.nreg 43102 = A := by
    show upd e₁.nreg 43201 0 43102 = A
    rw [upd_other _ _ _ (⊛), f₁.1 43102 (⌖), he₀]; Θ hA
  obtain ⟨e₃, k₃, x₃, hk₃, w₃, f₃, m₃'⟩ := arcCntLoop_exec (P := P) e₂ z2.wb_right (m₀ := m₃)
    (CA := H + 17 + 30 * K) (R := K + 1) (A := A) (AT := H + 12 + 5 * K)
    (WT := H + 17 + 28 * K) (fC := fun _ => 0) C₂.rCA C₂.rR C₂.r1 (by rw [he₂]; simp) hA₂
    C₂.rAT C₂.rWT (⋄) (⋄) (⋄) hkR' (by rw [he₂]; exact m₁)
  have C₃ := C₂.frame f₃ (⌖)
  -- 3. chord counts
  have z4 := Exec.constN (P := P) w₃ 43201 0 (Nat.zero_le _)
  set e₄ : Config := { e₃ with nreg := upd e₃.nreg 43201 0 } with he₄
  have C₄ : BConst D T K B H lo hd kd e₄ := C₃.frame (Bw := fun r => decide (r = 43201))
    (exec_frameM z4 (⌖)) (⌖)
  obtain ⟨e₅, k₅, x₅, hk₅, w₅, f₅, m₅⟩ := chCntLoop_exec (P := P) e₄ z4.wb_right (m₀ := m₃)
    (CA := H + 17 + 30 * K) (R := K + 1) (K := K) (CT := H + 12)
    (fA := cntF (fun j => m₃ (H + 12 + 5 * K + 5 * j)) A)
    (fW := wmaxF (fun j => m₃ (H + 12 + 5 * K + 5 * j)) (fun j => m₃ (H + 17 + 28 * K + j)) A)
    C₄.rCA C₄.rR C₄.r1 C₄.r3 (by rw [he₄]; simp) C₄.rK C₄.rCT (⋄) (⋄)
    (fun i hi => by rw [hu i hi]; exact huR i hi) (fun i hi => by rw [hv i hi]; exact hvR i hi)
    (by rw [he₄]; exact m₃')
  have C₅ := C₄.frame f₅ (⌖)
  have hA₅ : e₅.nreg 43102 = A := by
    Ξ f₅.1 43102 (⌖)
    show upd e₃.nreg 43201 0 43102 = A
    Ξ upd_other _ _ _ (⊛), f₃.1 43102 (⌖), hA₂
  -- abbreviations of the counts
  obtain ⟨cA, hcA⟩ : ∃ f : ℕ → ℕ, f = cntF (fun j => m₃ (H + 12 + 5 * K + 5 * j)) A := ⟨_, rfl⟩
  obtain ⟨cC, hcC⟩ : ∃ f : ℕ → ℕ,
      f = cnt2F (fun i => m₃ (H + 12 + 5 * i + 3)) (fun i => m₃ (H + 12 + 5 * i + 4)) K :=
    ⟨_, rfl⟩
  obtain ⟨wR, hwR⟩ : ∃ f : ℕ → ℕ, f = wmaxF (fun j => m₃ (H + 12 + 5 * K + 5 * j))
      (fun j => m₃ (H + 17 + 28 * K + j)) A := ⟨_, rfl⟩
  Ξ' ← hcA, ← hcC, ← hwR at m₅
  have hoffR : offF cA cC (K + 1) ≤ A + 2 * K := by
    rw [hcA, hcC]; exact offF_R_le _ _ _ hkR'
  -- 4. region records
  have y1 := Exec.constN (P := P) w₅ 43201 0 (Nat.zero_le _)
  have y2 := Exec.constN (P := P) y1.wb_right 43210 0 (Nat.zero_le _)
  have X6 : Exec P W (block [.constN 43201 0, .constN 43210 0]) e₅ _ 2 :=
    .seq y1 (.seq y2 (.skip y2.wb_right))
  set e₆ := { ({ e₅ with nreg := upd e₅.nreg 43201 0 } : Config) with
    nreg := upd (upd e₅.nreg 43201 0) 43210 0 } with he₆
  have C₆ : BConst D T K B H lo hd kd e₆ := C₅.frame (Bw := fun r => decide (r = 43201 ∨ r = 43210))
    (exec_frameM X6 (⌖)) (⌖)
  obtain ⟨e₇, k₇, x₇, hk₇, hk₇', w₇, f₇, m₇⟩ := regRecLoop_exec (P := P) e₆ X6.wb_right
    (m₀ := m₃) (CA := H + 17 + 30 * K) (R := K + 1) (RT := H + 12 + 15 * K)
    (FA := H + 20 + 33 * K) (cA := cA) (cC := cC) (wR := wR) C₆.rCA C₆.rR C₆.r1
    (by rw [he₆]; simp) (by rw [he₆]; simp) C₆.rRT C₆.rFA (⋄) (⋄) (⋄)
    ⟨⋄, ⋄⟩ (⋄) (⋄) (by rw [he₆]; exact m₅)
  have C₇ := C₆.frame f₇ (⌖)
  have hA₇ : e₇.nreg 43102 = A := by
    Ξ f₇.1 43102 (⌖), he₆
    show upd (upd e₅.nreg 43201 0) 43210 0 43102 = A
    Ξ upd_other _ _ _ (⊛), upd_other _ _ _ (⊛), hA₅
  obtain ⟨mem₇, hmem₇⟩ : ∃ f : ℕ → ℕ, f = recRMem (regMem m₃ (H + 17 + 30 * K) (K + 1) cA cC wR)
      (H + 12 + 15 * K) (H + 20 + 33 * K) (K + 1) cA cC wR (K + 1) := ⟨_, rfl⟩
  Ξ' ← hmem₇ at m₇
  have r₇ : ∀ a, (a < H + 12 + 15 * K ∨ (H + 17 + 20 * K ≤ a ∧ a < H + 17 + 30 * K)) →
      mem₇ a = m₃ a := fun a ha => by
    rw [hmem₇]; unfold recRMem
    Ξ ite_eq_right (⋄), ite_eq_right (⋄), ite_eq_right (⋄), regMem_out _ _ _ _ _ _ (⋄)
  have rFA₇ : ∀ r, r < K + 1 → mem₇ (H + 20 + 33 * K + r) = offF cA cC r := fun r hr => by
    rw [hmem₇]; unfold recRMem
    rw [ite_eq_right (⋄), ite_eq_left (⋄), show H + 20 + 33 * K + r - (H + 20 + 33 * K) = r by
      omega]
  have rFC₇ : ∀ r, r < K + 1 → mem₇ (H + 20 + 33 * K + (K + 1) + r) = offF cA cC r + cA r :=
    fun r hr => by
    rw [hmem₇]; unfold recRMem
    rw [ite_eq_right (⋄), ite_eq_right (⋄), ite_eq_left (⋄),
      show H + 20 + 33 * K + (K + 1) + r - (H + 20 + 33 * K + (K + 1)) = r by omega]
  have rRT₇ : ∀ r, r < K + 1 → ∀ f, f < 5 →
      mem₇ (H + 12 + 15 * K + 5 * r + f) = rtv cA cC wR (5 * r + f) := fun r hr f hf => by
    rw [hmem₇]; unfold recRMem
    rw [ite_eq_left (⋄), show H + 12 + 15 * K + 5 * r + f - (H + 12 + 15 * K) = 5 * r + f by
      omega]
  -- 5. the arc lists
  have z8 := Exec.constN (P := P) w₇ 43201 0 (Nat.zero_le _)
  set e₈ : Config := { e₇ with nreg := upd e₇.nreg 43201 0 } with he₈
  have C₈ : BConst D T K B H lo hd kd e₈ := C₇.frame (Bw := fun r => decide (r = 43201))
    (exec_frameM z8 (⌖)) (⌖)
  have hA₈ : e₈.nreg 43102 = A := by
    show upd e₇.nreg 43201 0 43102 = A
    Ξ upd_other _ _ _ (⊛), hA₇
  have hoffR' : H + 17 + 22 * K + offF (cntF (fun j => m₃ (H + 12 + 5 * K + 5 * j)) A) cC (K + 1)
      ≤ H + 17 + 26 * K := by rw [← hcA]; omega
  obtain ⟨e₉, k₉, x₉, hk₉, w₉, f₉, a1, a2, a3⟩ := arcFillLoop_exec (P := P) e₈ z8.wb_right
    (m₂ := mem₇) (A := A) (R := K + 1) (AT := H + 12 + 5 * K) (FA := H + 20 + 33 * K)
    (LT := H + 17 + 22 * K) (key := fun j => m₃ (H + 12 + 5 * K + 5 * j)) (cC := cC)
    hA₈ C₈.rR C₈.r1 (by rw [he₈]; simp) C₈.rAT C₈.rFA C₈.rLT
    (fun j hj => r₇ _ (⋄)) hkR' (fun r hr => Ρ rFA₇ r hr, hcA) (⋄) (⋄)
    (⋄) (⋄) (⋄) (⋄) (by rw [he₈]; exact m₇)
  Ξ' ← hcA at a1 a2 a3
  have C₉ := C₈.frame f₉ (⌖)
  have hA₉ : e₉.nreg 43102 = A := Ρ f₉.1 43102 (⌖), hA₈
  have hoffA : ∀ r, r < K + 1 → ∀ t, t < cA r → offF cA cC r + t < offF cA cC (K + 1) :=
    fun r hr t ht => by
    have := offF_succ cA cC r
    have := offF_mono cA cC (show r + 1 ≤ K + 1 by omega)
    omega
  have hoffC : ∀ r, r < K + 1 → ∀ t, t < cC r → offF cA cC r + cA r + t < offF cA cC (K + 1) :=
    fun r hr t ht => by
    have := offF_succ cA cC r
    have := offF_mono cA cC (show r + 1 ≤ K + 1 by omega)
    omega
  -- memory after the arc lists, outside the pointers and the arc cells
  have r₉ : ∀ a, (a < H + 17 + 22 * K ∨ H + 17 + 26 * K ≤ a) → (a < H + 20 + 33 * K ∨
      H + 21 + 34 * K ≤ a) → e₉.nmem a = mem₇ a := fun a h1 h2 =>
    a3 a (⋄) (fun r hr t ht => by have := hoffA r hr t ht; omega)
  have hu₉ : ∀ i, i < K → e₉.nmem (H + 12 + 5 * i + 3) = uF i := fun i hi => by
    Ξ r₉ _ (⋄) (⋄), r₇ _ (⋄), hu i hi
  have hv₉ : ∀ i, i < K → e₉.nmem (H + 12 + 5 * i + 4) = vF i := fun i hi => by
    Ξ r₉ _ (⋄) (⋄), r₇ _ (⋄), hv i hi
  have ccC : cnt2F (fun i => e₉.nmem (H + 12 + 5 * i + 3)) (fun i => e₉.nmem (H + 12 + 5 * i + 4))
      K = cC := Ρ cnt2F_congr hu₉ hv₉, hcC, cc2
  -- 6. the chord lists
  have z10 := Exec.constN (P := P) w₉ 43201 0 (Nat.zero_le _)
  set e₁₀ : Config := { e₉ with nreg := upd e₉.nreg 43201 0 } with he₁₀
  have C₁₀ : BConst D T K B H lo hd kd e₁₀ := C₉.frame (Bw := fun r => decide (r = 43201))
    (exec_frameM z10 (⌖)) (⌖)
  obtain ⟨e₁₁, k₁₁, x₁₁, hk₁₁, w₁₁, f₁₁, FI⟩ := chFillLoop_exec (P := P) e₁₀ z10.wb_right
    (m₃ := e₉.nmem) (K := K) (R := K + 1) (CT := H + 12) (FC := H + 21 + 34 * K)
    (LT := H + 17 + 22 * K) (b := fun r => offF cA cC r + cA r) C₁₀.rK C₁₀.r1 C₁₀.r3
    (by rw [he₁₀]; simp) C₁₀.rCT C₁₀.rFC C₁₀.rLT
    (fun i hi => by rw [hu₉ i hi]; exact huR i hi) (fun i hi => by rw [hv₉ i hi]; exact hvR i hi)
    (fun r hr => by
      rw [r₉ _ (⋄) (⋄), show H + 21 + 34 * K + r = H + 20 + 33 * K + (K + 1) + r by
        omega, rFC₇ r hr])
    (fun r r' h1 h2 => by
      Ξ ccC
      have := offF_succ cA cC r
      have := offF_mono cA cC (show r + 1 ≤ r' by omega)
      omega)
    (fun r hr t ht => by rw [ccC] at ht; have := hoffC r hr t ht; omega)
    (fun r hr t ht => by rw [ccC] at ht; have := hoffC r hr t ht; omega)
    (fun r hr => ⋄) (⋄) (⋄) (Ρ he₁₀)
  Ξ' ccC at FI
  have C₁₁ := C₁₀.frame f₁₁ (⌖)
  have hA₁₁ : e₁₁.nreg 43102 = A := by
    Ξ f₁₁.1 43102 (⌖)
    show upd e₉.nreg 43201 0 43102 = A
    Ξ upd_other _ _ _ (⊛), hA₉
  -- 7. the sequence table
  have z12 := Exec.constN (P := P) w₁₁ 43201 0 (Nat.zero_le _)
  set e₁₂ : Config := { e₁₁ with nreg := upd e₁₁.nreg 43201 0 } with he₁₂
  have C₁₂ : BConst D T K B H lo hd kd e₁₂ := C₁₁.frame (Bw := fun r => decide (r = 43201))
    (exec_frameM z12 (⌖)) (⌖)
  obtain ⟨e₁₃, k₁₃, x₁₃, hk₁₃, w₁₃, f₁₃, m₁₃⟩ := seqLoop_exec (P := P) e₁₂ z12.wb_right
    (A := A) (QT := H + 17 + 20 * K)
    (by show upd e₁₁.nreg 43201 0 43102 = A; rw [upd_other _ _ _ (⊛), hA₁₁])
    C₁₂.rQT C₁₂.r1 (by rw [he₁₂]; simp) (⋄)
  have C₁₃ := C₁₂.frame f₁₃ (⌖)
  have hA₁₃ : e₁₃.nreg 43102 = A := by
    Ξ f₁₃.1 43102 (⌖)
    show upd e₁₁.nreg 43201 0 43102 = A
    Ξ upd_other _ _ _ (⊛), hA₁₁
  -- 8. the header
  obtain ⟨e₁₄, k₁₄, x₁₄, hk₁₄, w₁₄, f₁₄, h40003, hh1, hh2⟩ := hdrB_exec (P := P) e₁₃ w₁₃
    (K := K) (A := A) (R := K + 1) (CT := H + 12) (AT := H + 12 + 5 * K) (RT := H + 12 + 15 * K)
    (QT := H + 17 + 20 * K) (LT := H + 17 + 22 * K) (H := H) C₁₃.rH C₁₃.rK hA₁₃ C₁₃.rR C₁₃.rCT
    C₁₃.rAT C₁₃.rRT C₁₃.rQT C₁₃.rLT C₁₃.r0 C₁₃.r1 (⋄)
  have X : Exec P W regPhase d e₁₄ _ :=
    .seq z0 (.seq x₁ (.seq z2 (.seq x₃ (.seq z4 (.seq x₅ (.seq X6 (.seq x₇ (.seq z8 (.seq x₉
      (.seq z10 (.seq x₁₁ (.seq z12 (.seq x₁₃ x₁₄)))))))))))))
  -- the memory of `e₁₄` through the later writes
  have back : ∀ a, (a < H ∨ H + 12 ≤ a) → (a < H + 17 + 20 * K ∨ H + 17 + 20 * K + A ≤ a) →
      (a < H + 21 + 34 * K ∨ H + 21 + 34 * K + (K + 1) ≤ a) →
      (∀ r, r < K + 1 → ∀ t, t < cC r → a ≠ H + 17 + 22 * K + (offF cA cC r + cA r) + t) →
      e₁₄.nmem a = e₉.nmem a := fun a h1 h2 h3 h4 => by
    Ξ hh2 a h1, m₁₃
    unfold seqMem
    Ξ ite_eq_right (⋄)
    exact FI.rest a h3 h4
  have notch : ∀ a, (a < H + 17 + 22 * K ∨ H + 17 + 26 * K ≤ a) →
      ∀ r, r < K + 1 → ∀ t, t < cC r → a ≠ H + 17 + 22 * K + (offF cA cC r + cA r) + t :=
    fun a ha r hr t ht => by have := hoffC r hr t ht; omega
  have ecA : cA = cntF keyF A := Ρ hcA, ckey
  have ecC : cC = cnt2F uF vF K := Ρ hcC, cc2
  have ewR : wR = wmaxF keyF wF A := Ρ hwR, cwmax
  refine ⟨e₁₄, _, X, ⋄, ⋄, w₁₄, exec_frameM X wr_regPhase, h40003, hh1,
    fun a ha => ?_, fun r hr f hf => ?_, fun r hr t ht => ?_, fun r hr t ht => ?_, fun j hj => ?_⟩
  · -- below `H` and the chord and arc tables
    rcases ha with ha | ha
    · rw [back a (⋄) (⋄) (⋄) (notch a (⋄)), r₉ a (⋄) (⋄),
        r₇ a (⋄)]
    · rw [back a (⋄) (⋄) (⋄) (notch a (⋄)), r₉ a (⋄) (⋄),
        r₇ a (⋄)]
  · -- the region table
    rw [back _ (⋄) (⋄) (⋄) (notch _ (⋄)), r₉ _ (⋄) (⋄),
      rRT₇ r hr f hf, ecA, ecC, ewR]
  · -- the arc lists
    Ξ' ← ecA at ht
    Ξ ← ecA, ← ecC
    have hlt := hoffA r hr t ht
    rw [back _ (⋄) (⋄) (⋄) (fun r' hr' t' ht' => by
      rcases Nat.lt_trichotomy r' r with h' | rfl | h'
      · have := offF_succ cA cC r'
        have := offF_mono cA cC (show r' + 1 ≤ r by omega)
        omega
      · omega
      · have := offF_succ cA cC r
        have := offF_mono cA cC (show r + 1 ≤ r' by omega)
        omega), a2 r hr t ht, lstF_congr hkey]
  · -- the chord lists
    Ξ' ← ecC at ht
    Ξ ← ecA, ← ecC
    have hlt := hoffC r hr t ht
    Ξ hh2 _ (⋄), m₁₃
    unfold seqMem
    Ξ ite_eq_right (⋄), FI.cells r hr t ht, lst2F_congr hu₉ hv₉
  · -- the sequence table
    Ξ hh2 _ (⋄), m₁₃
    unfold seqMem
    Ξ ite_eq_left (⋄)
    omega

end exec

end

end BuildRam

end Chazelle.Core
