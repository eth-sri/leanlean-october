module

public import Chazelle.Machine.FrameFields

meta import Chazelle.Programs.RamEval

public import Chazelle.Core.FuseAsmSweep

/-!
# WP-F fusion assembly, part 24: collecting the answers of both sweeps

`collectS` runs `clqLoop` on the query and result lists of side `0` (bases in `70150`, `70153`,
count in `70152`) and then of side `1` (`70151`, `70155`, `70154`): the list
`collectQ L₀ R₀ ++ collectQ L₁ R₁` at the allocator (base saved in `70156`, length in `70110`)
(`collectS_exec`).
-/

namespace Chazelle.Core

namespace FuseAsm

open Machine Machine.Stmt Programs SignK

@[expose] public section

theorem resultList_agree {m m' : ℕ → ℕ} {B E : ℕ} {R : List (ℕ × ℕ × ℕ × ℕ)}
    (h : ResultListAt m B R) (hE : B + 4 * R.length ≤ E) (he : MemEqBelow E m' m) :
    ResultListAt m' B R := fun i hi => by
  obtain ⟨h0, h1, h2, h3⟩ := h i hi
  exact ⟨by ram_simp [he] <;> omega, by ram_simp [he] <;> omega,
    by ram_simp [he] <;> omega, by ram_simp [he] <;> omega⟩

/-- The arguments of the first collection loop. -/
def clSet : Stmt := block [.constN 70110 0, .constN 70116 3, .constN 70117 4, .constN 70118 2,
  .copyN 70156 ALLOC, .copyN 70111 70152, .constN 70112 0, .copyN 70113 70153,
  .copyN 70115 70150]

/-- The arguments of the second collection loop. -/
def clSet2 : Stmt := block [.copyN 70111 70154, .constN 70112 0, .copyN 70113 70155,
  .copyN 70115 70151]

/-- **The collection.** -/
def collectS : Stmt := .seq clSet (.seq clqLoop (.seq clSet2 clqLoop))

set_option maxHeartbeats 16000000 in
theorem collectS_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c)
    {L₀ L₁ : List (ℕ × ℕ × ℕ)} {R₀ R₁ : List (ℕ × ℕ × ℕ × ℕ)}
    (h05 : c.nreg 70105 = 1) (h08 : c.nreg 70108 = 0)
    (hL₀ : ChordListAt c.nmem (c.nreg 70150) L₀) (hn₀ : c.nreg 70152 = L₀.length)
    (hR₀ : ResultListAt c.nmem (c.nreg 70153) R₀) (hl₀ : R₀.length = L₀.length)
    (hb₀ : c.nreg 70150 + 3 * L₀.length ≤ c.nreg ALLOC)
    (hb₀' : c.nreg 70153 + 4 * R₀.length ≤ c.nreg ALLOC)
    (hL₁ : ChordListAt c.nmem (c.nreg 70151) L₁) (hn₁ : c.nreg 70154 = L₁.length)
    (hR₁ : ResultListAt c.nmem (c.nreg 70155) R₁) (hl₁ : R₁.length = L₁.length)
    (hb₁ : c.nreg 70151 + 3 * L₁.length ≤ c.nreg ALLOC)
    (hb₁' : c.nreg 70155 + 4 * R₁.length ≤ c.nreg ALLOC)
    (hroom : c.nreg ALLOC + 30 * (L₀.length + L₁.length) + 40 ≤ W) :
    ∃ c' k, Exec P W collectS c c' k ∧ k ≤ 24 * (L₀.length + L₁.length) + 20 ∧
      c'.nreg 70156 = c.nreg ALLOC ∧
      c'.nreg 70110 = (collectQ L₀ R₀ ++ collectQ L₁ R₁).length ∧
      c'.nreg ALLOC = c.nreg ALLOC + 3 * (collectQ L₀ R₀ ++ collectQ L₁ R₁).length ∧
      ChordListAt c'.nmem (c.nreg ALLOC) (collectQ L₀ R₀ ++ collectQ L₁ R₁) ∧
      Frame FB c c' k ∧
      (∀ r, (r < 70110 ∨ 70119 < r) → r ≠ 70156 → r ≠ ALLOC → c'.nreg r = c.nreg r) := by
  obtain ⟨A, hA⟩ := exists_eq' (a' := c.nreg ALLOC)
  have hA' := hA
  obtain ⟨c₁, k₁, e₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W clSet c c₁ k₁ ∧ k₁ = 9 ∧
      (c₁.nreg 70110 = 0 ∧ c₁.nreg 70116 = 3 ∧ c₁.nreg 70117 = 4 ∧ c₁.nreg 70118 = 2 ∧
        c₁.nreg 70156 = A ∧ c₁.nreg 70111 = L₀.length ∧ c₁.nreg 70112 = 0 ∧
        c₁.nreg 70113 = c.nreg 70153 ∧ c₁.nreg 70115 = c.nreg 70150 ∧
        (∀ r, (r < 70110 ∨ 70119 < r) → r ≠ 70156 → c₁.nreg r = c.nreg r) ∧
        Machine.NatRegFrame c c₁) := by
    unfold clSet
    exec_block
    all_goals try omega
    refine ⟨rfl, ?_⟩
    simp (disch := omega) only [Machine.upd_same, Machine.upd_other, hA', hn₀, ALLOC]
    and_intros
    all_goals first | trivial | rfl |
      (intro r h1 h2; simp (disch := omega) only [Machine.upd_other])
  obtain ⟨t10, t16, t17, t18, t56, t11, t12, t13, t15, tr, tm, trr, trm, tou⟩ := q
  have w₁ := e₁.wb_right
  have a₁ : c₁.nreg ALLOC = A := by ram_finish
  have c05 : c₁.nreg 70105 = 1 := by ram_finish
  have c08 : c₁.nreg 70108 = 0 := by ram_finish
  -- the first loop
  have I0 : CLQI W L₀ R₀ (c.nreg 70150) (c.nreg 70153) A [] c₁ c₁ :=
    ⟨w₁, by omega, by rw [t13, t12]; ring, by rw [t15, t12]; ring,
      by rw [a₁, t12]; simp [collectQ], by ram_finish,
      fun _ _ _ _ _ _ _ _ => rfl, fun _ _ => rfl, by rw [t12]; simp [collectQ]; intro i hi; simp at hi,
      rfl, rfl, rfl⟩
  obtain ⟨c₂, k₂, e₂, hk₂, hk₂', I₂, h₂⟩ := clqLoop_exec (P := P) (L := L₀) (R := R₀)
    (pre := []) c05 c08 t16 t17 t18 (by rw [t11, hl₀]) hl₀.symm
    (by rwa [tm]) (by rwa [tm]) (by omega) (by omega)
    (by simp only [List.length_nil]; omega) (by simp only [List.length_nil]; omega)
    R₀.length c₁ I0 (by rw [t12]; simp)
  have tk0 : L₀.take (c₂.nreg 70112) = L₀ := by simp_all <;> omega
  have tk0' : R₀.take (c₂.nreg 70112) = R₀ := by rw [h₂]; exact List.take_of_length_le le_rfl
  have i2a := I₂.alloc
  have i2c := I₂.cnt
  have i2l := I₂.list
  rw [tk0, tk0'] at i2a i2c i2l
  have w₂ := I₂.wb
  set C₀ := collectQ L₀ R₀ with hC₀
  have hC₀l : C₀.length ≤ L₀.length := collectQ_length_le _ _
  have g₂ := I₂.regs
  -- the second loop
  obtain ⟨c₃, k₃, e₃, hk₃, q⟩ : ∃ c₃ k₃, Exec P W clSet2 c₂ c₃ k₃ ∧ k₃ = 4 ∧
      (c₃.nreg 70111 = L₁.length ∧ c₃.nreg 70112 = 0 ∧
        c₃.nreg 70113 = c.nreg 70155 ∧ c₃.nreg 70115 = c.nreg 70151 ∧
        (∀ r, r ≠ 70111 → r ≠ 70112 → r ≠ 70113 → r ≠ 70115 → c₃.nreg r = c₂.nreg r) ∧
        Machine.NatRegFrame c₂ c₃) := by
    have r54 : c₂.nreg 70154 = L₁.length := by
      frame_finish
    have r55 : c₂.nreg 70155 = c.nreg 70155 := by
      frame_finish
    have r51 : c₂.nreg 70151 = c.nreg 70151 := by
      frame_finish
    unfold clSet2
    exec_block
    all_goals try omega
    refine ⟨rfl, ?_⟩
    simp (disch := omega) only [Machine.upd_same, Machine.upd_other, r54, r55, r51]
    and_intros
    all_goals first | trivial | rfl |
      (intro r h1 h2 h3 h4; simp (disch := omega) only [Machine.upd_other])
  obtain ⟨u11, u12, u13, u15, ur, um, urr, urm, uou⟩ := q
  have w₃ := e₃.wb_right
  have c305 : c₃.nreg 70105 = 1 := by
    ram_post
  have c308 : c₃.nreg 70108 = 0 := by
    ram_post
  have c3k : ∀ r, r = 70116 ∨ r = 70117 ∨ r = 70118 → c₃.nreg r = c₁.nreg r := by
    rintro r (rfl | rfl | rfl) <;>
    ram_post
  have mA : MemEqBelow A c₃.nmem c.nmem := fun a ha => by
    rw [um, I₂.low a (by simpa using ha), tm]
  have a₂ : c₂.nreg ALLOC = A + 3 * C₀.length := by rw [i2a]; simp
  have a₃ : c₃.nreg ALLOC = A + 3 * C₀.length := by
    ram_post [ur, a₂]
  have n₃ : c₃.nreg 70110 = C₀.length := by
    ram_post
  have J0 : CLQI W L₁ R₁ (c.nreg 70151) (c.nreg 70155) A C₀ c₃ c₃ :=
    ⟨w₃, by omega, by rw [u13, u12]; ring, by rw [u15, u12]; ring,
      by rw [a₃, u12]; simp [collectQ], by rw [n₃, u12]; simp [collectQ],
      fun _ _ _ _ _ _ _ _ => rfl, fun _ _ => rfl,
      by ram_simp [u12, um, List.take_zero, collectQ, List.zip_nil_left, List.filter_nil, List.map_nil, List.append_nil] <;> reg_omega, rfl, rfl, rfl⟩
  obtain ⟨c₄, k₄, e₄, hk₄, hk₄', I₄, h₄⟩ := clqLoop_exec (P := P) (L := L₁) (R := R₁)
    (pre := C₀) c305 c308 (by ram_rw [c3k, t16]) (by ram_rw [c3k, t17])
    (by ram_rw [c3k, t18]) (by rw [u11, hl₁]) hl₁.symm
    (resultList_agree hR₁ (by omega) mA) (hL₁.below (by omega) mA) (by omega)
    (by omega) (by omega) (by omega) R₁.length c₃ J0 (by rw [u12]; simp)
  have tk1 : L₁.take (c₄.nreg 70112) = L₁ := by rw [h₄]; exact List.take_of_length_le (by omega)
  have tk1' : R₁.take (c₄.nreg 70112) = R₁ := by rw [h₄]; exact List.take_of_length_le le_rfl
  have i4a := I₄.alloc
  have i4c := I₄.cnt
  have i4l := I₄.list
  rw [tk1, tk1'] at i4a i4c i4l
  set C₁ := collectQ L₁ R₁ with hC₁
  have hC₁l : C₁.length ≤ L₁.length := collectQ_length_le _ _
  have ex : Exec P W collectS c c₄ (k₁ + (k₂ + (k₃ + k₄))) := (by ram_path)
  have g₄ := I₄.regs
  have regs : ∀ r, (r < 70110 ∨ 70119 < r) → r ≠ 70156 → r ≠ ALLOC → c₄.nreg r = c.nreg r :=
    fun r h1 h2 h3 => by
      ram_rw [g₄ r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) h3,
        ur r,
        g₂ r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) h3, tr r h1 h2]
  have a₄ := i4a
  have hlen : (C₀ ++ C₁).length ≤ L₀.length + L₁.length := by
    rw [List.length_append]; omega
  refine ⟨c₄, _, ex, by omega, ?_, i4c, by rw [a₄, hA], by rwa [hA],
    ⟨fun r hr ha => ?_, fun r _ => by rw [I₄.rr, urr, I₂.rr, trr], fun a ha => ?_,
      fun a _ => by rw [I₄.rm, urm, I₂.rm, trm], by rw [I₄.out, uou, I₂.out, tou],
      by rw [a₄, hA]; omega, by rw [a₄, hA]; omega⟩, regs⟩
  · ram_rw [g₄, ur,
      g₂,
      t56, hA]
  · have h7 : bandOf r ≠ bFuse := fun h => hr (h ▸ band7)
    have : r < 70000 ∨ 80000 ≤ r := by unfold bandOf bFuse at h7; omega
    exact regs r (by omega) (by omega) ha
  · rw [I₄.low a (by rw [hA] at ha; omega), um, I₂.low a (by simp only [List.length_nil]; omega),
      tm]

end

end FuseAsm

end Chazelle.Core
