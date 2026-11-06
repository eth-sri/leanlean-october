module

public import Chazelle.Golf

public import Chazelle.Core.FuseAsmScan

/-!
# WP-F fusion assembly, part 10: the deduplication procedure

`ddRun` (inputs `70240`: base `T` of `K` stored triples, `70241`: `K`) writes the indices
`0 … K - 1`, sorts them by their triples (`cmp3`), and scans the sorted indices (`dsLoop`).
Output: at `70242` a fresh list `D` of triples (length in `70219`) with the same elements as the
input and no repetition (`ddRun_exec`).
-/

namespace Chazelle.Core

namespace FuseAsm

open Machine Machine.Stmt Programs SignK

@[expose] public section

/-- Initialisation. -/
def ddInit : Stmt := block [.constN 70105 1, .constN 70108 0, .copyN 70216 70240,
  .copyN 70217 70241, .copyN 70201 70241, .copyN 70230 70241, .constN 70200 0,
  .copyN 70202 ALLOC]

/-- The arguments of the sort. -/
def ddMid : Stmt := block [.copyN 30003 70202, .copyN 30004 70241]

/-- The start of the scan. -/
def ddPost : Stmt := block [.copyN 70242 ALLOC, .constN 70220 0, .copyN 70221 30005,
  .constN 70219 0, .constN 70105 1, .constN 70108 0, .copyN 70230 70217]

/-- **The deduplication.** -/
def ddRun : Stmt :=
  .seq ddInit (.seq ixLoop (.seq ddMid (.seq (SortR.sortStmt cmp3) (.seq ddPost dsLoop))))

/-- The stored triples. -/
def tlist (m : ℕ → ℕ) (T K : ℕ) : List (ℕ × ℕ × ℕ) := (List.range K).map (trip m T)

theorem tle_of_le3 {m : ℕ → ℕ} {T K a b : ℕ} (ha : a < K) (hb : b < K)
    (h : le3 m T K a b = true) : tle (trip m T a) (trip m T b) := by
  unfold le3 at h; ϴ' ha, hb, ite_true, decide_eq_true_eq at h; exact h

/-- The scanned list of a sorted permutation of the indices: same elements, no repetition. -/
theorem dd_spec {m : ℕ → ℕ} {T K : ℕ} {L' : List ℕ} (hp : L'.Perm (List.range K))
    (hs : L'.Pairwise fun a b => le3 m T K a b = true) :
    (∀ x, x ∈ dd (L'.map (trip m T)) (0, 0, 0) ↔ x ∈ tlist m T K) ∧
      (dd (L'.map (trip m T)) (0, 0, 0)).Nodup ∧
      (dd (L'.map (trip m T)) (0, 0, 0)).length ≤ K := by
  have hlt : ∀ a ∈ L', a < K := fun a ha => List.mem_range.1 (hp.subset ha)
  refine ⟨fun x => ?_, ?_, ?_⟩
  · Ξ mem_dd, tlist
    ϴ List.mem_map
    constructor
    · rintro ⟨a, ha, rfl⟩; exact ⟨a, hp.subset ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩; exact ⟨a, hp.symm.subset ha, rfl⟩
  · refine dd_nodup (r := tle) (fun x y h1 h2 => tle_antisymm h1 h2) ?_ _
    Ξ List.pairwise_map
    exact hs.imp_of_mem fun {a b} ha hb h => tle_of_le3 (hlt a ha) (hlt b hb) h
  · unfold dd
    refine (ddp_length_le _ _ _).trans ?_
    Ξ List.length_map, hp.length_eq, List.length_range

/-- The cost bound of `ddRun`. -/
def ddCost (K : ℕ) : ℕ := SortR.sortCost 40 K + 70 * K + 30

theorem frameFS_of_regs {c c' : Config} {k : ℕ}
    (hr : ∀ r, (r < 30000 ∨ (40000 ≤ r ∧ r < 70000) ∨ 80000 ≤ r) → r ≠ ALLOC → c'.nreg r = c.nreg r)
    (hrr : ∀ r, bandOf r ∉ ({bFuse, bSort} : Finset ℕ) → c'.rreg r = c.rreg r)
    (hm : ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a)
    (hrm : ∀ a, a < c.nreg ALLOC → c'.rmem a = c.rmem a) (ho : c'.output = c.output)
    (ha1 : c.nreg ALLOC ≤ c'.nreg ALLOC) (ha2 : c'.nreg ALLOC ≤ c.nreg ALLOC + k) :
    Frame {bFuse, bSort} c c' k := by
  refine ⟨fun r hb hra => hr r ?_ hra, hrr, hm, hrm, ho, ha1, ha2⟩
  by_contra h
  push Not at h
  apply hb
  ϴ Finset.mem_insert, Finset.mem_singleton, bandOf, bFuse, bSort
  omega

set_option maxHeartbeats 8000000 in
/-- **The deduplication procedure.** -/
theorem ddRun_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) {T K : ℕ}
    (h40 : c.nreg 70240 = T) (h41 : c.nreg 70241 = K) (hT : T + 3 * K ≤ c.nreg ALLOC)
    (hroom : c.nreg ALLOC + ddCost K ≤ W) :
    ∃ c' k, Exec P W ddRun c c' k ∧ k ≤ ddCost K ∧ Frame {bFuse, bSort} c c' k ∧
      (∀ r, 70000 ≤ r → r < 70105 → c'.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c'.nreg 70242 ∧ c'.nreg 70242 + 3 * c'.nreg 70219 ≤ c'.nreg ALLOC ∧
      ∃ D : List (ℕ × ℕ × ℕ), ChordListAt c'.nmem (c'.nreg 70242) D ∧
        c'.nreg 70219 = D.length ∧ D.length ≤ K ∧
        (∀ x, x ∈ D ↔ x ∈ tlist c.nmem T K) ∧ D.Nodup := by
  obtain ⟨A₀, hA₀⟩ : ∃ x, c.nreg ALLOC = x := ⟨_, rfl⟩
  have hA' := hA₀
  have hsc := SortR.sortCost_room 40 K
  unfold ddCost at hroom
  -- initialisation
  obtain ⟨c₁, k₁, e₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W ddInit c c₁ k₁ ∧ k₁ = 8 ∧
      (c₁.nreg 70105 = 1 ∧ c₁.nreg 70108 = 0 ∧ c₁.nreg 70216 = T ∧ c₁.nreg 70217 = K ∧
        c₁.nreg 70201 = K ∧ c₁.nreg 70230 = K ∧ c₁.nreg 70200 = 0 ∧ c₁.nreg 70202 = A₀ ∧
        c₁.nreg ALLOC = A₀ ∧
        (∀ r, (r < 70105 ∨ 70230 < r) → r ≠ ALLOC → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem ∧
        c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output) := by
    unfold ddInit
    exec_block
    all_goals try omega
    refine ⟨rfl, ?_⟩
    simp (disch := omega) only [Machine.upd_same, Machine.upd_other, h40, h41, hA', ALLOC]
    and_intros
    all_goals first | trivial | rfl |
      (intro r hr ha; simp (disch := omega) only [Machine.upd_other])
  obtain ⟨q05, q08, q16, q17, q01, q30, q00, q02, qA, qr, qm, qrr, qrm, qo⟩ := q
  -- the indices
  have I0 : IXI W K A₀ c₁ c₁ := ⟨e₁.wb_right, ⋄, by rw [qA, q00]; rfl, fun _ _ _ => rfl,
    fun _ _ => rfl, fun j hj => ⋄, rfl, rfl, rfl⟩
  obtain ⟨c₂, k₂, e₂, hk₂, hk₂', I₂, h₂⟩ := ixLoop_exec (P := P) q05 q01 (⋄) K c₁ I0
    (⋄)
  have hseg : SortL.seg c₂.nmem A₀ K = List.range K := seg_range fun j hj => I₂.done j (⋄)
  have a₂ : c₂.nreg ALLOC = A₀ + K := Ρ I₂.alloc, h₂
  have g₂ := I₂.regs
  -- the sort
  obtain ⟨c₃, k₃, e₃, hk₃, q3⟩ : ∃ c₃ k₃, Exec P W ddMid c₂ c₃ k₃ ∧ k₃ = 2 ∧
      (c₃.nreg 30003 = A₀ ∧ c₃.nreg 30004 = K ∧
        (∀ r, r ≠ 30003 → r ≠ 30004 → c₃.nreg r = c₂.nreg r) ∧ c₃.nmem = c₂.nmem ∧
        c₃.rreg = c₂.rreg ∧ c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output) := by
    have hw₂ := I₂.wb
    have r02 : c₂.nreg 70202 = A₀ := by rw [g₂ _ (⌖) (by decide), q02]
    have r41 : c₂.nreg 70241 = K := by
      rw [g₂ _ (⌖) (by decide), qr _ (by norm_num) (by decide), h41]
    unfold ddMid
    exec_block
    refine ⟨rfl, ?_⟩
    simp (disch := omega) only [Machine.upd_same, Machine.upd_other, r02, r41]
    and_intros
    all_goals first | trivial | rfl | (intro r h1 h2; simp (disch := omega) only [Machine.upd_other])
  obtain ⟨s03, s04, sr₃, sm₃, srr₃, srm₃, so₃⟩ := q3
  have a₃ : c₃.nreg ALLOC = A₀ + K := by rw [sr₃ _ (⌖) (by decide), a₂]
  have cmp := cmp3_ok (P := P) (W := W) (m₀ := c₃.nmem) (A₀ := A₀ + K) (T := T) (K := K)
    (g := c₃.nreg)
    (⋄) (by omega) (by omega)
  have hJ : Cmp3J c₃.nmem (A₀ + K) T K c₃.nreg c₃ := ⟨by
      rw [sr₃ _ (⌖) (by decide), g₂ _ (by decide) (by decide), q16],
    by rw [sr₃ _ (⌖) (by decide), g₂ _ (by decide) (by decide), q17],
    fun _ _ => rfl, fun _ _ _ => rfl⟩
  obtain ⟨c₄, k₄, e₄, hk₄, hJ₄, fr₄, b₄, b₄', L', hL', hperm, hsorted⟩ :=
    SortR.sortStmt_exec (P := P) cmp (⌖) (le3_trans c₃.nmem T K)
      (le3_total c₃.nmem T K) e₃.wb_right hJ (by rw [a₃]; exact cmp3J_stable _ _ _ _ _)
      (List.range K) (by rw [List.length_range, s03, sm₃]; exact hseg)
      (Ρ List.length_range, s04) (by rw [List.length_range, s03, a₃])
      (by rw [List.length_range, a₃]; omega)
  rw [List.length_range] at hk₄ b₄' hL'
  -- the scan
  obtain ⟨B', hB'⟩ : ∃ x, c₄.nreg 30005 = x := ⟨_, rfl⟩
  obtain ⟨LB, hLB⟩ : ∃ x, c₄.nreg ALLOC = x := ⟨_, rfl⟩
  have hw₄ := e₄.wb_right
  obtain ⟨j16, j17, j4, j5⟩ := hJ₄
  obtain ⟨c₅, k₅, e₅, hk₅, q5⟩ : ∃ c₅ k₅, Exec P W ddPost c₄ c₅ k₅ ∧ k₅ = 7 ∧
      (c₅.nreg 70242 = LB ∧ c₅.nreg 70220 = 0 ∧ c₅.nreg 70221 = B' ∧ c₅.nreg 70219 = 0 ∧
        c₅.nreg 70105 = 1 ∧ c₅.nreg 70108 = 0 ∧ c₅.nreg 70230 = K ∧ c₅.nreg 70216 = T ∧
        (∀ r, (r < 70105 ∨ 70242 < r) → c₅.nreg r = c₄.nreg r) ∧
        c₅.nmem = c₄.nmem ∧ c₅.rreg = c₄.rreg ∧ c₅.rmem = c₄.rmem ∧ c₅.output = c₄.output) := by
    have hLB' := hLB
    unfold ddPost
    exec_block
    all_goals try omega
    refine ⟨rfl, ?_⟩
    simp (disch := omega) only [Machine.upd_same, Machine.upd_other, hLB', hB', j16, j17, ALLOC]
    and_intros
    all_goals first | trivial | rfl | (intro r h1; simp (disch := omega) only [Machine.upd_other])
  obtain ⟨t42, t20, t21, t19, t05, t08, t30, t16, tr₅, tm₅, trr₅, trm₅, to₅⟩ := q5
  have hitems : ∀ j, j < K → c₅.nmem (B' + j) < K := by
    intro j hj
    have hmem : c₅.nmem (B' + j) ∈ L' := by
      Ξ ← hL', tm₅, ← hB'
      ϴ SortL.seg, List.mem_map, List.mem_range
      exact ⟨j, hj, rfl⟩
    exact List.mem_range.1 (hperm.subset hmem)
  have a₅ : c₅.nreg ALLOC = LB := by rw [tr₅ _ (⌖), hLB]
  have hK4 := hk₄
  have hLBb : LB ≤ A₀ + K + k₄ := by rw [← hLB, ← a₃]; exact fr₄.2.2.2.2.2.2
  have hBL : B' + K ≤ LB := by rw [← hB', ← hLB]; exact b₄'
  have D0 : DSI W K T B' LB c₅.nmem c₅ c₅ := by
    refine ⟨e₅.wb_right, by rw [t20]; omega, by rw [t21, t20]; simp, fun h => by rw [t20] at h; omega,
      by rw [a₅, t20]; simp [ddp], by rw [t20]; intro i hi; simp [ddp] at hi,
      by rw [t19, t20]; simp [ddp], fun _ _ => rfl, fun _ _ _ => rfl, rfl, rfl, rfl⟩
  obtain ⟨c₆, k₆, e₆, hk₆, hk₆', D₆, h₆⟩ := dsLoop_exec (P := P) (m₀ := c₅.nmem) t05 t08 t16 t30
    hitems (⋄) hBL (by omega) K c₅ D0 (by rw [t20]; simp)
  -- assembling
  have ex : Exec P W ddRun c c₆ (k₁ + (k₂ + (k₃ + (k₄ + (k₅ + k₆))))) :=
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ e₆))))
  set D := ddp (stl c₅.nmem T B' K) (0, 0, 0) K with hD
  have hDdd : D = dd (L'.map (trip c.nmem T)) (0, 0, 0) := by
    have e1 : stl c₅.nmem T B' K = L'.map (trip c.nmem T) := by
      unfold stl
      Ξ tm₅, ← hB', hL'
      apply List.map_congr_left
      intro a ha
      have haK : a < K := List.mem_range.1 (hperm.subset ha)
      unfold trip
      have hm : ∀ x, x < A₀ → c₄.nmem x = c.nmem x := fun x hx => by
        Ξ fr₄.2.2.1 x (by rw [a₃]; omega), sm₃, I₂.low x hx, qm
      rw [hm _ (⋄), hm _ (by omega), hm _ (by omega)]
    rw [hD, e1]; unfold dd; rw [List.length_map, hperm.length_eq, List.length_range]
  have hsorted' : L'.Pairwise fun a b => le3 c.nmem T K a b = true := by
    refine hsorted.imp_of_mem fun {a b} ha hb h => ?_
    have haK : a < K := List.mem_range.1 (hperm.subset ha)
    have hbK : b < K := List.mem_range.1 (hperm.subset hb)
    have hm : ∀ x, x < A₀ → c₃.nmem x = c.nmem x := fun x hx => Ρ sm₃, I₂.low x hx, qm
    have ht : ∀ y, y < K → trip c₃.nmem T y = trip c.nmem T y := fun y hy => by
      unfold trip; rw [hm _ (⋄), hm _ (by omega), hm _ (by omega)]
    unfold le3 at h ⊢
    simp only [haK, hbK, ite_true] at h ⊢
    rw [← ht a haK, ← ht b hbK]; exact h
  obtain ⟨hmemD, hnodD, hlenD⟩ := dd_spec (m := c.nmem) (T := T) hperm hsorted'
  rw [← hDdd] at hmemD hnodD hlenD
  have hc6 := D₆.cnt
  rw [h₆] at hc6
  have hl6 := D₆.list
  rw [h₆] at hl6
  have ha6 := D₆.alloc
  rw [h₆] at ha6
  have r42 : c₆.nreg 70242 = LB := by rw [D₆.regs _ (⊛) (by decide), t42]
  refine ⟨c₆, _, ex, ?_, ?_, fun r h1 h2 => ?_, ?_, ?_, D, by rw [r42]; exact hl6, hc6, hlenD,
    hmemD, hnodD⟩
  · have := hlenD; unfold ddCost; omega
  · have a4 : A₀ + K ≤ LB := by rw [← hLB, ← a₃]; exact fr₄.2.2.2.2.2.1
    have hA6 : c₆.nreg ALLOC = LB + 3 * D.length := ha6
    refine frameFS_of_regs (fun r hr ha => ?_) (fun r hr => ?_) (fun a ha => ?_) (fun a ha => ?_)
      ?_ (⋄) (by rw [hA6, hA₀]; have := hlenD; omega)
    · rw [D₆.regs r (⋄) ha, tr₅ r (by omega),
        fr₄.1 r (by simp only [Finset.mem_insert, Finset.mem_singleton, bandOf, bSort, bFuse]; omega)
          ha, sr₃ r (⋄) (by omega), g₂ r (by omega) ha, qr r (by omega) ha]
    · Ξ D₆.rr, trr₅, fr₄.2.1 r (by simp only [Finset.mem_insert, Finset.mem_singleton] at hr ⊢; tauto), srr₃, I₂.rr, qrr
    · rw [hA₀] at ha
      rw [D₆.low a (⋄), tm₅, fr₄.2.2.1 a (by rw [a₃]; omega), sm₃, I₂.low a ha, qm]
    · rw [hA₀] at ha
      Ξ D₆.rm, trm₅, fr₄.2.2.2.1 a (by rw [a₃]; omega), srm₃, I₂.rm, qrm
    · Ξ D₆.out, to₅, fr₄.2.2.2.2.1, so₃, I₂.out, qo
  · have hA : r ≠ ALLOC := by unfold ALLOC; omega
    rw [D₆.regs r (⋄) hA, tr₅ r (by omega), j5 r h1 h2, sr₃ r (by omega) (by omega),
      g₂ r (⋄) hA, qr r (by omega) hA]
  · rw [r42, hA₀]; have : A₀ + K ≤ LB := by rw [← hLB, ← a₃]; exact fr₄.2.2.2.2.2.1
    omega
  · Ξ r42, hc6, ha6

end

end FuseAsm

end Chazelle.Core
