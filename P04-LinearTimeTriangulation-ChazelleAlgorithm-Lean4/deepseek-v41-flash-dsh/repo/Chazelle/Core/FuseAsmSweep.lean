module

public import Chazelle.Golf

public import Chazelle.Core.FuseAsmSideQ
public import Chazelle.Core.SweepSpecH

/-!
# WP-F fusion assembly, part 23: the two sweeps

* `SwPre`, `SwPost`, `SwCost`: the contract of `SweepSpec` (`sweep_meets`).
* `FPre`: the facts of the fusion's precondition beyond `FCtx` (tops, oracle models, degree
  and weight bounds, the oracle context), kept by the driver (`FPre.keep`).
* `swStage i S Lr RB`: the sweep arguments from the fusion registers (side `i`, query base in
  `S`, count in `Lr`, saved in `Lr + 24 + 2 i`), the sweep, and the result base saved in `RB`
  (`swStage_exec`).
-/

namespace Chazelle.Core

namespace FuseAsm

open Machine Machine.Stmt Programs SignK SweepPrim MergeAsm

@[expose] public section

/-- The precondition of the sweep. -/
def SwPre (X : MemCtx) (Ok : Polygon → Model → Prop) (P : Polygon) (W : ℕ) (c : Config) : Prop :=
  GoodEnv P ∧ hostWords P.n ≤ W ∧
    X.holds P c.nmem (rd c bSweep 10) (c.nreg ALLOC) ∧
    rd c bSweep 5 ≤ X.cap P c.nmem (rd c bSweep 10) ∧ rd c bSweep 7 ≤ 1 ∧
    JunctionWF P (c.nreg ALLOC) c.nmem (rd c bSweep 0) (rd c bSweep 1) (rd c bSweep 2) ∧
    ∃ H J N₁ N₂ L, JunctionAt c.nmem (rd c bSweep 0) (rd c bSweep 1) (rd c bSweep 2)
        (Qof P) H J ∧
      J.P.Simple ∧
      Ok P (chainModel J.left) ∧ Ok P (chainModel J.right) ∧
      NFWithin c.nmem (rd c bSweep 3) (c.nreg ALLOC) N₁ ∧
      NFWithin c.nmem (rd c bSweep 4) (c.nreg ALLOC) N₂ ∧
      IsNF (chainModel J.left) (Qof P) N₁ ∧ IsNF (chainModel J.right) (Qof P) N₂ ∧
      (chainModel J.left).DegLe (N₁.F (chainModel J.left) (Qof P)) (rd c bSweep 6) ∧
      (chainModel J.right).DegLe (N₂.F (chainModel J.right) (Qof P)) (rd c bSweep 6) ∧
      (chainModel J.left).Semigranular (N₁.F (chainModel J.left) (Qof P)) (rd c bSweep 5) ∧
      (chainModel J.right).Semigranular (N₂.F (chainModel J.right) (Qof P)) (rd c bSweep 5) ∧
      rd c bSweep 9 = L.length ∧ rd c bSweep 8 + 3 * L.length ≤ c.nreg ALLOC ∧
      ChordListAt c.nmem (rd c bSweep 8) L ∧
      (∀ q ∈ L, QueryOK J (Qof P) (rd c bSweep 7) q) ∧
      (rd c bSweep 7 = 1 → ∃ L₁ : List (ℕ × ℕ × ℕ), L = sweepEndQ N₂.chords ++ L₁ ∧
        L₁.length ≤ 3) ∧
      ∀ q ∈ L, ((chainModel (sideChain J (rd c bSweep 7))).pos (Qof P) ⟨q.1, q.2.1⟩).2 =
        ((Qof P).vtx (q.2.1 - 1)).2

/-- The postcondition of the sweep. -/
def SwPost (P : Polygon) (c c' : Config) : Prop :=
  ∀ H J (L : List (ℕ × ℕ × ℕ)),
    JunctionAt c.nmem (rd c bSweep 0) (rd c bSweep 1) (rd c bSweep 2) (Qof P) H J →
    rd c bSweep 9 = L.length → ChordListAt c.nmem (rd c bSweep 8) L →
    ∃ R : List (ℕ × ℕ × ℕ × ℕ), c.nreg ALLOC ≤ rd c' bSweep 11 ∧
      rd c' bSweep 11 + 4 * L.length ≤ c'.nreg ALLOC ∧ R.length = L.length ∧
      ResultListAt c'.nmem (rd c' bSweep 11) R ∧
      ∀ j, j < L.length →
        SeesInWhole J (Qof P) (rd c bSweep 7) (L.getD j (0, 0, 0)) (R.getD j (0, 0, 0, 0))

/-- The cost of the sweep. -/
def SwCost (κ : ℕ → ℕ) (F : ℕ → ℕ) (_ : Polygon) (c : Config) : ℕ :=
  κ (rd c bSweep 6) * (c.nmem (rd c bSweep 3) + c.nmem (rd c bSweep 4) + rd c bSweep 9 + 1) *
    (F (rd c bSweep 5) +
      Nat.clog 2 (c.nmem (rd c bSweep 3) + c.nmem (rd c bSweep 4) + rd c bSweep 9 + 1) + 1)

theorem sweep_meets (hS : SweepSpecH) : ∃ (mk : Stmt → Stmt) (κ : ℕ → ℕ),
    ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx) (Ok : Polygon → Model → Prop),
      X.CapLocal → Bs ⊆ oracleBands → ShooterOK sh Bs F X Ok →
      Meets (mk sh) (sweepBands ∪ oracleBands) (SwPre X Ok) SwPost (SwCost κ F) := hS

theorem holds_frameF {X : MemCtx} {P : Polygon} {g : ℕ} {B : Finset ℕ} {c c' : Config} {k : ℕ}
    (hX : X.holds P c.nmem g (c.nreg ALLOC)) (hf : Frame B c c' k) :
    X.holds P c'.nmem g (c'.nreg ALLOC) :=
  X.mono _ _ _ _ _ hf.2.2.2.2.2.1 (X.local_ _ _ _ _ _ (fun a ha => (hf.2.2.1 a ha).symm) hX)

theorem cap_frameF {X : MemCtx} (hloc : X.CapLocal) {P : Polygon} {g : ℕ} {B : Finset ℕ}
    {c c' : Config} {k : ℕ} (hX : X.holds P c.nmem g (c.nreg ALLOC)) (hf : Frame B c c' k) :
    X.cap P c'.nmem g = X.cap P c.nmem g :=
  hloc P c.nmem c'.nmem g _ (fun a ha => hf.2.2.1 a ha) hX

/-- The facts of the fusion's precondition beyond `FCtx`. -/
structure FPre (P : Polygon) (X : MemCtx) (Ok : Polygon → Model → Prop) (J : Merge.Junction)
    (N₁ N₂ : NF) (c : Config) : Prop where
  okL : Ok P (chainModel J.left)
  okR : Ok P (chainModel J.right)
  okW : Ok P (chainModel J.whole)
  degL : (chainModel J.left).DegLe (N₁.F (chainModel J.left) (Qof P)) (c.nreg 70006)
  degR : (chainModel J.right).DegLe (N₂.F (chainModel J.right) (Qof P)) (c.nreg 70006)
  sgL : (chainModel J.left).Semigranular (N₁.F (chainModel J.left) (Qof P)) (c.nreg 70005)
  sgR : (chainModel J.right).Semigranular (N₂.F (chainModel J.right) (Qof P)) (c.nreg 70005)
  holds : X.holds P c.nmem (c.nreg 70008) (c.nreg ALLOC)
  cap : c.nreg 70005 ≤ X.cap P c.nmem (c.nreg 70008)

theorem FPre.keep {P : Polygon} {X : MemCtx} {Ok : Polygon → Model → Prop} {J : Merge.Junction}
    {N₁ N₂ : NF} {c c' : Config} (h : FPre P X Ok J N₁ N₂ c) (hloc : X.CapLocal)
    (hr : ∀ r, 70005 ≤ r → r < 70009 → c'.nreg r = c.nreg r) {B : Finset ℕ} {k : ℕ}
    (hf : Frame B c c' k) : FPre P X Ok J N₁ N₂ c' := by
  obtain ⟨o1, o2, o3, d1, d2, s1, s2, hh, hc⟩ := h
  have e5 := hr 70005 (⊛) (⊛)
  have e6 := hr 70006 (⊛) (⊛)
  have e8 := hr 70008 (⊛) (⊛)
  refine ⟨o1, o2, o3, by rw [e6]; exact d1, by rw [e6]; exact d2, by rw [e5]; exact s1,
    by rw [e5]; exact s2, by rw [e8]; exact holds_frameF hh hf, ?_⟩
  rw [e5, e8, cap_frameF hloc hh hf]; exact hc

theorem junctionWF_mono {P : Polygon} {E E' : ℕ} {m : ℕ → ℕ} {bl br bw : ℕ}
    (h : JunctionWF P E m bl br bw) (hE : E ≤ E') : JunctionWF P E' m bl br bw :=
  ⟨h.1.mono hE, h.2.1.mono hE, h.2.2.1.mono hE, h.2.2.2⟩

/-- The sweep arguments. -/
def swSet (i S Lr : ℕ) : Stmt := block [.copyN 240000 70000, .copyN 240001 70001,
  .copyN 240002 70002, .copyN 240003 70003, .copyN 240004 70004, .copyN 240005 70005,
  .copyN 240006 70006, .constN 240007 i, .copyN 240008 S, .copyN 240009 Lr,
  .copyN 240010 70008, .copyN (Lr + 24 + 2 * i) Lr]

/-- **One sweep stage.** -/
def swStage (mk : Stmt) (i S Lr RB : ℕ) : Stmt :=
  .seq (swSet i S Lr) (.seq mk (block [.copyN RB 240011]))

theorem swSet_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) {i S Lr : ℕ}
    (hi : i ≤ 1) (hW1 : 1 ≤ W) (hS : 70000 ≤ S ∧ S < 80000) (hLr : 70100 ≤ Lr ∧ Lr < 70200) :
    ∃ c' k, Exec P W (swSet i S Lr) c c' k ∧ k = 12 ∧
      (∀ j, j < 7 → c'.nreg (240000 + j) = c.nreg (70000 + j)) ∧ c'.nreg 240007 = i ∧
      c'.nreg 240008 = c.nreg S ∧ c'.nreg 240009 = c.nreg Lr ∧ c'.nreg 240010 = c.nreg 70008 ∧
      c'.nreg (Lr + 24 + 2 * i) = c.nreg Lr ∧
      (∀ r, bandOf r ≠ bSweep → r ≠ Lr + 24 + 2 * i → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold swSet
  exec_block
  all_goals try omega
  refine ⟨rfl, fun j hj => ?_, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  · interval_cases j <;> simp (disch := omega) only [Machine.upd_same,
      Machine.upd_other, Nat.add_zero]
  all_goals try (simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other])
  · have : r < 240000 ∨ 250000 ≤ r := by
      unfold bandOf bSweep at h1; omega
    simp (disch := omega) only [Machine.upd_other]

/-- The bands of the fusion. -/
def FB : Finset ℕ := fuseBands ∪ oracleBands

theorem ftrF {c c₁ c₂ : Config} {k₁ k₂ : ℕ} (h₁ : Frame FB c c₁ k₁) (h₂ : Frame FB c₁ c₂ k₂) :
    Frame FB c c₂ (k₁ + k₂) :=
  (h₁.trans h₂).mono (Ρ Finset.union_self) le_rfl

theorem sweep_sub : sweepBands ∪ oracleBands ⊆ FB := ⌖

theorem band7 : bFuse ∈ FB := ⌖

theorem band24 : bSweep ∈ FB := ⌖

set_option maxHeartbeats 8000000 in
/-- **One sweep stage.** -/
theorem swStage_exec {mk : Stmt} {κs F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
    (hM : Meets mk (sweepBands ∪ oracleBands) (SwPre X Ok) SwPost (SwCost κs F))
    {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) {J : Merge.Junction} {H : Host}
    {N₁ N₂ : NF} {A : ℕ} (hF : FCtx P W J H N₁ N₂ A c) (hP : FPre P X Ok J N₁ N₂ c)
    {i S Lr RB : ℕ} (hi : i ≤ 1) (hS : 70000 ≤ S ∧ S < 80000) (hLr : 70100 ≤ Lr ∧ Lr < 70200)
    (hRB : 70000 ≤ RB ∧ RB < 80000) (hRB' : RB ≠ Lr + 24 + 2 * i)
    {L : List (ℕ × ℕ × ℕ)} (hLl : c.nreg Lr = L.length) (hL : ChordListAt c.nmem (c.nreg S) L)
    (hQB : c.nreg S + 3 * L.length ≤ c.nreg ALLOC) (hOK : ∀ q ∈ L, QueryOK J (Qof P) i q)
    (hend : i = 1 → ∃ L₁ : List (ℕ × ℕ × ℕ), L = sweepEndQ N₂.chords ++ L₁ ∧ L₁.length ≤ 3)
    (hHt : ∀ q ∈ L, ((chainModel (sideChain J i)).pos (Qof P) ⟨q.1, q.2.1⟩).2 =
      ((Qof P).vtx (q.2.1 - 1)).2)
    (hroom : c.nreg ALLOC + 13 + κs (c.nreg 70006) * (N₁.nChords + N₂.nChords + L.length + 1) *
      (F (c.nreg 70005) + Nat.clog 2 (N₁.nChords + N₂.nChords + L.length + 1) + 1) ≤ W) :
    ∃ c' k R, Exec P W (swStage mk i S Lr RB) c c' k ∧
      k ≤ 13 + κs (c.nreg 70006) * (N₁.nChords + N₂.nChords + L.length + 1) *
        (F (c.nreg 70005) + Nat.clog 2 (N₁.nChords + N₂.nChords + L.length + 1) + 1) ∧
      R.length = L.length ∧ c.nreg ALLOC ≤ c'.nreg RB ∧
      c'.nreg RB + 4 * L.length ≤ c'.nreg ALLOC ∧ ResultListAt c'.nmem (c'.nreg RB) R ∧
      (∀ j, j < L.length →
        SeesInWhole J (Qof P) i (L.getD j (0, 0, 0)) (R.getD j (0, 0, 0, 0))) ∧
      Frame FB c c' k ∧
      (∀ r, bandOf r = bFuse → r ≠ RB → r ≠ Lr + 24 + 2 * i → c'.nreg r = c.nreg r) ∧
      c'.nreg (Lr + 24 + 2 * i) = L.length := by
  have hW1 : 1 ≤ W := by have := hF.hw; unfold hostWords at this; omega
  obtain ⟨c₁, k₁, e₁, hk₁, q0, q7, q8, q9, q10, q24, qr, qm, qrr, qrm, qo⟩ :=
    swSet_exec (P := P) c hw hi hW1 hS hLr
  have w₁ := e₁.wb_right
  have a₁ : c₁.nreg ALLOC = c.nreg ALLOC := qr _ (by decide) (by unfold ALLOC; omega)
  have F₁ : Frame FB c c₁ k₁ := ⟨fun r hr ha => qr r (fun h => hr (h ▸ band24)) (fun h => hr (by
      rw [h]; unfold bandOf; rw [show (Lr + 24 + 2 * i) / 10000 = 7 by omega]; exact band7)),
    fun r _ => by rw [qrr], fun a _ => by rw [qm], fun a _ => by rw [qrm], qo, by rw [a₁],
    by rw [a₁]; omega⟩
  have r0 : rd c₁ bSweep 0 = c.nreg 70000 := q0 0 (by norm_num)
  have r1 : rd c₁ bSweep 1 = c.nreg 70001 := q0 1 (by norm_num)
  have r2 : rd c₁ bSweep 2 = c.nreg 70002 := q0 2 (by norm_num)
  have r3 : rd c₁ bSweep 3 = c.nreg 70003 := q0 3 (by norm_num)
  have r4 : rd c₁ bSweep 4 = c.nreg 70004 := q0 4 (by norm_num)
  have r5 : rd c₁ bSweep 5 = c.nreg 70005 := q0 5 (by norm_num)
  have r6 : rd c₁ bSweep 6 = c.nreg 70006 := q0 6 (by norm_num)
  have r7 : rd c₁ bSweep 7 = i := q7
  have r8 : rd c₁ bSweep 8 = c.nreg S := q8
  have r9 : rd c₁ bSweep 9 = L.length := by rw [← hLl]; exact q9
  have r10 : rd c₁ bSweep 10 = c.nreg 70008 := q10
  have hK1 : c.nmem (c.nreg 70003) = N₁.nChords := (Robust.holds hF.nf₁).1
  have hK2 : c.nmem (c.nreg 70004) = N₂.nChords := (Robust.holds hF.nf₂).1
  have hpre : SwPre X Ok P W c₁ := by
    unfold SwPre
    rw [qm, a₁, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10]
    exact ⟨hF.good, hF.hw, hP.holds, hP.cap, hi, junctionWF_mono hF.jwf hF.le, H, J, N₁, N₂, L,
      hF.jat, hF.simple, hP.okL, hP.okR, hF.nf₁.mono hF.le, hF.nf₂.mono hF.le,
      hF.is₁, hF.is₂, hP.degL, hP.degR, hP.sgL, hP.sgR, rfl, hQB, hL, hOK, hend, hHt⟩
  have hcost : SwCost κs F P c₁ = κs (c.nreg 70006) * (N₁.nChords + N₂.nChords + L.length + 1) *
      (F (c.nreg 70005) + Nat.clog 2 (N₁.nChords + N₂.nChords + L.length + 1) + 1) := by
    unfold SwCost; rw [qm, r3, r4, r5, r6, r9, hK1, hK2]
  obtain ⟨c₂, k₂, e₂, hk₂, post, F₂⟩ := hM P W c₁ w₁ hpre (by rw [hcost, a₁]; omega)
  rw [hcost] at hk₂
  obtain ⟨R, hR1, hR2, hRl, hRL, hsees⟩ := post H J L (by rw [qm, r0, r1, r2]; exact hF.jat)
    r9 (by rw [qm, r8]; exact hL)
  rw [r7] at hsees
  have w₂ := e₂.wb_right
  obtain ⟨c₃, k₃, e₃, hk₃, t0, tr, tm, trr, trm, tou⟩ : ∃ c₃ k₃, Exec P W
      (block [.copyN RB 240011]) c₂ c₃ k₃ ∧ k₃ = 1 ∧ c₃.nreg RB = c₂.nreg 240011 ∧
      (∀ r, r ≠ RB → c₃.nreg r = c₂.nreg r) ∧ c₃.nmem = c₂.nmem ∧ c₃.rreg = c₂.rreg ∧
      c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    exec_block
    refine ⟨rfl, ?_, fun r h => ?_, rfl, rfl, rfl, rfl⟩
    all_goals simp (disch := omega) only [Machine.upd_same, Machine.upd_other]
  have hRBA : RB ≠ ALLOC := by unfold ALLOC; omega
  have F₃ : Frame FB c₂ c₃ k₃ := ⟨fun r hr ha => tr r (fun h => hr (by
      rw [h]; unfold bandOf; rw [show RB / 10000 = 7 by omega]; exact band7)),
    fun r _ => by rw [trr], fun a _ => by rw [tm], fun a _ => by rw [trm], tou,
    by rw [tr _ hRBA.symm], by rw [tr _ hRBA.symm]; omega⟩
  have ex : Exec P W (swStage mk i S Lr RB) c c₃ (k₁ + (k₂ + k₃)) := .seq e₁ (.seq e₂ e₃)
  have Ft : Frame FB c c₃ (k₁ + (k₂ + k₃)) :=
    ftrF F₁ (ftrF (F₂.mono sweep_sub le_rfl) F₃)
  have hband : ∀ r, bandOf r = bFuse → bandOf r ∉ sweepBands ∪ oracleBands := fun r h => by
    rw [h]; decide
  refine ⟨c₃, _, R, ex, by omega, hRl, ?_, ?_, ?_, ?_, Ft, fun r h1 h2 h3 => ?_, ?_⟩
  · rw [t0]; rw [a₁] at hR1; exact hR1
  · rw [t0, tr _ hRBA.symm]; exact hR2
  · rw [tm, t0]; exact hRL
  · exact hsees
  · have hA : r ≠ ALLOC := by intro h; rw [h] at h1; exact absurd h1 (by decide)
    rw [tr r h2, F₂.1 r (hband r h1) hA, qr r (by rw [h1]; decide) h3]
  · rw [tr _ (Ne.symm hRB'), F₂.1 _ (hband _ (by unfold bandOf bFuse; omega)) (by unfold ALLOC; omega),
      q24, hLl]

end

end FuseAsm

end Chazelle.Core
