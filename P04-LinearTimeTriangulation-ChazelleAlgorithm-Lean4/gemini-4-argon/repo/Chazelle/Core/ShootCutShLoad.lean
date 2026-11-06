module

public import Chazelle.Core.ShootCutShEdge

/-!
# WP-G, part 43: the shooting environment and point records in band `bShoot`

* `ShEnv`: the facts the shooting loop of the ray-shooter keeps (the chain descriptor at the
  address in `140403`, the constant `K1`, the records of the origin `z`: abscissa `140230 …`
  (weak), ordinate `140234 …`, and the direction bit `140241`);
* `ptLoad e h B`: the point record (`ptKey`) of the walk position in the registers `e`, `h` into
  `B … B + 10` (abscissa, ordinate with slot, symbolic point).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace Chazelle.Core

namespace ShootCut

open Machine Machine.Stmt Programs SignK WalkKey NFLoc SweepPrim

@[expose] public section

/-- **The shooting environment.** -/
structure ShEnv (P : Polygon) (W : ℕ) (H : Host) (C : Chain) (z : Point) (σ : ℝ) (c : Config) :
    Prop where
  hG : GoodEnv P
  hW : hostWords P.n ≤ W
  hD : ChainDescAt c.nmem (c.nreg 140403) (Qof P) H C
  hwf : ChainWF P (c.nreg ALLOC) c.nmem (c.nreg 140403)
  hreg : ∀ H', HostAt c.nmem (c.nmem (c.nreg 140403)) H' → HostRegular P.n H'
  k1 : c.nreg K1 = 1
  ox : AbsRecW P c 140230 z.1 C.radius
  oy : HRecS P c 140234 z.2 C.radius
  sig : c.nreg 140241 ≤ 1 ∧ (c.nreg 140241 = 1 ↔ σ = 1)
  hσ : σ = 1 ∨ σ = -1

/-- The registers the environment reads. -/
def envR (r : ℕ) : Prop :=
  r = 140403 ∨ r = K1 ∨ (140230 ≤ r ∧ r < 140237) ∨ r = 140241 ∨ r = ALLOC

/-- **The environment survives** any step that keeps its registers and the memory. -/
theorem ShEnv.keep {P : Polygon} {W : ℕ} {H : Host} {C : Chain} {z : Point} {σ : ℝ}
    {c c' : Config} (h : ShEnv P W H C z σ c) (hm : c'.nmem = c.nmem)
    (hr : ∀ r, envR r → c'.nreg r = c.nreg r) : ShEnv P W H C z σ c' := by
  have e403 := hr 140403 (Or.inl rfl)
  have eA := hr ALLOC (by unfold envR; simp)
  refine ⟨h.hG, h.hW, by rw [hm, e403]; exact h.hD, by rw [hm, e403, eA]; exact h.hwf,
    by rw [hm, e403]; exact h.hreg, by rw [hr K1 (by unfold envR; simp)]; exact h.k1,
    h.ox.copy (hr _ (by unfold envR; simp)) (hr _ (by unfold envR; simp))
      (hr _ (by unfold envR; simp)) (hr _ (by unfold envR; simp)),
    h.oy.copy (hr _ (by unfold envR; simp)) (hr _ (by unfold envR; simp))
      (hr _ (by unfold envR; simp)), ?_, h.hσ⟩
  rw [hr 140241 (by unfold envR; simp)]; exact h.sig

theorem ShEnv.frame {P : Polygon} {W : ℕ} {H : Host} {C : Chain} {z : Point} {σ : ℝ}
    {c c' : Config} {B : ℕ → Bool} (h : ShEnv P W H C z σ c) (hf : FrameB B c c')
    (hB : ∀ r, envR r → B r = false) : ShEnv P W H C z σ c' :=
  h.keep hf.2.2.1 fun r hr => hf.1 r (hB r hr)

/-! ## Loading a point record -/

/-- The point record of the walk position `(e, h)` into `B … B + 10`. -/
def ptLoad (e h B : ℕ) : Stmt :=
  .seq (block (copies [(50200, 140403), (50201, e), (50202, h)]))
    (.seq ptKey (.seq (block (copies [(B, 50210), (B + 1, 50211), (B + 2, 50212), (B + 3, 50213),
      (B + 4, 50214), (B + 6, 50215), (B + 7, 50216), (B + 8, 50217), (B + 9, 50218),
      (B + 10, 50219)])) (.instr (.constN (B + 5) 0))))

/-- The registers written by `ptLoad _ _ B`. -/
def Bld (B r : ℕ) : Bool := Bprim r || decide (50200 ≤ r ∧ r < 50203) || decide (B ≤ r ∧ r < B + 11)

/-- The point record of `z` at `B`. -/
def PtRecB (P : Polygon) (c : Config) (B : ℕ) (z : Point) (R : ℝ) : Prop :=
  AbsRec P c B z.1 R ∧ HRecS P c (B + 4) z.2 R ∧ FRec P c (B + 7) z

variable {P : Polygon} {W : ℕ} {H : Host} {C : Chain} {z : Point} {σ : ℝ}

/-- The facts of the environment that loading a point record needs. -/
structure LdEnv (P : Polygon) (W : ℕ) (H : Host) (C : Chain) (c : Config) : Prop where
  hG : GoodEnv P
  hW : hostWords P.n ≤ W
  hD : ChainDescAt c.nmem (c.nreg 140403) (Qof P) H C
  hwf : ChainWF P (c.nreg ALLOC) c.nmem (c.nreg 140403)
  hreg : ∀ H', HostAt c.nmem (c.nmem (c.nreg 140403)) H' → HostRegular P.n H'

theorem ShEnv.ld {c : Config} (E : ShEnv P W H C z σ c) : LdEnv P W H C c :=
  ⟨E.hG, E.hW, E.hD, E.hwf, E.hreg⟩

theorem ptLoad_exec' (c : Config) (hw : WordsBounded W c) (E : LdEnv P W H C c)
    {e h B : ℕ} (he : 140000 ≤ e ∧ e < 150000) (hh : 140000 ≤ h ∧ h < 150000)
    (hB : 140000 ≤ B ∧ B + 11 ≤ 150000)
    (hen : c.nreg e < (chainModel C).W.n)
    (hp : ProperPos (chainModel C) (Qof P) P.n ⟨c.nreg e, c.nreg h⟩)
    (hy : c.nreg h = 0 ∨
      |((chainModel C).pos (Qof P) ⟨c.nreg e, c.nreg h⟩).2| < C.radius)
    (hroom : c.nreg ALLOC + 15800 ≤ W) :
    ∃ c' k, Exec P W (ptLoad e h B) c c' k ∧ k ≤ 15820 ∧
      PtRecB P c' B ((chainModel C).pos (Qof P) ⟨c.nreg e, c.nreg h⟩) C.radius ∧
      FrameB (Bld B) c c' ∧
      (6 ≤ c.nreg e → (c.nreg e < 2 * C.m + 6 ∨
        (chainModel C).param (Qof P) ⟨c.nreg e, c.nreg h⟩ = 0) → c'.nreg (B + 7) = 1) := by
  obtain ⟨c₁, e₁, v₁, k₁, rr₁, m₁, rm₁, o₁⟩ := copies_exec (P := P)
    [(50200, 140403), (50201, e), (50202, h)] c hw (by first | (simp; done) | (simp; omega)) (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at v₁
  obtain ⟨v00, v01, v02⟩ := v₁
  have k₁' : ∀ r, ¬ (50200 ≤ r ∧ r < 50203) → c₁.nreg r = c.nreg r := fun r hr =>
    k₁ r (by first | (simp; done) | (simp; omega))
  have hA₁ : c₁.nreg ALLOC = c.nreg ALLOC := k₁' _ (by unfold ALLOC; omega)
  obtain ⟨c₂, k₂, e₂, hk₂, post₂, -⟩ := ptKey_meets P W c₁ e₁.wb_right
    ⟨E.hG, E.hW, by rw [hA₁, m₁, v00]; exact E.hwf, H, C, by rw [m₁, v00]; exact E.hD,
      ⟨by rwa [v01], by rwa [v01, v02], by rwa [v01, v02],
        by rw [m₁, v00]; exact E.hreg⟩⟩ (by rw [hA₁]; show _ + 15800 ≤ W; omega)
  replace hk₂ : k₂ ≤ 15800 := hk₂
  have pr' := post₂ H C (by rw [m₁, v00]; exact E.hD)
  have pr : PtRec P c₂ ((chainModel C).pos (Qof P) ⟨c₁.nreg 50201, c₁.nreg 50202⟩) C.radius :=
    pr'.1
  have fl : 6 ≤ c.nreg e → (c.nreg e < 2 * C.m + 6 ∨
      (chainModel C).param (Qof P) ⟨c.nreg e, c.nreg h⟩ = 0) → c₂.nreg 50216 = 1 := by
    have := pr'.2; rwa [v01, v02] at this
  rw [v01, v02] at pr
  obtain ⟨ax, hy', fr⟩ := pr
  have F₂ := exec_frameB e₂ wr_ptKey
  -- the copies
  obtain ⟨c₃, e₃, v₃, k₃, rr₃, m₃, rm₃, o₃⟩ := copies_exec (P := P) [(B, 50210), (B + 1, 50211),
    (B + 2, 50212), (B + 3, 50213), (B + 4, 50214), (B + 6, 50215), (B + 7, 50216),
    (B + 8, 50217), (B + 9, 50218), (B + 10, 50219)] c₂ e₂.wb_right (by first | (simp; done) | (simp; omega))
    (by first | (simp; done) | (simp; omega))
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at v₃
  obtain ⟨w0, w1, w2, w3, w4, w6, w7, w8, w9, w10⟩ := v₃
  have e₄ := Exec.constN (P := P) e₃.wb_right (B + 5) 0 (by omega)
  set c₄ : Config := { c₃ with nreg := upd c₃.nreg (B + 5) 0 } with hc₄
  have g₄ : ∀ r, r ≠ B + 5 → c₄.nreg r = c₃.nreg r := fun r hr => by
    rw [hc₄]; simp [upd_other _ _ _ hr]
  have ex : Exec P W (ptLoad e h B) c c₄ (3 + (k₂ + (10 + 1))) := by
    unfold ptLoad
    exact .seq e₁ (.seq e₂ (.seq e₃ e₄))
  refine ⟨c₄, _, ex, by omega, ⟨?_, ?_, ?_⟩, ?_, fun h1 h2 => by rw [g₄ _ (by omega), w7]; exact fl h1 h2⟩
  · exact absRec_copy' ax (by rw [g₄ _ (by omega), w0]) (by rw [g₄ _ (by omega), w1])
      (by rw [g₄ _ (by omega), w2]) (by rw [g₄ _ (by omega), w3])
  · have n4 : c₄.nreg (B + 4) = c₂.nreg 50214 := by rw [g₄ _ (by omega), w4]
    have n5 : c₄.nreg (B + 4 + 1) = 0 := by rw [hc₄]; simp
    have n6 : c₄.nreg (B + 4 + 2) = c₂.nreg 50215 := by
      rw [g₄ _ (by omega), show B + 4 + 2 = B + 6 by omega, w6]
    rcases hy' with ⟨k, hv⟩ | ⟨k, hv⟩ | ⟨k, hv, hl, he'⟩
    · exact Or.inl ⟨n4.trans k, hv⟩
    · exact Or.inr (Or.inl ⟨n4.trans k, hv⟩)
    · exact Or.inr (Or.inr ⟨n4.trans k, hv, n5, by rwa [n6], by rwa [n6]⟩)
  · intro h7
    have n7 : c₄.nreg (B + 7) = c₂.nreg 50216 := by rw [g₄ _ (by omega), w7]
    obtain ⟨s, hs, hl, hv⟩ := fr (by rwa [← n7])
    refine ⟨s, NFLoc.symPtIn_copy hs ?_ ?_ ?_, hl, hv⟩
    · rw [g₄ _ (by omega), w8]
    · rw [show B + 7 + 1 + 1 = B + 9 by omega, g₄ _ (by omega), w9]
    · rw [show B + 7 + 1 + 2 = B + 10 by omega, g₄ _ (by omega), w10]
  · refine ⟨fun r hr => ?_, fun r hr => ?_, ?_, ?_, ?_⟩
    · simp only [Bld, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr
      rw [g₄ r (by omega), k₃ r (by first | (simp; done) | (simp; omega)), F₂.1 r hr.1.1, k₁' r hr.1.2]
    · simp only [Bld, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr
      show c₃.rreg r = c.rreg r
      rw [rr₃, F₂.2.1 r hr.1.1, rr₁]
    · show c₃.nmem = c.nmem; rw [m₃, F₂.2.2.1, m₁]
    · show c₃.rmem = c.rmem; rw [rm₃, F₂.2.2.2.1, rm₁]
    · show c₃.output = c.output; rw [o₃, F₂.2.2.2.2, o₁]

theorem ptLoad_exec (c : Config) (hw : WordsBounded W c) (E : ShEnv P W H C z σ c)
    {e h B : ℕ} (he : 140000 ≤ e ∧ e < 150000) (hh : 140000 ≤ h ∧ h < 150000)
    (hB : 140000 ≤ B ∧ B + 11 ≤ 150000)
    (hen : c.nreg e < (chainModel C).W.n)
    (hp : ProperPos (chainModel C) (Qof P) P.n ⟨c.nreg e, c.nreg h⟩)
    (hy : c.nreg h = 0 ∨
      |((chainModel C).pos (Qof P) ⟨c.nreg e, c.nreg h⟩).2| < C.radius)
    (hroom : c.nreg ALLOC + 15800 ≤ W) :
    ∃ c' k, Exec P W (ptLoad e h B) c c' k ∧ k ≤ 15820 ∧
      PtRecB P c' B ((chainModel C).pos (Qof P) ⟨c.nreg e, c.nreg h⟩) C.radius ∧
      FrameB (Bld B) c c' := by
  obtain ⟨c', k, ex, hk, pr, fr, -⟩ := ptLoad_exec' c hw E.ld he hh hB hen hp hy hroom
  exact ⟨c', k, ex, hk, pr, fr⟩

end

end ShootCut

end Chazelle.Core
