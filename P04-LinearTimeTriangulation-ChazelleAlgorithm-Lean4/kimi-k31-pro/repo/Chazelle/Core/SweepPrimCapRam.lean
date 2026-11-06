module

public import Chazelle.Core.SweepPrimCap
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.SimpTactics
set_option maxHeartbeats 8000000

/-!
# Sweep RAM primitives (WP-D2), part 15: `capPrim` (the cap data, for WP-F)

Registers: slots `50130` (`u`), `50133` (`v`), `50136` (`w`); comparison bits `50141 … 50152`
(`cmp4` of `u`/`v`, `w`/`v`, `u`/`w`); `near` in `50153`, `far` in `50156`, its height code in
`50159`; orientation bits `50160`, `50161`; formulas at `50162` (extremum), `50170` (nearer arm
`u`), `50182` (cap direction `+1`).  Outputs `50210 … 50213` (`CapOut`).
-/

namespace Chazelle.Core

namespace SweepPrim

open Machine Machine.Stmt Programs SignK WalkKey NFLoc

@[expose] public section

/-! ## The program -/

/-- The host points of `u, v, w`. -/
def capLoad : Stmt :=
  .seq (.instr (.subN 50120 50201 50032)) (.seq (cvLoad 50130)
    (.seq (.instr (.copyN 50120 50201)) (.seq (cvLoad 50133)
      (.seq (.instr (.addN 50120 50201 50032)) (cvLoad 50136)))))

/-- The height comparisons. -/
def capBits : Stmt :=
  .seq (cmp4 50130 50133 50141) (.seq (cmp4 50136 50133 50145) (cmp4 50130 50136 50149))

/-- `v` below both neighbours. -/
def fBelow : BF := .and (.var 50142) (.var 50146)
/-- `v` above both neighbours. -/
def fAbove : BF := .and (.var 50141) (.var 50145)
/-- A local extremum. -/
def fExt : BF := .or fBelow fAbove
/-- The nearer arm is `u`. -/
def fNearU : BF := .or (.and fBelow (.var 50149)) (.and fAbove (.var 50150))
/-- The cap direction is `+1`. -/
def fPos : BF :=
  .not (.or (.and fBelow (.var 50160)) (.and fAbove (.and (.not (.var 50160)) (.not (.var 50161)))))

/-- Select `near` and `far`. -/
def capSel : Stmt :=
  .ifLtN 50170 50032
    (block (copies [(50153, 50136), (50154, 50137), (50155, 50138), (50156, 50130),
      (50157, 50131), (50158, 50132)]))
    (block (copies [(50153, 50130), (50154, 50131), (50155, 50132), (50156, 50136),
      (50157, 50137), (50158, 50138)]))

/-- The height code of `near`. -/
def capCode : Stmt :=
  .seq (.ifLtN 50153 50032 (.instr (.copyN 50159 50154)) (.instr (.copyN 50159 50155)))
    (.instr (.addN 50159 50159 50032))

/-- The orientation of `v`, `far`, `near`. -/
def capDet : Stmt := .seq (kbit 50133 50156 50153 2 50160) (kbit 50133 50156 50153 3 50161)

/-- The outputs. -/
def capOutS : Stmt := block [.copyN 50210 50162, .copyN 50211 50170, .copyN 50212 50159,
  .copyN 50213 50182]

/-- The core. -/
def capCore : Stmt :=
  .seq capLoad (.seq capBits (.seq (fExt.compile 50162) (.seq (fNearU.compile 50170)
    (.seq capSel (.seq capCode (.seq capDet (.seq (fPos.compile 50182) capOutS)))))))

/-- **The primitive `capPrim`.** -/
def capPrim : Stmt := .seq pHead capCore

theorem wr_capPrim : wr Bprim capPrim = true := by decide

/-! ## The contract -/

/-- The input condition: an index with two neighbours on the chain. -/
def CapIn (_ : Polygon) (_ : ℕ) (C : Chain) (c : Config) : Prop :=
  1 ≤ c.nreg 50201 ∧ c.nreg 50201 + 1 ≤ C.m

/-- The output condition. -/
def CapOut (P : Polygon) (C : Chain) (c c' : Config) : Prop :=
  let k := c.nreg 50201
  let u := C.vertex (k - 1)
  let v := C.vertex k
  let w := C.vertex (k + 1)
  let nearU := |u.2 - v.2| < |w.2 - v.2|
  let near := if nearU then u else w
  let far := if nearU then w else u
  BitIs c' 50210 (0 < (u.2 - v.2) * (w.2 - v.2)) ∧
    (0 < (u.2 - v.2) * (w.2 - v.2) → BitIs c' 50211 nearU) ∧
    1 ≤ c'.nreg 50212 ∧ c'.nreg 50212 ≤ P.n ∧
    (0 < (u.2 - v.2) * (w.2 - v.2) → ((Qof P).vtx (c'.nreg 50212 - 1)).2 = near.2) ∧
    (0 < (u.2 - v.2) * (w.2 - v.2) → u.2 ≠ w.2 →
      BitIs c' 50213 (¬ near.1 < (Geometry.lerp v far ((near.2 - v.2) / (far.2 - v.2))).1))

/-! ## Real arithmetic of the tests -/

theorem ext_iff' (u v w : ℝ) : 0 < (u - v) * (w - v) ↔ (v < u ∧ v < w) ∨ (u < v ∧ w < v) := by
  constructor
  · intro h
    rcases lt_trichotomy u v with h1 | h1 | h1
    · right; refine ⟨h1, ?_⟩; by_contra h2; push Not at h2; nlinarith
    · subst h1; simp at h
    · left; refine ⟨h1, ?_⟩; by_contra h2; push Not at h2; nlinarith
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> nlinarith

theorem nearU_iff' {u v w : ℝ} (h : (v < u ∧ v < w) ∨ (u < v ∧ w < v)) :
    |u - v| < |w - v| ↔ ((v < u ∧ v < w) ∧ u < w) ∨ ((u < v ∧ w < v) ∧ w < u) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]
    constructor
    · intro h; left; exact ⟨⟨h1, h2⟩, by linarith⟩
    · rintro (⟨-, h⟩ | ⟨⟨h3, -⟩, -⟩) <;> linarith
  · rw [abs_of_neg (by linarith), abs_of_neg (by linarith)]
    constructor
    · intro h; right; exact ⟨⟨h1, h2⟩, by linarith⟩
    · rintro (⟨⟨h3, -⟩, -⟩ | ⟨-, h⟩) <;> linarith

/-! ## Execution -/

/-- The host points of `u, v, w`. -/
theorem capLoad_exec {P : Polygon} {W : ℕ} {H : Host} {C : Chain} (c : Config)
    (hE : CEnv P W H C c) {k : ℕ} (h201 : c.nreg 50201 = k) (hk1 : 1 ≤ k) (hk2 : k + 1 ≤ C.m) :
    ∃ c' k', Exec P W capLoad c c' k' ∧ k' ≤ 81 * H.length + 63 ∧ CEnv P W H C c' ∧
      (∀ r, 50200 ≤ r → c'.nreg r = c.nreg r) ∧
      ∃ su sv sw : SymPt, SymPtIn c' 50130 su ∧ SymPtIn c' 50133 sv ∧ SymPtIn c' 50136 sw ∧
        su.Lt P.n ∧ sv.Lt P.n ∧ sw.Lt P.n ∧ su.eval (Qof P) = C.vertex (k - 1) ∧
        sv.eval (Qof P) = C.vertex k ∧ sw.eval (Qof P) = C.vertex (k + 1) := by
  have hBcv : ∀ (d : ℕ) (r : ℕ), 50200 ≤ r → Bcv d r = false → True := fun _ _ _ _ => trivial
  have keep200 : ∀ {c₁ c₂ : Config} {d : ℕ}, FrameB (Bcv d) c₁ c₂ → d < 50200 → d + 3 ≤ 50200 →
      ∀ r, 50200 ≤ r → c₂.nreg r = c₁.nreg r := fun hf _ hd r hr => hf.1 r (by
    simp only [Bcv, Bhost, Bool.or_eq_false_iff, beq_eq_false_iff_ne, decide_eq_false_iff_not]
    omega)
  have e₁ := Exec.subN (P := P) hE.wb 50120 50201 50032
  have hE₁ := hE.step e₁ (by decide)
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, hE₂, su, iu, lu, vu⟩ := cvLoad_exec _ hE₁ (k := k - 1)
    (by simp [h201, hE.r32]) (by omega) (dst := 50130) (by norm_num)
  have r₂ : ∀ r, 50200 ≤ r → c₂.nreg r = c.nreg r := fun r hr => by
    rw [keep200 f₂ (by norm_num) (by norm_num) r hr]; simp only
    rw [upd_other _ _ _ (by omega)]
  have e₃ := Exec.copyN (P := P) e₂.wb_right 50120 50201
  have hE₃ := hE₂.step e₃ (by decide)
  obtain ⟨c₄, k₄, e₄, hk₄, f₄, hE₄, sv, iv, lv, vv⟩ := cvLoad_exec _ hE₃ (k := k)
    (by simp only [upd_same]; rw [r₂ 50201 (by norm_num), h201]) (by omega)
    (dst := 50133) (by norm_num)
  have r₄ : ∀ r, 50200 ≤ r → c₄.nreg r = c.nreg r := fun r hr => by
    rw [keep200 f₄ (by norm_num) (by norm_num) r hr]; simp only
    rw [upd_other _ _ _ (by omega), r₂ r hr]
  have iu₄ : SymPtIn c₄ 50130 su := symPtIn_keep (symPtIn_of_eq iu fun j h1 h2 => by
    simp only [upd]; rw [ite_eq_right (by omega)]) f₄ (by intro j h1 h2; interval_cases j <;> decide)
  have e₅ := Exec.addN (P := P) e₄.wb_right 50120 50201 50032
    (by rw [r₄ _ (by norm_num), h201, hE₄.r32]; have := hE₄.NW; have := C.m_lt;
        have := hE₄.n_eq; omega)
  have hE₅ := hE₄.step e₅ (by decide)
  obtain ⟨c₆, k₆, e₆, hk₆, f₆, hE₆, sw, iw, lw, vw⟩ := cvLoad_exec _ hE₅ (k := k + 1)
    (by simp only [upd_same]; rw [r₄ 50201 (by norm_num), h201, hE₄.r32])
    (by omega) (dst := 50136) (by norm_num)
  have r₆ : ∀ r, 50200 ≤ r → c₆.nreg r = c.nreg r := fun r hr => by
    rw [keep200 f₆ (by norm_num) (by norm_num) r hr]; simp only
    rw [upd_other _ _ _ (by omega), r₄ r hr]
  have iu₆ : SymPtIn c₆ 50130 su := symPtIn_keep (symPtIn_of_eq iu₄ fun j h1 h2 => by
    simp only [upd]; rw [ite_eq_right (by omega)]) f₆ (by intro j h1 h2; interval_cases j <;> decide)
  have iv₆ : SymPtIn c₆ 50133 sv := symPtIn_keep (symPtIn_of_eq iv fun j h1 h2 => by
    simp only [upd]; rw [ite_eq_right (by omega)]) f₆ (by intro j h1 h2; interval_cases j <;> decide)
  have ex : Exec P W capLoad c c₆ (1 + (k₂ + (1 + (k₄ + (1 + k₆))))) :=
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ e₆))))
  exact ⟨c₆, _, ex, by omega, hE₆, r₆, su, sv, sw, iu₆, iv₆, iw, lu, lv, lw, vu, vv, vw⟩

theorem BitIs.decEq {c : Config} {r : ℕ} {p : Prop} [Decidable p] (h : BitIs c r p) :
    decide (c.nreg r = 1) = decide p := by
  by_cases hp : p
  · rw [decide_eq_true hp]; exact decide_eq_true (h.2.2 hp)
  · rw [decide_eq_false hp]; exact decide_eq_false fun h' => hp (h.2.1 h')

/-- The tests after the loads. -/
theorem capTail_exec {P : Polygon} {W : ℕ} {H : Host} {C : Chain} (c : Config)
    (hE : CEnv P W H C c) {su sv sw : SymPt} (iu : SymPtIn c 50130 su) (iv : SymPtIn c 50133 sv)
    (iw : SymPtIn c 50136 sw) (lu : su.Lt P.n) (lv : sv.Lt P.n) (lw : sw.Lt P.n) :
    ∃ c' k', Exec P W (.seq capBits (.seq (fExt.compile 50162) (.seq (fNearU.compile 50170)
        (.seq capSel (.seq capCode (.seq capDet (.seq (fPos.compile 50182) capOutS))))))) c c' k' ∧
      k' ≤ 4000 ∧
      let U := su.eval (Qof P)
      let V := sv.eval (Qof P)
      let X := sw.eval (Qof P)
      let nearU := |U.2 - V.2| < |X.2 - V.2|
      let near := if nearU then U else X
      let far := if nearU then X else U
      BitIs c' 50210 (0 < (U.2 - V.2) * (X.2 - V.2)) ∧
        (0 < (U.2 - V.2) * (X.2 - V.2) → BitIs c' 50211 nearU) ∧
        1 ≤ c'.nreg 50212 ∧ c'.nreg 50212 ≤ P.n ∧
        (0 < (U.2 - V.2) * (X.2 - V.2) → ((Qof P).vtx (c'.nreg 50212 - 1)).2 = near.2) ∧
        (0 < (U.2 - V.2) * (X.2 - V.2) → U.2 ≠ X.2 →
          BitIs c' 50213 (¬ near.1 < (Geometry.lerp V far ((near.2 - V.2) / (far.2 - V.2))).1)) := by
  have hG := hE.hG
  have hW := hE.hW
  have hW2 : 2 ≤ W := by omega
  -- the comparison bits
  obtain ⟨c₁, k₁, e₁, hk₁, f₁, a1, a2, -, -⟩ := cmp4_exec (base := 50141) hG hW c hE.wb
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) lu lv iu iv
  have iu₁ := symPtIn_keep iu f₁ (by intro j h1 h2; interval_cases j <;> decide)
  have iv₁ := symPtIn_keep iv f₁ (by intro j h1 h2; interval_cases j <;> decide)
  have iw₁ := symPtIn_keep iw f₁ (by intro j h1 h2; interval_cases j <;> decide)
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, a5, a6, -, -⟩ := cmp4_exec (base := 50145) hG hW c₁ e₁.wb_right
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) lw lv iw₁ iv₁
  have iu₂ := symPtIn_keep iu₁ f₂ (by intro j h1 h2; interval_cases j <;> decide)
  have iv₂ := symPtIn_keep iv₁ f₂ (by intro j h1 h2; interval_cases j <;> decide)
  have iw₂ := symPtIn_keep iw₁ f₂ (by intro j h1 h2; interval_cases j <;> decide)
  obtain ⟨c₃, k₃, e₃, hk₃, f₃, a9, a10, -, -⟩ := cmp4_exec (base := 50149) hG hW c₂ e₂.wb_right
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) lu lw iu₂ iw₂
  have iu₃ := symPtIn_keep iu₂ f₃ (by intro j h1 h2; interval_cases j <;> decide)
  have iv₃ := symPtIn_keep iv₂ f₃ (by intro j h1 h2; interval_cases j <;> decide)
  have iw₃ := symPtIn_keep iw₂ f₃ (by intro j h1 h2; interval_cases j <;> decide)
  have b41 := (a1.keep f₂ (by decide)).keep f₃ (by decide)
  have b42 := (a2.keep f₂ (by decide)).keep f₃ (by decide)
  have b45 := a5.keep f₃ (by decide)
  have b46 := a6.keep f₃ (by decide)
  have b49 := a9
  have b50 := a10
  simp only [Ys] at b41 b42 b45 b46 b49 b50
  dsimp only
  generalize hU : su.eval (Qof P) = U at b41 b42 b45 b46 b49 b50 ⊢
  generalize hV : sv.eval (Qof P) = V at b41 b42 b45 b46 b49 b50 ⊢
  generalize hX : sw.eval (Qof P) = X at b41 b42 b45 b46 b49 b50 ⊢
  -- the extremum
  have vars : ∀ r, r ∈ [50141, 50142, 50145, 50146, 50149, 50150] → c₃.nreg r ≤ 1 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [b41.1, b42.1, b45.1, b46.1, b49.1, b50.1]
  obtain ⟨c₄, k₄, e₄, hk₄, v₄, f₄⟩ := BF.compile_exec (P := P) hW2 fExt 50162 c₃ e₃.wb_right
    (by simp only [fExt, fBelow, fAbove, BF.VarsOK]
        exact ⟨⟨⟨by norm_num, vars _ (by simp)⟩, ⟨by norm_num, vars _ (by simp)⟩⟩,
          ⟨⟨by norm_num, vars _ (by simp)⟩, ⟨by norm_num, vars _ (by simp)⟩⟩⟩)
  have k34 : ∀ r, r < 50162 → c₄.nreg r = c₃.nreg r := fun r hr =>
    f₄.1 r (by sio only [BF.wset, decide_eq_false_iff_not])
  obtain ⟨c₅, k₅, e₅, hk₅, v₅, f₅⟩ := BF.compile_exec (P := P) hW2 fNearU 50170 c₄ e₄.wb_right
    (by simp only [fNearU, fBelow, fAbove, BF.VarsOK]
        refine ⟨⟨⟨⟨by norm_num, ?_⟩, ⟨by norm_num, ?_⟩⟩, ⟨by norm_num, ?_⟩⟩,
          ⟨⟨⟨by norm_num, ?_⟩, ⟨by norm_num, ?_⟩⟩, ⟨by norm_num, ?_⟩⟩⟩ <;>
        rw [k34 _ (by norm_num)] <;> exact vars _ (by simp))
  have k45 : ∀ r, r < 50170 → c₅.nreg r = c₄.nreg r := fun r hr =>
    f₅.1 r (by sio only [BF.wset, decide_eq_false_iff_not])
  have k35 : ∀ r, r < 50162 → c₅.nreg r = c₃.nreg r := fun r hr => by
    rw [k45 r (by omega), k34 r hr]
  have extE : fExt.eval (fun r => decide (c₃.nreg r = 1)) =
      decide ((V.2 < U.2 ∧ V.2 < X.2) ∨ (U.2 < V.2 ∧ X.2 < V.2)) := by
    simp only [fExt, fBelow, fAbove, BF.eval, b41.decEq, b42.decEq, b45.decEq, b46.decEq]
    simp only [Bool.decide_and, Bool.decide_or]
  have nearE : fNearU.eval (fun r => decide (c₄.nreg r = 1)) =
      decide (((V.2 < U.2 ∧ V.2 < X.2) ∧ U.2 < X.2) ∨ ((U.2 < V.2 ∧ X.2 < V.2) ∧ X.2 < U.2)) := by
    have e : ∀ r, r < 50162 → decide (c₄.nreg r = 1) = decide (c₃.nreg r = 1) := fun r hr => by
      rw [k34 r hr]
    simp only [fNearU, fBelow, fAbove, BF.eval, e _ (show 50141 < 50162 by norm_num),
      e _ (show 50142 < 50162 by norm_num), e _ (show 50145 < 50162 by norm_num),
      e _ (show 50146 < 50162 by norm_num), e _ (show 50149 < 50162 by norm_num),
      e _ (show 50150 < 50162 by norm_num), b41.decEq, b42.decEq, b45.decEq, b46.decEq,
      b49.decEq, b50.decEq]
    simp only [Bool.decide_and, Bool.decide_or]
  have ext_bit : BitIs c₅ 50162 (0 < (U.2 - V.2) * (X.2 - V.2)) := by
    refine BitIs.of_bf (f := fExt) (v := fun r => decide (c₃.nreg r = 1))
      (by rwx [k45 _ (by norm_num)]) ?_
    rw [extE, decide_eq_true_iff, ext_iff']
  have near_bit : BitIs c₅ 50170
      (((V.2 < U.2 ∧ V.2 < X.2) ∧ U.2 < X.2) ∨ ((U.2 < V.2 ∧ X.2 < V.2) ∧ X.2 < U.2)) := by
    refine BitIs.of_bf (f := fNearU) (v := fun r => decide (c₄.nreg r = 1)) v₅ ?_
    rw [nearE, decide_eq_true_iff]
  -- the environment so far
  have hE₅ : CEnv P W H C c₅ :=
    ((((hE.frame f₁ e₁.wb_right (by decide)).frame f₂ e₂.wb_right (by decide)).frame f₃
      e₃.wb_right (by decide)).frame f₄ e₄.wb_right (by decide)).frame f₅ e₅.wb_right (by decide)
  have iu₅ : SymPtIn c₅ 50130 su := symPtIn_of_eq iu₃ fun j h1 h2 => k35 j (by omega)
  have iv₅ : SymPtIn c₅ 50133 sv := symPtIn_of_eq iv₃ fun j h1 h2 => k35 j (by omega)
  have iw₅ : SymPtIn c₅ 50136 sw := symPtIn_of_eq iw₃ fun j h1 h2 => k35 j (by omega)
  -- the selection
  set sel : Prop := ((V.2 < U.2 ∧ V.2 < X.2) ∧ U.2 < X.2) ∨ ((U.2 < V.2 ∧ X.2 < V.2) ∧ X.2 < U.2)
    with hsel
  obtain ⟨c₆, k₆, e₆, hk₆, sn, sf, isn, isf, hsn, r₆, m₆, rr₆, rm₆, o₆⟩ : ∃ c₆ k₆,
      Exec P W capSel c₅ c₆ k₆ ∧ k₆ ≤ 8 ∧ ∃ sn sf : SymPt, SymPtIn c₆ 50153 sn ∧
        SymPtIn c₆ 50156 sf ∧ (sn, sf) = (if sel then (su, sw) else (sw, su)) ∧
        (∀ r, (r < 50153 ∨ 50158 < r) → c₆.nreg r = c₅.nreg r) ∧ c₆.nmem = c₅.nmem ∧
        c₆.rreg = c₅.rreg ∧ c₆.rmem = c₅.rmem ∧ c₆.output = c₅.output := by
    have h32 := hE₅.r32
    have cp := fun (l : List (ℕ × ℕ)) => copies_exec (P := P) l c₅ e₅.wb_right
    by_cases hs : sel
    · have h1 : c₅.nreg 50170 = 1 := near_bit.2.2 hs
      obtain ⟨c₆, e, h3, h3', hrr, hm, hrm, ho⟩ := cp [(50153, 50130), (50154, 50131),
        (50155, 50132), (50156, 50136), (50157, 50137), (50158, 50138)] (by decide) (by decide)
      refine ⟨c₆, _, .ifLtN_false (by rwo [h1, h32]) e, by simp, su, sw, ?_, ?_,
        by simp [hs], fun r hr => h3' r (by sio), hm, hrr, hrm, ho⟩
      · exact symPtIn_copy iu₅ (h3 (50153, 50130) (by simp)) (h3 (50154, 50131) (by simp))
          (h3 (50155, 50132) (by simp))
      · exact symPtIn_copy iw₅ (h3 (50156, 50136) (by simp)) (h3 (50157, 50137) (by simp))
          (h3 (50158, 50138) (by simp))
    · have h0 : c₅.nreg 50170 = 0 := by
        have := near_bit.1; have := near_bit.2; by_contra h; apply hs; exact near_bit.2.1 (by omega)
      obtain ⟨c₆, e, h3, h3', hrr, hm, hrm, ho⟩ := cp [(50153, 50136), (50154, 50137),
        (50155, 50138), (50156, 50130), (50157, 50131), (50158, 50132)] (by decide) (by decide)
      refine ⟨c₆, _, .ifLtN_true (by rwo [h0, h32]) e, by simp, sw, su, ?_, ?_,
        by simp [hs], fun r hr => h3' r (by sio), hm, hrr, hrm, ho⟩
      · exact symPtIn_copy iw₅ (h3 (50153, 50136) (by simp)) (h3 (50154, 50137) (by simp))
          (h3 (50155, 50138) (by simp))
      · exact symPtIn_copy iu₅ (h3 (50156, 50130) (by simp)) (h3 (50157, 50131) (by simp))
          (h3 (50158, 50132) (by simp))
  have hE₆ : CEnv P W H C c₆ := hE₅.keep e₆.wb_right m₆ fun r hr => r₆ r (by
    sio only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr)
  have lsn : sn.Lt P.n := by
    have := congrArg Prod.fst hsn; simp only at this; rw [this]; split_ifs <;> assumption
  have lsf : sf.Lt P.n := by
    have := congrArg Prod.snd hsn; simp only at this; rw [this]; split_ifs <;> assumption
  -- the height code
  obtain ⟨c₇, k₇, e₇, hk₇, v59, r₇, m₇, rr₇, rm₇, o₇⟩ : ∃ c₇ k₇, Exec P W capCode c₆ c₇ k₇ ∧
      k₇ ≤ 4 ∧ c₇.nreg 50159 = shv sn + 1 ∧ (∀ r, r ≠ 50159 → c₇.nreg r = c₆.nreg r) ∧
      c₇.nmem = c₆.nmem ∧ c₇.rreg = c₆.rreg ∧ c₇.rmem = c₆.rmem ∧ c₇.output = c₆.output := by
    have h32 : c₆.nreg 50032 = 1 := hE₆.r32
    have hnW : shv sn + 1 ≤ W := by
      cases sn with
      | vtx i => sio only [shv, SymPt.Lt] at lsn ⊢
      | onEdge e h => sio only [shv, SymPt.Lt] at lsn ⊢
    cases sn with
    | vtx i =>
      obtain ⟨i0, i1⟩ := isn
      have e₁ := Exec.copyN (P := P) e₆.wb_right 50159 50154
      have e₂ := Exec.addN (P := P) e₁.wb_right 50159 50159 50032 (by
        simp only [upd_same, upd_other _ _ _ (show (50032 : ℕ) ≠ 50159 by decide)]
        rw [i1, h32]; sio only [shv] at hnW)
      refine ⟨_, _, .seq (.ifLtN_true (by rwo [i0, h32]) e₁) e₂, by omega, ?_,
        fun r hr => by simp [upd_other _ _ _ hr], rfl, rfl, rfl, rfl⟩
      simp only [upd_same, upd_other _ _ _ (show (50032 : ℕ) ≠ 50159 by decide)]
      rwr [i1, h32]
    | onEdge e h =>
      obtain ⟨i0, i1, i2⟩ := isn
      have e₁ := Exec.copyN (P := P) e₆.wb_right 50159 50155
      have e₂ := Exec.addN (P := P) e₁.wb_right 50159 50159 50032 (by
        simp only [upd_same, upd_other _ _ _ (show (50032 : ℕ) ≠ 50159 by decide)]
        rw [i2, h32]; sio only [shv] at hnW)
      refine ⟨_, _, .seq (.ifLtN_false (by rwo [i0, h32]) e₁) e₂, by omega, ?_,
        fun r hr => by simp [upd_other _ _ _ hr], rfl, rfl, rfl, rfl⟩
      simp only [upd_same, upd_other _ _ _ (show (50032 : ℕ) ≠ 50159 by decide)]
      rwr [i2, h32]
  have hE₇ : CEnv P W H C c₇ := hE₆.keep e₇.wb_right m₇ fun r hr => r₇ r (by
    sio only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr)
  have isn₇ : SymPtIn c₇ 50153 sn := symPtIn_of_eq isn fun j h1 h2 => r₇ j (by omega)
  have isf₇ : SymPtIn c₇ 50156 sf := symPtIn_of_eq isf fun j h1 h2 => r₇ j (by omega)
  have iv₇ : SymPtIn c₇ 50133 sv := symPtIn_of_eq iv₅ fun j h1 h2 => by
    rw [r₇ j (by omega), r₆ j (by omega)]
  -- the orientation bits
  obtain ⟨c₈, k₈, e₈, hk₈, f₈, d₈, t₈⟩ := kbit_exec (op := 2) (dst := 50160) hG hW c₇
    e₇.wb_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) lv lsf lsn
    iv₇ isf₇ isn₇
  have iv₈ := symPtIn_keep iv₇ f₈ (by intro j h1 h2; interval_cases j <;> decide)
  have isf₈ := symPtIn_keep isf₇ f₈ (by intro j h1 h2; interval_cases j <;> decide)
  have isn₈ := symPtIn_keep isn₇ f₈ (by intro j h1 h2; interval_cases j <;> decide)
  obtain ⟨c₉, k₉, e₉, hk₉, f₉, d₉, t₉⟩ := kbit_exec (op := 3) (dst := 50161) hG hW c₈
    e₈.wb_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) lv lsf lsn
    iv₈ isf₈ isn₈
  have b60 : BitIs c₉ 50160 (0 < det V (sf.eval (Qof P)) (sn.eval (Qof P))) := by
    have := BitIs.keep ⟨d₈, t₈⟩ f₉ (by decide)
    simp only [SignTest, hV] at this; exact this
  have b61 : BitIs c₉ 50161 (det V (sf.eval (Qof P)) (sn.eval (Qof P)) = 0) := by
    have : BitIs c₉ 50161 _ := ⟨d₉, t₉⟩
    simp only [SignTest, hV] at this; exact this
  -- transport of the early bits to `c₉`
  have k59 : ∀ r, 50100 ≤ r → r < 50153 → c₉.nreg r = c₅.nreg r := fun r hr' hr => by
    rw [f₉.1 r (by simp only [Bkb, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not,
        beq_eq_false_iff_ne]; omega),
      f₈.1 r (by simp only [Bkb, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not,
        beq_eq_false_iff_ne]; omega), r₇ r (by omega), r₆ r (by omega)]
  have g41 : BitIs c₉ 50141 (U.2 < V.2) := b41.of_eq (by rw [k59 _ (by norm_num) (by norm_num), k35 _ (by norm_num)])
  have g42 : BitIs c₉ 50142 (V.2 < U.2) := b42.of_eq (by rw [k59 _ (by norm_num) (by norm_num), k35 _ (by norm_num)])
  have g45 : BitIs c₉ 50145 (X.2 < V.2) := b45.of_eq (by rw [k59 _ (by norm_num) (by norm_num), k35 _ (by norm_num)])
  have g46 : BitIs c₉ 50146 (V.2 < X.2) := b46.of_eq (by rw [k59 _ (by norm_num) (by norm_num), k35 _ (by norm_num)])
  have h9w := e₉.wb_right
  obtain ⟨c₁₀, k₁₀, e₁₀, hk₁₀, v₁₀, f₁₀⟩ := BF.compile_exec (P := P) hW2 fPos 50182 c₉ h9w
    (by simp only [fPos, fBelow, fAbove, BF.VarsOK]
        exact ⟨⟨⟨⟨by norm_num, g42.1⟩, ⟨by norm_num, g46.1⟩⟩, ⟨by norm_num, b60.1⟩⟩,
          ⟨⟨⟨by norm_num, g41.1⟩, ⟨by norm_num, g45.1⟩⟩, ⟨⟨by norm_num, b60.1⟩,
            ⟨by norm_num, b61.1⟩⟩⟩⟩)
  have k910 : ∀ r, r < 50182 → c₁₀.nreg r = c₉.nreg r := fun r hr =>
    f₁₀.1 r (by sio only [BF.wset, decide_eq_false_iff_not])
  set below : Prop := V.2 < U.2 ∧ V.2 < X.2 with hbelow
  set above : Prop := U.2 < V.2 ∧ X.2 < V.2 with habove
  set dt := det V (sf.eval (Qof P)) (sn.eval (Qof P)) with hdt
  have posE : fPos.eval (fun r => decide (c₉.nreg r = 1)) =
      decide (¬ ((below ∧ 0 < dt) ∨ (above ∧ ¬ 0 < dt ∧ ¬ dt = 0))) := by
    simp only [fPos, fBelow, fAbove, BF.eval, g41.decEq, g42.decEq, g45.decEq, g46.decEq,
      b60.decEq, b61.decEq]
    simp only [hbelow, habove, Bool.decide_and, Bool.decide_or, decide_not]
  have pos_bit : BitIs c₁₀ 50182 (¬ ((below ∧ 0 < dt) ∨ (above ∧ ¬ 0 < dt ∧ ¬ dt = 0))) :=
    BitIs.of_bf (f := fPos) (v := fun r => decide (c₉.nreg r = 1)) v₁₀
      (by rw [posE, decide_eq_true_iff])
  -- the outputs
  obtain ⟨c₁₁, k₁₁, e₁₁, hk₁₁, q⟩ : ∃ c₁₁ k₁₁, Exec P W capOutS c₁₀ c₁₁ k₁₁ ∧ k₁₁ = 4 ∧
      (c₁₁.nreg 50210 = c₁₀.nreg 50162 ∧ c₁₁.nreg 50211 = c₁₀.nreg 50170 ∧
        c₁₁.nreg 50212 = c₁₀.nreg 50159 ∧ c₁₁.nreg 50213 = c₁₀.nreg 50182) := by
    have hw := e₁₀.wb_right
    unfold capOutS
    exec_block
    exact ⟨rfl, by config_simp, by config_simp, by config_simp, by config_simp⟩
  obtain ⟨q10, q11, q12, q13⟩ := q
  have ex : Exec P W (.seq capBits (.seq (fExt.compile 50162) (.seq (fNearU.compile 50170)
      (.seq capSel (.seq capCode (.seq capDet (.seq (fPos.compile 50182) capOutS))))))) c c₁₁
      ((k₁ + (k₂ + k₃)) + (k₄ + (k₅ + (k₆ + (k₇ + ((k₈ + k₉) + (k₁₀ + k₁₁))))))) :=
    .seq (.seq e₁ (.seq e₂ e₃)) (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ (.seq (.seq e₈ e₉)
      (.seq e₁₀ e₁₁))))))
  have hsz1 : fExt.size = 7 := rfl
  have hsz2 : fNearU.size = 11 := rfl
  have hsz3 : fPos.size = 16 := rfl
  -- values at the end
  have c62 : c₁₀.nreg 50162 = c₅.nreg 50162 := by
    rw [k910 _ (by norm_num), f₉.1 _ (by decide), f₈.1 _ (by decide), r₇ _ (by decide),
      r₆ _ (by norm_num)]
  have c70 : c₁₀.nreg 50170 = c₅.nreg 50170 := by
    rw [k910 _ (by norm_num), f₉.1 _ (by decide), f₈.1 _ (by decide), r₇ _ (by decide),
      r₆ _ (by norm_num)]
  have c59 : c₁₀.nreg 50159 = shv sn + 1 := by
    rw [k910 _ (by norm_num), f₉.1 _ (by decide), f₈.1 _ (by decide), v59]
  have hsnE : sn = if sel then su else sw := by
    have := congrArg Prod.fst hsn; simp only at this; rw [this]; split_ifs <;> rfl
  have hsfE : sf = if sel then sw else su := by
    have := congrArg Prod.snd hsn; simp only at this; rw [this]; split_ifs <;> rfl
  refine ⟨c₁₁, _, ex, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ext_bit.of_eq (by rw [q10, c62])
  · intro hext
    refine (near_bit.of_eq (by rw [q11, c70])).congr ?_
    exact (nearU_iff' ((ext_iff' _ _ _).1 hext)).symm
  · rwo [q12, c59]
  · rw [q12, c59]
    cases sn with
    | vtx i => sio only [shv, SymPt.Lt] at lsn ⊢
    | onEdge e h => sio only [shv, SymPt.Lt] at lsn ⊢
  · intro hext
    have hselE : sel ↔ |U.2 - V.2| < |X.2 - V.2| := (nearU_iff' ((ext_iff' _ _ _).1 hext)).symm
    rw [q12, c59, Nat.add_sub_cancel, ← eval_snd_shv, hsnE]
    by_cases hs : sel
    · rw [ite_eq_left hs, ite_eq_left (hselE.1 hs), hU]
    · rw [ite_eq_right hs, ite_eq_right (fun h => hs (hselE.2 h)), hX]
  · intro hext hUX
    have hselE : sel ↔ |U.2 - V.2| < |X.2 - V.2| := (nearU_iff' ((ext_iff' _ _ _).1 hext)).symm
    refine (pos_bit.of_eq (by rw [q13])).congr ?_
    have hext' := (ext_iff' _ _ _).1 hext
    by_cases hs : sel
    · have hn : |U.2 - V.2| < |X.2 - V.2| := hselE.1 hs
      simp only [ite_eq_left hn]
      rw [hdt, hsnE, hsfE, ite_eq_left hs, ite_eq_left hs, hU, hX]
      have hne : X.2 ≠ V.2 := by rcases hext' with ⟨-, h⟩ | ⟨-, h⟩ <;> [exact ne_of_gt h; exact ne_of_lt h]
      rw [capx_iff V X U hne]
      constructor
      · intro h1 h2; apply h1
        rcases h2 with ⟨h3, h4⟩ | ⟨h3, h4, h5⟩
        · left; exact ⟨⟨by rcases hext' with h | h <;> [exact h.1; exact absurd h3 (by linarith [h.2])], h3⟩, h4⟩
        · right; exact ⟨⟨by rcases hext' with h | h <;> [exact absurd h3 (by linarith [h.2]); exact h.1], h3⟩, h4, h5⟩
      · intro h1 h2; apply h1
        rcases h2 with ⟨⟨-, h3⟩, h4⟩ | ⟨⟨-, h3⟩, h4, h5⟩
        · left; exact ⟨h3, h4⟩
        · right; exact ⟨h3, h4, h5⟩
    · have hn : ¬ |U.2 - V.2| < |X.2 - V.2| := fun h => hs (hselE.2 h)
      simp only [ite_eq_right hn]
      rw [hdt, hsnE, hsfE, ite_eq_right hs, ite_eq_right hs, hU, hX]
      have hne : U.2 ≠ V.2 := by rcases hext' with ⟨h, -⟩ | ⟨h, -⟩ <;> [exact ne_of_gt h; exact ne_of_lt h]
      rw [capx_iff V U X hne]
      constructor
      · intro h1 h2; apply h1
        rcases h2 with ⟨h3, h4⟩ | ⟨h3, h4, h5⟩
        · left; exact ⟨⟨h3, by rcases hext' with h | h <;> [exact h.2; exact absurd h3 (by linarith [h.1])]⟩, h4⟩
        · right; exact ⟨⟨h3, by rcases hext' with h | h <;> [exact absurd h3 (by linarith [h.1]); exact h.2]⟩, h4, h5⟩
      · intro h1 h2; apply h1
        rcases h2 with ⟨⟨h3, -⟩, h4⟩ | ⟨⟨h3, -⟩, h4, h5⟩
        · left; exact ⟨h3, h4⟩
        · right; exact ⟨h3, h4, h5⟩

/-- **Contract of `capPrim`** (at most `10100` steps). -/
theorem capPrim_meets : Meets capPrim primBands (PrimPre CapIn) (PrimPost CapOut)
    (fun _ _ => 10100) := by
  refine prim_meets (K := 9300) (fun _ => id) wr_capPrim ?_
  intro P W H C c₀ c _hC hE ⟨hk1, hk2⟩ hinp
  have h201 : c.nreg 50201 = c₀.nreg 50201 := hinp 50201 (by norm_num) (by norm_num)
  obtain ⟨c₁, k₁, e₁, hk₁, hE₁, -, su, sv, sw, iu, iv, iw, lu, lv, lw, vu, vv, vw⟩ :=
    capLoad_exec c hE h201 hk1 hk2
  obtain ⟨c₂, k₂, e₂, hk₂, hout⟩ := capTail_exec c₁ hE₁ iu iv iw lu lv lw
  have hlen := hE.hlen
  refine ⟨c₂, _, .seq e₁ e₂, by omega, ?_⟩
  simp only [vu, vv, vw] at hout
  exact hout

/-! ## The height index of a chain vertex -/

/-- The core of `hvPrim`: the height index of the host point of chain vertex `50201`. -/
def hvCore : Stmt :=
  .seq (.instr (.copyN 50120 50201)) (.seq (cvLoad 50130)
    (.ifLtN 50130 50032 (.instr (.copyN 50210 50131)) (.instr (.copyN 50210 50132))))

/-- **The primitive `hvPrim`.** -/
def hvPrim : Stmt := .seq pHead hvCore

theorem wr_hvPrim : wr Bprim hvPrim = true := by decide

/-- The input condition of `hvPrim`. -/
def HvIn (_ : Polygon) (_ : ℕ) (C : Chain) (c : Config) : Prop := c.nreg 50201 ≤ C.m

/-- The output condition of `hvPrim`: a vertex of `Q` at the height of the chain vertex. -/
def HvOut (P : Polygon) (C : Chain) (c c' : Config) : Prop :=
  c'.nreg 50210 < P.n ∧ ((Qof P).vtx (c'.nreg 50210)).2 = (C.vertex (c.nreg 50201)).2

/-- **Contract of `hvPrim`** (at most `3000` steps). -/
theorem hvPrim_meets : Meets hvPrim primBands (PrimPre HvIn) (PrimPost HvOut)
    (fun _ _ => 3000) := by
  refine prim_meets (K := 2200) (fun _ => id) wr_hvPrim ?_
  intro P W H C c₀ c _hC hE hk hinp
  have h201 : c.nreg 50201 = c₀.nreg 50201 := hinp 50201 (by norm_num) (by norm_num)
  have e₁ := Exec.copyN (P := P) hE.wb 50120 50201
  have hE₁ := hE.step e₁ (by decide)
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, hE₂, sp, isp, lsp, vsp⟩ := cvLoad_exec _ hE₁ (k := c₀.nreg 50201)
    (by simp only [upd_same]; exact h201) hk (dst := 50130) (by norm_num)
  have h32 := hE₂.r32
  have hlen := hE.hlen
  have hw₂ := e₂.wb_right
  have key : ∀ (c₃ : Config) (v : ℕ), c₃.nreg 50210 = v → v = shv sp →
      HvOut P C c₀ c₃ := fun c₃ v h1 h2 => by
    refine ⟨by rw [h1, h2]; cases sp <;> simp only [shv, SymPt.Lt] at lsp ⊢ <;> omega, ?_⟩
    rw [h1, h2, ← eval_snd_shv, vsp]
  cases sp with
  | vtx i =>
    obtain ⟨i0, i1⟩ := isp
    have e₃ := Exec.copyN (P := P) hw₂ 50210 50131
    exact ⟨_, _, .seq e₁ (.seq e₂ (.ifLtN_true (by rwo [i0, h32]) e₃)), by omega,
      key _ (c₂.nreg 50131) (by simp) (by simp [i1, shv])⟩
  | onEdge e h =>
    obtain ⟨i0, i1, i2⟩ := isp
    have e₃ := Exec.copyN (P := P) hw₂ 50210 50132
    exact ⟨_, _, .seq e₁ (.seq e₂ (.ifLtN_false (by rwo [i0, h32]) e₃)), by omega,
      key _ (c₂.nreg 50132) (by simp) (by simp [i2, shv])⟩

end

end SweepPrim

end Chazelle.Core
