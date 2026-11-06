module

public import Chazelle.Core.NFBuildPhaseB
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.MiscTactics
set_option maxHeartbeats 4000000

/-!
# WP-C (BuildNF), RAM part 25: the empty chord list

For `K = 0`, `buildNF` is the normal form of the root region alone: one arc `(0, 0)` (the whole
walk) whose weight is the number of counted edges (`arcWt_self`).  `zeroCase` writes it at
`H = ALLOC` (24 words) — `zeroCase_exec`.
-/

namespace Chazelle.Core

open Set
open Chazelle.Chain (sideInArc)

@[expose] public section

/-- **The weight of the full arc** `(x, x)` is the number of counted edges. -/
theorem Model.arcWt_self (M : Model) {lo hi : ℕ}
    (hc : ∀ p, p < M.W.n → (M.counted p ↔ lo ≤ p ∧ p < hi)) (hhi : hi ≤ M.W.n) (x : ℝ) :
    M.arcWt x x = hi - lo := by
  unfold Model.arcWt
  have hset : {p : ℕ | p < M.W.n ∧ M.counted p ∧ ∃ t : ℝ, 0 < t ∧ t < 1 ∧
      sideInArc x x (p + t)} = ↑(Finset.Ico lo hi) := by
    ext p
    simp only [mem_ofPred_eq, Finset.coe_Ico, mem_Ico]
    rw [Model.mem_arcEdges_iff, ite_eq_right (lt_irrefl x)]
    constructor
    · rintro ⟨hp, hcp, -⟩
      exact (hc p hp).1 hcp
    · rintro ⟨h1, h2⟩
      refine ⟨by omega, (hc p (by omega)).2 ⟨h1, h2⟩, ?_⟩
      by_cases h : (p : ℝ) < x
      · exact Or.inl h
      · right; push Not at h; linarith
  rw [hset, ncard_coe_finset, Nat.card_Ico]

namespace BuildRam

open Machine Machine.Stmt Programs SignK NFLoc

/-- The normal form for `K = 0`. -/
def zeroCase : Stmt :=
  .seq (block [.copyN 44000 9999, .constN 44030 24, .addN 9999 9999 44030]) (.seq lohiS
    (block [.constN 44033 1, .copyN 44031 44000,
      .constN 44032 0, .storeN 44031 44032, .addN 44031 44031 44033,
      .constN 44032 1, .storeN 44031 44032, .addN 44031 44031 44033,
      .storeN 44031 44032, .addN 44031 44031 44033,
      .constN 44034 12, .addN 44032 44000 44034, .storeN 44031 44032,
      .addN 44031 44031 44033,
      .storeN 44031 44032, .addN 44031 44031 44033,
      .constN 44034 17, .addN 44032 44000 44034, .storeN 44031 44032,
      .addN 44031 44031 44033,
      .constN 44034 22, .addN 44032 44000 44034, .storeN 44031 44032,
      .addN 44031 44031 44033,
      .constN 44034 23, .addN 44032 44000 44034, .storeN 44031 44032,
      .addN 44031 44031 44033,
      .copyN 44032 44000, .storeN 44031 44032, .addN 44031 44031 44033,
      .constN 44032 0, .storeN 44031 44032, .addN 44031 44031 44033,
      .copyN 44032 44000, .storeN 44031 44032, .addN 44031 44031 44033,
      .constN 44032 0, .storeN 44031 44032, .addN 44031 44031 44033,
      .storeN 44031 44032, .addN 44031 44031 44033,
      .storeN 44031 44032, .addN 44031 44031 44033,
      .storeN 44031 44032, .addN 44031 44031 44033,
      .storeN 44031 44032, .addN 44031 44031 44033,
      .storeN 44031 44032, .addN 44031 44031 44033,
      .constN 44032 1, .storeN 44031 44032, .addN 44031 44031 44033,
      .constN 44032 0, .storeN 44031 44032, .addN 44031 44031 44033,
      .storeN 44031 44032, .addN 44031 44031 44033,
      .constN 44032 1, .storeN 44031 44032, .addN 44031 44031 44033,
      .copyN 44032 44021, .storeN 44031 44032, .addN 44031 44031 44033,
      .constN 44032 0, .storeN 44031 44032, .addN 44031 44031 44033,
      .storeN 44031 44032,
      .copyN 40003 44000]))

/-- The 24 words written by `zeroCase` at `H`. -/
def zeroW (H wt : ℕ) (f : ℕ) : ℕ :=
  if f = 1 ∨ f = 2 ∨ f = 17 ∨ f = 20 then 1 else if f = 3 ∨ f = 4 then H + 12
  else if f = 5 then H + 17 else if f = 6 then H + 22 else if f = 7 then H + 23
  else if f = 8 ∨ f = 10 then H else if f = 21 then wt else 0

theorem zeroW_eq (H wt f : ℕ) (hf : f < 24) : zeroW H wt f =
    [0, 1, 1, H + 12, H + 12, H + 17, H + 22, H + 23, H, 0, H, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, wt,
      0, 0].getD f 0 := by
  unfold zeroW
  interval_cases f <;> simp

/-- **The layout for `K = 0`.** -/
theorem nfAt_zero {M : Model} {Q : Polygon} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ}
    (hL : L.length = 0) {m : ℕ → ℕ} {H : ℕ}
    (hm : ∀ f, f < 24 → m (H + f) =
      zeroW H (BuildNF.regWt M Q L E 0) f) :
    NFAt m H (BuildNF.buildNF M Q L E) := by
  have hL'  := List.length_eq_zero_iff.1 hL
  subst hL'
  have hz  := hm
  have v : ∀ f, f < 24 → m (H + f) = [0, 1, 1, H + 12, H + 12, H + 17, H + 22, H + 23, H, 0, H, 0,
      0, 0, 0, 0, 0, 1, 0, 0, 1, BuildNF.regWt M Q [] E 0, 0, 0].getD f 0 := fun f hf => by
    rw [hz f hf, zeroW_eq _ _ _ hf]
  have e0 : m H = 0 := v 0 (by norm_num)
  have e1 : m (H + 1) = 1 := v 1 (by norm_num)
  have e2 : m (H + 2) = 1 := v 2 (by norm_num)
  have e4 : m (H + 4) = H + 12 := v 4 (by norm_num)
  have e5 : m (H + 5) = H + 17 := v 5 (by norm_num)
  have e6 : m (H + 6) = H + 22 := v 6 (by norm_num)
  have e7 : m (H + 7) = H + 23 := v 7 (by norm_num)
  have e9 : m (H + 9) = 0 := v 9 (by norm_num)
  have e11 : m (H + 11) = 0 := v 11 (by norm_num)
  have e12 : m (H + 12) = 0 := v 12 (by norm_num)
  have e13 : m (H + 13) = 0 := v 13 (by norm_num)
  have e14 : m (H + 14) = 0 := v 14 (by norm_num)
  have e15 : m (H + 15) = 0 := v 15 (by norm_num)
  have e16 : m (H + 16) = 0 := v 16 (by norm_num)
  have e17 : m (H + 17) = 1 := v 17 (by norm_num)
  have e18 : m (H + 18) = 0 := v 18 (by norm_num)
  have e19 : m (H + 19) = 0 := v 19 (by norm_num)
  have e20 : m (H + 20) = 1 := v 20 (by norm_num)
  have e21 : m (H + 21) = BuildNF.regWt M Q [] E 0 := v 21 (by norm_num)
  have e22 : m (H + 22) = 0 := v 22 (by norm_num)
  have e23 : m (H + 23) = 0 := v 23 (by norm_num)
  have hA : BuildNF.arcList M Q [] E = [⟨0, ⟨0, 0⟩, ⟨0, 0⟩⟩] := by
    ufs BuildNF.arcList
  have hRA : BuildNF.regArcs M Q [] E 0 = [0] := by
    unfold BuildNF.regArcs; rwd [hA]
  have hRC : BuildNF.regChords M Q [] E 0 = [] := by
    ufs BuildNF.regChords
  refine ⟨?_, ?_, ?_, ?_, ?_, fun i hi => ?_, fun j hj => ?_, fun r hr => ?_, fun j hj => ?_,
    fun k hk => ?_, fun r hr => ?_⟩
  · rw [e0]; simp [BuildNF.buildNF]
  · rw [e1]; show 1 = (BuildNF.arcList M Q [] E).length; rwr [hA]
  · rw [e2]; simp [BuildNF.buildNF]
  · rwr [e9]
  · rwr [e11]
  · simp [BuildNF.buildNF] at hi
  · have hj' : j = 0 := by
      have : (BuildNF.buildNF M Q [] E).arcs = BuildNF.arcList M Q [] E := rfl
      rw [this, hA] at hj; simp at hj; exact hj
    subst hj'
    have ha : (BuildNF.buildNF M Q [] E).arc 0 = ⟨0, ⟨0, 0⟩, ⟨0, 0⟩⟩ := by
      unfold NF.arc; show (BuildNF.arcList M Q [] E).getD 0 _ = _; rwr [hA]
    rw [e4, ha]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [Nat.mul_zero, Nat.add_zero, show H + 12 = H + 12 from rfl, e12]
    · rw [Nat.mul_zero, Nat.add_zero, show H + 12 + 1 = H + 13 from rfl, e13]
    · rw [Nat.mul_zero, Nat.add_zero, show H + 12 + 2 = H + 14 from rfl, e14]
    · rw [Nat.mul_zero, Nat.add_zero, show H + 12 + 3 = H + 15 from rfl, e15]
    · rw [Nat.mul_zero, Nat.add_zero, show H + 12 + 4 = H + 16 from rfl, e16]
  · have hr' : r = 0 := by simpa [BuildNF.buildNF] using hr
    subst hr'
    have hreg := (show (BuildNF.buildNF M Q [] E).region 0 =
      ⟨BuildNF.regArcs M Q [] E 0, BuildNF.regChords M Q [] E 0, BuildNF.regWt M Q [] E 0⟩ by
        ufr NF.region BuildNF.buildNF)
    rw [e5, hreg, hRA, hRC]
    simp only [Nat.mul_zero, Nat.add_zero]
    refine ⟨?_, ?_, ?_, fun t ht => ?_, fun t ht => ?_⟩
    · rwr [show H + 17 = H + 17 from rfl, e17]
    · rwr [show H + 17 + 2 = H + 19 from rfl, e19]
    · rw [show H + 17 + 4 = H + 21 from rfl, e21]
    · simp only [List.length_singleton, Nat.lt_one_iff] at ht
      subst ht
      rw [e7, show H + 17 + 1 = H + 18 from rfl, e18, Nat.add_zero, Nat.add_zero,
        show H + 23 = H + 23 from rfl, e23]; rfl
    · simp at ht
  · have hj' : j = 0 := by
      have : (BuildNF.buildNF M Q [] E).seq = List.range (BuildNF.arcList M Q [] E).length := rfl
      rw [this, hA] at hj; simp at hj; exact hj
    subst hj'
    rw [e6, Nat.add_zero, show H + 22 = H + 22 from rfl, e22]
    rfl
  · simp [BuildNF.buildNF] at hk
  · simp [BuildNF.buildNF] at hr

/-- The stores of `zeroCase`. -/
def zeroStores : Stmt :=
  match zeroCase with
  | .seq _ (.seq _ s) => s
  | _ => .skip

theorem zeroCase_eq : zeroCase = .seq (block [.copyN 44000 9999, .constN 44030 24,
    .addN 9999 9999 44030]) (.seq lohiS zeroStores) := rfl

section exec

variable {P : Polygon} {W : ℕ}

theorem zeroStores_exec (d : Config) (hw : WordsBounded W d) {H hd : ℕ}
    (hH : d.nreg 44000 = H) (hhd : d.nreg 44021 = hd) (hW : H + 24 ≤ W) :
    ∃ d' k, Exec P W zeroStores d d' k ∧ k ≤ 90 ∧ 24 ≤ k ∧ d'.nreg 40003 = H ∧
      (∀ r, (r < 44031 ∨ 44034 < r) → r ≠ 40003 → d'.nreg r = d.nreg r) ∧
      (∀ f, f < 24 → d'.nmem (H + f) = zeroW H hd f) ∧
      (∀ a, (a < H ∨ H + 24 ≤ a) → d'.nmem a = d.nmem a) := by
  unfold zeroStores zeroCase
  simp only
  exec_block
  all_goals first
    | (config_simp; simp (config := { failIfUnchanged := false }) only [hH]; omega)
    | skip
  refine ⟨by omega, by omega, ?_, fun r h1 h2 => ?_, fun f hf => ?_, fun a ha => ?_⟩ <;>
    config_simp
  · rw [hH]
  · simp (disch := omega) only [upd_other]
  · simp only [hH, hhd, upd_apply]
    rw [zeroW_eq _ _ _ hf]
    interval_cases f <;> ifs_omega <;> rfl
  · simp only [hH, upd_apply]
    ifs_omega

end exec

theorem regWt_zero {M : Model} {P : Polygon} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ}
    (hL : L.length = 0) {m : ℕ → ℕ} {D : ℕ} (hM : ModelDescAt m D (Qof P) M) :
    BuildNF.regWt M (Qof P) L E 0 = hdOf m D P.n := by
  have hL'  := List.length_eq_zero_iff.1 hL
  subst hL'
  have hA : BuildNF.arcList M (Qof P) [] E = [⟨0, ⟨0, 0⟩, ⟨0, 0⟩⟩] := by
    ufs BuildNF.arcList
  have hRA : BuildNF.regArcs M (Qof P) [] E 0 = [0] := by
    unfold BuildNF.regArcs; rwd [hA]
  obtain ⟨hc, hhi⟩ := countedIv (P := P) hM
  have hlohi : loOf m D ≤ hiOf m D P.n := by unfold loOf hiOf; splao
  unfold BuildNF.regWt
  rw [hRA, hA]
  simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, List.getD_cons_zero]
  unfold BuildNF.arcW
  rw [M.arcWt_self hc hhi, hdOf_eq]
  omega

section exec

variable {P : Polygon} {W : ℕ}

theorem wr_zeroCase : wrM BphaseB zeroCase = true := by decide

/-- **The empty chord list.** -/
theorem zeroCase_exec (hWn : hostWords P.n ≤ W) (c : Config) (hw : WordsBounded W c)
    {M : Model} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ} {D H : ℕ} (hL : L.length = 0)
    (hD : c.nreg 40000 = D) (hH : c.nreg 9999 = H) (hwf : ModelDescWF P H c.nmem D)
    (hM : ModelDescAt c.nmem D (Qof P) M) (hroom : H + 24 ≤ W) :
    ∃ c' k, Exec P W zeroCase c c' k ∧ k ≤ 110 ∧ 24 ≤ k ∧ WordsBounded W c' ∧
      FrameM BphaseB c c' ∧ c'.nreg 40003 = H ∧ c'.nreg 9999 = H + 24 ∧
      (∀ a, a < H → c'.nmem a = c.nmem a) ∧
      NFWithin c'.nmem H (c'.nreg 9999) (BuildNF.buildNF M (Qof P) L E) := by
  have hHW : H ≤ W := by omega
  obtain ⟨hDW, hCW⟩ := locChainWF_of hwf hHW hWn
  have hD6 := hwf.1
  obtain ⟨c₁, k₁, x₁, hk₁, v1, v2, g₁, mm₁⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 44000 9999,
      .constN 44030 24, .addN 9999 9999 44030]) c c₁ k₁ ∧ k₁ = 3 ∧ c₁.nreg 44000 = H ∧
      c₁.nreg 9999 = H + 24 ∧ (∀ r, r ≠ 44000 → r ≠ 44030 → r ≠ 9999 → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem := by
    exec_block
    · omega
    · config_simp; rwo [hH]
    · refine ⟨rfl, ?_, ?_, fun r h1 h2 h3 => ?_, rfl⟩ <;> config_simp
      · rw [hH]
      · rw [hH]
      · simp (disch := omega) only [upd_other]
  have w₁ := x₁.wb_right
  obtain ⟨c₂, k₂, x₂, hk₂, l1, l2, l3, l4, f₂⟩ := lohiS_exec (P := P) c₁ w₁ (D := D)
    (by rw [g₁ _ (by norm_num) (by norm_num) (by norm_num), hD])
    (by rw [mm₁]; exact twice_m_le hM hCW) (by omega) (by ufo hostWords at hWn)
    (by ufo hostWords at hWn)
  rw [mm₁] at l1 l2 l3
  have w₂ := x₂.wb_right
  obtain ⟨c₃, k₃, x₃, hk₃, hk₃', v40003, g₃, T1, T2⟩ := zeroStores_exec (P := P) c₂ w₂ (H := H)
    (hd := hdOf c.nmem D P.n) (by rw [f₂.1 _ (by decide), v1]) l2 hroom
  have X : Exec P W zeroCase c c₃ (k₁ + (k₂ + k₃)) := by
    rw [zeroCase_eq]; exact .seq x₁ (.seq x₂ x₃)
  have h9999 : c₃.nreg 9999 = H + 24 := by rw [g₃ _ (by omega) (by omega), f₂.1 _ (by decide), v2]
  refine ⟨c₃, _, X, by omega, by omega, x₃.wb_right, exec_frameM X wr_zeroCase, v40003, h9999,
    fun a ha => by rw [T2 a (Or.inl ha), f₂.2.2.1, mm₁], ?_⟩
  intro m' hm'
  rw [h9999] at hm'
  apply nfAt_zero hL
  intro f hf
  rw [hm' _ (by omega), T1 f hf, regWt_zero hL hM]

end exec

end BuildRam

end

end Chazelle.Core
