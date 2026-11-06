module

public import Chazelle.Core.RestoreFVert
public import Chazelle.Core.RestoreKind0
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.SimpTactics
public import Chazelle.ChainTactics

/-!
# WP-E, the search on the RAM (`FindOK`), part 7: a light piece

A kind-`0` piece of the cutter starting on walk edge `e₀` (register `81070`): test the walk
vertices `(e₀ + t) mod n` for `t < 10` (`81071` the vertex, `81072` the counter), those in the
range of candidate vertices `[81021, 81019]` (the tour of a chain model, every vertex of the
interior model), in both directions.  By `kind0_cover` this covers every walk vertex of the
piece.
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Machine Machine.Stmt Programs SweepPrim

/-- Test the vertex in `81071` if it is in the candidate range. -/
def vTest (sT : Stmt) : Stmt :=
  .ifLtN 81071 81021 .skip (.ifLtN 81019 81071 .skip (tVert 81071 sT))

/-- The step of the vertex: `t + 1`, `v + 1 mod n`. -/
def k0StepL : List Instr := [.addN 81072 81072 81012, .addN 81071 81071 81012]

/-- **The light piece.** -/
def kind0 (sT : Stmt) : Stmt :=
  .seq (Stmt.block [.copyN 81071 81070, .constN 81072 0])
    (.whileLtN 81072 81024 (.seq (vTest sT) (.seq (Stmt.block k0StepL)
      (.ifLtN 81071 81017 .skip (Stmt.block [.constN 81071 0])))))

/-- The cost bound of `kind0`. -/
def k0K (E : FEnv) : ℕ := 10 * tvK E + 114

variable {E : FEnv} {c₀ c : Config}

/-- The candidate condition of a walk vertex: in a chain model, a point of the chain. -/
def VSet (E : FEnv) (v : ℕ) : Prop :=
  ∀ C : Chain, E.M = chainModel C → E.M.pos (Qof E.P) ⟨v, 0⟩ ∈ C.set

theorem FWin.congr {c' : Config} (h : FWin E c) (h7 : c'.nreg 81007 = c.nreg 81007)
    (h8 : c'.nreg 81008 = c.nreg 81008) (h9 : c'.nreg 81009 = c.nreg 81009)
    (h10 : c'.nreg 81010 = c.nreg 81010) : FWin E c' := by
  unfold FWin; rwx [h7, h8, h9, h10]

/-- **Testing a vertex in the candidate range.** -/
theorem vTest_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B)
    (hBT : restoreBands ∪ E.Bo ⊆ B) (hI : FInv E.W c₀ c) (hw : FWin E c)
    (hv : c.nreg 81071 < E.M.W.n) (hroom : c.nreg ALLOC + tvK E ≤ E.W) :
    FRS B E.P E.W c₀ (vTest E.sT) c (tvK E + 4) (fun c' => FWin E c' ∧
      (∀ q, 81011 ≤ q → q < 83000 → ¬ VertW q → c'.nreg q = c.nreg q) ∧
      (c.nreg 81007 = 1 → c'.nreg 81007 = 1) ∧
      (∀ reg, NFRegs E.M (Qof E.P) E.N reg → (E.N.region E.r).chords ≠ [] →
        VSet E (c.nreg 81071) → ∀ σb, σb ≤ 1 → GoodAt E reg (c.nreg 81071) σb →
          c'.nreg 81007 = 1)) := by
  have r21 : c.nreg 81021 = c₀.nreg 81021 := hI.hin _ (by ufo FFix)
  have r19 : c.nreg 81019 = c₀.nreg 81019 := hI.hin _ (by ufo FFix)
  by_cases h1 : c.nreg 81071 < c.nreg 81021
  · refine (FRS.ifT h1 (FRS.skip (K := 0) hI ⟨hw, fun _ _ _ _ => rfl, id,
      fun reg _ _ hs _ _ _ => ?_⟩)).mono (by omega) (fun _ => id)
    have := (hE.hvc _ hv hs).1
    omega
  refine (FRS.ifF h1 ?_).mono (K := tvK E + 4) (by omega) (fun _ => id)
  by_cases h2 : c.nreg 81019 < c.nreg 81071
  · refine (FRS.ifT h2 (FRS.skip (K := 0) hI ⟨hw, fun _ _ _ _ => rfl, id,
      fun reg _ _ hs _ _ _ => ?_⟩)).mono (by omega) (fun _ => id)
    have := (hE.hvc _ hv hs).2
    omega
  refine (FRS.ifF h2 ?_).mono (K := tvK E + 2) (by omega) (fun _ => id)
  refine (tVert_fs hE hB hBT hI hw hv (hE.hvr _ hv (by omega) (by omega)) hroom).mono le_rfl
    (fun c' ⟨h1', h2', h3', h4'⟩ => ⟨h1', h2', h3', fun reg hr hch _ => h4' reg hr hch⟩)

theorem mod_step {n a : ℕ} (hn : 0 < n) :
    (if a % n + 1 < n then a % n + 1 else 0) = (a + 1) % n := by
  have hlt := Nat.mod_lt a hn
  have e := WalkEmbed.mod_succ_mod n a 0
  simp only [Nat.add_zero] at e
  split_ifs with h
  · rw [← e, Nat.mod_eq_of_lt h]
  · have : a % n + 1 = n := by omega
    rw [← e, this, Nat.mod_self]

/-- **A light piece** as a run step of the search. -/
theorem kind0_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B)
    (hBT : restoreBands ∪ E.Bo ⊆ B) (hI : FInv E.W c₀ c) (hw : FWin E c) {e₀ : ℕ}
    (he : c.nreg 81070 = e₀) (he₀ : e₀ < E.M.W.n) (hroom : c.nreg ALLOC + k0K E ≤ E.W) :
    FRS B E.P E.W c₀ (kind0 E.sT) c (k0K E) (fun c' => FWin E c' ∧
      (∀ q, 81011 ≤ q → q < 83000 → ¬ VertW q → q ≠ 81071 → q ≠ 81072 →
        c'.nreg q = c.nreg q) ∧
      (c.nreg 81007 = 1 → c'.nreg 81007 = 1) ∧
      (∀ reg, NFRegs E.M (Qof E.P) E.N reg → (E.N.region E.r).chords ≠ [] →
        ∀ t, t < 10 → VSet E ((e₀ + t) % E.M.W.n) → ∀ σb, σb ≤ 1 →
          GoodAt E reg ((e₀ + t) % E.M.W.n) σb → c'.nreg 81007 = 1)) := by
  set n := E.M.W.n with hn
  have hn0 : 0 < n := by omega
  have hW10 : 10 ≤ E.W := by
    have := hE.hWh; have := hE.hG.1.1; ufo hostWords at *
  have hnW : n ≤ E.W := by
    have := hI.hw.1 81017
    rwa [hI.hin _ (by ufo FFix), hE.wn] at this
  have fx : ∀ c', FInv E.W c₀ c' → c'.nreg 81017 = n ∧ c'.nreg 81024 = 10 ∧
      c'.nreg 81012 = 1 := fun c' hI' =>
    ⟨by rw [hI'.hin _ (by ufo FFix), hE.wn],
      by rw [hI'.hin _ (by ufo FFix), hE.k10],
      by rw [hI'.hin _ (by ufo FFix), hE.k1]⟩
  have ok0 : okB E.W c.nmem [.copyN 81071 81070, .constN 81072 0] c.nreg := by
    simp only [okB, okI]
    exact ⟨Or.inl (Or.inl ⟨by norm_num, by norm_num⟩),
      ⟨Or.inl (Or.inl ⟨by norm_num, by norm_num⟩), by omega⟩, trivial⟩
  refine (FRS.seq (K₂ := (tvK E + 11) * 10 + 2) (FRS.block hB _ hI ok0)
    (fun c₁ hI₁ hA₁ h₁ => ?_)).mono
    (by sio only [List.length_cons, List.length_nil, k0K]) (fun _ => id)
  have e₁ : ∀ q, c₁.nreg q = regB c.nmem [.copyN 81071 81070, .constN 81072 0] c.nreg q :=
    fun q => by rw [h₁]
  have v71 : c₁.nreg 81071 = e₀ := by rw [e₁]; simp [regB, regI, upd, he]
  have v72 : c₁.nreg 81072 = 0 := by rw [e₁]; simp [regB, regI, upd]
  have f₁ : ∀ q, q ≠ 81071 → q ≠ 81072 → c₁.nreg q = c.nreg q := fun q h1 h2 => by
    rw [e₁]; simp [regB, regI, upd, h1, h2]
  have hA₁' : c₁.nreg ALLOC = c.nreg ALLOC := f₁ _ (by ufo ALLOC)
    (by ufo ALLOC)
  -- the loop
  let I : Config → Prop := fun c' => c'.nreg 81072 ≤ 10 ∧
    c'.nreg 81071 = (e₀ + c'.nreg 81072) % n ∧ FWin E c' ∧
    (∀ q, 81011 ≤ q → q < 83000 → ¬ VertW q → q ≠ 81071 → q ≠ 81072 → c'.nreg q = c.nreg q) ∧
    (c.nreg 81007 = 1 → c'.nreg 81007 = 1) ∧
    (∀ reg, NFRegs E.M (Qof E.P) E.N reg → (E.N.region E.r).chords ≠ [] →
      ∀ t, t < c'.nreg 81072 → VSet E ((e₀ + t) % n) → ∀ σb, σb ≤ 1 →
        GoodAt E reg ((e₀ + t) % n) σb → c'.nreg 81007 = 1)
  have hI1 : I c₁ := by
    refine ⟨by omega, by rw [v71, v72, Nat.add_zero, Nat.mod_eq_of_lt he₀], ?_,
      fun q _ _ _ h4 h5 => f₁ q h4 h5, fun h => by rwx [f₁ _ (by norm_num) (by norm_num)],
      fun _ _ _ t ht => by omega⟩
    exact hw.congr (f₁ _ (by norm_num) (by norm_num)) (f₁ _ (by norm_num) (by norm_num))
      (f₁ _ (by norm_num) (by norm_num)) (f₁ _ (by norm_num) (by norm_num))
  have hbody : ∀ c', FInv E.W c₀ c' → I c' → c'.nreg 81072 < c'.nreg 81024 →
      c'.nreg ALLOC + (tvK E + 9) ≤ E.W →
      FRS B E.P E.W c₀ (.seq (vTest E.sT) (.seq (Stmt.block k0StepL)
        (.ifLtN 81071 81017 .skip (Stmt.block [.constN 81071 0])))) c' (tvK E + 9)
        (fun c'' => I c'' ∧ 10 - c''.nreg 81072 < 10 - c'.nreg 81072) := by
    intro c' hI' ⟨i1, i2, i3, i4, i5, i6⟩ ht hr
    obtain ⟨g17, g24, g12⟩ := fx c' hI'
    rw [g24] at ht
    have hv' : c'.nreg 81071 < n := by rw [i2]; exact Nat.mod_lt _ hn0
    refine FRS.seq (K₂ := 5) (vTest_fs hE hB hBT hI' i3 hv' (by omega))
      (fun c₂ hI₂ hA₂ ⟨j1, j2, j3, j4⟩ => ?_)
    have k71 : c₂.nreg 81071 = c'.nreg 81071 := j2 _ (by norm_num) (by norm_num)
      (by ufo VertW)
    have k72 : c₂.nreg 81072 = c'.nreg 81072 := j2 _ (by norm_num) (by norm_num)
      (by ufo VertW)
    obtain ⟨-, -, h12⟩ := fx c₂ hI₂
    have ok : okB E.W c₂.nmem k0StepL c₂.nreg := by
      simp only [k0StepL, okB, okI, regI]
      refine ⟨⟨Or.inl (Or.inl ⟨by norm_num, by norm_num⟩), by rwo [k72, h12]⟩,
        ⟨Or.inl (Or.inl ⟨by norm_num, by norm_num⟩), ?_⟩, trivial⟩
      rwo [upd_ne (by norm_num), upd_ne (by norm_num), k71, h12]
    refine FRS.seq (K₂ := 3) (FRS.block hB _ hI₂ ok) (fun c₃ hI₃ hA₃ h₃ => ?_)
    have e₃ : ∀ q, c₃.nreg q = regB c₂.nmem k0StepL c₂.nreg q := fun q => by rw [h₃]
    have u71 : c₃.nreg 81071 = c'.nreg 81071 + 1 := by
      rw [e₃]; simp [k0StepL, regB, regI, upd, k71, h12]
    have u72 : c₃.nreg 81072 = c'.nreg 81072 + 1 := by
      rw [e₃]; simp [k0StepL, regB, regI, upd, k72, h12]
    have f₃ : ∀ q, q ≠ 81071 → q ≠ 81072 → c₃.nreg q = c₂.nreg q := fun q h1 h2 => by
      rw [e₃]; simp [k0StepL, regB, regI, upd, h1, h2]
    obtain ⟨h17, -, -⟩ := fx c₃ hI₃
    -- the post-state facts, given the new vertex
    have fin : ∀ c₄ : Config, c₄.nreg 81072 = c'.nreg 81072 + 1 →
        c₄.nreg 81071 = (e₀ + (c'.nreg 81072 + 1)) % n →
        (∀ q, q ≠ 81071 → c₄.nreg q = c₃.nreg q) →
        I c₄ ∧ 10 - c₄.nreg 81072 < 10 - c'.nreg 81072 := by
      intro c₄ w72 w71 f₄
      have g : ∀ q, q ≠ 81071 → q ≠ 81072 → c₄.nreg q = c₂.nreg q := fun q h1 h2 => by
        rw [f₄ q h1, f₃ q h1 h2]
      refine ⟨⟨by omega, by rw [w71, w72], ?_, fun q h1 h2 h3 h4 h5 => ?_, fun h => ?_,
        fun reg hr hch t htl hs σb hσb hg => ?_⟩, by omega⟩
      · exact j1.congr (g _ (by norm_num) (by norm_num)) (g _ (by norm_num) (by norm_num))
          (g _ (by norm_num) (by norm_num)) (g _ (by norm_num) (by norm_num))
      · rw [g q h4 h5, j2 q h1 h2 h3, i4 q h1 h2 h3 h4 h5]
      · rw [g _ (by norm_num) (by norm_num)]; exact j3 (i5 h)
      · rw [g _ (by norm_num) (by norm_num)]
        rw [w72] at htl
        rcases Nat.lt_succ_iff_lt_or_eq.1 htl with htl | rfl
        · exact j3 (i6 reg hr hch t htl hs σb hσb hg)
        · rw [← i2] at hs hg; exact j4 reg hr hch hs σb hσb hg
    by_cases hc : c₃.nreg 81071 < c₃.nreg 81017
    · refine (FRS.ifT hc (FRS.skip (K := 0) hI₃ (fin c₃ u72 ?_ (fun _ _ => rfl)))).mono
        (by omega) (fun _ => id)
      rw [u71, i2, ← Nat.add_assoc, ← mod_step hn0, ite_eq_left (by rwx [← i2, ← u71, ← h17])]
    · have okc : okB E.W c₃.nmem [.constN 81071 0] c₃.nreg := by
        simp only [okB, okI]
        exact ⟨⟨Or.inl (Or.inl ⟨by norm_num, by norm_num⟩), by omega⟩, trivial⟩
      refine (FRS.ifF hc (FRS.block hB _ hI₃ okc)).mono (by simp) (fun c₄ h₄ => ?_)
      have e₄ : ∀ q, c₄.nreg q = regB c₃.nmem [.constN 81071 0] c₃.nreg q := fun q => by
        rw [h₄]
      refine fin c₄ (by rw [e₄]; simp [regB, regI, upd, u72]) ?_
        (fun q hq => by rw [e₄]; simp [regB, regI, upd, hq])
      rw [e₄]; simp only [regB, regI, upd, ite_true]
      rw [← Nat.add_assoc, ← mod_step hn0, ite_eq_right (by rwx [← i2, ← u71, ← h17])]
  have hroom₁ : c₁.nreg ALLOC + (tvK E + 9 + 2) * (10 - c₁.nreg 81072) ≤ E.W := by
    ruo [hA₁', v72] k0K at hroom
  have k24  := (fx c hI).2.1
  have w24 : ∀ c', I c' → c'.nreg 81024 = 10 := fun c' hc' => by
    rw [hc'.2.2.2.1 _ (by norm_num) (by norm_num) (by ufo VertW) (by norm_num)
      (by norm_num), k24]
  refine (FRS.while I (fun c' => 10 - c'.nreg 81072) (tvK E + 9) (fun c' hc' ht => ?_) hbody
    hI₁ hI1 hroom₁).mono (by rw [v72]) (fun c' ⟨hc', ht⟩ => ⟨hc'.2.2.1, hc'.2.2.2.1,
      hc'.2.2.2.2.1, fun reg hr hch t ht' => hc'.2.2.2.2.2 reg hr hch t (by
        rwo [w24 c' hc'] at ht)⟩)
  rwo [w24 c' hc'] at ht

end

end Restore

end Chazelle.Core
