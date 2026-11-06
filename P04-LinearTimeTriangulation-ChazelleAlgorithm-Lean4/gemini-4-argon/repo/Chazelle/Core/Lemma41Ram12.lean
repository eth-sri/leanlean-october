module

public import Chazelle.Core.Lemma41Ram11

/-!
# WP-J, part 20: the merge tree

`treeS sM`: while more than one node is left, run a level (`levelS`).  `tree_exec`: from a level of
`j ≥ 1` consecutive nodes of granularities `≤ γ₀` with `γ₀ + ⌈log₂ j⌉ ≤ Gλ`, the loop ends with a
single node, of the union of the chains and of granularity exactly `Gλ` (when `j ≥ 2`), within
`totCost` steps.  The invariant is `TreeSt`.
-/

namespace Chazelle.Core.L41

open Machine Machine.Stmt Programs Chazelle.Merge Finset

@[expose] public section

/-- **The merge tree.** -/
def treeS (sM : Stmt) : Stmt := .whileLtN 160024 160014 (levelS sM)

/-- The cost bound of the merge tree (with `f` levels of fuel). -/
def totCost (κ F G H : ℕ → ℕ) (Gl : ℕ) : ℕ → List Shp → ℕ → ℕ
  | 0, _, _ => 0
  | f + 1, ns, γ₀ => if ns.length ≤ 1 then 0 else
      lvCost κ F G H ns γ₀ + 2 + totCost κ F G H Gl f (pairUp ns (lvTgt Gl ns.length γ₀))
        (lvTgt Gl ns.length γ₀)

/-- **The state of the merge tree** at a level `ns` with granularity bound `γ₀`. -/
def TreeSt (P : Polygon) (W : ℕ) (X : MemCtx) (cs : Config) (As hp hX Gl a L : ℕ)
    (ns : List Shp) (γ₀ : ℕ) (c : Config) : Prop :=
  WordsBounded W c ∧ c.nreg 160014 = ns.length ∧ c.nreg 160033 = γ₀ ∧
    (∃ B, c.nreg 160066 = B ∧ B + 2 * ns.length ≤ c.nreg ALLOC ∧
      LevelAt P c.nmem (c.nreg ALLOC) B hp ns) ∧
    Consec ns ∧ 1 ≤ ns.length ∧ (nd ns 0).1 = a ∧ (ns.map fun x => x.2.1).sum = L ∧
    (∀ k, k < ns.length → (nd ns k).2.2 ≤ γ₀) ∧ (∀ k, k < ns.length → 1 ≤ (nd ns k).2.2) ∧
    (ns.length = 1 → (nd ns 0).2.2 = Gl) ∧ γ₀ + Nat.clog 2 ns.length ≤ Gl ∧
    As ≤ c.nreg ALLOC ∧ (∀ a, a < As → c.nmem a = cs.nmem a) ∧
    (∀ a, a < As → c.rmem a = cs.rmem a) ∧ c.output = cs.output ∧
    (∀ r, bandOf r ∉ mergeBands ∪ oracleBands → ¬ LvRG r → r ≠ ALLOC → c.nreg r = cs.nreg r) ∧
    (∀ r, bandOf r ∉ mergeBands ∪ oracleBands → ¬ LvRG r → c.rreg r = cs.rreg r) ∧
    X.holds P c.nmem hX (c.nreg ALLOC) ∧ X.cap P c.nmem hX = X.cap P cs.nmem hX

theorem clog_half {j : ℕ} (hj : 2 ≤ j) : Nat.clog 2 j = Nat.clog 2 ((j + 1) / 2) + 1 := by
  rw [Nat.clog_of_two_le (by norm_num) hj, show j + 2 - 1 = j + 1 by omega]

section proofs

variable {P : Polygon} {W : ℕ}

set_option maxHeartbeats 16000000 in
/-- **The merge tree on the RAM.** -/
theorem tree_exec (hG : GoodEnv P) (hWh : hostWords P.n ≤ W) (hWn : P.n + 3 ≤ W)
    {sM : Stmt} {κ F G H : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
    (hMM : MergeMeets sM κ F G H X Ok) (hXc : X.CapLocal)
    (hOk : ∀ C : Chain, C.P = Qof P → Ok P (chainModel C))
    {cs : Config} {As hp hX Gl a L : ℕ}
    (s32 : cs.nreg 160032 = Gl) (s00 : cs.nreg 160000 = hX)
    (s24 : cs.nreg 160024 = 1) (s80 : cs.nreg 160080 = 2) (s81 : cs.nreg 160081 = 5)
    (s83 : cs.nreg 160083 = 3) (s84 : cs.nreg 160084 = 4)
    (hGcap : Gl ≤ X.cap P cs.nmem hX) (hGW : Gl ≤ W) :
    ∀ (f : ℕ) (ns : List Shp) (γ₀ : ℕ) (c : Config), ns.length ≤ f →
      TreeSt P W X cs As hp hX Gl a L ns γ₀ c →
      c.nreg ALLOC + totCost κ F G H Gl f ns γ₀ ≤ W →
      ∃ c' k ns' γ', Exec P W (treeS sM) c c' k ∧ k ≤ totCost κ F G H Gl f ns γ₀ + 2 ∧
        c'.nreg ALLOC ≤ c.nreg ALLOC + k ∧ ns'.length = 1 ∧
        TreeSt P W X cs As hp hX Gl a L ns' γ' c' := by
  have hAl : ALLOC = 9999 := rfl
  intro f
  induction f with
  | zero =>
    intro ns γ₀ c hf hst _
    have := hst.2.2.2.2.2.1; omega
  | succ f ih =>
    intro ns γ₀ c hf hst hbud
    obtain ⟨hw, h14, h33, ⟨B, h66, hB, hL⟩, hc, hj1, ha, hsum, hγ, hγ1, hone, hclog, hAs, hm,
      hrm, ho, hr, hrr, hX', hcap'⟩ := hst
    have cr : ∀ r, 160000 ≤ r → r < 170000 → ¬ LvRG r → c.nreg r = cs.nreg r := fun r a b h =>
      hr r (bandOK_l41 a b) h (by rw [hAl]; omega)
    have nl : ∀ r, (r < 160035 ∨ (160056 < r ∧ r < 160062) ∨ (160067 < r ∧ r < 160090)) →
        r ≠ 160014 → r ≠ 160033 → r ≠ 160034 → ¬ LvRG r := by
      intro r h1 h2 h3 h4 h5
      unfold LvRG PairRG DescRG RbRG at h5; omega
    by_cases hlen : ns.length ≤ 1
    · -- the loop ends
      have h1 : ns.length = 1 := by omega
      refine ⟨c, 2, ns, γ₀, .whileLtN_false ?_ hw, by omega, by omega, h1,
        ⟨hw, h14, h33, ⟨B, h66, hB, hL⟩, hc, hj1, ha, hsum, hγ, hγ1, hone, hclog, hAs, hm, hrm,
          ho, hr, hrr, hX', hcap'⟩⟩
      rw [h14, cr _ (by omega) (by omega) (nl _ (by omega) (by omega) (by omega) (by omega))]
      rw [s24]; omega
    · -- one level
      have hj2 : 2 ≤ ns.length := by omega
      set t := lvTgt Gl ns.length γ₀ with ht
      have hcl := clog_half hj2
      have hfl : fuseLoss = 1 := rfl
      have htg : γ₀ + fuseLoss ≤ t := by
        rw [ht]; unfold lvTgt; split_ifs <;> omega
      have hbud' : c.nreg ALLOC + lvCost κ F G H ns γ₀ ≤ W := by
        have : totCost κ F G H Gl (f + 1) ns γ₀ = lvCost κ F G H ns γ₀ + 2 +
            totCost κ F G H Gl f (pairUp ns t) t := by
          rw [totCost, ite_eq_right_of_eq_false _ _ (eq_false hlen)]
        omega
      have cv : ∀ r, (r < 160035 ∨ (160067 < r ∧ r < 160090)) → 160000 ≤ r →
          r ≠ 160014 → r ≠ 160033 → r ≠ 160034 → c.nreg r = cs.nreg r :=
        fun r h1 h2 h3 h4 h5 => cr r h2 (by omega) (nl r (by omega) h3 h4 h5)
      have c32 : c.nreg 160032 = Gl := by
        rwa [cv _ (by omega) (by omega) (by omega) (by omega) (by omega)]
      have c00 : c.nreg 160000 = hX := by
        rwa [cv _ (by omega) (by omega) (by omega) (by omega) (by omega)]
      have c24 : c.nreg 160024 = 1 := by
        rwa [cv _ (by omega) (by omega) (by omega) (by omega) (by omega)]
      have c80 : c.nreg 160080 = 2 := by
        rwa [cv _ (by omega) (by omega) (by omega) (by omega) (by omega)]
      have c81 : c.nreg 160081 = 5 := by
        rwa [cv _ (by omega) (by omega) (by omega) (by omega) (by omega)]
      have c83 : c.nreg 160083 = 3 := by
        rwa [cv _ (by omega) (by omega) (by omega) (by omega) (by omega)]
      have c84 : c.nreg 160084 = 4 := by
        rwa [cv _ (by omega) (by omega) (by omega) (by omega) (by omega)]
      obtain ⟨c1, k1, e1, hk1, hw1, hA1, hA1', l14, l33, ⟨B', l66, hB', hL'⟩, lm, lrm, lo, lr, lrr,
          lX, lcap⟩ :=
        level_exec hG hWh hWn hMM hXc hOk hw (A0 := c.nreg ALLOC) (B := B) (hp := hp) (hX := hX)
          (γ₀ := γ₀) (Gl := Gl) (ns := ns) hj2 rfl h66 h14 h33 c32 c00 c24 c80 c81 c83 c84
          hL hc hB hγ hγ1 hX' (by rw [hcap']; omega) htg (by omega) hbud'
      have hlen' : (pairUp ns t).length = (ns.length + 1) / 2 := pairUp_length ns t
      have hγt : γ₀ ≤ t := by omega
      have hst1 : TreeSt P W X cs As hp hX Gl a L (pairUp ns t) t c1 := by
        refine ⟨hw1, l14, l33, ⟨B', l66, hB', hL'⟩, consec_pairUp t hc, by omega,
          by rw [nd_pairUp_zero ns t (by omega)]; exact ha, by rw [pairUp_sum]; exact hsum,
          pairUp_gran hγ hγt, pairUp_gran_pos hγ1 (by omega), fun h => ?_, ?_, by omega,
          fun x hx => by rw [lm x (by omega)]; exact hm x hx,
          fun x hx => by rw [lrm x (by omega)]; exact hrm x hx, by rw [lo, ho],
          fun r h1 h2 h3 => by rw [lr r h1 h2 h3]; exact hr r h1 h2 h3,
          fun r h1 h2 => by rw [lrr r h1 h2]; exact hrr r h1 h2, lX, by rw [lcap, hcap']⟩
        · rw [nd_pairUp_merge ns t 0 (by omega)]
          simp only [ht]; unfold lvTgt; rw [ite_eq_left (by omega)]
        · rw [hlen']
          rw [ht]; unfold lvTgt; split_ifs with h3
          · have : (ns.length + 1) / 2 = 1 := by omega
            rw [this, Nat.clog_one_right]; omega
          · omega
      have hbud1 : c1.nreg ALLOC + totCost κ F G H Gl f (pairUp ns t) t ≤ W := by
        have : totCost κ F G H Gl (f + 1) ns γ₀ = lvCost κ F G H ns γ₀ + 2 +
            totCost κ F G H Gl f (pairUp ns t) t := by
          rw [totCost, ite_eq_right_of_eq_false _ _ (eq_false hlen)]
        omega
      obtain ⟨c', k, ns', γ', e', hk', hA', h1', hst'⟩ :=
        ih (pairUp ns t) t c1 (by omega) hst1 hbud1
      refine ⟨c', k1 + 2 + k, ns', γ', .whileLtN_true ?_ e1 e', ?_, by omega, h1', hst'⟩
      · rw [h14, c24]; omega
      · have : totCost κ F G H Gl (f + 1) ns γ₀ = lvCost κ F G H ns γ₀ + 2 +
            totCost κ F G H Gl f (pairUp ns t) t := by
          rw [totCost, ite_eq_right_of_eq_false _ _ (eq_false hlen)]
        omega

end proofs

end

end Chazelle.Core.L41
