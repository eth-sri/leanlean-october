module

public import Chazelle.Core.SweepPrimLeft
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.SimpTactics

/-!
# Sweep RAM primitives (WP-D2), part 9: classifying a walk position

`classify boxK vtxK intK` is the common skeleton of the primitives that take a walk position
`x = (e, h)` of `chainModel C` (`leftSec`, `arrivalPos`, `absKey`): it computes the direction
code of the edge `e` (`dirAt`) and decides whether `x` lies on the box block (`e < 6`, then inside
its edge), at a tour vertex (`param x = 0`), or inside an edge of the tour or of the up-slit edge,
and continues with `boxK`, `vtxK` or `intK` (`classify_exec`, in continuation-passing style).
-/

namespace Chazelle.Core

namespace SweepPrim

open Machine Machine.Stmt Programs SignK WalkKey NFLoc
open Chazelle.Chain (sideLeft sidePt)

@[expose] public section

/-- **The classification skeleton.** -/
def classify (boxK vtxK intK : Stmt) : Stmt :=
  .seq (.instr (.copyN 50002 50201)) (.seq dirAt
    (.ifLtN 50201 50081 boxK
      (.ifLtN 50202 50032 vtxK
        (.ifLtN 10502 50032 vtxK
          (.seq (.instr (.subN 50120 50201 50081)) (.seq (tvLoad 50133)
            (.seq (block [.constN 50160 0, .subN 50161 50202 50032])
              (.seq (kbit 50133 50160 50133 1 50170) (.seq (kbit 50160 50133 50160 1 50171)
                (.ifLtN 50170 50032 (.ifLtN 50171 50032 vtxK intK) intK))))))))))

/-- **Execution of the classification**: the continuation of the case of `x` runs from a
configuration with the chain environment and the inputs `50200 … 50209`. -/
theorem classify_exec {P : Polygon} {W : ℕ} {H : Host} {C : Chain} {boxK vtxK intK : Stmt}
    {Kb Kv Ki : ℕ} {R : Config → Prop} (c₀ c : Config) (hE : CEnv P W H C c)
    (hinp : ∀ r, 50200 ≤ r → r < 50210 → c.nreg r = c₀.nreg r)
    (hen : c₀.nreg 50201 < (chainModel C).W.n)
    (hp0 : 0 ≤ (chainModel C).param (Qof P) ⟨c₀.nreg 50201, c₀.nreg 50202⟩)
    (_hp1 : (chainModel C).param (Qof P) ⟨c₀.nreg 50201, c₀.nreg 50202⟩ < 1)
    (hhn : c₀.nreg 50202 ≤ P.n)
    (hy : |((chainModel C).pos (Qof P) ⟨c₀.nreg 50201, c₀.nreg 50202⟩).2| < C.radius)
    (hbox : ∀ c₂ : Config, CEnv P W H C c₂ →
      (∀ r, 50200 ≤ r → r < 50210 → c₂.nreg r = c₀.nreg r) →
      c₂.nreg 10502 = dirCode (chainModel C) (c₀.nreg 50201) → c₀.nreg 50201 < 6 →
      0 < (chainModel C).param (Qof P) ⟨c₀.nreg 50201, c₀.nreg 50202⟩ →
      ∃ c' k, Exec P W boxK c₂ c' k ∧ k ≤ Kb ∧ R c')
    (hvtx : ∀ c₂ : Config, CEnv P W H C c₂ →
      (∀ r, 50200 ≤ r → r < 50210 → c₂.nreg r = c₀.nreg r) → 6 ≤ c₀.nreg 50201 →
      (chainModel C).param (Qof P) ⟨c₀.nreg 50201, c₀.nreg 50202⟩ = 0 →
      ∃ c' k, Exec P W vtxK c₂ c' k ∧ k ≤ Kv ∧ R c')
    (hint : ∀ c₂ : Config, CEnv P W H C c₂ →
      (∀ r, 50200 ≤ r → r < 50210 → c₂.nreg r = c₀.nreg r) →
      c₂.nreg 10502 = dirCode (chainModel C) (c₀.nreg 50201) → 6 ≤ c₀.nreg 50201 →
      0 < (chainModel C).param (Qof P) ⟨c₀.nreg 50201, c₀.nreg 50202⟩ →
      ∃ c' k, Exec P W intK c₂ c' k ∧ k ≤ Ki ∧ R c') :
    ∃ c' k, Exec P W (classify boxK vtxK intK) c c' k ∧
      k ≤ 110 * H.length + 1200 + Kb + Kv + Ki ∧ R c' := by
  have i01 := hinp 50201 (by norm_num) (by norm_num)
  have i02 := hinp 50202 (by norm_num) (by norm_num)
  have i03 := hinp 50203 (by norm_num) (by norm_num)
  set e := c₀.nreg 50201 with he_def
  set hc := c₀.nreg 50202 with hc_def
  set σ := c₀.nreg 50203 with hσ_def
  set M := chainModel C with hM
  set x : WPos := ⟨e, hc⟩ with hx
  have hn : M.W.n = 2 * C.m + 7 := C.sideWalk_n _
  have hlen := hE.hlen
  have hW := hE.hW
  -- the edge direction
  have e₁ := Exec.copyN (P := P) hE.wb 50002 50201
  set c₁ : Config := { c with nreg := upd c.nreg 50002 (c.nreg 50201) } with hc₁
  have hE₁ : CEnv P W H C c₁ := hE.frame (exec_frameB e₁ (B := fun r => r == 50002)
    (by decide)) e₁.wb_right (by decide)
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, hE₂, d₂⟩ := dirAt_exec c₁ hE₁ (e := e)
    (by rw [hc₁]; simp [i01]) (by omega)
  have w₂ := e₂.wb_right
  have g₂ : ∀ r, 50200 ≤ r → r < 50210 → c₂.nreg r = c₀.nreg r := fun r h1 h2 => by
    rw [f₂.1 r (by sio only [Bdir, Bool.or_eq_false_iff, decide_eq_false_iff_not]),
      hc₁]
    simp only
    rw [upd_other _ _ _ (by omega), hinp r h1 h2]
  have q01 := g₂ 50201 (by norm_num) (by norm_num)
  have q02 := g₂ 50202 (by norm_num) (by norm_num)
  have q03 := g₂ 50203 (by norm_num) (by norm_num)
  have hd2 : c₂.nreg 10502 ≤ 2 := by rw [d₂]; exact dirCode_le_two _ _
  by_cases hsm : e < 6
  · -- the box block
    have hpos : 0 < M.param (Qof P) x := box_param_pos C hsm hp0 hy
    obtain ⟨c', k, ex, hk, b⟩ := hbox c₂ hE₂ g₂ d₂ hsm hpos
    exact ⟨c', _, .seq e₁ (.seq e₂ (.ifLtN_true (by rwx [q01, hE₂.r81]) ex)),
      by omega, b⟩
  have t1 : ¬ c₂.nreg 50201 < c₂.nreg 50081 := by rwx [q01, hE₂.r81]
  by_cases hh0 : hc < 1
  · obtain ⟨c', k, ex, hk, b⟩ := hvtx c₂ hE₂ g₂ (by omega)
      ((param_eq_zero_iff _ _ _).2 (Or.inl (by sio [hx])))
    exact ⟨c', _, .seq e₁ (.seq e₂ (.ifLtN_false t1 (.ifLtN_true
      (by rwx [q02, hE₂.r32]) ex))), by omega, b⟩
  have t2 : ¬ c₂.nreg 50202 < c₂.nreg 50032 := by rwx [q02, hE₂.r32]
  by_cases hd0 : c₂.nreg 10502 < 1
  · have hdir : dirCode M e = 0 := by rwo [← d₂]
    have hhor : (M.wa x.edge).2 = (M.wb x.edge).2 := by
      unfold dirCode at hdir
      split_ifs at hdir with h1 h2
      exact le_antisymm (not_lt.1 h2) (not_lt.1 h1)
    obtain ⟨c', k, ex, hk, b⟩ := hvtx c₂ hE₂ g₂ (by omega)
      ((param_eq_zero_iff _ _ _).2 (Or.inr (Or.inl hhor)))
    exact ⟨c', _, .seq e₁ (.seq e₂ (.ifLtN_false t1 (.ifLtN_false t2 (.ifLtN_true
      (by rwx [hE₂.r32]) ex)))), by omega, b⟩
  have t3 : ¬ c₂.nreg 10502 < c₂.nreg 50032 := by rwx [hE₂.r32]
  -- the start vertex of the edge and the height vertex
  have e₃ := Exec.subN (P := P) w₂ 50120 50201 50081
  set c₃ : Config := { c₂ with nreg := upd c₂.nreg 50120 (c₂.nreg 50201 - c₂.nreg 50081) }
    with hc₃
  have hE₃ : CEnv P W H C c₃ := hE₂.frame (exec_frameB e₃ (B := fun r => r == 50120)
    (by decide)) e₃.wb_right (by decide)
  obtain ⟨c₄, k₄, e₄, hk₄, f₄, hE₄, sa, ia, la, va, -⟩ := tvLoad_exec c₃ hE₃ (i := e - 6)
    (by rw [hc₃]; simp only [upd_same]; rw [q01, hE₂.r81]) (by omega)
    (dst := 50133) (by norm_num)
  have w₄ := e₄.wb_right
  obtain ⟨c₅, k₅, e₅, hk₅, q⟩ : ∃ c₅ k₅, Exec P W (block [.constN 50160 0,
      .subN 50161 50202 50032]) c₄ c₅ k₅ ∧ k₅ = 2 ∧ (c₅.nreg 50160 = 0 ∧
        c₅.nreg 50161 = hc - 1 ∧ ∀ r, r ≠ 50160 → r ≠ 50161 → c₅.nreg r = c₄.nreg r) := by
    exec_block
    · omega
    · refine ⟨rfl, by config_simp, ?_, fun r h1 h2 => by simp [h1, h2]⟩
      config_simp
      rw [f₄.1 50202 (by decide), f₄.1 50032 (by decide), hc₃]
      simp only
      rw [upd_other _ _ _ (by decide), upd_other _ _ _ (by decide), q02, hE₂.r32]
  obtain ⟨q60, q61, r₅⟩ := q
  have w₅ := e₅.wb_right
  have ih : SymPtIn c₅ 50160 (.vtx (hc - 1)) := ⟨q60, q61⟩
  have hhn' : hc ≤ P.n := hhn
  have lh : (SymPt.vtx (hc - 1)).Lt P.n := by show hc - 1 < P.n; omega
  have ia₅ : SymPtIn c₅ 50133 sa := symPtIn_of_eq ia fun j h1 h2 => r₅ j (by omega) (by omega)
  obtain ⟨c₆, k₆, e₆, hk₆, f₆, b₆, t₆⟩ := kbit_exec (op := 1) (dst := 50170) hE.hG hW c₅ w₅
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) la lh la ia₅ ih ia₅
  have ia₆ := symPtIn_keep ia₅ f₆ (by intro j h1 h2; interval_cases j <;> decide)
  have ih₆ := symPtIn_keep ih f₆ (by intro j h1 h2; interval_cases j <;> decide)
  obtain ⟨c₇, k₇, e₇, hk₇, f₇, b₇, t₇⟩ := kbit_exec (op := 1) (dst := 50171) hE.hG hW c₆
    e₆.wb_right (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) lh la lh
    ih₆ ia₆ ih₆
  have w₇ := e₇.wb_right
  have hE₅ : CEnv P W H C c₅ := hE₄.keep w₅ (exec_frameB e₅ (B := fun r => r == 50160 ||
    r == 50161) (by decide)).2.2.1 (fun r hr => r₅ r (by intro h; subst h; revert hr; decide)
      (by intro h; subst h; revert hr; decide))
  have hE₆ := hE₅.frame f₆ e₆.wb_right (by decide)
  have hE₇ := hE₆.frame f₇ w₇ (by decide)
  -- registers kept since `c₂`
  have g₇ : ∀ r, (50200 ≤ r ∧ r < 50210) ∨ r = 10502 → c₇.nreg r = c₂.nreg r := by
    intro r hr
    have hB : ∀ B : ℕ → Bool, (∀ j, 50200 ≤ j → j < 50210 → B j = false) → B 10502 = false →
        B r = false := fun B h1 h2 => by rcases hr with ⟨h3, h4⟩ | rfl; exacts [h1 r h3 h4, h2]
    rw [f₇.1 r (hB _ (fun j h1 h2 => by interval_cases j <;> decide) (by decide)),
      f₆.1 r (hB _ (fun j h1 h2 => by interval_cases j <;> decide) (by decide)),
      r₅ r (by omega) (by omega), f₄.1 r (hB _ (fun j h1 h2 => by interval_cases j <;> decide)
        (by decide)), hc₃]
    simp only
    rw [upd_other _ _ _ (by omega)]
  have g₇' : ∀ r, 50200 ≤ r → r < 50210 → c₇.nreg r = c₀.nreg r := fun r h1 h2 => by
    rw [g₇ r (Or.inl ⟨h1, h2⟩), g₂ r h1 h2]
  have b70 : BitIs c₇ 50170 ((SymPt.eval (Qof P) sa).2 < ((SymPt.vtx (hc - 1)).eval (Qof P)).2) :=
    BitIs.keep ⟨b₆, t₆⟩ f₇ (by decide)
  have b71 : BitIs c₇ 50171 (((SymPt.vtx (hc - 1)).eval (Qof P)).2 < (SymPt.eval (Qof P) sa).2) :=
    ⟨b₇, t₇⟩
  rw [va, show e - 6 + 6 = e by omega] at b70 b71
  have hwa : M.wa x.edge = M.W.vtx e := rfl
  have hQ : ((SymPt.vtx (hc - 1)).eval (Qof P)) = (Qof P).vtx (x.hgt - 1) := rfl
  rw [hQ] at b70 b71
  by_cases hlt : c₇.nreg 50170 < c₇.nreg 50032
  · rw [hE₇.r32] at hlt
    have n70 : ¬ (M.W.vtx e).2 < ((Qof P).vtx (x.hgt - 1)).2 := fun h => by
      have := b70.2.2 h; omega
    by_cases hlt2 : c₇.nreg 50171 < c₇.nreg 50032
    · rw [hE₇.r32] at hlt2
      have n71 : ¬ ((Qof P).vtx (x.hgt - 1)).2 < (M.W.vtx e).2 := fun h => by
        have := b71.2.2 h; omega
      have heq : ((Qof P).vtx (x.hgt - 1)).2 = (M.wa x.edge).2 := by
        rw [hwa]; linarith [not_lt.1 n70, not_lt.1 n71]
      obtain ⟨c', k, ex, hk, b⟩ := hvtx c₇ hE₇ g₇' (by omega)
        ((param_eq_zero_iff _ _ _).2 (Or.inr (Or.inr heq)))
      exact ⟨c', _, .seq e₁ (.seq e₂ (.ifLtN_false t1 (.ifLtN_false t2 (.ifLtN_false t3
        (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ (.ifLtN_true (by rwx [hE₇.r32])
          (.ifLtN_true (by rwx [hE₇.r32]) ex))))))))))), by omega, b⟩
    · have p71 : ((Qof P).vtx (x.hgt - 1)).2 < (M.W.vtx e).2 := b71.2.1 (by
        have := b71.1; rwo [hE₇.r32] at hlt2)
      have hpos : 0 < M.param (Qof P) x := lt_of_le_of_ne hp0 (fun h => by
        rcases (param_eq_zero_iff _ _ _).1 h.symm with h' | h' | h'
        · sio [hx] at h'
        · exact hd0 (by rw [d₂]; unfold dirCode; rw [ite_eq_right (by rw [h']; exact lt_irrefl _),
            ite_eq_right (by rw [h']; exact lt_irrefl _)]; omega)
        · rwli [hwa] at h')
      obtain ⟨c', k, ex, hk, b⟩ := hint c₇ hE₇ g₇' (by rw [g₇ _ (Or.inr rfl), d₂]) (by omega)
        hpos
      exact ⟨c', _, .seq e₁ (.seq e₂ (.ifLtN_false t1 (.ifLtN_false t2 (.ifLtN_false t3
        (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ (.ifLtN_true (by rwx [hE₇.r32])
          (.ifLtN_false hlt2 ex))))))))))), by omega, b⟩
  · have p70 : (M.W.vtx e).2 < ((Qof P).vtx (x.hgt - 1)).2 := b70.2.1 (by
      have := b70.1; rwo [hE₇.r32] at hlt)
    have hpos : 0 < M.param (Qof P) x := lt_of_le_of_ne hp0 (fun h => by
      rcases (param_eq_zero_iff _ _ _).1 h.symm with h' | h' | h'
      · sio [hx] at h'
      · exact hd0 (by rw [d₂]; unfold dirCode; rw [ite_eq_right (by rw [h']; exact lt_irrefl _),
          ite_eq_right (by rw [h']; exact lt_irrefl _)]; omega)
      · rwli [hwa] at h')
    obtain ⟨c', k, ex, hk, b⟩ := hint c₇ hE₇ g₇' (by rw [g₇ _ (Or.inr rfl), d₂]) (by omega) hpos
    exact ⟨c', _, .seq e₁ (.seq e₂ (.ifLtN_false t1 (.ifLtN_false t2 (.ifLtN_false t3
      (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ (.ifLtN_false hlt ex)))))))))), by omega, b⟩



end

end SweepPrim

end Chazelle.Core
