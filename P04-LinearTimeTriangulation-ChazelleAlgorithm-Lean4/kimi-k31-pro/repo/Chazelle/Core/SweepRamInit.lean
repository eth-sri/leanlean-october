module

public import Chazelle.Core.SweepRamLog
public import Chazelle.Core.NFLocateSpec
public import Chazelle.Core.ShotListFrame
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.ChainTactics

/-!
# The sweep RAM (WP-D), part 3: stage 0 — descriptors and bases

The program of `SweepSpec` works in band `bSweep` (registers `sw i = 240000 + i`).  Stage 0
(`initS`) normalises the side `i = rd 7`: the **query chain** (`C₁` for `i = 0`, `C₂` for `i = 1`)
and the **label chain** (the other one), their normal forms, the constants of the two
correspondences (`junConst`: the label side's stretch, the query side's stretch), and three model
descriptors built in fresh memory (the query model, the label model, the model of `C`), which the
oracles and `Locate` take.

## Registers of stage 0

| register | content |
|---|---|
| `sw 20`, `sw 21`, `sw 22` | chain descriptors of the query chain, the label chain, `C` |
| `sw 23`, `sw 24` | normal forms of the query side and of the label side |
| `sw 30`, `sw 31`, `sw 32` | model descriptors (query, label, `C`) |
| `sw 40` … `sw 44` | the label correspondence `g, g', L1, L2, δ` |
| `sw 45` … `sw 49` | the query correspondence |
| `sw 90`, `sw 91` | the constants `0`, `1` |
| `sw 96` … `sw 98` | scratch |

* `copyDesc_exec`: writing `0` and a copy of the five words of a chain descriptor (a model
  descriptor of a chain model);
* `modelDesc_of_copy`: the copy describes the chain model and is well formed;
* `junction_unique`: the junction is determined by its descriptors.
-/

namespace Chazelle.Core

namespace SweepRam

open Machine Machine.Stmt Programs
open ShotList (hostAt_agree chainDescAt_copy chainWF_copy)

@[expose] public section

/-- Register `i` of the sweep's band. -/
def sw (i : ℕ) : ℕ := 240000 + i

/-! ## Copying a chain descriptor -/

/-- Copy one word from the address in `sw 97` to the address in `sw 96`, advancing both. -/
def cp1 : Stmt := block [.loadN (sw 98) (sw 97), .storeN (sw 96) (sw 98),
  .addN (sw 96) (sw 96) (sw 91), .addN (sw 97) (sw 97) (sw 91)]

/-- A model descriptor of a chain model: `0`, then the five words of the chain descriptor at the
address in `sw 97` (the destination pointer `sw 96` advances by `6`). -/
def copyDesc : Stmt :=
  .seq (block [.storeN (sw 96) (sw 90), .addN (sw 96) (sw 96) (sw 91)])
    (.seq cp1 (.seq cp1 (.seq cp1 (.seq cp1 cp1))))

theorem cp1_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c)
    (h1 : c.nreg (sw 91) = 1) (hP : c.nreg (sw 96) + 1 ≤ W) (hS : c.nreg (sw 97) + 1 ≤ W) :
    ∃ c' k, Exec P W cp1 c c' k ∧ k = 4 ∧
      c'.nreg (sw 96) = c.nreg (sw 96) + 1 ∧ c'.nreg (sw 97) = c.nreg (sw 97) + 1 ∧
      c'.nmem = upd c.nmem (c.nreg (sw 96)) (c.nmem (c.nreg (sw 97))) ∧
      (∀ r, r ≠ sw 96 → r ≠ sw 97 → r ≠ sw 98 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold cp1 sw at *
  exec_block
  · config_simp; rwx [h1]
  · config_simp; rwx [h1]
  · refine ⟨rfl, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
    · config_simp; rw [h1]
    · config_simp; rw [h1]
    · config_simp
    · intro r h96 h97 h98; config_simp; simp [h96, h97, h98]

/-- **Copying a chain descriptor**: `copyDesc` writes `0` at the destination `D` and the five
words at `S` after it, and advances the destination pointer by `6` (source below destination). -/
theorem copyDesc_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c)
    (h0 : c.nreg (sw 90) = 0) (h1 : c.nreg (sw 91) = 1) (hSD : c.nreg (sw 97) + 5 ≤ c.nreg (sw 96))
    (hDW : c.nreg (sw 96) + 6 ≤ W) :
    ∃ c' k, Exec P W copyDesc c c' k ∧ k = 22 ∧
      c'.nreg (sw 96) = c.nreg (sw 96) + 6 ∧
      c'.nmem (c.nreg (sw 96)) = 0 ∧
      (∀ j, j < 5 → c'.nmem (c.nreg (sw 96) + 1 + j) = c.nmem (c.nreg (sw 97) + j)) ∧
      (∀ a, a < c.nreg (sw 96) → c'.nmem a = c.nmem a) ∧
      (∀ a, c.nreg (sw 96) + 6 ≤ a → c'.nmem a = c.nmem a) ∧
      (∀ r, r ≠ sw 96 → r ≠ sw 97 → r ≠ sw 98 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  set D := c.nreg (sw 96) with hD
  set S := c.nreg (sw 97) with hS
  -- the head: `0` at `D`
  have e₁ := Exec.storeN (P := P) hw (sw 96) (sw 90)
  set c₁ : Config := { c with nmem := upd c.nmem (c.nreg (sw 96)) (c.nreg (sw 90)) } with hc₁
  have w₁ := e₁.wb_right
  have e₂ := Exec.addN (P := P) w₁ (sw 96) (sw 96) (sw 91) (by
    rws [hc₁]; ruo [h1] sw at hD ⊢)
  set c₂ : Config := { c₁ with nreg := upd c₁.nreg (sw 96) (c₁.nreg (sw 96) + c₁.nreg (sw 91)) }
    with hc₂
  have w₂ := e₂.wb_right
  have r₂ : ∀ r, r ≠ sw 96 → c₂.nreg r = c.nreg r := fun r hr => by
    rw [hc₂, hc₁]; simp [hr]
  have d₂ : c₂.nreg (sw 96) = D + 1 := by rw [hc₂, hc₁]; simp [upd_same]; rw [h1]
  have m₂ : c₂.nmem = upd c.nmem D 0 := by rws [hc₂, hc₁]; rw [h0]
  -- five copies, with the invariant after `k` of them
  have step : ∀ (cc : Config) (k : ℕ), WordsBounded W cc → k < 5 → cc.nreg (sw 96) = D + 1 + k →
      cc.nreg (sw 97) = S + k → cc.nreg (sw 91) = 1 →
      (∀ a, (a < D + 1 ∨ D + 1 + k ≤ a) → cc.nmem a = c₂.nmem a) →
      (∀ j, j < k → cc.nmem (D + 1 + j) = c.nmem (S + j)) →
      ∃ c' k', Exec P W cp1 cc c' k' ∧ k' = 4 ∧ c'.nreg (sw 96) = D + 1 + (k + 1) ∧
        c'.nreg (sw 97) = S + (k + 1) ∧
        (∀ a, (a < D + 1 ∨ D + 1 + (k + 1) ≤ a) → c'.nmem a = c₂.nmem a) ∧
        (∀ j, j < k + 1 → c'.nmem (D + 1 + j) = c.nmem (S + j)) ∧
        (∀ r, r ≠ sw 96 → r ≠ sw 97 → r ≠ sw 98 → c'.nreg r = cc.nreg r) ∧
        c'.rreg = cc.rreg ∧ c'.rmem = cc.rmem ∧ c'.output = cc.output := by
    intro cc k hcc hk hd hs hone hkeep hval
    obtain ⟨c', k', ex, hk', a, b, m, r, x, y, z⟩ := cp1_exec (P := P) cc hcc hone
      (by rwo [hd]) (by rwo [hs])
    have hread : cc.nmem (S + k) = c.nmem (S + k) := by
      rw [hkeep _ (Or.inl (by omega)), m₂, upd_other _ _ _ (by omega)]
    refine ⟨c', k', ex, hk', by rwring [a, hd], by rwring [b, hs], fun a' ha' => ?_,
      fun j hj => ?_, r, x, y, z⟩
    · rw [m, hd, hs, upd_other _ _ _ (by omega)]
      exact hkeep a' (by omega)
    · rw [m, hd, hs]
      rcases (Nat.lt_succ_iff.1 hj).lt_or_eq with hj' | rfl
      · rw [upd_other _ _ _ (by omega)]; exact hval j hj'
      · rw [upd_same, hread]
  have hr2  := r₂
  obtain ⟨c₃, k₃, e₃, hk₃, d₃, s₃, m₃, v₃, r₃, x₃, y₃, z₃⟩ :=
    step c₂ 0 w₂ (by omega) (by rw [d₂]) (by rwr [hr2 _ (by ufo sw)])
      (by rw [hr2 _ (by ufo sw), h1]) (fun _ _ => rfl) (fun j hj => absurd hj (by omega))
  have o3 : c₃.nreg (sw 91) = 1 := by
    rw [r₃ _ (by ufo sw) (by ufo sw) (by ufo sw),
      hr2 _ (by ufo sw), h1]
  obtain ⟨c₄, k₄, e₄, hk₄, d₄, s₄, m₄, v₄, r₄, x₄, y₄, z₄⟩ :=
    step c₃ 1 e₃.wb_right (by omega) d₃ s₃ o3 m₃ v₃
  have o4 : c₄.nreg (sw 91) = 1 := by
    rw [r₄ _ (by ufo sw) (by ufo sw) (by ufo sw), o3]
  obtain ⟨c₅, k₅, e₅, hk₅, d₅, s₅, m₅, v₅, r₅, x₅, y₅, z₅⟩ :=
    step c₄ 2 e₄.wb_right (by omega) d₄ s₄ o4 m₄ v₄
  have o5 : c₅.nreg (sw 91) = 1 := by
    rw [r₅ _ (by ufo sw) (by ufo sw) (by ufo sw), o4]
  obtain ⟨c₆, k₆, e₆, hk₆, d₆, s₆, m₆, v₆, r₆, x₆, y₆, z₆⟩ :=
    step c₅ 3 e₅.wb_right (by omega) d₅ s₅ o5 m₅ v₅
  have o6 : c₆.nreg (sw 91) = 1 := by
    rw [r₆ _ (by ufo sw) (by ufo sw) (by ufo sw), o5]
  obtain ⟨c₇, k₇, e₇, hk₇, d₇, s₇, m₇, v₇, r₇, x₇, y₇, z₇⟩ :=
    step c₆ 4 e₆.wb_right (by omega) d₆ s₆ o6 m₆ v₆
  have ex : Exec P W copyDesc c c₇ (1 + 1 + 0 + (k₃ + (k₄ + (k₅ + (k₆ + k₇))))) := by
    unfold copyDesc
    exact .seq (Exec.block_cons e₁ (Exec.block_cons e₂ (Exec.block_nil w₂)))
      (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ e₇))))
  refine ⟨c₇, _, ex, by omega, by rw [d₇], ?_, v₇, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [m₇ _ (Or.inl (by omega)), m₂, upd_same]
  · intro a ha
    rw [m₇ _ (Or.inl (by omega)), m₂, upd_other _ _ _ (by omega)]
  · intro a ha
    rw [m₇ _ (Or.inr (by omega)), m₂, upd_other _ _ _ (by omega)]
  · intro r h96 h97 h98
    rw [r₇ r h96 h97 h98, r₆ r h96 h97 h98, r₅ r h96 h97 h98, r₄ r h96 h97 h98,
      r₃ r h96 h97 h98, hr2 r h96]
  · rw [x₇, x₆, x₅, x₄, x₃]
  · rw [y₇, y₆, y₅, y₄, y₃]
  · rw [z₇, z₆, z₅, z₄, z₃]

/-! ## The copied descriptor describes the chain model -/

/-- **The copied model descriptor** describes the chain model and is well formed. -/
theorem modelDesc_of_copy {P : Polygon} {m m' : ℕ → ℕ} {bw A E E' : ℕ} {H : Host} {C : Chain}
    (hwf : ChainWF P E m bw) (hC : ChainDescAt m bw (Qof P) H C) (hEA : E ≤ A)
    (he : ∀ a, a < E → m' a = m a) (h0 : m' A = 0)
    (hc : ∀ j, j < 5 → m' (A + 1 + j) = m (bw + j)) (hE' : A + 6 ≤ E') :
    ModelDescAt m' A (Qof P) (chainModel C) ∧ ModelDescWF P E' m' A ∧
      ChainDescAt m' (A + 1) (Qof P) H C := by
  obtain ⟨-, -, hEb, -⟩ := hwf.2 H C hC
  have hC' := chainDescAt_copy hC hEb he hc
  exact ⟨Or.inl ⟨h0, H, C, hC', rfl⟩,
    ⟨by omega, fun _ => chainWF_copy hwf hC he hc (by omega) (by omega)⟩, hC'⟩

/-! ## The junction of the descriptors -/

/-- **The junction is determined by its descriptors.** -/
theorem junction_unique {m : ℕ → ℕ} {bl br bw : ℕ} {Q : Polygon} {H H' : Host}
    {J J' : Merge.Junction} (h : JunctionAt m bl br bw Q H J) (h' : JunctionAt m bl br bw Q H' J') :
    J = J' := by
  have hl := NFLoc.chain_eq_of_desc h.1 h'.1
  have hr := NFLoc.chain_eq_of_desc h.2.1 h'.2.1
  obtain ⟨P, s, m₁, m₂, a, b, c⟩ := J
  obtain ⟨P', s', m₁', m₂', a', b', c'⟩ := J'
  simp [Merge.Junction.left, Merge.Junction.right, Chain.mk.injEq] at hl hr
  obtain ⟨rfl, rfl, rfl⟩ := hl
  obtain ⟨-, -, rfl⟩ := hr
  rfl

end

end SweepRam

end Chazelle.Core
