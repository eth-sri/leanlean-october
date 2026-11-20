module

public import Chazelle.Core.SpecRam

/-! Costed execution with a stage invariant and a compositional frame. The frame records
which parts of the machine state the stage may write and bounds allocator growth. -/

namespace Chazelle.Core
open Machine

@[expose] public section

class RunFrame (F : Config → Config → ℕ → Prop) where
  refl : ∀ c, F c c 0
  comp : ∀ {c d e i j}, F c d i → F d e j → F c e (i + j)
  pad : ∀ {c d i j}, F c d i → i ≤ j → F c d j
  base_le : ∀ {c d k}, F c d k → c.nreg ALLOC ≤ d.nreg ALLOC
  base_le_add : ∀ {c d k}, F c d k → d.nreg ALLOC ≤ c.nreg ALLOC + k

/-- An execution with an invariant `I` at exit, a frame `F`, and a specific postcondition `Q`. -/
def RunSpec (I : Config → Prop) (F : Config → Config → ℕ → Prop)
    (P : Polygon) (W : ℕ) (s : Stmt) (c : Config) (K : ℕ) (Q : Config → Prop) : Prop :=
  ∃ d k, Exec P W s c d k ∧ k ≤ K ∧ I d ∧ F c d k ∧ Q d

namespace RunSpec

variable {I : Config → Prop} {F : Config → Config → ℕ → Prop} {P : Polygon} {W : ℕ}
variable {s t : Stmt} {c : Config} {K K' : ℕ} {Q Q' : Config → Prop}

theorem mono (h : RunSpec I F P W s c K Q) (hk : K ≤ K') (hq : ∀ d, Q d → Q' d) :
    RunSpec I F P W s c K' Q' := by
  obtain ⟨d, k, e, hk', hi, hf, hp⟩ := h
  exact ⟨d, k, e, hk'.trans hk, hi, hf, hq d hp⟩

/-- Increase the step budget without changing the postcondition. -/
theorem budget (h : RunSpec I F P W s c K Q) (hk : K ≤ K' := by omega) : RunSpec I F P W s c K' Q :=
  h.mono hk (fun _ hq => hq)

variable [RunFrame F]

theorem seq (h : RunSpec I F P W s c K Q)
    (h' : ∀ d, I d → c.nreg ALLOC ≤ d.nreg ALLOC → d.nreg ALLOC ≤ c.nreg ALLOC + K → Q d →
      RunSpec I F P W t d K' Q') : RunSpec I F P W (.seq s t) c (K + K') Q' := by
  obtain ⟨d, i, e, hk, hi, hf, hq⟩ := h
  have := RunFrame.base_le_add hf
  obtain ⟨d', j, e', hk', hi', hf', hq'⟩ := h' d hi (RunFrame.base_le hf) (by omega) hq
  exact ⟨d', i + j, .seq e e', by omega, hi', RunFrame.comp hf hf', hq'⟩

theorem ifT {a b : ℕ} (ht : c.nreg a < c.nreg b) (h : RunSpec I F P W s c K Q) :
    RunSpec I F P W (.ifLtN a b s t) c (K + 2) Q := by
  obtain ⟨d, k, e, hk, hi, hf, hq⟩ := h
  exact ⟨d, _, .ifLtN_true ht e, by omega, hi, RunFrame.pad hf (by omega), hq⟩

theorem ifF {a b : ℕ} (ht : ¬ c.nreg a < c.nreg b) (h : RunSpec I F P W t c K Q) :
    RunSpec I F P W (.ifLtN a b s t) c (K + 2) Q := by
  obtain ⟨d, k, e, hk, hi, hf, hq⟩ := h
  exact ⟨d, _, .ifLtN_false ht e, by omega, hi, RunFrame.pad hf (by omega), hq⟩

theorem skip (hw : WordsBounded W c) (hi : I c) (hq : Q c) : RunSpec I F P W .skip c K Q :=
  ⟨c, 0, .skip hw, Nat.zero_le _, hi, RunFrame.refl c, hq⟩

/-- Bounded iterations, with enough allocator room for all of them. -/
theorem whileN {a b : ℕ} (J : Config → Prop) (μ : Config → ℕ) (B : ℕ)
    (hw : ∀ d, I d → WordsBounded W d)
    (hpos : ∀ d, J d → d.nreg a < d.nreg b → 0 < μ d)
    (hbody : ∀ d, I d → J d → d.nreg a < d.nreg b → d.nreg ALLOC + B ≤ W →
      RunSpec I F P W s d B (fun d' => J d' ∧ μ d' < μ d))
    (hi : I c) (hj : J c) (hr : c.nreg ALLOC + (B + 2) * μ c ≤ W) :
    RunSpec I F P W (.whileLtN a b s) c ((B + 2) * μ c + 2)
      (fun d => J d ∧ ¬ d.nreg a < d.nreg b) := by
  obtain ⟨d, k, e, ⟨hi', hj'⟩, ht, hk, hf⟩ := Exec.whileLtN_budgeted
    (fun d => I d ∧ J d) μ (·.nreg ALLOC) B F (fun _ h => hw _ h.1)
    (fun d => RunFrame.pad (RunFrame.refl d) (by decide))
    (fun f g => RunFrame.pad (RunFrame.comp f g) (by omega)) RunFrame.base_le_add
    (fun d h => hpos d h.2) (fun d h ht hr' => by
      obtain ⟨d', k, e, hk, hi', hf, hj', hμ⟩ := hbody d h.1 h.2 ht hr'
      exact ⟨d', k, e, ⟨hi', hj'⟩, hk, hμ, hf⟩) ⟨hi, hj⟩ hr
  exact ⟨d, k, e, hk, hi', hf, hj', ht⟩

end RunSpec
end
end Chazelle.Core
