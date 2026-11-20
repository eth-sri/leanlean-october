/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SelectedCommonCharts
public import VaughtConjecture.Knight.PairedTrace

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower KnightRealization

universe w

/-- An admissibility predicate on rooted extensions: root embedding, base label, extension
label. -/
abbrev RootedAdmissibility (α : LimitStage) : Type 1 :=
  ∀ {n N : ℕ}, (Fin n ↪ Fin N) → S α.1 n → S α.1 N → Prop

variable {α : LimitStage} {M : Type w}

/-- **The core-rooted extension property** (Prop. 7.3.3 shape): over every evaluated tuple
containing the core, every admissible rooted extension of the realized label is realized. -/
def RootedExtensionOver (W : KnightRealization α M) {c : ℕ} (core : Fin c ↪ M)
    (Adm : RootedAdmissibility α) : Prop :=
  ∀ {n : ℕ} (t : Fin n ↪ M) (p : S α.1 n), (∃ e : Fin c ↪ Fin n, e.trans t = core) →
    W.eval t = some p →
    ∀ {N : ℕ} (f : Fin n ↪ Fin N) (P : S α.1 N), typeMap f P = some p → Adm f p P →
      ∃ u : Fin N ↪ M, f.trans u = t ∧ W.eval u = some P

/-- The rooted embedding of a chart into a covering of its one-point extension. -/
theorem trans_snoc_cover {n k : ℕ} {t : Fin n ↪ M} {x : M} {hx : x ∉ Set.range t}
    {s : Fin (n + 1 + k) ↪ M} (hst : (Fin.castAddEmb k).trans s = snoc t x hx) :
    (Fin.castSuccEmb.trans (Fin.castAddEmb k)).trans s = t := by
  ext i
  have h := DFunLike.congr_fun hst (Fin.castSucc i)
  simp only [Function.Embedding.trans_apply, Fin.castAddEmb_apply] at h
  simp_all

theorem cover_mem_range {n k : ℕ} {t : Fin n ↪ M} {x : M} {hx : x ∉ Set.range t}
    {s : Fin (n + 1 + k) ↪ M} (hst : (Fin.castAddEmb k).trans s = snoc t x hx) :
    ∃ i, s i = x := by
  refine ⟨Fin.castAdd k (Fin.last n), ?_⟩
  have h := DFunLike.congr_fun hst (Fin.last n)
  simp only [Function.Embedding.trans_apply, Fin.castAddEmb_apply] at h
  simp_all

end VaughtConjecture.Knight
