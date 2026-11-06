/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.Model
public import Mathlib.Data.Set.Finite.Range

/-! # Finite tuple and padded-face geometry

Factorization, append embeddings and designated faces, independent of request enumeration
and infinite runs. All occurrence equations retain their original names and definitions. -/

@[expose] public section

namespace VaughtConjecture.Knight
open TypeTower Value ExtOrd
universe w
namespace FixedHeight
open KnightRealization
variable {M : Type w}

/-- The face of the one-point extension over the face `g` of the base: `extendFace g` maps
`i < n` to `(g i).castSucc` and the new last index to the new last index — the embedding
along which a coface of the master restricts to a coface of the face. -/
def extendFace {n N} (g : Fin n ↪ Fin N) : Fin (n + 1) ↪ Fin (N + 1) :=
  ⟨Fin.snoc (fun i => (g i).castSucc) (Fin.last N),
    Fin.snoc_injective_of_injective (Fin.castSucc_injective N |>.comp g.injective)
      (fun ⟨i, hi⟩ => (Fin.castSucc_lt_last (g i)).ne hi)⟩

section
variable {n N : ℕ} (g : Fin n ↪ Fin N)

@[simp] theorem extendFace_castSucc (i : Fin n) :
    extendFace g (Fin.castSucc i) = (g i).castSucc := by
  simp [extendFace]

@[simp] theorem extendFace_last  :
    extendFace g (Fin.last n) = Fin.last N := by
  simp [extendFace]

/-- The `extendFace` equation on concatenations: extending the master event tuple restricts
along `extendFace g` to the extension of the face tuple. -/
theorem extendFace_trans_snoc {w : Fin N ↪ M} {y}
    hyw hyt :
    (extendFace g).trans (snoc w y hyw) = snoc (g.trans w) y hyt := by
  ext i
  induction i using Fin.lastCases with
  | last => simp [snoc]
  | cast i => simp [snoc]

end

end FixedHeight
end VaughtConjecture.Knight
