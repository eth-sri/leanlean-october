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
variable {M : Type w} {β : LimitStage}

/-- The face of the one-point extension over the face `g` of the base: `extendFace g` maps
`i < n` to `(g i).castSucc` and the new last index to the new last index — the embedding
along which a coface of the master restricts to a coface of the face. -/
def extendFace {n N : ℕ} (g : Fin n ↪ Fin N) : Fin (n + 1) ↪ Fin (N + 1) :=
  ⟨Fin.snoc (fun i => (g i).castSucc) (Fin.last N),
    Fin.snoc_injective_of_injective (Fin.castSucc_injective N |>.comp g.injective)
      (fun ⟨i, hi⟩ => (Fin.castSucc_lt_last (g i)).ne hi)⟩

@[simp] theorem extendFace_castSucc {n N : ℕ} (g : Fin n ↪ Fin N) (i : Fin n) :
    extendFace g (Fin.castSucc i) = (g i).castSucc := by
  simp [extendFace]

@[simp] theorem extendFace_last {n N : ℕ} (g : Fin n ↪ Fin N) :
    extendFace g (Fin.last n) = Fin.last N := by
  simp [extendFace]

/-- The `extendFace` equation on concatenations: extending the master event tuple restricts
along `extendFace g` to the extension of the face tuple. -/
theorem extendFace_trans_snoc {n N : ℕ} (g : Fin n ↪ Fin N) {w : Fin N ↪ M} {y : M}
    (hyw : y ∉ Set.range w) (hyt : y ∉ Set.range (g.trans w)) :
    (extendFace g).trans (snoc w y hyw) = snoc (g.trans w) y hyt := by
  ext i
  induction i using Fin.lastCases with
  | last => simp [snoc]
  | cast i => simp [snoc]

/-- The padded event tuple: the master `w` followed by the fresh block `ys`. -/
def appendEmb {N m : ℕ} (w : Fin N ↪ M) (ys : Fin m ↪ M)
    (hdisj : ∀ j, ys j ∉ Set.range w) : Fin (N + m) ↪ M :=
  ⟨Fin.append w ys, by
    intro a b hab
    induction a using Fin.addCases with
    | left i =>
      induction b using Fin.addCases with
      | left i' =>
        rw [Fin.append_left, Fin.append_left] at hab
        rw [w.injective hab]
      | right j' =>
        rw [Fin.append_left, Fin.append_right] at hab
        exact absurd ⟨i, hab⟩ (hdisj j')
    | right j =>
      induction b using Fin.addCases with
      | left i' =>
        rw [Fin.append_right, Fin.append_left] at hab
        exact absurd ⟨i', hab.symm⟩ (hdisj j)
      | right j' =>
        rw [Fin.append_right, Fin.append_right] at hab
        rw [ys.injective hab]⟩

@[simp] theorem appendEmb_castAdd {N m : ℕ} (w : Fin N ↪ M) (ys : Fin m ↪ M)
    (hdisj : ∀ j, ys j ∉ Set.range w) (i : Fin N) :
    appendEmb w ys hdisj (Fin.castAdd m i) = w i :=
  Fin.append_left _ _ i

@[simp] theorem appendEmb_natAdd {N m : ℕ} (w : Fin N ↪ M) (ys : Fin m ↪ M)
    (hdisj : ∀ j, ys j ∉ Set.range w) (j : Fin m) :
    appendEmb w ys hdisj (Fin.natAdd N j) = ys j :=
  Fin.append_right _ _ j

/-- The designated extended face of a `k`-padded one-point master extension: `i < n` goes to
`g i` in the initial block, the new last index to the new last index (the designated
coordinate, AFTER the padding block). -/
def extendFacePad (k : ℕ) {n N : ℕ} (g : Fin n ↪ Fin N) :
    Fin (n + 1) ↪ Fin (N + (k + 1)) where
  toFun := Fin.snoc (fun i => Fin.castAdd (k + 1) (g i)) (Fin.last (N + k))
  inj' := Fin.snoc_injective_of_injective
    (fun a b hab => g.injective
      (Fin.ext (congrArg (Fin.val : Fin (N + (k + 1)) → ℕ) hab)))
    (fun ⟨i, hi⟩ => by
      have h1 : (Fin.castAdd (k + 1) (g i)).val < N := Fin.castAdd_lt _ (g i)
      have hi' : Fin.castAdd (k + 1) (g i) = Fin.last (N + k) := hi
      rw [hi'] at h1
      simp only [Fin.val_last] at h1
      omega)

@[simp] theorem extendFacePad_castSucc (k : ℕ) {n N : ℕ} (g : Fin n ↪ Fin N) (i : Fin n) :
    extendFacePad k g (Fin.castSucc i) = Fin.castAdd (k + 1) (g i) := by
  simp [extendFacePad]

@[simp] theorem extendFacePad_last (k : ℕ) {n N : ℕ} (g : Fin n ↪ Fin N) :
    extendFacePad k g (Fin.last n) = Fin.last (N + k) := by
  simp [extendFacePad]

end FixedHeight
end VaughtConjecture.Knight
