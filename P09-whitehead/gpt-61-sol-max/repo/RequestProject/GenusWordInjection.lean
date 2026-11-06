import Mathlib.Tactic

import RequestProject.GenusFiniteMarking
import RequestProject.SurfaceWordExpansion

/-! Structural group injectivity for substitution of arbitrary words in a finite genus block. -/


namespace FiniteChains.Davis.Genus



variable {α Jr : Type} (ρ : Jr ⊕ PUnit.{1} → FreeGroup α)
  (q : ℕ) [NeZero q] (u : Fin q × Bool → FreeGroup α)

/-- Named generators for the two loops of a handle, extended periodically. -/
def namedA (h : ℕ) : α ⊕ (Fin q × Bool) :=
  Sum.inr (⟨h % q, Nat.mod_lt _ (Nat.pos_of_neZero q)⟩, false)

def namedB (h : ℕ) : α ⊕ (Fin q × Bool) :=
  Sum.inr (⟨h % q, Nat.mod_lt _ (Nat.pos_of_neZero q)⟩, true)

abbrev namedPres := SurfaceWordExpansion.expandedRel ρ u (finitePairs q)

 theorem namedPres_surface : namedPres ρ q u (Sum.inr PUnit.unit) =
    FreeGroup.mk (surfWord (namedA (α := α) q) (namedB (α := α) q) q) := by
  change commWord (fun x => FreeGroup.of (Sum.inr x)) (finitePairs q) = _
  have h : (fun x : Fin q × Bool =>
      FreeGroup.mk (genLw (namedA (α := α) q) (namedB (α := α) q) (x.1.val, x.2))) =
        (fun x => FreeGroup.of (Sum.inr x)) := by
    funext x
    obtain ⟨h, b⟩ := x
    have hm  := Nat.mod_eq_of_lt h.isLt
    cases b <;> simp [genLw, namedA, namedB, hm] <;> rfl
  rw [← h, commWord_finitePairs q (fun x =>
    FreeGroup.mk (genLw (namedA (α := α) q) (namedB (α := α) q) x))]
  exact (mk_surfWord (namedA (α := α) q) (namedB (α := α) q) q).symm

 theorem namedLw_eq (s : PUnit.{1}) (x : Fin q × Bool) :
    finiteLw (namedA (α := α) q) (namedB (α := α) q) q s x = [(Sum.inr x, true)] := by
  obtain ⟨h, b⟩ := x
  have hm  := Nat.mod_eq_of_lt h.isLt
  cases b
  · change [sLet (namedA (α := α) q) (namedB (α := α) q) (4 * (h.val % q) + 0)] = _
    rw [hm]
    rw [sLet, if_pos (by omega), show (4 * h.val + 0) / 4 = h.val from by omega]
    simp [namedA, hm]
  · change [sLet (namedA (α := α) q) (namedB (α := α) q) (4 * (h.val % q) + 1)] = _
    rw [hm]
    rw [sLet, if_neg (by omega), if_pos (by omega),
      show (4 * h.val + 1) / 4 = h.val from by omega]
    simp [namedB, hm]





end FiniteChains.Davis.Genus
