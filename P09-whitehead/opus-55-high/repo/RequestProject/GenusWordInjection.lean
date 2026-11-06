import RequestProject.GenusFiniteMarking
import RequestProject.SurfaceWordExpansion
import RequestProject.Tac


/-! Structural group injectivity for substitution of arbitrary words in a finite genus block. -/

bwd

namespace FiniteChains.Davis.Genus

open RACG Mirror Comb PresModel BlockFamily

variable {α Jr : Type} (ρ : Jr ⊕ PUnit.{1} → FreeGroup α)
  (q : ℕ) [NeZero q] (u : Fin q × Bool → FreeGroup α)

/-- Named generators for the two loops of a handle, extended periodically. -/
def namedA (h : ℕ) : α ⊕ (Fin q × Bool) :=
  Sum.inr (⟨h % q, Nat.mod_lt _ q.pos_of_neZero⟩, false)

def namedB (h : ℕ) : α ⊕ (Fin q × Bool) :=
  Sum.inr (⟨h % q, Nat.mod_lt _ q.pos_of_neZero⟩, true)

abbrev namedPres := SurfaceWordExpansion.expandedRel ρ u (finitePairs q)

 theorem namedPres_surface : namedPres ρ q u (Sum.inr PUnit.unit) =
    FreeGroup.mk (surfWord (namedA (α := α) q) (namedB (α := α) q) q) := by
  change commWord (fun x => FreeGroup.of (Sum.inr x)) (finitePairs q) = _
  have h : (fun x =>
      FreeGroup.mk (genLw (namedA (α := α) q) (namedB (α := α) q) (x.1.val, x.2))) =
        (fun x => FreeGroup.of (Sum.inr x)) := by
    funext x
    cases' x with h b
    have hm := Nat.mod_eq_of_lt h.isLt
    cases b <;> simp [genLw, namedA, namedB, hm] <;> rfl
  rw [← h, commWord_finitePairs q (fun x =>
    FreeGroup.mk (genLw (namedA (α := α) q) (namedB (α := α) q) x))]
  exact (mk_surfWord _ _ q).symm

 theorem namedLw_eq s x :
    finiteLw (namedA (α := α) q) (namedB (α := α) q) q s x = [(Sum.inr x, true)] := by
  cases' x with h b
  have hm := Nat.mod_eq_of_lt h.isLt
  cases b
  · change [sLet (namedA (α := α) q) (namedB (α := α) q) (4 * (h.val % q) + 0)] = _
    rw [sLet]
    simp [namedA, hm]
  · change [sLet (namedA (α := α) q) (namedB (α := α) q) (4 * (h.val % q) + 1)] = _
    rw [hm]
    rw [sLet, show (4 * h.val + 1) / 4 = h.val from by omega]
    simp [namedB, hm]

variable (T : SpanningTree (orderCx (QOld (cmpRel (SCell (gvc q) (gec q) (gc q))))))

variable (hrho : ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q))
