import RequestProject.SurfaceCellularCycle
import RequestProject.CombLoopWord
import RequestProject.Tac


/-! The literal signed word and literal edge path around the genus polygon.
The equality is before passing to homotopy or to edge-chain augmentation.
 -/

bwd

namespace FiniteChains.Davis
open Comb
universe u v

def commutatorLetterBlock (p : ι × ι) :=
  [(p.1, true), (p.2, true), (p.1, false), (p.2, false)]

def commutatorLetters (ps : List (ι × ι)) :=
  ps.flatMap commutatorLetterBlock

theorem mk_commutatorLetterBlock (p : ι × ι) :
    FreeGroup.mk (commutatorLetterBlock p) =
      FreeGroup.of p.1 * FreeGroup.of p.2 * (FreeGroup.of p.1)⁻¹ * (FreeGroup.of p.2)⁻¹ := by
  rfl

theorem mk_commutatorLetters (ps : List (ι × ι)) :
    FreeGroup.mk (commutatorLetters ps) = commWord FreeGroup.of ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      rwd [← FreeGroup.mul_mk, mk_commutatorLetterBlock, ih, commWord_cons]

theorem wordPath_commutatorLetters {ι : Type u}
    (f : ι → Loop X a) ps :
    wordPath f (commutatorLetters ps) = surfacePath f ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      change wordPath f (commutatorLetterBlock p ++ commutatorLetters ps) = _
      simp [wordPath_append, ih, commutatorLetterBlock, wordPath_cons, wordPath_nil, germLoopPath_pos, germLoopPath_neg, List.append_nil, surfacePath, List.append_assoc]

theorem surfacePath_append {ι : Type u}
    (f : ι → Loop X a) ps rs :
    surfacePath f (ps ++ rs) = surfacePath f ps ++ surfacePath f rs := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [List.cons_append, surfacePath, ih, List.append_assoc]

theorem surfacePath_eq_flatMap {ι : Type u}
    (f : ι → Loop X a) ps :
    surfacePath f ps = ps.flatMap (fun p =>
      (f p.1).1 ++ (f p.2).1 ++ revPath (f p.1).1 ++ revPath (f p.2).1) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [surfacePath, List.flatMap_cons, ih, List.append_assoc]

theorem wordPath_map_letters {X : Complex2.{u}} {a} {ι κ : Type v}
    (f : κ → Loop X a) (j : ι → κ) l :
    wordPath f (l.map (fun x => (j x.1, x.2))) = wordPath (fun i => f (j i)) l := by
  induction l <;> aesop

namespace Genus
open RACG Mirror PresModel BlockFamily
variable (q : ℕ)

/-- Exactly the four oriented letters of each handle, in polygon order. -/
def genusSurfaceLetters :=
  (finitePairs q).flatMap (fun p =>
    [(p.1, true), (p.2, true), (p.1, false), (p.2, false)])

theorem genusSurfaceLetters_mk :
    FreeGroup.mk (genusSurfaceLetters q) = commWord FreeGroup.of (finitePairs q) :=
  mk_commutatorLetters _

variable [NeZero q]

def naturalSurfaceLoops (i : ℕ × Bool) : Loop (sdCx (gc q)) (gBase q) :=
  ⟨gSig q i, isPath_gSig q i⟩

theorem naturalSurfaceLoops_block (hn : n < q) :
    surfacePath (naturalSurfaceLoops q) [((n, false), (n, true))] = gBlock q n := by
  have ha : (naturalSurfaceLoops q (n, false)).1 = gPath q (8 * n) := by
    simp [naturalSurfaceLoops, gSig, Nat.mod_eq_of_lt hn, Bool.false_eq_true,
      ↓reduceIte, Nat.add_zero]
  have hb : (naturalSurfaceLoops q (n, true)).1 = gPath q (8 * n + 2) := by
    simp [naturalSurfaceLoops, gSig, Nat.mod_eq_of_lt hn, ↓reduceIte]
  simp [surfacePath, ha, hb, List.append_nil, ← gPath_rev_a q hn, ← gPath_rev_b q hn]

/-- Every initial string of complete handle blocks is the actual polygon
boundary prefix, with its original edge order and signs. -/
theorem surfacePath_genPairs_eq_bdPath (hn : n ≤ q) :
    surfacePath (naturalSurfaceLoops q) (genPairs n) = bdPath (gc q) (8 * n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hlt : n < q := by omega
      have hpairs : genPairs (n + 1) = genPairs n ++ [((n, false), (n, true))] := by
        simp [genPairs, List.range_succ, List.map_append, List.map_singleton]
      simp [hpairs, surfacePath_append, ih (by omega), naturalSurfaceLoops_block q hlt, bdPath_block]

theorem finiteSurfacePath_eq_bdPath :
    surfacePath (finiteMarkedLoops q) (finitePairs q) = bdPath (gc q) (8 * q) := by
  have hreindex : surfacePath (finiteMarkedLoops q) (finitePairs q) =
      surfacePath (naturalSurfaceLoops q) (genPairs q) := by
    simp [surfacePath_eq_flatMap, finitePairs, genPairs, List.flatMap_map]
    have hrange := List.map_coe_finRange_eq_range (n := q)
    rwd [← hrange, List.flatMap_map]
    rfl
  exact hreindex.trans (surfacePath_genPairs_eq_bdPath q (le_refl q))

/-- The marked free-group word traverses the genuine polygon boundary exactly. -/
theorem genusSurfaceLetters_wordPath :
    wordPath (finiteMarkedLoops q) (genusSurfaceLetters q) = bdPath (gc q) (8 * q) := by
  rwd [wordPath_commutatorLetters, finiteSurfacePath_eq_bdPath]

variable {I : Type}

/-- The same literal word on the named alphabet; no internal generator occurs. -/
def genusNamedSurfaceLetters : List ((I ⊕ (Fin q × Bool)) × Bool) :=
  (genusSurfaceLetters q).map (fun x => (Sum.inr x.1, x.2))

omit [NeZero q] in
theorem genusNamedSurfaceLetters_mk :
    FreeGroup.mk (genusNamedSurfaceLetters (I := I) q) =
      commWord (fun i : Fin q × Bool => FreeGroup.of (Sum.inr (α := I) i)) (finitePairs q) := by
  simp [genusNamedSurfaceLetters, ← FreeGroup.map.mk, genusSurfaceLetters_mk, map_commWord]
