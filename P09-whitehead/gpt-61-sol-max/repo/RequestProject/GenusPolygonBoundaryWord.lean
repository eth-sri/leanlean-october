import Mathlib.Tactic

import RequestProject.SurfaceCellularCycle
import RequestProject.CombLoopWord

/-! The literal signed word and literal edge path around the genus polygon.
The equality is before passing to homotopy or to edge-chain augmentation.
 -/

set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis
open Comb

variable {ι : Type u}
def commutatorLetterBlock  (p : ι × ι)  :=
  [(p.1, true), (p.2, true), (p.1, false), (p.2, false)]

variable (ps : List (ι × ι))
def commutatorLetters    :=
  ps.flatMap commutatorLetterBlock

theorem mk_commutatorLetterBlock  (p : ι × ι) :
    FreeGroup.mk (commutatorLetterBlock p) =
      FreeGroup.of p.1 * FreeGroup.of p.2 * (FreeGroup.of p.1)⁻¹ * (FreeGroup.of p.2)⁻¹ := rfl

theorem mk_commutatorLetters   :
    FreeGroup.mk (commutatorLetters ps) = commWord FreeGroup.of ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      
      rw (config := { transparency := .default }) [← FreeGroup.mul_mk, mk_commutatorLetterBlock, ih, commWord_cons]

variable {X : Complex2.{u}}
variable {a : X.V}
theorem wordPath_commutatorLetters   {ι : Type u}
    (f : ι → Loop X a) (ps : List (ι × ι)) :
    wordPath f (commutatorLetters ps) = surfacePath f ps := by
  induction ps <;> simp_all [commutatorLetterBlock, commutatorLetters, surfacePath]

theorem surfacePath_append   {ι : Type u}
    (f : ι → Loop X a) (ps rs : List (ι × ι)) :
    surfacePath f (ps ++ rs) = surfacePath f ps ++ surfacePath f rs := by
  induction ps <;> simp_all [surfacePath]

theorem surfacePath_eq_flatMap   {ι : Type u}
    (f : ι → Loop X a) (ps : List (ι × ι)) :
    surfacePath f ps = ps.flatMap (fun p =>
      (f p.1).1 ++ (f p.2).1 ++ revPath (f p.1).1 ++ revPath (f p.2).1) := by
  induction ps <;> simp_all [surfacePath]

theorem wordPath_map_letters   {ι κ : Type v}
    (f : κ → Loop X a) (j : ι → κ) (l : List (ι × Bool)) :
    wordPath f (l.map (fun x => (j x.1, x.2))) = wordPath (fun i => f (j i)) l := by
  induction l <;> aesop (add simp [List.map_cons, wordPath_cons])

namespace Genus

variable (q : ℕ)

/-- Exactly the four oriented letters of each handle, in polygon order. -/
def genusSurfaceLetters  :=
  (finitePairs q).flatMap (fun p =>
    [(p.1, true), (p.2, true), (p.1, false), (p.2, false)])

abbrev genusSurfaceLetters_mk  :=
  FiniteChains.Davis.mk_commutatorLetters (FiniteChains.Davis.Genus.finitePairs q)

variable [NeZero q]

def naturalSurfaceLoops (i : ℕ × Bool) : Loop (sdCx (gc q)) (gBase q) :=
  ⟨gSig q i, isPath_gSig q i⟩

theorem naturalSurfaceLoops_block {n : ℕ} (hn : n < q) :
    surfacePath (naturalSurfaceLoops q) [((n, false), (n, true))] = gBlock q n := by
  have ha : (naturalSurfaceLoops q (n, false)).1 = gPath q (8 * n) := by
    simp only [naturalSurfaceLoops, gSig, Nat.mod_eq_of_lt hn, Bool.false_eq_true,
      ↓reduceIte, Nat.add_zero]
  have hb : (naturalSurfaceLoops q (n, true)).1 = gPath q (8 * n + 2) := by
    simp only [naturalSurfaceLoops, gSig, Nat.mod_eq_of_lt hn, ↓reduceIte]
  simp only [surfacePath, ha, hb, List.append_nil]
  rw  [← gPath_rev_a q hn, ← gPath_rev_b q hn]

/-- Every initial string of complete handle blocks is the actual polygon
boundary prefix, with its original edge order and signs. -/
theorem surfacePath_genPairs_eq_bdPath {n : ℕ} (hn : n ≤ q) :
    surfacePath (naturalSurfaceLoops q) (genPairs n) = bdPath (gc q) (8 * n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hlt : n < q := by omega
      have hpairs : genPairs (n + 1) = genPairs n ++ [((n, false), (n, true))] := by
        simp_all [genPairs, List.range_succ]
      rw  [hpairs, surfacePath_append, ih (by omega),
        naturalSurfaceLoops_block q hlt, bdPath_block]

theorem finiteSurfacePath_eq_bdPath :
    surfacePath (finiteMarkedLoops q) (finitePairs q) = bdPath (gc q) (8 * q) := by
  have hreindex : surfacePath (finiteMarkedLoops q) (finitePairs q) =
      surfacePath (naturalSurfaceLoops q) (genPairs q) := by
    simp only [surfacePath_eq_flatMap, finitePairs, genPairs, List.flatMap_map]
    have hrange := List.map_coe_finRange_eq_range (n := q)
    rw  [← hrange, List.flatMap_map]
    rfl
  exact hreindex.trans (surfacePath_genPairs_eq_bdPath q (le_refl q))

/-- The marked free-group word traverses the genuine polygon boundary exactly. -/
theorem genusSurfaceLetters_wordPath :
    wordPath (finiteMarkedLoops q) (genusSurfaceLetters q) = bdPath (gc q) (8 * q) := by
  
  rw (config := { transparency := .default }) [wordPath_commutatorLetters, finiteSurfacePath_eq_bdPath]

variable {I : Type}

/-- The same literal word on the named alphabet; no internal generator occurs. -/
def genusNamedSurfaceLetters : List ((I ⊕ (Fin q × Bool)) × Bool) :=
  (genusSurfaceLetters q).map (fun x => (Sum.inr x.1, x.2))

omit [NeZero q] in
theorem genusNamedSurfaceLetters_mk :
    FreeGroup.mk (genusNamedSurfaceLetters (I := I) q) =
      commWord (fun i : Fin q × Bool => FreeGroup.of (Sum.inr (α := I) i)) (finitePairs q) := by
  rw (config := { transparency := .default }) [genusNamedSurfaceLetters, ← FreeGroup.map.mk, genusSurfaceLetters_mk, map_commWord]
  exact commWord_congr (fun i => FreeGroup.map.of) _

end FiniteChains.Davis.Genus

