import RequestProject.CombPi1
import RequestProject.Tac


bwd

namespace FiniteChains.Comb
universe u
variable {X : Complex2.{u}} {o a b c : X.V}

/-- The actual based loop obtained by joining a path to chosen paths from the root. -/
def rootedPathLoop r (hr : IsPathX X r o a)
    p (hp : IsPathX X p a b)
    s (hs : IsPathX X s o b) : Loop X o :=
  ⟨r ++ p ++ revPath s, (hr.append hp).append (isPath_revPath hs)⟩

/-- Actual rooted path classes multiply by concatenation; the intermediate root path cancels. -/
theorem rootedPathLoop_append r hr
    p (hp : IsPathX X p a b)
    s hs
    q hq
    t (ht : IsPathX X t o c) :
    Pi1.mk (rootedPathLoop r hr (p ++ q) (hp.append hq) t ht) =
      Pi1.mk (rootedPathLoop r hr p hp s hs) *
        Pi1.mk (rootedPathLoop s hs q hq t ht) := by
  apply Quotient.sound
  have h := (htpy_revPath_append hs).congr_append (hr.append hp)
    (hq.append (isPath_revPath ht))
  change Htpy X o o ((r ++ (p ++ q)) ++ revPath t)
    ((r ++ p ++ revPath s) ++ (s ++ q ++ revPath t))
  simpa [List.append_assoc, List.nil_append] using h.symm

/-- Closing the empty actual path at a vertex gives the trivial based loop. -/
theorem rootedPathLoop_nil r (hr : IsPathX X r o a) :
    Pi1.mk (rootedPathLoop r hr [] rfl r hr) = 1 := by
  apply Quotient.sound
  change Htpy X o o _ _
  simpa [rootedPathLoop, List.append_nil] using htpy_append_revPath hr

/-- Close an actual oriented edge by actual paths from the root to its endpoints. -/
def rootedGermLoop (r : X.V → List (X.E × Bool))
    (hr : ∀ v, IsPathX X (r v) o v) (e : X.E × Bool) :=
  rootedPathLoop _ (hr _) _ (isPath_single e)
    _ (hr _)

/-- Every actual rooted path class factors into its actual rooted single-edge classes. -/
theorem rootedPathLoop_eq_prod r
    (hr : ∀ v, IsPathX X (r v) o v)
    p a b hp :
    Pi1.mk (rootedPathLoop (r a) (hr a) p hp (r b) (hr b)) =
      (p.map (fun e => Pi1.mk (rootedGermLoop r hr e))).prod := by
  induction p generalizing a with
  | nil =>
    subst b
    exact rootedPathLoop_nil _ _
  | cons e p ih =>
    cases' hp with he hp
    subst a
    have h := rootedPathLoop_append _ (hr _)
      _ (isPath_single e) _ (hr _) p hp _ (hr b)
    aesop

/-- Reversing an actual rooted germ inverts its actual loop class. -/
theorem rootedGermLoop_rev r
    (hr : ∀ v, IsPathX X (r v) o v) e :
    Pi1.mk (rootedGermLoop r hr (revGerm e)) =
      (Pi1.mk (rootedGermLoop r hr e))⁻¹ := by
  apply Quotient.sound
  simp [rootedGermLoop, rootedPathLoop, germSrc_revGerm, germTgt_revGerm, revPath_append, revPath_revPath, revPath_cons, revPath_nil, List.nil_append, List.append_assoc]
