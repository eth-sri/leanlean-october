module

public import RequestProject.ClassicalCWChainCanonicalHomotopies
public import RequestProject.PresWordEmbeddingCombPi2
public import RequestProject.PresChainTopologicalFinsupp

@[expose] public section

/-! The actual topological pi2 hypotheses of an original CW filtration
give a finite-support presentation chain. The initial presentation here
is the simultaneous model of this filtration's C0. Identifying it with
one fixed model across different ambient filtrations is a separate step.
Unverified source. -/

noncomputable section
namespace FiniteChains.ClassicalCW.ChainWords
open ClassicalSkeletonAttachment ClassicalGraphModel RelativeAttachment PresModel
open Set Topology
open scoped Classical
variable (K : Whitehead.TwoComplex) {n : ℕ}
  (C : Fin (n + 1) → CWComplex.Subcomplex (Set.univ : Set K))
  (hC : Monotone C) (hconn : ∀ i, ConnectedSpace (C i : Set K))
  [Choices C]
  [TreeChoice K C]

theorem canonicalInclusion_zeroPi2 {i k : Fin (n + 1)} (hik : i ≤ k)
    (h : Whitehead.KillsPi2 (⟨Set.inclusion (hC hik), continuous_inclusion (hC hik)⟩ :
        C((C i : Set K), (C k : Set K)))) :
    Comb.ZeroPi2 (Comb.presInclHom (canonicalGenInclusion K C hC hconn hik)
      (canonicalGenInclusion K C hC hconn hik).injective
      (canonicalRelators K C hC hconn i) (canonicalRelators K C hC hconn k)
      (canonicalCellInclusion K C hC hik) (canonicalRelators_natural K C hC hconn hik)) := by
  let e := canonicalWordEmbedding K C hC hconn hik
  have h₁ := e.killsPi2_iff_combPi2
    (fun j => List.length_pos_of_ne_nil (canonicalWords_ne_nil K C hC hconn i j))
    (fun j => List.length_pos_of_ne_nil (canonicalWords_ne_nil K C hC hconn k j))
    (canonicalRelators K C hC hconn i) (canonicalRelators K C hC hconn k)
    (canonicalWords_mk K C hC hconn i) (canonicalWords_mk K C hC hconn k)
  have h₂ := e.classicalWordDiskMap_killsPi2_iff
    (canonicalWords_ne_nil K C hC hconn i) (canonicalWords_ne_nil K C hC hconn k)
  exact h₁.mp (h₂.mp ((canonicalDiskInclusion_killsPi2_iff K C hC hconn hik).mpr h))

end FiniteChains.ClassicalCW.ChainWords
