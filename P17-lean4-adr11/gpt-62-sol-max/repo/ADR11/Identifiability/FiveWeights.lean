module

public import ADR11.Computation.Shapes
meta import ADR11.Computation.Small
public import ADR11.Identifiability.Factors

/-!
A five-leaf unrooted species tree has at most two cherries. We label them `ab` and `de`
(only `ab` if there is just one). Use the vertex incident to `c` as the reference root.

Moving the root away from that vertex contributes a weight to each leaf on the far side of
an edge traversed by the root. The informative gene trees are one per leaf, with that leaf
as the sole leaf not in a cherry. After subtracting the reference distribution, their
probabilities read out these weights up to a common additive constant.
-/

@[expose] public section

namespace ADR11
open Finset Real _root_.ADR11.Computation

private theorem five_vals : (0 : Fin 5).val = 0 ∧ (1 : Fin 5).val = 1 ∧ (2 : Fin 5).val = 2 ∧
    (3 : Fin 5).val = 3 ∧ (4 : Fin 5).val = 4 := by decide

noncomputable def e5 (τ : TreeOn 5) (c : ℕ) : ℝ := edgeFactor τ (decC 5 c)

noncomputable def x5 (τ : TreeOn 5) : ℝ := exp (-τ.unrootedLength (decC 5 3))
noncomputable def y5 (τ : TreeOn 5) : ℝ := exp (-τ.unrootedLength (decC 5 24))

theorem x5_edges (τ : TreeOn 5) : x5 τ = e5 τ 3 * e5 τ 28 :=
  unrooted_factor τ (by decide) (by decide) (by decide)

theorem y5_edges (τ : TreeOn 5) : y5 τ = e5 τ 24 * e5 τ 7 :=
  unrooted_factor τ (by decide) (by decide) (by decide)

def groupCode (i : Fin 5) : ℕ := if i < 2 then 28 else if 2 < i then 7 else 0

noncomputable def groupFactor (τ : TreeOn 5) (i : Fin 5) : ℝ := e5 τ (groupCode i)

noncomputable def rootWeight (τ : TreeOn 5) (i : Fin 5) : ℝ :=
  3 * (1 - groupFactor τ i ^ 2) + groupFactor τ i ^ 2 * (1 - e5 τ (pendantCode i) ^ 6)

def weightSum (w : Fin 5 → ℝ) : ℝ := w 0 + w 1 + w 2 + w 3 + w 4

/-- One gene tree for each choice of leaf outside both cherries. -/
def readingTree (i : Fin 5) : ClusterFamily (Fin 5) :=
  unroot (codedHierarchy 5 [(![6, 5, 3, 3, 3] : Fin 5 → ℕ) i, (![24, 24, 24, 20, 12] : Fin 5 → ℕ) i])

/-- The probabilities at the reference root. -/
noncomputable def referenceProb (x y : ℝ) (i : Fin 5) : ℝ :=
  if i < 2 then x / 3 - 4 * x * y / 15
  else if 2 < i then y / 3 - 4 * x * y / 15
  else 1 - 2 * x / 3 - 2 * y / 3 + 2 * x * y / 5

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
set_option linter.unusedSimpArgs false in
/-- With unrooted edge factors `x,y`, moving the root from the reference vertex changes the five
readings by a common scale times the centered weights. This polynomial identity is verified
by evaluating the coalescent on the finitely many rootings. -/
theorem five_reading (τ : TreeOn 5) {cs : List ℕ} (hm : cs ∈ fiveRootings)
    (hτ : τ.clusters = codedHierarchy 5 cs) (i : Fin 5) :
    τ.unrootedDist id (readingTree i) = referenceProb (x5 τ) (y5 τ) i +
      x5 τ * y5 τ / 90 * (5 * rootWeight τ i - weightSum (rootWeight τ)) := by
  rw [dist_small_poly τ hτ]
  rw [rootings_literal.2] at hm
  verify_readings hm i [referenceProb, x5_edges, y5_edges, rootWeight, weightSum,
    groupFactor, groupCode, e5, edgeFactor, hτ, five_vals, pendantCode]

end ADR11
