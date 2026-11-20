module
public import KKP.Bridge
public import BN.Definition
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Fin.Tuple.Reflection
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.CasesM
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
public section

/-!
Only five coordinates are needed: distinguish the bridge endpoints, the rest of
part zero, the other two parts together, and the rest of the clique. We lift two
roots of the quotient polynomial to actual eigenvalues. Isolating the roots in
disjoint intervals gives a slightly stronger, uniform excess bound.
-/
namespace KKP
open Matrix Module SimpleGraph
-- Expand sums over a vertex by side, then by part or clique index.
attribute [local simp] bridgeGraph bridgeAdj
  Fintype.sum_sum_type Fintype.sum_prod_type Fin.sum_univ_succ

local notation "Λ" s:arg => BN.lambda1 (bridgeGraph s)^2 + BN.lambda2 (bridgeGraph s)^2

/-- After clearing the positive denominators, the endpoint sign checks are just
polynomials with nonnegative coefficients in `k = s - 3`. -/
local macro "cert" : tactic => `(tactic| (
  apply sub_nonneg.mp
  try dsimp +zetaDelta
  ring_nf
  field_simp <;> ring_nf <;> positivity))

/-- A lower bound giving an excess of at least `1/6` over four thirds of the edge count. -/
theorem mass_bound (k : ℕ) : 4 * (k + 3 : ℝ)^2 + 19/2 ≤ Λ (k + 3) := by
  let r : ℝ := k + 3
  let E := BN.adjacencyEigenvalues₀ (bridgeGraph (k + 3))
  -- Normalize the ordinary vertices of part zero to `u`. The two tripartite
  -- equations then give an additional `t` at the bridge, and `x*t` across it.
  let u := 2 * r
  let vec (x : ℝ) : BridgeVertex (k + 3) → ℝ :=
    let t := (x - u) * (x + r)
    fun | L i j => ![if j.val = 0 then t + u else u, x, x] i
        | R 0 => x * t
        | R _ => ((x^2 - 1) * t - u) / 3
  -- The only remaining equation is at an ordinary clique vertex.
  let P (x : ℝ) := (x - 2) * vec x (R 1) - vec x (R 0)
  have root {I} : 0 ∈ P '' I → ∃ i, E i ∈ I := by
    rintro ⟨x, hi, h⟩
    suffices ∃ i, E i = x by grind
    apply LinearMap.IsSymmetric.exists_eigenvalues_eq
    refine End.hasEigenvalue_of_hasEigenvector (x := WithLp.toLp 2 (vec x))
      ⟨End.mem_eigenspace_iff.mpr ?_, ?_⟩
    · ext (⟨i, j⟩ | i) <;> fin_cases i
      all_goals
        simp_all +zetaDelta [mulVec, dotProduct, adjMatrix]
        grind
    · exact fun hz => (by positivity : u ≠ 0) congr($hz (L 0 1))
  -- Isolate two roots. Their intervals are disjoint since `4 < 6 ≤ a`.
  let a := u + 1 / (8 * r^2)
  let b := 3 + (k + 2) / (12 * r)
  obtain ⟨j, hy, _⟩ := root <|
    intermediate_value_Icc (show a ≤ u + 1 by cert) (by fun_prop) (by constructor <;> cert)
  obtain ⟨i, hx, hx4⟩ := root <|
    intermediate_value_Icc' (show b ≤ 4 by cert) (by fun_prop) (by constructor <;> cert)
  have ant : Antitone E := IsHermitian.eigenvalues₀_antitone _
  have : j < i := ant.reflect_lt (by linarith! [show 6 ≤ a by cert])
  calc
    _ ≤ a^2 + b^2 := by cert
    _ ≤ _ := by gcongr <;> apply_rules [hy.trans, hx.trans, ant] <;> grind

local notation "m" s:arg => Finset.card (SimpleGraph.edgeFinset (bridgeGraph s))
local notation "T" s:arg => (4 / 3 : ℝ) * m s
local notation "δ" z:arg => (656 * z^2 - 1366 * z + 62) / (3 * (37 * z - 1)^2)

/-- Color-criticality, connectivity, forbidden-freeness and the certified spectral excess. -/
theorem connected_counterexample_family (s : ℕ) (hs : 3 ≤ s) :
    forbiddenGraph.chromaticNumber = 4 ∧
    (∃ i j, forbiddenGraph.Adj i j ∧
      (forbiddenGraph.deleteEdges {s(i, j)}).chromaticNumber < forbiddenGraph.chromaticNumber) ∧
    (bridgeGraph s).Connected ∧ forbiddenGraph.Free (bridgeGraph s) ∧ m s = 3 * s^2 + 7 ∧
    δ (s : ℝ) ≤ Λ s - T s ∧ T s < Λ s := by
  -- Count each edge twice, once at each endpoint.
  have e : m s = 3 * s^2 + 7 := by
    cases s
    · omega
    apply Nat.eq_of_mul_eq_mul_left zero_lt_two
    simp only [← sum_degrees_eq_twice_card_edges, degree, neighborFinset_eq_filter, Finset.card_filter]
    simp
    ring
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hs
  refine ⟨forbidden_chromaticNumber, ⟨0, 1, by decide, ?_⟩,
    ?_, ?_, e, ?_⟩
  · apply (Colorable.chromaticNumber_le (n := 3) ⟨.mk ![0, 0, 1, 2, 2] (by decide)⟩).trans_lt
    norm_num [forbidden_chromaticNumber]
  -- Reach every vertex from the left bridge endpoint.
  · rw [connected_iff_exists_forall_reachable]
    use L 0 0
    rintro (⟨i, j⟩ | b)
    case' inl =>
      fin_cases i
      trans L 1 0
    case' inr =>
      trans R 0
      on_goal 2 => fin_cases b
    all_goals first | rfl | apply Adj.reachable; simp
  -- Expand a putative copy into five vertices. No assignment to left and right
  -- respects both adjacency and injectivity.
  · rintro ⟨⟨g, h⟩, (hi : Function.Injective g)⟩
    revert g
    rw [← FinVec.forall_iff]
    iterate 5 intro
    simp [Fin.forall_fin_succ, Function.Injective, forbiddenGraph]
    casesm* BridgeVertex _ <;> simp <;> omega
  push_cast [e]
  have : δ (k + 3 : ℝ) ≤ 1/6 := by cert
  grind [mass_bound k]

/-- The edge counts of the counterexamples are unbounded. -/
theorem unbounded_connected_counterexamples (B : ℕ) : ∃ s, 3 ≤ s ∧ B ≤ m s ∧
    (bridgeGraph s).Connected ∧ forbiddenGraph.Free (bridgeGraph s) ∧ T s < Λ s := by
  use B + 3
  have := connected_counterexample_family (B + 3) (by omega)
  grind
end KKP
