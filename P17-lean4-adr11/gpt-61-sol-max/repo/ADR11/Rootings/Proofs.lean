module
public import ADR11.Computation.Engine
/-!
# Machinery for the closed forms of `ADR11.Rootings.Statements`

The gene tree distributions of the rootings of the standard unrooted trees are computed by the
verified engine of `ADR11.Computation.Engine`: for a tree shape `T` of the species tree,
`root_u5` (five taxa) and `root_q4` (four taxa) give the probabilities of all the gene trees
`T5 i` (resp. the three quartets) as polynomials `evalPoly τ.length Pᵢ`, from one certificate
`root_certsB … = true` checked by `decide +kernel`. The tactic `root_finish` then turns these
polynomials into the closed forms in the variables `exp (-τ.length C)`.

`root_certsB` is a cheaper variant of `ADR11.Computation.certB` for several gene trees at once:
families of clusters are compared through their bitmasks (`root_collect`), and polynomials by
combining like terms of their difference (`root_polyEqB`).
-/
@[expose] public section

namespace ADR11

open Finset _root_.ADR11.Computation

/-- Build a population tree from its cluster codes. -/
def buildTree : ℕ → ℕ → List ℕ → PTree
  | 0, a, _ => .node a []
  | n + 1, a, cs => .node a ((cs.filter fun b => b != a && b &&& a == b &&
      !(cs.any fun c => b != c && c != a && b &&& c == b && c &&& a == c)).map
        (fun b => buildTree n b cs))

/-! ### Comparing polynomials by combining like terms -/

/-- Adds a term to a polynomial, combining it with the term of the same monomial if there is
one. -/
def coefficients (P : Poly) : Π₀ _ : Key, ℚ :=
  (P.map fun p => DFinsupp.single p.2 p.1).sum

/-! ### Certificates for several gene trees at once -/

/-- Checks that the computation `R` succeeded with valid codes, and that for each target
`(u, P)` the probability of the family with codes `u` is the polynomial `P`. -/
def root_certsB (m : ℕ) (H : Family (Fin m)) (T : PTree)
    (targets : List (Family (Fin m) × Poly)) : Bool :=
  T.wfB m H && decide (T.code = 2 ^ m - 1) && match T.out m m id with
  | some M => targets.all fun t => decide (coefficients (collect M t.1) = coefficients t.2)
  | none => false

/-- The probability of an unrooted gene tree, from a certificate for several gene trees. -/
theorem root_unrootedDist_eq_evalPoly {n : ℕ} (σ : SpeciesTree (Fin n))
    {T : PTree} {targets : List (Family (Fin n) × Poly)}
    (hc : root_certsB n σ.clusters T targets = true)
    {t : Family (Fin n) × Poly} (hmem : t ∈ targets) : σ.unrootedDist id t.1 = evalPoly σ.length t.2 := by
  simp only [root_certsB, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨hwf, htop⟩, hc⟩ := hc
  cases hM : T.out n n id with
  | none => simp [hM] at hc
  | some M =>
    simp only [hM, List.all_eq_true] at hc
    have he := congrArg (DFinsupp.sumAddHom fun k =>
      (AddMonoidHom.mulRight (monoVal σ.length k)).comp (Rat.castHom ℝ).toAddMonoidHom)
      (of_decide_eq_true (hc t hmem))
    have ht : decC n T.code = univ := by rw [htop]; ext i; simp [decC]
    change (∑ G, if unroot G = t.1 then forestDist σ.clusters σ.length id univ G else 0) = _
    rw [← ht]
    simp_rw [T.out_spec σ.clusters σ.length hwf M hM]
    trans (M.map fun τ => if unroot τ.forest = t.1 then τ.val σ.length else 0).sum
    · simpa only [mul_ite, mul_one, mul_zero] using
        sum_collapse M (fun τ => τ.forest) (fun τ => τ.val σ.length)
          (fun G => if unroot G = t.1 then 1 else 0)
    · simpa [coefficients, evalPoly, map_multiset_sum, Multiset.map_bind,
        Multiset.sum_bind, Multiset.map_map, Function.comp_def, collect, CTerm.val,
        apply_ite] using he

/-! ### Four taxa -/

theorem root_decC4_3 : decC 4 3 = {0, 1} := by decide +kernel
theorem root_decC4_12 : decC 4 12 = {2, 3} := by decide +kernel

end ADR11
