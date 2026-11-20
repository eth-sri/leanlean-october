module

public import RequestProject.CellularHomotopyChain
public import RequestProject.FinsuppBasis

@[expose] public section

namespace FiniteChains.Comb
universe u
variable (X : Complex2.{u})

/-- Edge chains modulo actual finite face boundaries. -/
abbrev EdgeBoundaryQuotient := (X.E →₀ ℤ) ⧸ LinearMap.range (bdry2 X)

/-- The chain of a based loop, in the actual cellular boundary quotient. -/
noncomputable def loopBoundaryClass (a : X.V) :
    Pi1 X a →* Multiplicative (EdgeBoundaryQuotient X) where
  toFun := Quotient.lift (fun p : Loop X a =>
    Multiplicative.ofAdd (Submodule.Quotient.mk (pathChain p.val))) (by
      intro p q h
      apply congrArg Multiplicative.ofAdd
      apply (Submodule.Quotient.eq _).mpr
      exact h.exists_boundary)
  map_one' := by
    change Multiplicative.ofAdd (Submodule.Quotient.mk (pathChain [])) = 1
    simp
  map_mul' g h := by
    induction g using Quotient.inductionOn with
    | h p =>
      induction h using Quotient.inductionOn with
      | h q =>
        change Multiplicative.ofAdd (Submodule.Quotient.mk (pathChain (p.val ++ q.val))) = _
        rw [pathChain_append, Submodule.Quotient.mk_add]
        rfl

/-- A commutator loop has a genuine finite integral face filling. -/
theorem loop_bounds_of_mem_commutator (a : X.V) (p : Loop X a)
    (hp : Pi1.mk p ∈ commutator (Pi1 X a)) :
    ∃ d : X.F →₀ ℤ, bdry2 X d = pathChain p.val := by
  have hz := Abelianization.commutator_subset_ker (loopBoundaryClass X a) hp
  change Multiplicative.ofAdd (Submodule.Quotient.mk (pathChain p.val)) = 1 at hz
  have he  :=
    congrArg Multiplicative.toAdd hz
  exact (Submodule.Quotient.mk_eq_zero _).mp he

/-- Use one root and a path to each vertex in each component. The filled
loops along the edges give a chain contraction on one-cycles. -/
theorem oneCycle_filling_of_root_paths (r : X.V → X.V) (p : X.V → List (X.E × Bool))
    (hp : ∀ v, IsPath X.src X.tgt (p v) (r v) v)
    (hr : ∀ e, r (X.src e) = r (X.tgt e))
    (hloop : ∀ v (l : Loop X (r v)), ∃ d, bdry2 X d = pathChain l.val)
    (c : X.E →₀ ℤ) (hc : bdry1 X c = 0) :
    ∃ d, bdry2 X d = c := by
  have hface (e : X.E) : ∃ y, bdry2 X y =
      Finsupp.single e 1 + pathChain (p (X.src e)) - pathChain (p (X.tgt e)) := by
    have he : IsPath X.src X.tgt [(e, true)] (X.src e) (X.tgt e) := ⟨rfl, rfl⟩
    obtain ⟨y, hy⟩ := hloop (X.src e) ⟨_, ((hp _).append he).append ((hr e).symm ▸ isPath_revPath (hp _))⟩
    refine ⟨y, ?_⟩
    simpa [pathChain_append, pathChain_cons, pathChain_revPath, sub_eq_add_neg, add_left_comm, add_assoc, add_comm] using hy
  choose f hf using hface
  let s := Finsupp.linearCombination ℤ (fun v => pathChain (p v))
  let t := Finsupp.linearCombination ℤ f
  have ht (z : X.E →₀ ℤ) : bdry2 X (t z) = z - s (bdry1 X z) := by
    finsupp_basis z
    intro e
    simp [t, s, hf, bdry1_single]
    abel
  exact ⟨t c, by rw [ht, hc, map_zero, sub_zero]⟩

/-- Actual loop fillings give actual finite one-cycle fillings in a connected complex. -/
theorem oneCycle_filling_of_loop_fillings (a : X.V) (hX : IsConnected X)
    (hloop : ∀ p : Loop X a, ∃ d : X.F →₀ ℤ, bdry2 X d = pathChain p.val)
    (c : X.E →₀ ℤ) (hc : bdry1 X c = 0) :
    ∃ d : X.F →₀ ℤ, bdry2 X d = c := by
  choose p hp using hX a
  exact oneCycle_filling_of_root_paths X (fun _ => a) p hp (fun _ => rfl) (fun _ => hloop) c hc

/-- Perfect fundamental group kills every actual finite one-cycle. -/
theorem oneCycle_filling_of_perfect_pi1 (a : X.V) (hX : IsConnected X)
    (hperfect : commutator (Pi1 X a) = ⊤)
    (c : X.E →₀ ℤ) (hc : bdry1 X c = 0) :
    ∃ d : X.F →₀ ℤ, bdry2 X d = c := by
  apply oneCycle_filling_of_loop_fillings X a hX _ c hc
  intro p
  exact loop_bounds_of_mem_commutator X a p (by rw [hperfect]; trivial)

end FiniteChains.Comb
