module

public import RequestProject.CellularHomotopyChain

@[expose] public section

namespace FiniteChains.Comb
universe u
variable (X : Complex2.{u})

/-- Edge chains modulo actual finite face boundaries. -/
abbrev EdgeBoundaryQuotient := (X.E →₀ ℤ) ⧸ LinearMap.range (bdry2 X)

variable (a : X.V)

/-- The chain of a based loop, in the actual cellular boundary quotient. -/
noncomputable def loopBoundaryClass :
    Pi1 X a →* Multiplicative (EdgeBoundaryQuotient X) where
  toFun := Quotient.lift (fun p : Loop X a =>
    Multiplicative.ofAdd (Submodule.Quotient.mk (pathChain p.val))) (by
      intro p q h
      apply (Submodule.Quotient.eq _).mpr; exact h.exists_boundary)
  map_one' := rfl
  map_mul' g h := by
    induction g using Quotient.inductionOn with
    | h p =>
      induction h using Quotient.inductionOn with
      | h q =>
        change Multiplicative.ofAdd _ = _
        simp [pathChain_append, Submodule.Quotient.mk_add]

/-- A commutator loop has a genuine finite integral face filling. -/
theorem loop_bounds_of_mem_commutator (p : Loop X a)
    (hp : Pi1.mk p ∈ commutator _) :
    ∃ d : X.F →₀ ℤ, bdry2 X d = pathChain p.val := by
  have he :=
    congrArg Multiplicative.toAdd (Abelianization.commutator_subset_ker (loopBoundaryClass X a) hp); exact (Submodule.Quotient.mk_eq_zero _).mp he

variable (hX : IsConnected X)
include hX

/-- Actual loop fillings give actual finite one-cycle fillings in a connected complex. -/
theorem oneCycle_filling_of_loop_fillings
    (hloop : ∀ p : Loop X a, ∃ d : X.F →₀ ℤ, bdry2 X d = pathChain p.val)
    (c : X.E →₀ ℤ) (hc : bdry1 X c = 0) :
    ∃ d : X.F →₀ ℤ, bdry2 X d = c := by
  classical
  choose p hp using hX a
  have hface (e : X.E) : ∃ y : X.F →₀ ℤ,
      bdry2 X y = Finsupp.single e 1 + pathChain (p (X.src e)) -
        pathChain (p (X.tgt e)) := by
    let l := p (X.src e) ++ [(e, true)] ++ revPath (p (X.tgt e))
    have hl :=
      ((hp _).append (show IsPath X.src X.tgt [(e, true)] (X.src e) (X.tgt e)
        from ⟨rfl, rfl⟩)).append (isPath_revPath (hp _))
    obtain ⟨y, hy⟩ := hloop ⟨l, hl⟩
    refine ⟨y, ?_⟩
    simp_all [l, pathChain_append, pathChain_cons, pathChain_revPath, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  choose f hf using hface
  let s :=
    Finsupp.linearCombination ℤ (fun v => pathChain (p v))
  let t := Finsupp.linearCombination ℤ f
  have hs (v : X.V) : s (Finsupp.single v 1) = pathChain (p v) := by simp [s]
  have ht (z : X.E →₀ ℤ) : bdry2 X (t z) = z - s (bdry1 X z) := by
    induction z using Finsupp.induction_linear with
    | zero => simp
    | add z w hz hw => rw [map_add, map_add, hz, hw, map_add, map_add]; abel
    | single e n =>
      rw [Finsupp.linearCombination_single, map_smul, hf, bdry1_single,
        map_smul, map_sub, hs, hs, smul_sub, smul_add, smul_sub]; simp only [Finsupp.smul_single, smul_eq_mul, mul_one]; abel
  exact ⟨t c, by simp_all⟩

/-- Perfect fundamental group kills every actual finite one-cycle. -/
theorem oneCycle_filling_of_perfect_pi1
    (hperfect : commutator (Pi1 X a) = ⊤)
    (c : X.E →₀ ℤ) (hc : bdry1 X c = 0) :
    ∃ d : X.F →₀ ℤ, bdry2 X d = c := by
  apply oneCycle_filling_of_loop_fillings X a hX _ c hc
  simp_all [loop_bounds_of_mem_commutator]

end FiniteChains.Comb
