module

public import RequestProject.CoverAcyclic
public import RequestProject.MagnusKernel
public import RequestProject.CoverHomologyOne
public import RequestProject.UniversalCoefficients
public import RequestProject.PresentationDictionary

@[expose] public section

/-!
# Cycles lift modulo `m`: a theorem, not a citation

Formula (2.3) modulo `m` was derived in `RequestProject/ChainFormulaMod.lean` from the
property `CycleLiftsMod`, quoted in the paper from Hatcher: in the chain complex of the
universal cover of a stage, a chain whose boundary is divisible by `m` is congruent modulo
`m` to a genuine cycle.

For the two-complex of a finite presentation this is a consequence of what is already
proved here.  Write `C₂ --∂₂--> C₁ --∂₁--> C₀` for the chain complex of the universal cover
(the cover attached to the relator subgroup `R`, with deck group `G = π₁(K)`).  Then
`H₁ = 0` (`FiniteChains.exists_bdry2_preimage`, which for `Ñ = R` needs no hypothesis).
If `∂₂u = m·w` then `m·∂₁w = ∂₁∂₂u = 0`, so `∂₁w = 0` because the group ring is torsion
free, hence `w = ∂₂z` and `u - m·z` is a cycle congruent to `u` modulo `m`.

`FiniteChains.exists_cycle_of_bdry2_nsmul` is this statement in the coordinates used by
`ChainInput`.
-/

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains

open MonoidAlgebra

variable {β : Type*}
variable {K : Type*} (σ : K → FreeGroup β)

/-- The relators lie in the relator subgroup. -/
theorem rel_mem_relSub' (j : K) : σ j ∈ relSub σ :=
  Subgroup.subset_normalClosure (Set.mem_range_self j)

/-- A group ring over `ℤ` has no additive torsion. -/
theorem nsmul_eq_zero_iff_of_ne {G : Type*} (m : ℕ) (hm : m ≠ 0) (x : MonoidAlgebra ℤ G) :
    m • x = 0 ↔ x = 0 := by
  constructor
  · intro h
    apply MonoidAlgebra.coeff_injective
    refine Finsupp.ext fun g => ?_
    have hg : m • x.coeff g = 0 := by
      have := congrArg (fun y : MonoidAlgebra ℤ G => y.coeff g) h
      simpa only [MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_zero, Finsupp.zero_apply] using this
    have : (m : ℤ) * x.coeff g = 0 := by
      rw [← nsmul_eq_mul]
      exact hg
    rcases mul_eq_zero.1 this with h' | h'
    · exact absurd (Nat.cast_eq_zero.1 h') hm
    · simpa using h'
  · rintro rfl
    simp
