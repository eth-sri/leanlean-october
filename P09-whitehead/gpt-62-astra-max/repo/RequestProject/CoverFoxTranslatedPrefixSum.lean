module

public import RequestProject.CoverFoxPrefixSum

@[expose] public section

namespace FiniteChains
variable {α : Type*} [DecidableEq α]
  (N : Subgroup (FreeGroup α)) [N.Normal]

/-- A translated projected Fox coefficient is the translated signed prefix-incidence sum. -/
theorem coverFox_translated_prefix_sum (g : FreeGroup α ⧸ N)
    (i : α) (l : List _) :
    MonoidAlgebra.single g 1 * proj N (fox i (FreeGroup.mk l)) =
      ∑ k : Fin l.length,
        if i = l[k.val].1 then
          MonoidAlgebra.single
            (g * ((QuotientGroup.mk (FreeGroup.mk (l.take k.val))) *
              (if l[k.val].2 then 1 else
                (QuotientGroup.mk (FreeGroup.of l[k.val].1))⁻¹)))
            (if l[k.val].2 then 1 else -1)
        else 0 := by
  classical
  rw [coverFox_mk_prefix_sum, Finset.mul_sum]
  simp

end FiniteChains
