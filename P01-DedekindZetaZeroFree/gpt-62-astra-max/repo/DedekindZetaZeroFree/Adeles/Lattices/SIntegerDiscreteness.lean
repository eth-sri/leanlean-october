module

public import DedekindZetaZeroFree.Adeles.Lattices.SIntegerDiagonalClosedDiscrete

@[expose] public section

noncomputable section

open scoped NumberField
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree

variable (F : Type*) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))

theorem sIntegerDiagonal_injective :
    Function.Injective (sIntegerDiagonal F S) := by
  intro m n h

  have h1 : sLocalDiagonal F S (m : F) = sLocalDiagonal F S (n : F) := by
    simpa only [sIntegerDiagonal_apply] using h
  have h2 : (sLocalDiagonal F S (m : F)).1 = (sLocalDiagonal F S (n : F)).1 := by rw [h1]
  obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have hv : algebraMap F v.Completion (m : F) = algebraMap F v.Completion (n : F) := by
    have := congrFun h2 v
    simpa using this
  refine Subtype.ext ?_
  exact (RingHom.injective_iff_ker_eq_bot (algebraMap F v.Completion)).mpr (by
    rcases (Ideal.eq_bot_or_top (RingHom.ker (algebraMap F v.Completion))) with hh | hh
    · exact hh
    · exact absurd hh (RingHom.ker_ne_top _)) hv

theorem sIntegerDiagonal_finite_preimage_of_isCompact
    (C : Set (SLocalProduct F S)) (hC : IsCompact C) :
    Set.Finite {m : sIntegerRing F S | sIntegerDiagonal F S m ∈ C} := by

  haveI hdisc :=
    sIntegerDiagonalSubgroup_discreteTopology F S
  let f : sIntegerRing F S → sIntegerDiagonalSubgroup F S :=
    fun m => ⟨sIntegerDiagonal F S m, ⟨m, rfl⟩⟩
  have hinj : Function.Injective f := by
    intro x y h
    exact (sIntegerDiagonal_injective F S) (Subtype.ext_iff.mp h)
  convert (IsCompact.finite_of_discrete ((sIntegerDiagonalSubgroup_isClosed F S).isClosedEmbedding_subtypeVal.isCompact_preimage hC)).preimage hinj.injOn using 1
  ext m
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  rfl

end DedekindZetaZeroFree

end
