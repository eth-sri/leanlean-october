module

public import RequestProject.OrderNerveRealizationSubcomplex

@[expose] public section

namespace FiniteChains.Comb
open CategoryTheory Simplicial
open scoped Classical

section

variable {P Q : Type} [PartialOrder P] [PartialOrder Q] (f : P → Q) (hf : Monotone f)
include P Q

/-- Affine interpolation is natural under every actual realized monotone map. -/
theorem orderNerveAffineRealization_natural (v : Q → ℝ) (x : orderNerveRealization P) :
    orderNerveAffineRealization v (orderNerveRealizationMap f hf x) =
      orderNerveAffineRealization (v ∘ f) x := by
  obtain ⟨n, s, z, hx⟩ := orderNerveRealizationSimplex_jointly_surjective P x
  subst x
  have hn := congrArg (fun k => k z) (orderNerveRealizationSimplex_natural f hf s)
  change orderNerveRealizationMap f hf (orderNerveRealizationSimplex P s z) =
    orderNerveRealizationSimplex Q ((nerveMap hf.functor).app _ s) z at hn
  rw [hn]
  have hq := congrArg (fun k => k z)
    (orderNerveAffineRealization_simplex v ((nerveMap hf.functor).app _ s))
  have hp := congrArg (fun k => k z) (orderNerveAffineRealization_simplex (v ∘ f) s)
  aesop

section

variable (hi : Function.Injective f)
include hi

/-- An injective monotone map preserves each actual barycentric coordinate at its image vertex. -/
theorem orderNerveRealizationCoordinates_map_injective (x : orderNerveRealization P) (p : P) :
    orderNerveRealizationCoordinates Q (orderNerveRealizationMap f hf x) (f p) =
      orderNerveRealizationCoordinates P x p := by
  change orderNerveAffineRealization (fun q => if q = f p then 1 else 0)
    (orderNerveRealizationMap f hf x) = _
  rw [orderNerveAffineRealization_natural]
  have hv : ((fun q : Q => if q = f p then (1 : ℝ) else 0) ∘ f) =
      (fun q : P => if q = p then 1 else 0) := by
    funext q
    grind
  solve_by_elim

/-- Injective monotone maps induce injective maps of the actual geometric realizations. -/
theorem orderNerveRealizationMap_injective :
    Function.Injective (orderNerveRealizationMap f hf) := by
  intro x y h
  apply orderNerveRealizationCoordinates_injective P
  funext p
  have hc := congrArg (fun z => orderNerveRealizationCoordinates Q z (f p)) h
  grind [orderNerveRealizationCoordinates_map_injective]

end

variable (x : orderNerveRealization P)

/-- Vertices outside the image of a monotone map have zero coordinate in its realization. -/
theorem orderNerveRealizationCoordinates_map_outside (q : Q) (hq : q ∉ Set.range f) :
    orderNerveRealizationCoordinates Q (orderNerveRealizationMap f hf x) q = 0 := by
  change orderNerveAffineRealization (fun r => if r = q then 1 else 0)
    (orderNerveRealizationMap f hf x) = 0
  rw [orderNerveAffineRealization_natural]
  obtain ⟨n, s, z, hx⟩ := orderNerveRealizationSimplex_jointly_surjective P x
  subst x
  have he := congrArg (fun k => k z)
    (orderNerveAffineRealization_simplex ((fun r : Q => if r = q then (1 : ℝ) else 0) ∘ f) s)
  change orderNerveAffineRealization _ (orderNerveRealizationSimplex P s z) =
    orderNerveAffineSimplex _ s z at he
  rw [he]
  have hn : ∀ p : P, f p ≠ q := by
    intro p hp
    simp_all
  simp [orderNerveAffineSimplex, hn]

/-- The image of a realized monotone map lies in the genuine CW subcomplex
supported on its image vertices. -/
theorem orderNerveRealizationMap_mem_subcomplex :
    orderNerveRealizationMap f hf x ∈
      (orderNerveRealizationSubcomplex Q (Set.range f) : Set (orderNerveRealization Q)) := by
  apply orderNerveRealizationCoordinates_map_outside

end

variable {P : Type} [PartialOrder P] (A : Set P)

/-- Lift a simplex whose vertices lie in a subset to the induced subposet. -/
def orderNerveSimplexSubtype
    {n : SimplexCategory} (s : (nerve P).obj (Opposite.op n))
    (hs : ∀ i, s.obj i ∈ A) : (nerve A).obj (Opposite.op n) where
  obj i := ⟨s.obj i, hs i⟩
  map h := homOfLE (leOfHom (s.map h))

/-- Realizing the induced subposet has exactly the supported CW subcomplex as its image. -/
theorem orderNerveRealizationSubtype_range :
    Set.range (orderNerveRealizationMap (Subtype.val : A → P)
      (fun _ _ h => h)) =
      (orderNerveRealizationSubcomplex P A : Set (orderNerveRealization P)) := by
  apply Set.Subset.antisymm
  · rintro x ⟨y, rfl⟩
    have h := orderNerveRealizationMap_mem_subcomplex (Subtype.val : A → P)
      (fun _ _ h => h) y
    simp_all
  · intro x hx
    change x ∈ orderNerveRealizationSupported P A at hx
    rw [← orderNerveRealizationSupported_union P A] at hx
    obtain ⟨n, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨s, hx⟩ := Set.mem_iUnion.mp hx
    rw [orderNerveCharacteristicMap_openCell] at hx
    obtain ⟨z, _, hz⟩ := hx
    let t := orderNerveSimplexSubtype A s.val.val s.property
    refine ⟨orderNerveRealizationSimplex A t z, ?_⟩
    have ht : (nerveMap (show Monotone (Subtype.val : A → P) from
        fun _ _ h => h).functor).app _ t = s.val.val := CategoryTheory.Functor.ext (fun _ => rfl)
    have he := congrArg (fun k => k z)
      (orderNerveRealizationSimplex_natural (Subtype.val : A → P)
        (fun _ _ h => h) t)
    exact he.trans hz

end FiniteChains.Comb
