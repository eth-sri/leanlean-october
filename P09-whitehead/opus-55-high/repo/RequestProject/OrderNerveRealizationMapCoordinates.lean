import RequestProject.OrderNerveRealizationSubcomplex
import RequestProject.Tac


bwd

namespace FiniteChains.Comb
open CategoryTheory Simplicial
open scoped Classical

/-- Affine interpolation is natural under every actual realized monotone map. -/
theorem orderNerveAffineRealization_natural {P Q} [PartialOrder P] [PartialOrder Q]
    f hf (v : Q → ℝ) (x : orderNerveRealization P) :
    orderNerveAffineRealization v (orderNerveRealizationMap f hf x) =
      orderNerveAffineRealization (v ∘ f) x := by
  obtain ⟨n, s, z, hx⟩ := orderNerveRealizationSimplex_jointly_surjective P x
  subst x
  have hn := congrArg (· z) (orderNerveRealizationSimplex_natural f hf s)
  have hq := congrArg (· z)
    (orderNerveAffineRealization_simplex v ((nerveMap hf.functor).app _ s))
  have hp := congrArg (· z) (orderNerveAffineRealization_simplex (v ∘ f) s)
  aesop

/-- An injective monotone map preserves each actual barycentric coordinate at its image vertex. -/
theorem orderNerveRealizationCoordinates_map_injective {P Q}
    [PartialOrder P] [PartialOrder Q] f hf
    (hi : Function.Injective f) x p :
    orderNerveRealizationCoordinates Q (orderNerveRealizationMap f hf x) (f p) =
      orderNerveRealizationCoordinates P x p := by
  change orderNerveAffineRealization (if · = f p then 1 else 0)
    (orderNerveRealizationMap f hf x) = _
  rw [orderNerveAffineRealization_natural]
  have hv : ((if · = f p then (1 : ℝ) else 0) ∘ f) =
      (if · = p then 1 else 0) := by
    grind
  tauto

/-- Injective monotone maps induce injective maps of the actual geometric realizations. -/
theorem orderNerveRealizationMap_injective {P Q} [PartialOrder P] [PartialOrder Q]
    (f : P → Q) hf (hi : Function.Injective f) :
    Function.Injective (orderNerveRealizationMap f hf) := by
  intro x y h
  apply orderNerveRealizationCoordinates_injective P
  funext p
  have hc := congrArg (orderNerveRealizationCoordinates Q · (f p)) h
  grind [orderNerveRealizationCoordinates_map_injective f hf hi]

/-- Vertices outside the image of a monotone map have zero coordinate in its realization. -/
theorem orderNerveRealizationCoordinates_map_outside {P Q}
    [PartialOrder P] [PartialOrder Q] f hf
    (x : orderNerveRealization P) q (hq : q ∉ Set.range f) :
    orderNerveRealizationCoordinates Q (orderNerveRealizationMap f hf x) q = 0 := by
  change orderNerveAffineRealization (if · = q then 1 else 0)
    (orderNerveRealizationMap f hf x) = 0
  rw [orderNerveAffineRealization_natural]
  obtain ⟨n, s, z, hx⟩ := orderNerveRealizationSimplex_jointly_surjective P x
  subst x
  have he := congrArg (· z)
    (orderNerveAffineRealization_simplex ((if · = q then (1 : ℝ) else 0) ∘ f) s)
  change orderNerveAffineRealization _ (orderNerveRealizationSimplex P s z) =
    orderNerveAffineSimplex _ s z at he
  rw [he]
  have hn : ∀ p, f p ≠ q := by
    simp_all
  simp [orderNerveAffineSimplex, hn]

/-- The image of a realized monotone map lies in the genuine CW subcomplex
supported on its image vertices. -/
theorem orderNerveRealizationMap_mem_subcomplex {P Q}
    [PartialOrder P] [PartialOrder Q] f hf
    (x : orderNerveRealization P) :
    orderNerveRealizationMap f hf x ∈
      (orderNerveRealizationSubcomplex Q (Set.range f) : Set (orderNerveRealization Q)) := by
  intro q hq
  exact orderNerveRealizationCoordinates_map_outside f hf x q hq

/-- Lift a simplex whose vertices lie in a subset to the induced subposet. -/
def orderNerveSimplexSubtype {P : Type} [PartialOrder P] (A : Set P)
    {n} (s : (nerve P).obj (Opposite.op n))
    (hs : ∀ i, s.obj i ∈ A) : (nerve A).obj (Opposite.op n) where
  obj i := ⟨s.obj i, hs i⟩
  map h := homOfLE (leOfHom (s.map h))

/-- Realizing the induced subposet has exactly the supported CW subcomplex as its image. -/
theorem orderNerveRealizationSubtype_range {P} [PartialOrder P] (A : Set P) :
    Set.range (orderNerveRealizationMap (Subtype.val : A → P)
      (fun _ _ h => h)) =
      (orderNerveRealizationSubcomplex P A) := by
  apply Set.Subset.antisymm
  · rintro x ⟨y, rfl⟩
    have h := orderNerveRealizationMap_mem_subcomplex (Subtype.val : A → P)
      (by tauto) y
    simp_all
  · intro x hx
    change x ∈ orderNerveRealizationSupported P A at hx
    rw [← orderNerveRealizationSupported_union P A] at hx
    cases' Set.mem_iUnion.mp hx with n hx
    cases' Set.mem_iUnion.mp hx with s hx
    rw [orderNerveCharacteristicMap_openCell] at hx
    obtain ⟨z, _, hz⟩ := hx
    let t := orderNerveSimplexSubtype A s.val.val s.property
    have ht : (nerveMap (show Monotone Subtype.val from
        by tauto).functor).app _ t = s.val.val := by
      rfl
    have he := congrArg (· z)
      (orderNerveRealizationSimplex_natural (Subtype.val : A → P)
        (by grind) t)
    change orderNerveRealizationMap _ _ (orderNerveRealizationSimplex A t z) =
      orderNerveRealizationSimplex P ((nerveMap _).app _ t) z at he
    grind
