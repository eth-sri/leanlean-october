module

public import GS.UnitaryLocalModel.TopologyOuter
public import GS.UnitaryLocalModel.NormalizedPositivity

@[expose] public section


/-!
# The full compact unitary local model

The actual matrix image, including all outer factors, is homeomorphic to the
product of the anchored outer unitary group and the bounded rank-one cone.
The proof uses positive-anchor uniqueness and compact equal-fibre maps.
-/
noncomputable section
namespace GS.UnitaryLocalModel

def fullCompactCone {o : Fin q} {r : ℝ}
    (p : FullCompactParameters q o d r) : OuterFactors q o × boundedConeCoordinates d r :=
  (p.1, ⟨parameterCone p.2.val, parameterCone_image d r ▸ ⟨_, p.2.2, rfl⟩⟩)

/-- A homeomorphism for the full compact matrix image in the original ambient
matrix topology, with its action on every parameter recorded explicitly. -/
theorem exists_full_compact_homeomorphism {q d : ℕ} (Q : CMat q) (o : Fin q)
    (ψ : (Fin d → ℝ) → CMat q) (U : Set (Fin d → ℝ))
    (hψc : ContinuousOn ψ U) (hψi : Set.InjOn ψ U)
    (hpos : ∀ x ∈ U, (∀ i, ∃ a : ℝ, 0 < a ∧ ψ x i o / Q i o = a) ∧ ∀ j, ∃ a : ℝ, 0 < a ∧ ψ x o j / Q o j = a) (r : ℝ)
    (hargs : ∀ p ∈ localParameterBox d r, p.1+p.2.1 ∈ U ∧ p.1-p.2.1 ∈ U) :
    ∃ h : FullCompactImage ψ o r ≃ₜ
        (OuterFactors q o × boundedConeCoordinates d r),
      ∀ p : FullCompactParameters q o d r,
        h ⟨fullCompactMiddle ψ o r p,⟨p,rfl⟩⟩ = fullCompactCone p := by
  have hψ' : Set.InjOn (fun x (ij : Fin q × Fin q) => ψ x ij.1 ij.2) U :=
    fun x hx y hy he => hψi hx hy (funext₂ fun i j => congrFun he (i,j))
  have hP (p : FullCompactParameters q o d r) : NormalizedPositiveAnchors Q o (chartBlockFamily ψ p.2.val) := by
    have := hargs _ p.2.2
    exact ⟨fun i => middleBlock_ratio_posDef _ _ _ _ p.2.2.2.2 ((hpos _ this.1).1 i) ((hpos _ this.2).1 i),
      fun j => middleBlock_ratio_posDef _ _ _ _ p.2.2.2.2 ((hpos _ this.1).2 j) ((hpos _ this.2).2 j)⟩
  obtain ⟨h,hh⟩ := exists_homeomorph_ranges_of_same_fibres
    (fullCompactMiddle ψ o r) (@fullCompactCone q d o r)
    (continuous_fullCompactMiddle ψ U o r hψc hargs)
    (continuous_fst.prodMk (((continuous_parameterCone d).comp (continuous_subtype_val.comp continuous_snd)).subtype_mk _))
    fun p p' => by
      refine (Function.LeftInverse.injective extract_flattenBlockFamily).eq_iff.trans <|
        (normalized_chart_fibres_on Q o _ U hψ' _ _ _ _ _ _ _ _ _ _ (outerLeft_unitary p.1) (outerRight_unitary p.1)
          (outerLeft_unitary p'.1) (outerRight_unitary p'.1) (outerRight_anchor p.1) (outerRight_anchor p'.1)
          (hargs _ p.2.2).1 (hargs _ p.2.2).2 (hargs _ p'.2.2).1 (hargs _ p'.2.2).2 p.2.2.2.2 p'.2.2.2.2
          (hP p) (hP p')).trans ?_
      simp only [fullCompactCone, parameterCone, Prod.mk.injEq, Subtype.mk.injEq]
      exact ⟨fun ⟨hL,hR,hc,hz⟩ => ⟨Prod.ext (funext fun i => Subtype.ext (congrFun hL i))
        (funext fun j => Subtype.ext (by simpa [outerRight,j.property] using congrFun hR j.val)),hc,hz⟩, by grind⟩
  have hs : Function.Surjective (@fullCompactCone q d o r) := fun ⟨g,w⟩ => by
    obtain ⟨p,hp,he⟩ : w.1 ∈ parameterCone '' localParameterBox d r := by rw [parameterCone_image]; exact w.2
    exact ⟨(g,⟨p,hp⟩), Prod.ext rfl (Subtype.ext he)⟩
  refine ⟨h.trans ((Homeomorph.setCongr hs.range_eq).trans (Homeomorph.Set.univ _)),?_⟩
  aesop

end GS.UnitaryLocalModel
