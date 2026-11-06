import RequestProject.PresCoverRelatorChains


namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P]

theorem strictBelowCongr_val {a b : P} (h : a = b) p :
    (strictBelowCongr h p).val = p.val := by
  cases h
  rfl
end FiniteChains.Comb

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool))
  (f : P → PresPos w) (hf : IsPosetCover f) (v : P) (j : J) (hv : f v = apexOf w j)

/-- The actual inverse circle coordinates project to the actual attaching-circle vertex. -/
theorem presCoverConeCircleOrderIso_symm_projection x :
    f ((presCoverConeCircleOrderIso w f hf v j hv).symm x).val = iCirc w x.val := by
  have hx := congrArg (fun y => (relatorCircleOrderIso w j y).val)
    ((presCoverConeCircleOrderIso w f hf v j hv).apply_symm_apply x)
  change (relatorCircleOrderIso w j
    ((relatorCircleOrderIso w j).symm
      (strictBelowCongr hv (hf.lowerIntervalOrderIso v
        ((presCoverConeCircleOrderIso w f hf v j hv).symm x))))).val =
    (relatorCircleOrderIso w j x).val at hx
  rwa [OrderIso.apply_symm_apply, strictBelowCongr_val] at hx

/-- The actual first incidence triangle of a nonempty presentation relator. -/
noncomputable def presRelatorFirstTriangle (hpos : ∀ j, 0 < (w j).length) (j : J) :=
  strictConeTriangle _
    ((strictOrderEdgeEquiv (relatorCircleOrderIso w j))
      (relatorCircleEdge0 w j ⟨0, hpos j⟩))

/-- The coordinate triangle lies over the genuine first relator incidence triangle. -/
theorem presCoverRelatorTriangle_projection hpos
    p :
    (strictOrderCxMap f hf.strictMono).onF (presCoverRelatorTriangle w f hf hpos p) =
      presRelatorFirstTriangle w hpos p.1.2 := by
  apply Subtype.ext
  apply Prod.ext
  · exact presCoverConeCircleOrderIso_symm_projection w f hf p.1.1 p.1.2 p.2
      _
  · apply Prod.ext
    · exact presCoverConeCircleOrderIso_symm_projection w f hf p.1.1 p.1.2 p.2
        _
    · exact p.2
