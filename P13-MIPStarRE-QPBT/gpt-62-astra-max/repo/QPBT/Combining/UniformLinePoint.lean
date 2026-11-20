module

public import QPBT.Combining.Lines.SubLineTransport

/-!
# A uniform point of the extended space from the sub-line law

The first scalar estimate in the combining argument samples an extended line
from the directly indexed sub-line witness and then a uniform affine parameter.
This module records that the resulting extended point is uniform and hence
that its two source coordinate blocks are independent uniform points.
This is an auxiliary law. Transport to the source's seed-indexed extended
distribution remains open, as recorded in
`docs/paper-gaps/qpbt_subline-claims-line-marginal.tex`.

## References

These statements support `lem:claim-17-1` in
`blueprint/src/chapter/ch15_qpbt_combining.tex`.  The paper uses this sampling
fact at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1159-1166`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

/-- If every slice of a map of a pair carries the second uniform law to one
fixed law, then the map carries the uniform law of the pair to that law. -/
theorem uniformDistribution_map_uncurry {α β γ : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β] [DecidableEq γ]
    (g : α × β → γ) (ν : Distribution γ)
    (hg : ∀ a, (uniformDistribution β).map (fun b => g (a, b)) = ν) :
    (uniformDistribution (α × β)).map g = ν := by
  rw [← bind_uniformDistribution_map (fun a b => g (a, b)),
    (funext hg)]
  exact Distribution.bind_const _ (uniformDistribution_isProbability α) ν

section

variable (D : DirectLdParams)

section

variable (V : Fin D.m × (DirectPoint D) → (DirectPoint D))

/-- Reading a point at a uniform affine parameter on the canonical line of a
uniform direct sample gives a uniform point of the direct coordinate space. -/
theorem uniformDistribution_map_directLine_add_smul :
    (uniformDistribution (DirectLdSpace D × DirectScalarQ D)).map
        (fun p => lineRepMap (V (p.1.index, p.1.direction)) p.1.point +
          p.2 • V (p.1.index, p.1.direction)) =
      uniformDistribution (DirectPoint D) := by
  classical
  let e : DirectLdSpace D × DirectScalarQ D ≃
      _ ×
        _ :=
    { toFun := fun p => ((p.1.index, p.1.direction), (p.1.point, p.2))
      invFun := fun w => (⟨w.2.1, w.1.1, w.1.2⟩, w.2.2)
      left_inv := by rintro ⟨⟨pt, i, dir⟩, t⟩; rfl
      right_inv := by rintro ⟨⟨i, dir⟩, pt, t⟩; rfl }
  have hmap :
      (uniformDistribution (DirectLdSpace D × DirectScalarQ D)).map
          (fun p => lineRepMap (V (p.1.index, p.1.direction)) p.1.point +
            p.2 • V (p.1.index, p.1.direction)) =
        ((uniformDistribution (DirectLdSpace D × DirectScalarQ D)).map e).map
          (fun w => lineRepMap (V w.1) w.2.1 + w.2.2 • V w.1) := by
    rw [Distribution.map_map]
    rfl
  rw [hmap, (uniformDistribution_map_equiv e)]
  refine uniformDistribution_map_uncurry _ _ fun a => ?_
  exact uniformDistribution_map_lineRepMap_add_smul (V a)

/-- Averaging a function at a uniform affine parameter on the canonical line
of a uniform direct sample is averaging it at a uniform point. -/
theorem avgOver_uniform_directLdSpace_line_add_smul
    (g : (DirectPoint D) → ℝ) :
    avgOver (uniformDistribution (DirectLdSpace D)) (fun s =>
        avgOver (uniformDistribution (DirectScalarQ D)) (fun t =>
          g (lineRepMap (V (s.index, s.direction)) s.point +
            t • V (s.index, s.direction)))) =
      avgOver (uniformDistribution (DirectPoint D)) g := by
  classical
  rw [← avgOver_uniform_prod]
  refine Eq.trans ((Distribution.avgOver_map _ _ g).symm) ?_
  rw [uniformDistribution_map_directLine_add_smul]

end

/-- A uniform point on a line drawn from the directly indexed line-point law
is uniform in the ambient coordinate space. -/
theorem avgOver_directLinePointDist_line_add_smul
    (g : (DirectPoint D) → ℝ) :
    avgOver ((directLinePointDist D).map Prod.fst) (fun line =>
        avgOver (uniformDistribution (DirectScalarQ D)) (fun t =>
          g (line.base + t • line.direction))) =
      avgOver (uniformDistribution (DirectPoint D)) g := by
  classical
  have haxis :
      avgOver (directALinePointDist D) (fun sample =>
          avgOver (uniformDistribution (DirectScalarQ D)) (fun t =>
            g (sample.1.base + t • sample.1.direction))) =
        avgOver (uniformDistribution (DirectPoint D)) g := by
    rw [directALinePointDist, Distribution.avgOver_map]
    exact avgOver_uniform_directLdSpace_line_add_smul D
      (fun w => coordinateDirection w.1) g
  have hdiag :
      avgOver (directDLinePointDist D) (fun sample =>
          avgOver (uniformDistribution (DirectScalarQ D)) (fun t =>
            g (sample.1.base + t • sample.1.direction))) =
        avgOver (uniformDistribution (DirectPoint D)) g := by
    rw [directDLinePointDist, Distribution.avgOver_map]
    exact avgOver_uniform_directLdSpace_line_add_smul D
      (fun w => directPrefixProjection w.1 w.2) g
  rw [Distribution.avgOver_map, directLinePointDist,
    MIPStarRE.QPBT.avgOver_mix, haxis, hdiag]
  ring

end

/-- Under a sub-line witness, the two source blocks of the point at a uniform
affine parameter are independent uniform source points. -/
theorem SubLineWitness.avgOver_projX_projZ (P : AdmissibleParams)
    (sublines : SubLineWitness P)
    (f : ((PauliPoint P) × (PauliPoint P)) → ℝ) :
    avgOver sublines.D (fun sample =>
        avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd))
          (fun t =>
            f (projX (directPointToPauli
                (sample.1.base + t • sample.1.direction)),
              projZ (directPointToPauli
                (sample.1.base + t • sample.1.direction))))) =
      avgOver (uniformDistribution
        ((PauliPoint P) × (PauliPoint P))) f := by
  classical
  have hmarginal :
      avgOver sublines.D (fun sample =>
          avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd))
            (fun t => f (projX (directPointToPauli
                (sample.1.base + t • sample.1.direction)),
              projZ (directPointToPauli
                (sample.1.base + t • sample.1.direction))))) =
        avgOver ((directLinePointDist P.extendedDirectLd).map Prod.fst)
          (fun line =>
            avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd))
              (fun t => f (projX (directPointToPauli
                  (line.base + t • line.direction)),
                projZ (directPointToPauli
                  (line.base + t • line.direction))))) := by
    rw [← sublines.extended_marginal, Distribution.avgOver_map]
  apply hmarginal.trans
  refine (avgOver_directLinePointDist_line_add_smul P.extendedDirectLd
    (fun u => f (projX (directPointToPauli u),
      projZ (directPointToPauli u)))).trans ?_
  rw [uniformDistribution_prod, ← uniformDistribution_map_projX_projZ_pauli,
    Distribution.avgOver_map]

end

/-- Compatibility name for the uniform representative--parameter theorem.
Its proof is now shared with the subline construction in
`uniformDistribution_map_lineRepMap_add_smul`. -/
@[deprecated (since := "2026-09-12")]
alias uniformDistribution_map_lineRepMap_add_smul_current :=
  uniformDistribution_map_lineRepMap_add_smul

end MIPStarRE.QPBT
