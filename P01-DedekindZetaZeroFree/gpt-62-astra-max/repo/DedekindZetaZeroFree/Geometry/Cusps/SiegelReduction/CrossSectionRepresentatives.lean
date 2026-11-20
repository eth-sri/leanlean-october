module

public import DedekindZetaZeroFree.Geometry.Cusps.SiegelReduction.CompactComplement
public import DedekindZetaZeroFree.Geometry.ArithmeticQuotients.Cusps.EquivariantAffineUnitCharts

@[expose] public section

noncomputable section
open scoped Classical

namespace DedekindZetaZeroFree.KPCuspSiegel

private alias compact_orbit_lifts := DedekindZetaZeroFree.KPCuspChart.SectionConstruction.FiniteInvariantMeasure.compact_lifts

variable (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (S : Subgroup (KPCuspArithmetic.PGL2 F))
    (D : KPCuspCharts.ParabolicData F S)
    (O : KPCuspCharts.ChartOutput F hF S D)

private theorem chart_action_radial (g : S) (p : KPCuspCharts.Cross F) (t : ℝ) :
    action F (g : KPCuspArithmetic.PGL2 F) (KPCuspCharts.toArch F (p, t)) =
      KPCuspCharts.toArch F (O.crossAction g p, t) := by
  obtain ⟨A, hA, hc⟩ := D.upper g g.property
  rw [O.actual_action g A hA hc, O.crossAction_formula g A hA hc p]
  rfl

private theorem chart_cross_orbit_relation :
    letI := KPCuspCharts.homeomorphAction O.crossAction
    KPCuspCharts.crossRelation F S = MulAction.orbitRel S (KPCuspCharts.Cross F) := by
  have hinj : Function.Injective (fun p : KPCuspCharts.Cross F =>
      KPCuspCharts.toArch F (p, 0)) := by
    intro p q h
    exact congrArg Prod.fst ((KPCuspCharts.toArchHomeomorph F O.positive_dimension).injective h)
  apply Setoid.ext
  intro p q
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, hinj ((chart_action_radial F hF S D O g q 0).symm.trans hg)⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, (chart_action_radial F hF S D O g q 0).trans
      (congrArg (fun p => KPCuspCharts.toArch F (p, 0)) hg)⟩

include hF D O in

theorem exists_compact_cross_section_representatives :
    ∃ (P : Set (Fin (KPCuspLogShape.dimension F) → ℂ))
      (B : Set (KPCuspLogShape.hyperplane (KPCuspLogShape.dimension F))),
      IsCompact P ∧ P.Nonempty ∧ IsCompact B ∧ B.Nonempty ∧
      ∀ z : KPArch.Space (KPCuspLogShape.dimension F),
        ∃ (g : S), ∃ x ∈ P, ∃ b ∈ B,
          action F (g : KPCuspArithmetic.PGL2 F) z =
            fun i => (x i, KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) z +
              (b : Fin (KPCuspLogShape.dimension F) → ℝ) i) := by
  letI := KPCuspCharts.homeomorphAction O.crossAction
  letI : ContinuousConstSMul S (KPCuspCharts.Cross F) :=
    ⟨fun g => (O.crossAction g).continuous⟩
  letI : CompactSpace (Quotient (MulAction.orbitRel S (KPCuspCharts.Cross F))) := by
    rw [← chart_cross_orbit_relation F hF S D O]
    exact O.compact_cross
  obtain ⟨K, hK, hcover⟩ := compact_orbit_lifts (H := S) (X := KPCuspCharts.Cross F)
  have hKne : K.Nonempty := by
    obtain ⟨g, hg⟩ := hcover 0
    exact ⟨g • 0, hg⟩
  refine ⟨Prod.fst '' K, Prod.snd '' K, hK.image continuous_fst,
    hKne.image _, hK.image continuous_snd, hKne.image _, ?_⟩
  intro z
  let p := (KPCuspCharts.toArchHomeomorph F O.positive_dimension).symm z
  obtain ⟨g, hg⟩ := hcover p.1
  refine ⟨g, (O.crossAction g p.1).1, ⟨O.crossAction g p.1, hg, rfl⟩,
    (O.crossAction g p.1).2, ⟨O.crossAction g p.1, hg, rfl⟩, ?_⟩
  have hp : KPCuspCharts.toArch F p = z :=
    (KPCuspCharts.toArchHomeomorph F O.positive_dimension).apply_symm_apply z
  have ht : p.2 = KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) z := by
    rw [← hp, KPCuspCharts.toArch_meanHeight F O.positive_dimension]
  rw [← hp, chart_action_radial F hF S D O g p.1 p.2]
  rw [← hp] at ht
  rw [← ht]
  rfl

include hF in

theorem exists_arithmetic_cross_section_representatives
    (M : Submodule (KPCuspArithmetic.Order F) (KPCuspArithmetic.Vec F))
    (hM : KPCuspArithmetic.IsRankTwoLattice F M)
    (Γ : Subgroup (KPCuspArithmetic.PGL2 F))
    (hΓ : ∀ g ∈ Γ, KPCuspArithmetic.PreservesUpToHomothety F M g)
    (hcomm : Γ.Commensurable (KPCuspArithmetic.projectiveAutomorphisms F M))
    (q : KPCuspArithmetic.Cusp F) (σ : KPCuspArithmetic.PGL2 F)
    (hσ : σ • KPCuspArithmetic.infinity F = q) :
    ∃ (P : Set (Fin (KPCuspLogShape.dimension F) → ℂ))
      (B : Set (KPCuspLogShape.hyperplane (KPCuspLogShape.dimension F))),
      IsCompact P ∧ P.Nonempty ∧ IsCompact B ∧ B.Nonempty ∧
      ∀ z : KPArch.Space (KPCuspLogShape.dimension F),
        ∃ (g : KPCuspArithmetic.conjugatedStabilizer F Γ q σ),
          ∃ x ∈ P, ∃ b ∈ B,
          action F (g : KPCuspArithmetic.PGL2 F) z =
            fun i => (x i, KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) z +
              (b : Fin (KPCuspLogShape.dimension F) → ℝ) i) := by
  obtain ⟨D, O, _⟩ := kp_cusp_equivariant_nilmanifold_charts F hF M hM Γ hΓ hcomm q σ hσ
  exact exists_compact_cross_section_representatives F hF _ D O

include hF in

theorem exists_arithmetic_high_box_representatives
    (M : Submodule (KPCuspArithmetic.Order F) (KPCuspArithmetic.Vec F))
    (hM : KPCuspArithmetic.IsRankTwoLattice F M)
    (Γ : Subgroup (KPCuspArithmetic.PGL2 F))
    (hΓ : ∀ g ∈ Γ, KPCuspArithmetic.PreservesUpToHomothety F M g)
    (hcomm : Γ.Commensurable (KPCuspArithmetic.projectiveAutomorphisms F M))
    (q : KPCuspArithmetic.Cusp F) (σ : KPCuspArithmetic.PGL2 F)
    (hσ : σ • KPCuspArithmetic.infinity F = q) :
    ∃ (P : Set (Fin (KPCuspLogShape.dimension F) → ℂ))
      (B : Set (KPCuspLogShape.hyperplane (KPCuspLogShape.dimension F))),
      IsCompact P ∧ P.Nonempty ∧ IsCompact B ∧ B.Nonempty ∧
      (∀ z : KPArch.Space (KPCuspLogShape.dimension F),
        ∃ (g : KPCuspArithmetic.conjugatedStabilizer F Γ q σ),
          ∃ x ∈ P, ∃ b ∈ B,
          action F (g : KPCuspArithmetic.PGL2 F) z =
            fun i => (x i, KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) z +
              (b : Fin (KPCuspLogShape.dimension F) → ℝ) i)) ∧
      ∀ T : ℝ, projection F Γ '' highCusp F σ T =
        projection F Γ '' (action F σ '' box F P B (Set.Ioi T)) := by
  obtain ⟨P, B, hP, hPne, hB, hBne, hrep⟩ :=
    exists_arithmetic_cross_section_representatives F hF M hM Γ hΓ hcomm q σ hσ
  refine ⟨P, B, hP, hPne, hB, hBne, hrep, ?_⟩
  intro T
  apply Set.Subset.antisymm
  · rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    obtain ⟨g, x, hx, b, hb, he⟩ := hrep z
    obtain ⟨k, hk, hkg⟩ := Subgroup.mem_map.mp g.property
    have hkg' : σ⁻¹ * k * σ = (g : KPCuspArithmetic.PGL2 F) := by
      simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
        MulAut.conj_apply, inv_inv] using hkg
    let w : KPArch.Space (KPCuspLogShape.dimension F) :=
      fun i => (x i, KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) z +
        (b : Fin (KPCuspLogShape.dimension F) → ℝ) i)
    have hw : w ∈ box F P B (Set.Ioi T) :=
      ⟨x, hx, b, hb, KPCuspLogShape.meanHeight _ z, hz, rfl⟩
    refine ⟨action F σ w, ⟨w, hw, rfl⟩, ?_⟩
    have hact : action F σ w = action F k (action F σ z) := by
      change action F σ (fun i => (x i,
        KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) z +
        (b : Fin (KPCuspLogShape.dimension F) → ℝ) i)) = _
      rw [← he]
      change σ • ((g : KPCuspArithmetic.PGL2 F) • z) = k • (σ • z)
      rw [← hkg']
      simp only [mul_smul, smul_inv_smul]
    rw [hact]
    exact projection_action F Γ ⟨k, hk.1⟩ _
  · rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    refine ⟨action F σ w, ⟨w, ?_, rfl⟩, rfl⟩
    obtain ⟨x, hx, b, hb, t, ht, rfl⟩ := hw
    change T < KPCuspLogShape.meanHeight _ _
    rw [meanHeight_box_coordinate F (KPCuspLogShape.dimension_pos F hF)]
    exact ht

end DedekindZetaZeroFree.KPCuspSiegel

end
