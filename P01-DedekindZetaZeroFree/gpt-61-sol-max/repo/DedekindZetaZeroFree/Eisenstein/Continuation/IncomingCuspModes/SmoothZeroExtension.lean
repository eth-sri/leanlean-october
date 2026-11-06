module

public import DedekindZetaZeroFree.Eisenstein.Continuation.IncomingCuspModes.ChartJets

@[expose] public section

noncomputable section
open scoped Classical NumberField ContDiff
open Topology

namespace DedekindZetaZeroFree.KPContActualCutoffSmoothDescent

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
variable (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
variable {T : ℝ}
variable (B : KPContActualCollarBuffer.CollarBuffer F ζ hζ
  (level F ζ hζ C R P H U) R P H T)


local notation:max "current_coveredPoint" => coveredPoint F ζ hζ C R P H U


local notation:max "current_level" => level F ζ hζ C R P H U


local notation:max "current_z" => KPContSectorCoveredQuotientVocabulary.z F ζ hζ

private theorem coveredPoint_eq_central (a : Cusps F ζ hζ C R P H U) (ε : rootsOfUnity 3 F)
    (z : KPCuspCharts.Coordinates F) :
    current_coveredPoint a ε z =
      current_z (current_level) ε
        (current_coveredPoint a 1 z) := by
  simp [coveredPoint, KPContSectorCoveredQuotientVocabulary.z_mk, map_one]

private theorem coveredPoint_base (a : Cusps F ζ hζ C R P H U) (ε : rootsOfUnity 3 F)
    (z : KPCuspCharts.Coordinates F) :
    KPContSectorCoveredQuotientVocabulary.q F ζ hζ (current_level)
      (current_coveredPoint a ε z) =
      KPContActualCollarBuffer.chartLift F ζ hζ (current_level) R P H a z := by
  rw [coveredPoint_eq_central, KPContSectorCoveredQuotientVocabulary.q_z]
  simp [coveredPoint, KPContSectorCoveredQuotientVocabulary.q_mk,
    map_one, KPContActualCollarBuffer.chartLift,
    KPContSectorSmoothFramesSupport.cuspPoint, KPContFlatCuspIncomingEvaluation.atlas]


local notation:max "current_height" => height F ζ hζ C R P H U

private theorem height_coveredPoint (a : Cusps F ζ hζ C R P H U) (ε : rootsOfUnity 3 F)
    (z : KPCuspCharts.Coordinates F) (hz : B.τ < z.2) :
    current_height B a (current_coveredPoint a ε z) = z.2 := by
  unfold height
  rw [coveredPoint_base]
  exact B.height_coordinates a z hz


section
variable {F ζ hζ C R P H U}
private noncomputable abbrev context_coveredPoint := coveredPoint F ζ hζ C R P H U
end

private theorem coveredPoint_mem_end (a : Cusps F ζ hζ C R P H U) (ε : rootsOfUnity 3 F)
    (z : KPCuspCharts.Coordinates F) (hz : B.τ < z.2) :
    current_coveredPoint a ε z ∈ ends F ζ hζ C R P H U B a := by
  change KPContSectorCoveredQuotientVocabulary.q F ζ hζ (current_level)
    (_root_.DedekindZetaZeroFree.KPContActualCutoffSmoothDescent.context_coveredPoint a ε z) ∈
      KPContActualCollarBuffer.endSet F ζ hζ (current_level) R P H B.τ a
  rw [coveredPoint_base, ← B.lift_range a]
  exact ⟨z, hz, rfl⟩

 theorem coveredPoint_z_sheet (a : Cusps F ζ hζ C R P H U)
    (ε ε' : rootsOfUnity 3 F) (z : KPCuspCharts.Coordinates F) :
    current_coveredPoint a (ε * ε') z =
      current_z (current_level) ε
        (current_coveredPoint a ε' z) := by
  have h1 := coveredPoint_eq_central F ζ hζ C R P H U a (ε * ε') z
  have h2 := coveredPoint_eq_central F ζ hζ C R P H U a ε' z
  have h3 : current_z (current_level)
        (ε * ε') (_root_.DedekindZetaZeroFree.KPContActualCutoffSmoothDescent.context_coveredPoint a 1 z) =
      current_z (current_level) ε
        (current_z (current_level) ε'
          (_root_.DedekindZetaZeroFree.KPContActualCutoffSmoothDescent.context_coveredPoint a 1 z)) := by
    change (ε * ε') • (_root_.DedekindZetaZeroFree.KPContActualCutoffSmoothDescent.context_coveredPoint a 1 z) =
      ε • (ε' • (_root_.DedekindZetaZeroFree.KPContActualCutoffSmoothDescent.context_coveredPoint a 1 z))
    rw [mul_smul]
  rw [h1, h3, ← h2]


local notation:max "current_Covered" => Covered F ζ hζ C R P H U


local notation:max "current_EndLift" => EndLift F ζ hζ C R P H U

 def endLift_z {x : current_Covered}
    (l : current_EndLift B x) (ε : rootsOfUnity 3 F) :
    current_EndLift B
      (current_z (current_level) ε x) :=
  ⟨l.cusp, ε * l.sheet, l.coordinates, l.high,
    (coveredPoint_z_sheet F ζ hζ C R P H U l.cusp ε l.sheet l.coordinates).trans
      (congrArg (current_z
        (current_level) ε) l.point)⟩

 theorem z_inv_z (ε : rootsOfUnity 3 F) (x : current_Covered) :
    current_z (current_level) ε⁻¹
      (current_z (current_level) ε x) = x := by
  change ε⁻¹ • (ε • x) = x
  rw [← mul_smul, inv_mul_cancel, one_smul]

 def endLift_z_inv {x : current_Covered} (ε : rootsOfUnity 3 F)
    (l : current_EndLift B
      (current_z (current_level) ε x)) :
    current_EndLift B x :=
  z_inv_z F ζ hζ C R P H U ε x ▸ endLift_z F ζ hζ C R P H U B l ε⁻¹

private theorem incomingRealization_of_lift (s : ℂ) (hs : s ∈ KPContinuation.spectralDomain)
    (v : S) {x : current_Covered} (l : current_EndLift B x) :
    incomingRealization F ζ hζ C R P H U ι B s v x =
      (KPContSectorCoveredQuotientVocabulary.chi F ζ hζ l.sheet : ℂ) *
        incomingValue F ζ hζ C R P H U ι l.cusp s v l.coordinates := by
  have hne : Nonempty (current_EndLift B x) := ⟨l⟩
  change (if h : Nonempty (current_EndLift B x) then _ else _) = _
  rw [dite_eq_left hne]
  exact actual_endLift_incoming_transport F ζ hζ C R P H U ι B s hs v x
    (Classical.choice hne) l

private theorem incomingRealization_z (s : ℂ) (hs : s ∈ KPContinuation.spectralDomain)
    (v : S) (x : current_Covered) (ε : rootsOfUnity 3 F) :
    incomingRealization F ζ hζ C R P H U ι B s v
        (current_z (current_level) ε x) =
      (KPContSectorCoveredQuotientVocabulary.chi F ζ hζ ε : ℂ) *
        incomingRealization F ζ hζ C R P H U ι B s v x := by
  by_cases hx : Nonempty (current_EndLift B x)
  · obtain ⟨l⟩ := hx
    rw [incomingRealization_of_lift F ζ hζ C R P H U ι B s hs v l,
      incomingRealization_of_lift F ζ hζ C R P H U ι B s hs v
        (endLift_z F ζ hζ C R P H U B l ε)]
    simp only [endLift_z, map_mul, Circle.coe_mul]
    ring
  · have hx' : ¬ Nonempty (current_EndLift B
        (current_z (current_level) ε x)) :=
      fun h => hx ⟨endLift_z_inv F ζ hζ C R P H U B ε (Classical.choice h)⟩
    change (if h : Nonempty (current_EndLift B
        (current_z (current_level) ε x))
        then _ else _) =
      (KPContSectorCoveredQuotientVocabulary.chi F ζ hζ ε : ℂ) *
        (if h : Nonempty (current_EndLift B x) then _ else _)
    rw [dite_eq_right hx', dite_eq_right hx, mul_zero]


section
variable {F ζ hζ C R P H U}
private noncomputable abbrev context_ends := ends (T := T) F ζ hζ C R P H U
end


local notation:max "current_coveredRelation" => KPContSectorCoveredQuotientVocabulary.coveredRelation F ζ hζ

theorem actual_incoming_smooth_zero_extension
    (a : Cusps F ζ hζ C R P H U) (s : ℂ)
    (hs : s ∈ KPContinuation.spectralDomain) (v : S)
    (φ : ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hzero : ∀ t, t ≤ T → φ t = 0) :
    ∃ g : KPContSectorSmoothFramesSupport.smoothCovered F ζ hζ
      (current_level),
      g.val.val = (ends F ζ hζ C R P H U B a).indicator
        (fun x => φ (current_height B a x) *
          incomingRealization F ζ hζ C R P H U ι B s v x) := by
  let Ffun : current_Covered → ℂ :=
    (_root_.DedekindZetaZeroFree.KPContActualCutoffSmoothDescent.context_ends B a).indicator
      (fun x => φ (current_height B a x) *
        incomingRealization F ζ hζ C R P H U ι B s v x)
  have hgen : ∀ (ε : rootsOfUnity 3 F) (y : current_Covered),
      Ffun (current_z (current_level) ε y) =
        (KPContSectorCoveredQuotientVocabulary.chi F ζ hζ ε : ℂ) * Ffun y := by
    intro ε y
    by_cases hy : y ∈ _root_.DedekindZetaZeroFree.KPContActualCutoffSmoothDescent.context_ends B a
    · have hzy : current_z (current_level) ε y
          ∈ _root_.DedekindZetaZeroFree.KPContActualCutoffSmoothDescent.context_ends B a := by
        change KPContSectorCoveredQuotientVocabulary.q F ζ hζ (current_level)
          (current_z (current_level) ε y)
            ∈ KPContActualCollarBuffer.endSet F ζ hζ (current_level) R P H B.τ a
        rw [KPContSectorCoveredQuotientVocabulary.q_z]
        exact hy
      have hh : current_height B a
            (current_z (current_level) ε y) =
          current_height B a y := by
        unfold height
        rw [KPContSectorCoveredQuotientVocabulary.q_z]
      simp only [Ffun, Set.indicator_of_mem hy, Set.indicator_of_mem hzy, hh]
      rw [incomingRealization_z F ζ hζ C R P H U ι B s hs v y ε]
      ring
    · have hzy : current_z (current_level) ε y
          ∉ _root_.DedekindZetaZeroFree.KPContActualCutoffSmoothDescent.context_ends B a := by
        intro h
        apply hy
        change KPContSectorCoveredQuotientVocabulary.q F ζ hζ (current_level) y
          ∈ KPContActualCollarBuffer.endSet F ζ hζ (current_level) R P H B.τ a
        change KPContSectorCoveredQuotientVocabulary.q F ζ hζ (current_level)
          (current_z (current_level) ε y)
            ∈ KPContActualCollarBuffer.endSet F ζ hζ (current_level) R P H B.τ a at h
        rwa [KPContSectorCoveredQuotientVocabulary.q_z] at h
      simp only [Ffun, Set.indicator_of_notMem hy, Set.indicator_of_notMem hzy, mul_zero]
  have hsec : KPContSectorSmoothFramesSupport.IsSmoothSections F ζ hζ
      (current_level) R P H
      (KPContSectorScalarLineAlgebra.S F ζ hζ (current_level) R P H
        ⟨Ffun, hgen⟩) := by
    intro i
    have hfun : (KPContSectorScalarLineAlgebra.S F ζ hζ (current_level) R P H
          ⟨Ffun, hgen⟩ i).val =
        fun x : KPFiniteCuspAtlas.SymmetricSpace F =>
          Ffun (Quotient.mk (current_coveredRelation
            (current_level))
            (x, (H.atlas (current_level)).representative i)) := by
      funext x
      rw [KPContSectorScalarLineAlgebra.S_apply]
    rw [hfun, contDiff_iff_contDiffAt]
    intro x0
    have hqcont : Continuous (fun x : KPFiniteCuspAtlas.SymmetricSpace F =>
        KPContSectorCoveredQuotientVocabulary.q F ζ hζ (current_level)
          (Quotient.mk (current_coveredRelation
            (current_level))
            (x, (H.atlas (current_level)).representative i))) :=
      (KPContSectorQuotientRelationsComparison.q_continuous F ζ hζ
        (current_level)).comp
        (continuous_quotient_mk'.comp (continuous_id.prodMk continuous_const))
    by_cases hC : KPContSectorCoveredQuotientVocabulary.q F ζ hζ (current_level)
          (Quotient.mk (current_coveredRelation
            (current_level))
            (x0, (H.atlas (current_level)).representative i)) ∈
        interior (KPContActualCollarBuffer.endSet F ζ hζ (current_level) R P H B.τ a)
    · rw [IsOpen.interior_eq (B.open_ends a)] at hC
      have hmem : Quotient.mk (current_coveredRelation
            (current_level))
            (x0, (H.atlas (current_level)).representative i) ∈
          _root_.DedekindZetaZeroFree.KPContActualCutoffSmoothDescent.context_ends B a := hC
      obtain ⟨V, hVopen, hx0V, ε, z, hz, hzV⟩ :=
        actual_end_local_smooth_lift F ζ hζ C R P H U B a i x0 hmem
      have hcongr : ∀ x ∈ V, Ffun (Quotient.mk
            (current_coveredRelation
              (current_level))
            (x, (H.atlas (current_level)).representative i)) =
          φ ((z x).2) * ((KPContSectorCoveredQuotientVocabulary.chi F ζ hζ ε : ℂ) *
            incomingValue F ζ hζ C R P H U ι a s v (z x)) := by
        intro x hx
        obtain ⟨hzx, hzpx⟩ := hzV x hx
        have hF : Ffun (_root_.DedekindZetaZeroFree.KPContActualCutoffSmoothDescent.context_coveredPoint a ε (z x)) =
            φ (current_height B a (_root_.DedekindZetaZeroFree.KPContActualCutoffSmoothDescent.context_coveredPoint a ε (z x))) *
              incomingRealization F ζ hζ C R P H U ι B s v
                (_root_.DedekindZetaZeroFree.KPContActualCutoffSmoothDescent.context_coveredPoint a ε (z x)) := by
          simp only [Ffun,
            Set.indicator_of_mem (coveredPoint_mem_end F ζ hζ C R P H U B a ε (z x) hzx)]
        rw [← hzpx, hF, height_coveredPoint F ζ hζ C R P H U B a ε (z x) hzx,
          incomingRealization_of_lift F ζ hζ C R P H U ι B s hs v
            ⟨a, ε, z x, hzx, rfl⟩]
      have hz2 : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => (z x).2) V :=
        (contDiff_snd (𝕜 := ℝ)).comp_contDiffOn hz
      have hmain : ContDiffOn ℝ (⊤ : ℕ∞)
          (fun x => φ ((z x).2) * ((KPContSectorCoveredQuotientVocabulary.chi F ζ hζ ε : ℂ) *
            incomingValue F ζ hζ C R P H U ι a s v (z x))) V :=
        (hφ.comp_contDiffOn hz2).mul
          ((contDiffOn_const (c := (KPContSectorCoveredQuotientVocabulary.chi F ζ hζ ε : ℂ))).mul
            ((incomingValue_uniformizing_contDiff F ζ hζ C R P H U ι a s hs v).comp_contDiffOn hz))
      exact (hmain.congr hcongr).contDiffAt (hVopen.mem_nhds hx0V)
    · by_cases hA : KPContSectorCoveredQuotientVocabulary.q F ζ hζ (current_level)
            (Quotient.mk (current_coveredRelation
              (current_level))
              (x0, (H.atlas (current_level)).representative i)) ∈
          frontier (KPContActualCollarBuffer.endSet F ζ hζ (current_level) R P H B.τ a)
      · obtain ⟨V, hVopen, hqV, hzb⟩ := B.boundary_height_buffer a
          (KPContSectorCoveredQuotientVocabulary.q F ζ hζ (current_level)
            (Quotient.mk (current_coveredRelation
              (current_level))
              (x0, (H.atlas (current_level)).representative i))) hA
        have hW : ∀ᶠ x in 𝓝 x0, Ffun (Quotient.mk
              (current_coveredRelation
                (current_level))
              (x, (H.atlas (current_level)).representative i)) = 0 := by
          filter_upwards [(hVopen.preimage hqcont).mem_nhds hqV] with x hx
          by_cases hxe : Quotient.mk (current_coveredRelation
                (current_level))
                (x, (H.atlas (current_level)).representative i) ∈
              _root_.DedekindZetaZeroFree.KPContActualCutoffSmoothDescent.context_ends B a
          · have hh : current_height B a (Quotient.mk
                  (current_coveredRelation
                    (current_level))
                  (x, (H.atlas (current_level)).representative i)) < T :=
              hzb _ hx hxe
            simp only [Ffun, Set.indicator_of_mem hxe, hzero _ hh.le, zero_mul]
          · simp only [Ffun, Set.indicator_of_notMem hxe]
        exact ContDiffAt.congr_of_eventuallyEq (contDiffAt_const (c := (0 : ℂ))) hW
      · have hcl : KPContSectorCoveredQuotientVocabulary.q F ζ hζ (current_level)
            (Quotient.mk (current_coveredRelation
              (current_level))
              (x0, (H.atlas (current_level)).representative i)) ∉
            closure (KPContActualCollarBuffer.endSet F ζ hζ (current_level) R P H B.τ a) := by
          intro hc
          rw [closure_eq_interior_union_frontier] at hc
          rcases hc with h | h
          · exact hC h
          · exact hA h
        have hW : ∀ᶠ x in 𝓝 x0, Ffun (Quotient.mk
              (current_coveredRelation
                (current_level))
              (x, (H.atlas (current_level)).representative i)) = 0 := by
          have hopen : IsOpen {x : KPFiniteCuspAtlas.SymmetricSpace F |
              KPContSectorCoveredQuotientVocabulary.q F ζ hζ (current_level)
                (Quotient.mk (current_coveredRelation
                  (current_level))
                  (x, (H.atlas (current_level)).representative i)) ∉
                closure (KPContActualCollarBuffer.endSet F ζ hζ (current_level)
                  R P H B.τ a)} :=
            isClosed_closure.isOpen_compl.preimage hqcont
          filter_upwards [hopen.mem_nhds hcl] with x hx
          have hxe : Quotient.mk (current_coveredRelation
                (current_level))
                (x, (H.atlas (current_level)).representative i) ∉
              _root_.DedekindZetaZeroFree.KPContActualCutoffSmoothDescent.context_ends B a := fun he => hx (subset_closure he)
          simp only [Ffun, Set.indicator_of_notMem hxe]
        exact ContDiffAt.congr_of_eventuallyEq (contDiffAt_const (c := (0 : ℂ))) hW
  exact ⟨⟨⟨Ffun, hgen⟩,
    (KPContSectorSmoothFramesSupport.smooth_iff F ζ hζ (current_level) R P H
      ⟨Ffun, hgen⟩).mpr hsec⟩, rfl⟩

end DedekindZetaZeroFree.KPContActualCutoffSmoothDescent

end
