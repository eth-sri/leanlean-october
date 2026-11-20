module

public import DedekindZetaZeroFree.Metaplectic.Torus.Charts.WeightedJetEstimates

@[expose] public section

section

open scoped NumberField Classical NNReal BigOperators
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.KPGlobalTorusBorelTwistCompatibilityBorelInduction.UniformFiberLevel
open KPGlobalTorusBorelNormTwistTransport
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 2000

variable (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem exists_conjugate_finite_level
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) (g : G F ζ hζ) :
    ∃ U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ,
      ∀ t : KPGlobalTorusFunctionData.globalLevel F ζ hζ U,
        g⁻¹ * t.val * g ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ J := by
  have hn : (KPGlobalTorusFunctionData.finitePart F ζ hζ).Normal := by
    rw [KPGlobalTorusFiniteStagesCofinality.finitePart_eq_closure F ζ hζ]
    exact ActualFiniteFactor.finiteSubgroup_normal F ζ hζ
  let e : KPGlobalTorusFunctionData.finitePart F ζ hζ ≃ₜ*
      KPGlobalTorusFunctionData.finitePart F ζ hζ :=
    { toFun := fun u => ⟨g⁻¹ * u.val * g, by
        simpa using hn.conj_mem u.val u.property g⁻¹⟩
      invFun := fun u => ⟨g * u.val * g⁻¹, hn.conj_mem u.val u.property g⟩
      left_inv := by intro u; apply Subtype.ext; dsimp; group
      right_inv := by intro u; apply Subtype.ext; dsimp; group
      map_mul' := by intro u v; apply Subtype.ext; dsimp; group
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  refine ⟨(⟨J.toOpenSubgroup.comap e.toMonoidHom e.continuous,
    e.toHomeomorph.isCompact_preimage.mpr J.isCompact⟩), ?_⟩
  intro t
  obtain ⟨u, hu, he⟩ := t.property
  refine ⟨e u, hu, ?_⟩
  change g⁻¹ * u.val * g = g⁻¹ * t.val * g
  change u.val = t.val at he
  rw [he]

end
end DedekindZetaZeroFree.KPGlobalTorusBorelTwistCompatibilityBorelInduction.UniformFiberLevel

end

section

open scoped NumberField Classical NNReal BigOperators
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.KPGlobalTorusBorelTwistCompatibilityBorelInduction.UniformFiberLevel
open KPGlobalTorusBorelNormTwistTransport
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 2000

variable (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

private alias ordinaryTorus_isClosed := DedekindZetaZeroFree.KPGlobalTorusFiniteStagesCofinality.FiniteClassProjection.ordinary_torus_closed

theorem actualTorus_isClosed :
    IsClosed ((KPGlobalTorusFunctionData.torus F ζ hζ) : Set (G F ζ hζ)) := by apply @DedekindZetaZeroFree.KPGlobalTorusPeriodizationInverse.torus_closed <;> assumption

theorem exists_compact_conjugate_torus_level
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) (g : G F ζ hζ) :
    ∃ U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ,
      IsCompact (((KPGlobalTorusFunctionData.globalLevel F ζ hζ U).comap
        (KPGlobalTorusFunctionData.torus F ζ hζ).subtype) : Set (E F ζ hζ)) ∧
      ∀ t : (KPGlobalTorusFunctionData.globalLevel F ζ hζ U).comap
          (KPGlobalTorusFunctionData.torus F ζ hζ).subtype,
        g⁻¹ * t.val.val * g ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ J := by
  obtain ⟨U, hU⟩ := exists_conjugate_finite_level F ζ hζ J g
  refine ⟨U, ?_, ?_⟩
  · exact (actualTorus_isClosed F ζ hζ).isClosedEmbedding_subtypeVal.isCompact_preimage
      (globalLevel_isCompact F ζ hζ U)
  · intro t
    exact hU ⟨t.val.val, t.property⟩

end
end DedekindZetaZeroFree.KPGlobalTorusBorelTwistCompatibilityBorelInduction.UniformFiberLevel

end

section

open scoped NumberField Classical NNReal BigOperators
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.KPGlobalTorusBorelTwistCompatibilityBorelInduction.UniformFiberLevel
open KPGlobalTorusBorelNormTwistTransport
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 2000

variable (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

section

variable (P : Polarization F ζ hζ)

theorem fiber_rightAction_of_conjugate_mem
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (f : InducedLevel F ζ hζ P J) (g : G F ζ hζ) (t : E F ζ hζ)
    (hδ : KPGlobalTorusFunctionData.delta F ζ hζ t = 1)
    (ht : g⁻¹ * t.val * g ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ J) :
    KPGlobalTorusPeriodizationInverse.rightAction F ζ hζ P t (f.val.val g) =
      f.val.val g := by
  have hc := f.val.property t 0 g
  have hn : KPGlobalTorusFunctionData.N F ζ hζ
      (0 : KPGlobalTorusFunctionData.Adeles F) = 1 :=
    (KPGlobalTorusFunctionData.Nhom F ζ hζ).map_one
  have hhalf : KPGlobalTorusFunctionData.deltaHalf F ζ hζ t = 1 := by
    simp [KPGlobalTorusFunctionData.deltaHalf, hδ]
  have hm : t.val * g = g * (g⁻¹ * t.val * g) := by group
  simp only [hn, mul_one, hhalf, one_smul] at hc
  rw [hm, f.property.2 g ⟨_, ht⟩] at hc
  exact hc.symm

theorem chart_fiber_rightLevel_of_compact_conjugate
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (g : G F ζ hζ) (H : Subgroup (E F ζ hζ))
    (hc : IsCompact (H : Set (E F ζ hζ)))
    (hfin : ∀ t : H, t.val.val ∈ KPGlobalTorusFunctionData.finitePart F ζ hζ)
    (hconj : ∀ t : H,
      g⁻¹ * t.val.val * g ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ J)
    (f : InducedLevel F ζ hζ P J) (z : GroupArch F) :
    ∀ (t : H) (x : E F ζ hζ),
      (f.val.val (groupArchChart F ζ hζ z * g)).val.val (x * t.val) =
        (f.val.val (groupArchChart F ζ hζ z * g)).val.val x := by
  intro t x
  have hm : (groupArchChart F ζ hζ z * g)⁻¹ * t.val.val *
      (groupArchChart F ζ hζ z * g) = g⁻¹ * t.val.val * g := by
    calc
      _ = g⁻¹ * (groupArchChart F ζ hζ z)⁻¹ *
          (t.val.val * groupArchChart F ζ hζ z) * g := by group
      _ = _ := by rw [(TorusChartTransport.groupArchChart_commutes_finite
        F ζ hζ t.val.val (hfin t) z).symm.eq]; group
  exact congrArg (fun v : Smooth F ζ hζ P => v.val.val x) (fiber_rightAction_of_conjugate_mem F ζ hζ P J f
    (groupArchChart F ζ hζ z * g) t.val
    (delta_compact_subgroup F ζ hζ H hc t) (hm ▸ hconj t))

theorem chart_fiber_mem_torusSmoothLevel
    (J U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) (g : G F ζ hζ)
    (hc : IsCompact (((KPGlobalTorusFunctionData.globalLevel F ζ hζ U).comap
      (KPGlobalTorusFunctionData.torus F ζ hζ).subtype) : Set (E F ζ hζ)))
    (hconj : ∀ t : (KPGlobalTorusFunctionData.globalLevel F ζ hζ U).comap
        (KPGlobalTorusFunctionData.torus F ζ hζ).subtype,
      g⁻¹ * t.val.val * g ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ J)
    (f : InducedLevel F ζ hζ P J) (z : GroupArch F) :
    (f.val.val (groupArchChart F ζ hζ z * g)).val ∈
      KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ P U := by
  constructor
  · have hle : KPGlobalTorusFunctionData.TorusSmoothUnion F ζ hζ P ≤
        KPGlobalTorusFunctionData.ArchSmooth P.H P.character.toMonoidHom
          (KPGlobalTorusFunctionData.torusArchChart F ζ hζ)
          (KPGlobalTorusFunctionData.torusArchDomain F) :=
      iSup_le fun _ => inf_le_left
    exact hle (f.val.val (groupArchChart F ζ hζ z * g)).property
  · intro t
    apply Subtype.ext
    funext x
    refine chart_fiber_rightLevel_of_compact_conjugate F ζ hζ P J g _ hc ?_ hconj
      f z t x
    intro t
    rcases t.property with ⟨a, ha, he⟩
    change a.val = t.val.val at he
    rw [← he]
    exact a.property

end

theorem exists_uniform_chart_fiber_level
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) (g : G F ζ hζ) :
    ∃ U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ,
      ∀ (P : Polarization F ζ hζ) (f : InducedLevel F ζ hζ P J) (z : GroupArch F),
        (f.val.val (groupArchChart F ζ hζ z * g)).val ∈
          KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ P U := by
  obtain ⟨U, hc, hconj⟩ := exists_compact_conjugate_torus_level F ζ hζ J g
  exact ⟨U, fun P f z =>
    chart_fiber_mem_torusSmoothLevel F ζ hζ P J U g hc hconj f z⟩

end
end DedekindZetaZeroFree.KPGlobalTorusBorelTwistCompatibilityBorelInduction.UniformFiberLevel

end
