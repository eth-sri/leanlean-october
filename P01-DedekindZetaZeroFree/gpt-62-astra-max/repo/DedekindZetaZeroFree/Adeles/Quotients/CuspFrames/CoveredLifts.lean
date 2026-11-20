module
public import DedekindZetaZeroFree.Adeles.Quotients.Cusps.CuspFrames

public import DedekindZetaZeroFree.Adeles.Quotients.CuspFrames.Definitions

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped Classical NumberField Topology
namespace DedekindZetaZeroFree.KPMsGreenFlux.ActualFrames
open KPAdelicCoverRestrictedProduct
open KPMsGreenFlux
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
private theorem projection_compare (g : Cover F ζ hζ) (w : NumberField.InfinitePlace F) :
    PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ g w =
      Matrix.ProjGenLinGroup.map
        (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (KPHilbert.infinite_isComplex F ζ hζ w)).toRingHom
        (KPCuspGenuineMonodromy.archProjection F ζ hζ g w) := by apply @DedekindZetaZeroFree.KPMsFixedHaar.archProjection_compare <;> assumption

theorem arch_finite_factorization (g : Cover F ζ hζ) :
    ∃ (a : KPSmoothActualFlowData.GInfinity F) (c : KPFiniteCuspAtlas.FiniteCover F ζ hζ),
      g = KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a * c.val := by apply @DedekindZetaZeroFree.KPMsActualCuspSource.arch_finite_factorization <;> assumption

def archRational (σ : KPCuspArithmetic.PGL2 F) : KPSmoothActualFlowData.GInfinity F :=
  fun v => Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map v.embedding σ.out)

private theorem rationalLift_mk (m : Matrix.GeneralLinearGroup (Fin 2) F) :
    rationalLift F ζ hζ (Matrix.ProjGenLinGroup.mk m) =
      scalarQuotient F ζ hζ (rationalHom F ζ hζ m) := by
  let n := Classical.choose (Matrix.ProjGenLinGroup.mk_surjective (Matrix.ProjGenLinGroup.mk m))
  obtain ⟨z, hz⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp (Classical.choose_spec (Matrix.ProjGenLinGroup.mk_surjective (Matrix.ProjGenLinGroup.mk m)))
  let φ := (scalarQuotient F ζ hζ).comp (rationalHom F ζ hζ)
  have hscalar :=
    KPRationalAdelicSplitting.rationalScalars_le_ker F ζ hζ ⟨z, rfl⟩
  change φ n = φ m
  rw [← hz, map_mul, hscalar, mul_one]

private theorem rationalLift_archProjection (σ : KPCuspArithmetic.PGL2 F) :
    PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ (rationalLift F ζ hζ σ) = archRational F σ := by
  have hs : σ = Matrix.ProjGenLinGroup.mk σ.out := (Quotient.out_eq σ).symm
  rw [hs, rationalLift_mk]
  funext w
  change Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map _
    (projection F ζ hζ (rationalSection F ζ hζ σ.out))) = _
  rw [projection_rationalSection]
  have hmap : (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F ζ hζ w)).toRingHom.comp
      ((adeleEval F (Sum.inl w)).comp (algebraMap F (Adeles F))) = w.embedding := by
    ext x
    change NumberField.InfinitePlace.Completion.extensionEmbedding w
      (algebraMap F w.Completion x) = w.embedding x
    change NumberField.InfinitePlace.Completion.extensionEmbedding w
      ((WithAbs.equiv w.1).symm x : w.Completion) = _
    simp
  change Matrix.ProjGenLinGroup.mk
    (Matrix.GeneralLinearGroup.map _ (Matrix.GeneralLinearGroup.map _ σ.out)) = _
  simp only [← MonoidHom.comp_apply, ← Matrix.GeneralLinearGroup.map_comp]
  rw [RingHom.comp_assoc, hmap]
  unfold archRational
  simp only [MonoidHom.comp_apply]
  rw [← Matrix.ProjGenLinGroup.map_mk, ← Matrix.ProjGenLinGroup.map_mk]
  exact congrArg (Matrix.ProjGenLinGroup.map w.embedding)
    (Quotient.out_eq (Matrix.ProjGenLinGroup.mk σ.out)).symm

private alias finiteProjection_local_infinite := DedekindZetaZeroFree.KPMsActualCuspSource.finiteProjection_local_infinite

private alias finiteProjection_insertion := DedekindZetaZeroFree.KPMsActualCuspSource.finiteProjection_insertion

private theorem finiteProjection_rationalLift (σ : KPCuspArithmetic.PGL2 F) :
    KPCuspGenuineMonodromy.finiteProjection F ζ hζ
      (rationalLift F ζ hζ σ) = KPFiniteComponents.diagonal F σ := by
  obtain ⟨m, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective σ
  rw [rationalLift_mk]
  exact congrArg (fun k => Matrix.ProjGenLinGroup.mk
    (Matrix.GeneralLinearGroup.map (RingHom.snd _ _) k))
      (projection_rationalSection F ζ hζ m)

theorem rationalLift_finite_factor (γ : KPCuspArithmetic.PGL2 F) :
    ∃ ε : rootsOfUnity 3 F,
      rationalLift F ζ hζ γ = KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (archRational F γ) *
        ((KPCuspGenuineMonodromy.central F ζ hζ ε *
          KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ) : KPFiniteCuspAtlas.FiniteCover F ζ hζ) := by
  obtain ⟨a, s, hs⟩ := arch_finite_factorization F ζ hζ (rationalLift F ζ hζ γ)
  have ha : a = archRational F γ := by
    have h := congrArg (PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ) hs
    have hf : PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ s.val = 1 := by
      funext w
      rw [projection_compare]
      have hh := MonoidHom.mem_ker.mp s.property
      rw [hh]
      exact map_one _
    rw [map_mul, hf, mul_one, rationalLift_archProjection] at h
    change archRational F γ = PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ
      (PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ a) at h
    rw [PGLComplex.AdelicSlicesRaw.archProjection_archimedeanInsertion] at h
    exact h.symm
  subst a
  have hp := congrArg (KPCuspGenuineMonodromy.finiteProjection F ζ hζ) hs
  simp only [finiteProjection_rationalLift, map_mul, finiteProjection_insertion, one_mul] at hp
  have hf : KPCuspGenuineMonodromy.finiteBase F ζ hζ s =
      KPCuspGenuineMonodromy.finiteBase F ζ hζ (KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ) := by
    rw [← MonoidHom.comp_apply, (KPCuspGenuineMonodromy.finite_cover_exact F ζ hζ).2.2]
    exact hp.symm
  have hm : s * (KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ)⁻¹ ∈
      (KPCuspGenuineMonodromy.central F ζ hζ).range := by
    rw [(KPCuspGenuineMonodromy.finite_cover_exact F ζ hζ).1, MonoidHom.mem_ker,
      map_mul, map_inv, hf, mul_inv_cancel]
  obtain ⟨ε, hε⟩ := hm
  refine ⟨ε, ?_⟩
  have he : s = KPCuspGenuineMonodromy.central F ζ hζ ε *
      KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ := by
    rw [hε]
    group
  exact hs.trans (congrArg (fun c : KPFiniteCuspAtlas.FiniteCover F ζ hζ =>
    KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (archRational F γ) * c.val) he)

 alias insertion_commutes := DedekindZetaZeroFree.KPMsActualCuspSource.insertion_commutes

private alias central_comm := DedekindZetaZeroFree.KPMsActualCuspSource.central_comm

private alias projective_action_mk := DedekindZetaZeroFree.KPMsFixedHaar.projective_action_mk

 theorem archBasepoint_rational_mul (γ : KPCuspArithmetic.PGL2 F)
    (a : KPSmoothActualFlowData.GInfinity F) :
    KPMsFixedHaarDisintegration.archBasepoint F (archRational F γ * a) =
      KPCuspSiegel.action F γ (KPMsFixedHaarDisintegration.archBasepoint F a) := by apply @DedekindZetaZeroFree.KPMsActualCuspSource.archBasepoint_rational_mul <;> assumption

variable {F ζ hζ}
variable {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
    (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)

variable (j : Cusps A) (Y : ℝ) (x : X F ζ hζ) (hx : x ∈ cuspEnd A P j Y)

include hx in
theorem spherical_cusp_representative :
    ∃ (p : KPCuspCharts.Cross F) (t : ℝ),
      KPMsFixedHaarDisintegration.logHeight (F := F) Y < t ∧
      P.projection (U) x = Quotient.mk _
        (KPCuspSiegel.action F
          ((A.cuspAtlas j.1).representative j.2)
          (KPCuspCharts.toArch F (p,t)),
          A.representative j.1) := by
  obtain ⟨z, hz, he⟩ := hx
  obtain ⟨q, hq, rfl⟩ := hz
  obtain ⟨v, hv, rfl⟩ := hq
  let hd := KPCuspCharts.positive_dimension F hF
  let c := (KPCuspCharts.toArchHomeomorph F hd).symm v
  have hc : KPCuspCharts.toArch F c = v :=
    (KPCuspCharts.toArchHomeomorph F hd).apply_symm_apply v
  refine ⟨c.1, c.2, ?_, ?_⟩
  · change KPMsFixedHaarDisintegration.logHeight (F := F) Y <
      KPCuspLogShape.meanHeight _ v at hv
    rw [← hc, KPCuspCharts.toArch_meanHeight F hd] at hv
    exact hv
  · rw [← he, ← hc]
    rfl

include hx in
theorem cuspLift_exists :
    ∃ g : Cover F ζ hζ,
      KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g = x ∧
      AdmissibleFrame A j Y x g := by
  obtain ⟨p, t, ht, hx'⟩ := spherical_cusp_representative A P j Y x hx
  obtain ⟨a, c, hc⟩ := arch_finite_factorization F ζ hζ (Quotient.out x)
  have hqx : KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
      (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a * c.val) = x := by
    rw [← hc]
    exact Quotient.out_eq x
  have he := (P.formula (U) a c).symm.trans
    ((congrArg (P.projection (U)) hqx).trans hx')
  obtain ⟨γ, ε, u, ha, hf⟩ := Quotient.exact he
  change A.representative j.1 =
    KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ *
      KPCuspGenuineMonodromy.central F ζ hζ ε * c * u.val at hf
  obtain ⟨η, hγ⟩ := rationalLift_finite_factor F ζ hζ γ
  let a' := archRational F γ * a
  let ε' := η * ε⁻¹
  let u' : U.toOpenSubgroup := u⁻¹
  let g' := rationalLift F ζ hζ γ * Quotient.out x
  have hgx : KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g' = x := by
    change Quotient.mk (QuotientGroup.rightRel
      (KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ)) _ = _
    rw [← Quotient.out_eq x]
    apply Quotient.sound
    have hrat : rationalLift F ζ hζ γ ∈ KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ := by
      let m := Classical.choose (Matrix.ProjGenLinGroup.mk_surjective γ)
      exact ⟨KPRationalAdelicSplitting.rationalPGLQuotient F m,
        KPRationalAdelicSplitting.rationalPGLHom_mk F ζ hζ m⟩
    exact ⟨⟨rationalLift F ζ hζ γ, hrat⟩, rfl⟩
  refine ⟨g', hgx, hgx, a', p, t, ε', u', ht, ?_, ?_⟩
  · rw [archBasepoint_rational_mul]
    exact ha.symm
  · change rationalLift F ζ hζ γ * Quotient.out x = _
    rw [hc, hγ]
    have hm := (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.1
    change _ = KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (archRational F γ * a) * _ * _ * _
    rw [hm]
    rw [mul_assoc, ← mul_assoc
      ((KPCuspGenuineMonodromy.central F ζ hζ η * KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ) :
        KPFiniteCuspAtlas.FiniteCover F ζ hζ).val,
      (insertion_commutes F ζ hζ a _).symm.eq]
    have hfin : KPCuspGenuineMonodromy.central F ζ hζ η *
        KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ * c =
        A.representative j.1 *
          KPCuspGenuineMonodromy.central F ζ hζ ε' * (u⁻¹).val := by
      calc
        _ = KPCuspGenuineMonodromy.central F ζ hζ η *
          KPCuspGenuineMonodromy.central F ζ hζ ε⁻¹ *
          A.representative j.1 * (u⁻¹).val := by
            rw [hf, map_inv]
            rw [← central_comm F ζ hζ ε (KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ)]
            change _ = _ * _ * _ * (u.val)⁻¹
            group
        _ = _ := by
          rw [← map_mul, central_comm]
    have hfin' := congrArg Subtype.val hfin
    dsimp only [a', ε', u'] at *
    simp only [Subgroup.coe_mul] at hfin'
    change _ = _ at hfin'
    simpa only [mul_assoc, Subgroup.coe_mul, KPCuspGenuineMonodromy.central,
      MonoidHom.codRestrict_apply, KPSmoothLocalQuotientCharts.centreMap] using congrArg
      (fun k : Cover F ζ hζ => KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (archRational F γ) *
        KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a * k) hfin'
end DedekindZetaZeroFree.KPMsGreenFlux.ActualFrames

end
