module

public import NearlyMinimax.CardinalProductDesign
public import NearlyMinimax.ExponentialSpatialKernels
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Exact finite-product marginalization and subset kernel lifting on Q^k. -/
𝚫
𝛉
𝚨
𝚩

𝗃 𝔚 fun _ => ἀ
𝗇 𝔄 𝔚 μ
𝗇 𝔇 fun i => i ∈ s
𝗇 𝔈 𝔚 E
theorem pi_finset_subtype_instance_eq [Fintype I] [DecidableEq I]
    [MeasurableSpace E] (μ : Measure E) (s : Finset I) :
     @Measure.pi s 𝔈 (Subtype.fintype 𝔇)
      𝔚 inferInstance 𝔄 = Measure.pi 𝔄 := by
  congr 1
  exact Subsingleton.elim ..

𝗇 𝔅 f fun j => U j.val
𝗃 𝔛 ἀ → E
𝗇 𝔏 𝔛 s
𝗇 𝔑 {i : I // i ∉ s}
𝗇 𝔓 ∫ U : 𝔛 I, 𝔅 ∂Measure.pi 𝔄
𝗇 𝔖 ∫ V, f V ∂Measure.pi 𝔄
section

variable [Fintype I]
    [DecidableEq I]
    [MeasurableSpace E]
    (μ : Measure E)
    [IsFiniteMeasure μ]
    (s : Finset I)
    (f : 𝔏 → ℝ)

include μ s

𝗇 𝔔 μ.real univ ^ (Fintype.card I - s.card)
theorem finite_pi_subset_integral :
    𝔓 =
      𝔔 * 𝔖 := by
  let e := MeasurableEquiv.piEquivPiSubtypeProd 𝔈 𝔇
  have hp := measurePreserving_piEquivPiSubtypeProd 𝔄 𝔇
  rw [pi_finset_subtype_instance_eq μ s] at hp
  have he : 𝔓 =
      ∫ z : 𝔏 × 𝔛 𝔑, f z.1
        ∂(Measure.pi 𝔄).prod (Measure.pi 𝔄) := by
    have h := hp.symm.integral_comp' fun U => 𝔅
    simp_all
  rw [he, integral_fun_fst]
  have hc : (Measure.pi fun _ : 𝔑 => μ ).real univ =
      𝔔 := by
    simp only [measureReal_def, Measure.pi_univ]
    simp
  simp_all

theorem finite_pi_subset_integrable (hf : Integrable f $ Measure.pi 𝔄 ) :
    Integrable (fun U : 𝔛 I => 𝔅) $ Measure.pi 𝔄 := by
  have hp := measurePreserving_piEquivPiSubtypeProd 𝔄 𝔇
  rw [pi_finset_subtype_instance_eq μ s] at hp
  exact hp.integrable_comp_of_integrable $ hf.comp_fst _

end

𝗇 𝔉 𝘓₂
𝗇 𝔊 Fin k → Covariate d
𝗇 𝔘 k - s.card
𝗇 𝔍 2 ^ (d * 𝔘)
𝗇 𝔎 𝖪
𝗇 𝔙 f V ^ 2
𝗇 𝔐 fun V => 𝔙
theorem spatial_subset_square_integral (s : 𝔉)
    (f : (s → Covariate d) → ℝ) :
     ∫ U : 𝔊, 𝔅 ^ 2 ∂fullSpatialPatchDesign d k =
      𝔍 *
        ∫ V, 𝔙 ∂Measure.pi 𝔚 𝔎 := by
  rw [fullSpatialPatchDesign, finite_pi_subset_integral
    𝔎 s 𝔐]
  simp only [measureReal_def, Measure.restrict_apply_univ, Fintype.card_fin]
  change 𝗮₁ ^ 𝔘 * _ = _
  rw [spatialPatchBox_real_volume, ← pow_mul]

𝗇 𝔗 Fin s.card → Covariate d
def spatialSubsetConfiguration (s : 𝔉)
    (U : 𝔊) : 𝔗 :=
  fun j => U ((Fintype.equivFin s).symm $ Fin.cast (Fintype.card_coe s).symm j ).val

theorem spatialSubsetConfiguration_measurable (s : 𝔉) :
    Measurable $ spatialSubsetConfiguration (d := d) s := by
  apply Measurable.of_eval
  intro j
  exact measurable_pi_apply _

𝗃 𝔜 fun j => ἀ $ e.symm j
𝗇 𝔒 𝔜 U
theorem finite_pi_reindex_integral [Fintype I] [Fintype J]
    [MeasurableSpace E] (μ : Measure E) [SigmaFinite μ] (e : I ≃ J) (f : 𝔛 J → ℝ) :
     ∫ U : 𝔛 I, f 𝔒 ∂Measure.pi 𝔄 =
      𝔖 := by
  have h := (measurePreserving_piCongrLeft 𝔄 e).integral_comp' f
  have he U : (Equiv.piCongrLeft 𝔈 e) U =
      𝔒 := by
    funext j
    simp only [Equiv.piCongrLeft_apply_eq_cast, cast_eq]
  simp only [MeasurableEquiv.coe_piCongrLeft] at h
  simp_all

theorem spatial_subset_square_integral_enumerated (s : 𝔉)
    (f : 𝔗 → ℝ) :
     ∫ U : 𝔊, f (spatialSubsetConfiguration s U) ^ 2
      ∂fullSpatialPatchDesign d k = 𝔍 *
        ∫ V, 𝔙 ∂fullSpatialPatchDesign d s.card := by
  let e := (Fintype.equivFin s).trans $ finCongr $ Fintype.card_coe s
  have he (U : 𝔊) : spatialSubsetConfiguration s U =
      fun j => (fun l => U l.val) $ e.symm j := by
    funext j
    rfl
  simp_rw [he]
  rw [spatial_subset_square_integral s fun V => f 𝔜 V ]
  rw [finite_pi_reindex_integral 𝔎 e 𝔐]
  rfl
