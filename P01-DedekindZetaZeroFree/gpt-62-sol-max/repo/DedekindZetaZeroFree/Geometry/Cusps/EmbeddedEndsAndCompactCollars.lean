module

public import DedekindZetaZeroFree.Geometry.Cusps.MeanHeightDescent
public import DedekindZetaZeroFree.Geometry.ArithmeticQuotients.HausdorffTopology
public import DedekindZetaZeroFree.Eisenstein.Continuation.Cusps.CutoffSourceData

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal ContDiff
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPActualCollarBuffer

private theorem endSet_antitone
    (F : Type) [Field F] [NumberField F]
    (Γ : Subgroup (KPCuspArithmetic.PGL2 F)) (σ : KPCuspArithmetic.PGL2 F)
    {T₀ T : ℝ} (hT : T₀ ≤ T) :
    KPFiniteCuspAtlas.endSet F Γ σ T ⊆ KPFiniteCuspAtlas.endSet F Γ σ T₀ := by
  apply Set.image_mono
  apply Set.image_mono
  intro z hz
  exact lt_of_le_of_lt hT hz

theorem actual_end_charts_compact_collars
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (U : CompactOpenLevel (KPFiniteCuspAtlas.FiniteCover F ζ hζ))
    (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (τ T : ℝ) (hτ : A.threshold ≤ τ) (hT : τ < T) :
    (∀ a, IsOpen (endSet A τ a)) ∧
    Pairwise (fun a b => Disjoint (endSet A τ a) (endSet A τ b)) ∧
    IsCompact (KPCutoffSource.closedCollars (endSet A τ) (height A τ) T) := by
  classical
  letI : T2Space (KPFiniteCuspAtlas.rawXU F ζ hζ U) :=
    CoreChartLocalizers.quotient_hausdorff F ζ hζ hF U A
  refine ⟨end_open A τ, ?_, ?_⟩
  · intro a b hab
    refine Set.disjoint_left.mpr fun z hza hzb => ?_
    obtain ⟨x, hx, rfl⟩ := hza
    obtain ⟨y, hy, he⟩ := hzb
    have he' : A.components ⟨b.1, y⟩ = A.components ⟨a.1, x⟩ := by
      rw [A.components_formula, A.components_formula]
      exact he
    obtain ⟨hij, hyx⟩ := Sigma.mk.inj_iff.mp (A.components.injective he')
    rcases a with ⟨i, ai⟩
    rcases b with ⟨j, bj⟩
    simp only at hij
    subst j
    have hyx' : y = x := eq_of_heq hyx
    subst y
    have hne : ai ≠ bj := fun h => hab (by rw [h])
    have hd := (A.cuspAtlas i).disjoint_ends hne
    exact Set.disjoint_left.mp hd
      (endSet_antitone F _ _ (by rw [A.common_threshold]; exact hτ) hx)
      (endSet_antitone F _ _ (by rw [A.common_threshold]; exact hτ) hy)
  · rw [KPCutoffSource.closedCollars]
    apply isCompact_iUnion
    intro a
    suffices hc : IsCompact {x | x ∈ endSet A τ a ∧ height A τ a x ∈ Set.Icc T (T+1)} by
      simpa only [hc.isClosed.closure_eq] using hc
    letI : CompactSpace (KPCuspCharts.CrossQuotient F (Stabilizer A a)) :=
      ((A.cuspAtlas a.1).geometry a.2).compact_cross
    letI : CompactSpace (Set.Icc T (T+1)) := isCompact_iff_compactSpace.mp isCompact_Icc
    let lift : Set.Icc T (T+1) → Set.Ioi τ := fun t => ⟨t.val, hT.trans_le t.property.1⟩
    let f := radialChart A τ a ∘ Prod.map id lift
    have hc : Continuous f := (radialChart_embedding A hτ a).continuous.comp (by
      apply Continuous.prodMap continuous_id
      exact continuous_subtype_val.subtype_mk _)
    convert isCompact_range hc using 1
    ext x
    constructor
    · rintro ⟨hx, htx⟩
      rw [← chartLift_range A τ a] at hx
      obtain ⟨z,hz,rfl⟩ := hx
      rw [height_coordinates A hτ a z hz] at htx
      exact ⟨(Quotient.mk _ z.1, ⟨z.2,htx⟩), radialChart_mk A τ a z hz⟩
    · rintro ⟨⟨q,t⟩, rfl⟩
      obtain ⟨v,rfl⟩ := Quotient.mk_surjective q
      have hτt := hT.trans_le t.property.1
      change radialChart A τ a (Quotient.mk _ v, lift t) ∈ _
      rw [show lift t = (⟨t.val,hτt⟩ : Set.Ioi τ) from rfl, radialChart_mk A τ a (v,t.val) hτt]
      exact ⟨(chartLift_range A τ a) ▸ Set.mem_image_of_mem _ hτt,
        (height_coordinates A hτ a (v,t.val) hτt).symm ▸ t.property⟩

end DedekindZetaZeroFree.KPActualCollarBuffer

end
