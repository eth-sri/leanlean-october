module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.GenuineSector.TestEnergy

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree
namespace KPMeasurableLocalL2

open MeasureTheory Filter
open scoped Topology

variable {X E Γ : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [MeasurableSpace E] [BorelSpace E] [Group Γ] [Fintype Γ]

structure Data (X E Γ : Type*) [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [MeasurableSpace E] [BorelSpace E] [Group Γ] [Fintype Γ] where
  measure : Measure X
  action : Γ → X ≃ᵐ X
  action_one : ∀ x, action 1 x = x
  action_mul : ∀ γ δ x, action (γ * δ) x = action γ (action δ x)
  invariant_measure : ∀ γ, MeasurePreserving (action γ) measure measure
  tensor : Γ → X → E ≃ₗᵢ[ℂ] E
  measurable_tensor : ∀ γ, Measurable (fun p : X × E => tensor γ p.1 p.2)
  tensor_one : ∀ x, tensor 1 x = LinearIsometryEquiv.refl ℂ E
  tensor_mul : ∀ γ δ x v,
    tensor (γ * δ) x v = tensor γ (action δ x) (tensor δ x v)

variable (D : Data X E Γ)

structure Piece where
  set : Set X
  measurableSet : MeasurableSet set
  invariant : ∀ γ x, D.action γ x ∈ set ↔ x ∈ set

section

variable (S : Piece D)

def SupportedCovariant (f : Lp E 2 D.measure) : Prop :=
  (∀ γ : Γ, ∀ᵐ x ∂D.measure, f (D.action γ x) = D.tensor γ x (f x)) ∧
    (∀ᵐ x ∂D.measure, x ∉ S.set → f x = 0)

def Q : Submodule ℂ (Lp E 2 D.measure) where
  carrier := {f | SupportedCovariant D S f}
  zero_mem' := by
    refine ⟨?_, ?_⟩
    · intro γ
      filter_upwards [(D.invariant_measure γ).quasiMeasurePreserving.ae
        (Lp.coeFn_zero E 2 D.measure), Lp.coeFn_zero E 2 D.measure] with x h1 h2
      rw [h1, h2, Pi.zero_apply, Pi.zero_apply, map_zero]
    · filter_upwards [Lp.coeFn_zero E 2 D.measure] with x hx _
      exact hx
  add_mem' := by
    intro f g hf hg
    refine ⟨?_, ?_⟩
    · intro γ
      filter_upwards [(D.invariant_measure γ).quasiMeasurePreserving.ae_eq_comp
          (Lp.coeFn_add f g), Lp.coeFn_add f g, hf.1 γ, hg.1 γ] with x h1 h2 h3 h4
      simp only [Function.comp_apply] at h1
      simp only [h1, h2, Pi.add_apply, map_add, h3, h4]
    · filter_upwards [Lp.coeFn_add f g, hf.2, hg.2] with x h1 h2 h3 hx
      rw [h1, Pi.add_apply, h2 hx, h3 hx, add_zero]
  smul_mem' := by
    intro c f hf
    refine ⟨?_, ?_⟩
    · intro γ
      filter_upwards [(D.invariant_measure γ).quasiMeasurePreserving.ae_eq_comp
          (Lp.coeFn_smul c f), Lp.coeFn_smul c f, hf.1 γ] with x h1 h2 h3
      simp only [Function.comp_apply, Pi.smul_apply] at h1 h2
      rw [h1, h2, map_smul, h3]
    · filter_upwards [Lp.coeFn_smul c f, hf.2] with x h1 h2 hx
      rw [h1, Pi.smul_apply, h2 hx, smul_zero]

@[simp] theorem mem_Q_iff (f : Lp E 2 D.measure) :
    f ∈ Q D S ↔ SupportedCovariant D S f := Iff.rfl

theorem Q_isClosed : IsClosed (Q D S : Set (Lp E 2 D.measure)) := by
  rw [← isSeqClosed_iff_isClosed]
  intro u f hu hlim
  have hu' := fun n => (mem_Q_iff D S (u n)).mp (hu n)
  refine (mem_Q_iff D S f).mpr ⟨?_, ?_⟩
  · intro γ
    obtain ⟨ns, -, hns⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
    filter_upwards [hns, (ae_all_iff.mpr fun k => (hu' (ns k)).1 γ), ((D.invariant_measure γ).quasiMeasurePreserving.ae hns)] with x hx hcovx hx2
    have h3 :=
      ((D.tensor γ x).continuous.tendsto (f x)).comp hx
    have h4 : Tendsto (fun k => D.tensor γ x (u (ns k) x)) atTop (𝓝 (f (D.action γ x))) := by
      rw [show (fun k => D.tensor γ x (u (ns k) x)) =
        (fun k => u (ns k) (D.action γ x)) from funext fun k => (hcovx k).symm]
      exact hx2
    exact tendsto_nhds_unique h4 h3
  · obtain ⟨ns, -, hns⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
    filter_upwards [hns, (ae_all_iff.mpr fun k => (hu' (ns k)).2)] with x hx hsupx
    intro hxs
    apply tendsto_nhds_unique hx
    rw [show (fun k => u (ns k) x) = fun _ => (0 : E) from funext fun k => hsupx k hxs]
    exact tendsto_const_nhds

end

instance Q_innerProductSpace (S : Piece D) : InnerProductSpace ℂ (Q D S) :=
  inferInstanceAs (InnerProductSpace ℂ ↥(Q D S))

instance Q_completeSpace (S : Piece D) : CompleteSpace (Q D S) := by
  letI : CompleteSpace E := FiniteDimensional.complete ℂ E
  exact (Q_isClosed D S).completeSpace_coe

section

variable (S : Piece D) (f g : Q D S)

theorem Q_inner_eq_integral :
    inner ℂ f g = ∫ x, inner ℂ ((f : Lp E 2 D.measure) x)
      ((g : Lp E 2 D.measure) x) ∂D.measure := by
  rfl

theorem Q_integrable_inner :
    Integrable (fun x => inner ℂ ((f : Lp E 2 D.measure) x)
      ((g : Lp E 2 D.measure) x)) D.measure :=
  L2.integrable_inner (f : Lp E 2 D.measure) (g : Lp E 2 D.measure)

end

def fixedFiber (x : X) : Submodule ℂ E where
  carrier := {v | ∀ γ : Γ, D.action γ x = x → D.tensor γ x v = v}
  zero_mem' := by intro γ _; simp
  add_mem' := by
    intro a b ha hb γ hγ
    rw [map_add, ha γ hγ, hb γ hγ]
  smul_mem' := by
    intro c a ha γ hγ
    rw [map_smul, ha γ hγ]

@[simp] theorem mem_fixedFiber_iff (x : X) (v : E) :
    v ∈ fixedFiber D x ↔
      ∀ γ : Γ, D.action γ x = x → D.tensor γ x v = v := Iff.rfl

def supportedAverage (S : Piece D) (h : X → E) : X → E :=
  S.set.indicator (fun x => (Fintype.card Γ : ℂ)⁻¹ •
    ∑ γ : Γ, (D.tensor γ x).symm (h (D.action γ x)))

 def avgField (h : X → E) : X → E :=
  fun y => (Fintype.card Γ : ℂ)⁻¹ •
    ∑ γ : Γ, (D.tensor γ y).symm (h (D.action γ y))

private lemma supportedAverage_eq (S : Piece D) (h : X → E) :
    supportedAverage D S h = S.set.indicator (avgField D h) := rfl

private lemma tensor_mul_symm (δ γ : Γ) (x : X) (w : E) :
    (D.tensor δ (D.action γ x)).symm w =
      D.tensor γ x ((D.tensor (δ * γ) x).symm w) := by
  simpa [LinearIsometryEquiv.symm_apply_eq, LinearIsometryEquiv.apply_symm_apply] using D.tensor_mul δ γ x ((D.tensor (δ * γ) x).symm w)

section

variable (S : Piece D) (h : X → E)

theorem supportedAverage_measurable
    (hh : Measurable h) : Measurable (supportedAverage D S h) := by
  haveI : SecondCountableTopology E := by
    exact Homeomorph.secondCountableTopology (ContinuousLinearEquiv.ofFinrankEq (Eq.symm (Module.finrank_fin_fun ℂ))).toHomeomorph
  haveI : MeasurableAdd₂ E := inferInstance
  rw [supportedAverage_eq]
  refine Measurable.indicator ?_ S.measurableSet
  refine Measurable.const_smul ?_ _
  refine Finset.measurable_sum _ fun δ _ => ?_
  have hfun : (fun x => (D.tensor δ x).symm (h (D.action δ x)))
      = fun x => ∑ i, inner ℂ (D.tensor δ x ((stdOrthonormalBasis ℂ E) i))
          (h (D.action δ x)) • (stdOrthonormalBasis ℂ E) i := by
    funext x
    let T := (D.tensor δ x)
    let w := (h (D.action δ x))
    conv_lhs => rw [← (stdOrthonormalBasis ℂ E).sum_repr' (T.symm w)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← LinearIsometryEquiv.inner_map_map T ((stdOrthonormalBasis ℂ E) i) (T.symm w),
      LinearIsometryEquiv.apply_symm_apply]
  rw [hfun]
  refine Finset.measurable_sum _ fun i _ => ?_
  refine ((continuous_id.smul continuous_const).measurable.comp ?_)
  exact (continuous_inner).measurable.comp (Measurable.prodMk
    ((D.measurable_tensor δ).comp (measurable_id.prodMk measurable_const))
    (hh.comp (D.action δ).measurable))

theorem supportedAverage_covariant (γ : Γ) (x : X) :
    supportedAverage D S h (D.action γ x) =
      D.tensor γ x (supportedAverage D S h x) := by
  rw [supportedAverage_eq]
  by_cases hx : x ∈ S.set
  · rw [Set.indicator_of_mem ((S.invariant γ x).mpr hx) _, Set.indicator_of_mem hx _]
    rw [show avgField D h = (fun y => (Fintype.card Γ : ℂ)⁻¹ •
        ∑ δ : Γ, (D.tensor δ y).symm (h (D.action δ y))) from rfl]
    dsimp only
    rw [map_smul, map_sum]
    congr 1
    rw [show ∑ δ : Γ, (D.tensor δ (D.action γ x)).symm (h (D.action δ (D.action γ x)))
        = ∑ δ : Γ, D.tensor γ x ((D.tensor (δ * γ) x).symm (h (D.action (δ * γ) x))) from
      Finset.sum_congr rfl fun δ _ => by
        rw [tensor_mul_symm D δ γ x]
        congr 1
        rw [← D.action_mul]]
    exact Equiv.sum_comp (Equiv.mulRight γ)
      (fun δ => D.tensor γ x ((D.tensor δ x).symm (h (D.action δ x))))
  · rw [Set.indicator_of_notMem (fun hc => hx ((S.invariant γ x).mp hc)) _, Set.indicator_of_notMem hx _, map_zero]

theorem supportedAverage_zero_off (x : X)
    (hx : x ∉ S.set) : supportedAverage D S h x = 0 := by
  simp_all [supportedAverage_eq]

end

theorem supportedAverage_ae_eq (S : Piece D) (f : Q D S) (h : X → E)
    (hh : h =ᵐ[D.measure] (f : Lp E 2 D.measure)) :
    supportedAverage D S h =ᵐ[D.measure] (f : Lp E 2 D.measure) := by
  have hcov : ∀ᵐ x ∂D.measure, ∀ δ : Γ,
      h (D.action δ x) = D.tensor δ x ((f : Lp E 2 D.measure) x) := by
    refine ae_all_iff.mpr fun δ => ?_
    filter_upwards [(D.invariant_measure δ).quasiMeasurePreserving.ae hh, (f.2).1 δ] with x h1 h2
    rw [h1, h2]
  filter_upwards [hcov, (f.2).2] with x hcovx hsupx
  rw [supportedAverage_eq]
  by_cases hx : x ∈ S.set
  · rw [Set.indicator_of_mem hx _, avgField]
    have hsum : ∀ δ : Γ, (D.tensor δ x).symm (h (D.action δ x)) =
        (f : Lp E 2 D.measure) x := by
      intro δ
      rw [hcovx δ, LinearIsometryEquiv.symm_apply_apply]
    simp [Finset.sum_congr rfl fun δ _ => hsum δ]
    rw [← Nat.cast_smul_eq_nsmul ℂ]
    simp
  · rw [Set.indicator_of_notMem hx _, hsupx hx]

def borelVersion (f : Lp E 2 D.measure) : X → E :=
  (Lp.aestronglyMeasurable f).mk f

variable (S : Piece D) (f : Q D S)

def representative : X → E :=
  supportedAverage D S (borelVersion D (f : Lp E 2 D.measure))

theorem representative_spec :
    Measurable (representative D S f) ∧
    (representative D S f =ᵐ[D.measure] (f : Lp E 2 D.measure)) ∧
    (∀ x, x ∉ S.set → representative D S f x = 0) ∧
    (∀ γ x, representative D S f (D.action γ x) =
      D.tensor γ x (representative D S f x)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact supportedAverage_measurable D S _
      (Lp.aestronglyMeasurable (f : Lp E 2 D.measure)).stronglyMeasurable_mk.measurable
  · exact supportedAverage_ae_eq D S f _
      (Lp.aestronglyMeasurable (f : Lp E 2 D.measure)).ae_eq_mk.symm
  · apply supportedAverage_zero_off
  · apply supportedAverage_covariant

theorem representative_memLp :
    MemLp (representative D S f) 2 D.measure :=
  (Lp.memLp (f : Lp E 2 D.measure)).ae_eq (representative_spec D S f).2.1.symm

end KPMeasurableLocalL2
end DedekindZetaZeroFree

end
