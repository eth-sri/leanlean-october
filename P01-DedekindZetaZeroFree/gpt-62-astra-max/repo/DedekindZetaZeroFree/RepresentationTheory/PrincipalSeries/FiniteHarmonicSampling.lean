module
public import DedekindZetaZeroFree.Algebra.LinearAlgebra.FunctionInterpolation

public import DedekindZetaZeroFree.Eisenstein.Induction.ScalarCompactPicturesAndLocalQuotientTensors
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.HolomorphicKTypeGeneration

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped Classical BigOperators TensorProduct Topology

namespace DedekindZetaZeroFree.KPLiteralScalarArchIndependentSlices

 def pointEvaluation {X : Type*} (S : Submodule ℂ (X → ℂ)) (x : X) :
    Module.Dual ℂ S := (LinearMap.proj x).comp S.subtype

alias finite_interpolation := DedekindZetaZeroFree.FiniteFunctionSpaces.exists_finite_evaluation_interpolation

 def partialProducts {ι X : Type*} [Fintype ι] (S : ι → Submodule ℂ (X → ℂ))
    (s : Finset ι) : Submodule ℂ ((ι → X) → ℂ) :=
  Submodule.span ℂ (Set.range (fun f : ∀ i, S i => fun a => ∏ i ∈ s, (f i).val (a i)))

section

variable {ι X : Type*} [Fintype ι]

private theorem partialProducts_mul [DecidableEq ι]
    (S : ι → Submodule ℂ (X → ℂ)) (s : Finset ι) (w : ι) (hw : w ∉ s)
    (f : S w) (h : (ι → X) → ℂ) (hh : h ∈ partialProducts S s) :
    (fun a => f.val (a w) * h a) ∈ partialProducts S (insert w s) := by
  refine Submodule.span_induction

    ?_ ?_ ?_ ?_ hh
  · rintro _ ⟨g, rfl⟩
    apply Submodule.subset_span
    refine ⟨Function.update g w f, ?_⟩
    funext a
    dsimp only
    rw [Finset.prod_insert hw]
    simp only [Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    rw [Function.update_of_ne (ne_of_mem_of_not_mem hi hw)]
  · simpa only [Pi.zero_def, mul_zero] using
      (Submodule.zero_mem (partialProducts S (insert w s)))
  · intro h k _ _ hh hk
    simpa only [Pi.add_def, mul_add] using Submodule.add_mem _ hh hk
  · intro c h _ hh
    simpa only [Pi.smul_def, smul_eq_mul, mul_left_comm] using Submodule.smul_mem _ c hh

private theorem tensor_interpolation [DecidableEq ι]
    (S : ι → Submodule ℂ (X → ℂ)) (n : ι → ℕ)
    (x : ∀ i, Fin (n i) → X) (b : ∀ i, Fin (n i) → S i)
    (s : Finset ι) (h : (ι → X) → ℂ) (a₀ : ι → X)
    (hh : ∀ w ∈ s, ∀ a, h a = ∑ j, h (Function.update a w (x w j)) * (b w j).val (a w))
    (hd : ∀ a, h a = h (fun i => if i ∈ s then a i else a₀ i)) :
    h ∈ partialProducts S s := by
  induction s using Finset.induction_on generalizing h with
  | empty =>
    have he : h = fun _ => h a₀ := by funext a; exact hd a
    rw [he]
    have h1 : (fun _ : ι → X => (1 : ℂ)) ∈ partialProducts S ∅ :=
      Submodule.subset_span ⟨fun _ => 0, by simp⟩
    simpa only [Pi.smul_def, smul_eq_mul, mul_one] using Submodule.smul_mem _ (h a₀) h1
  | @insert w s hw ih =>
    have hqi : ∀ j : Fin (n w), (fun a => h (Function.update a w (x w j))) ∈ partialProducts S s := by
      intro j
      apply ih
      · intro v hv a
        have hne := ne_of_mem_of_not_mem hv hw
        simpa only [Function.update_of_ne hne, Function.update_comm hne] using (hh v (Finset.mem_insert_of_mem hv) (Function.update a w (x w j)))
      · intro a
        have hi := hd (Function.update a w (x w j))
        rw [hi, (hd (Function.update (fun i => if i ∈ s then a i else a₀ i) w (x w j)))]
        congr 1
        funext i
        by_cases hi : i = w
        · subst i; simp
        · by_cases his : i ∈ s <;> simp [hi, his]
    have he : h = ∑ j, (fun a => (b w j).val (a w) * h (Function.update a w (x w j))) := by
      funext a
      simpa only [Finset.sum_apply, mul_comm] using hh w (Finset.mem_insert_self w s) a
    rw [he]
    exact Submodule.sum_mem _ (fun j _ => partialProducts_mul S s w hw (b w j) _ (hqi j))

theorem independent_slices_mem_product_span [DecidableEq ι] [Nonempty X]
    (S : ι → Submodule ℂ (X → ℂ)) [∀ i, FiniteDimensional ℂ (S i)]
    (h : (ι → X) → ℂ)
    (hh : ∀ i a, (fun x => h (Function.update a i x)) ∈ S i) :
    h ∈ Submodule.span ℂ (Set.range (fun f : ∀ i, S i => fun a => ∏ i, (f i).val (a i))) := by
  choose n x b hb using fun i => finite_interpolation (S i)
  apply tensor_interpolation S n x b Finset.univ h (fun _ => Classical.choice ‹Nonempty X›)
  · intro i _ a
    simpa using (hb i ⟨_, hh i a⟩ (a i))
  · intro a
    simp

end

open KPCplxPrincipalSeriesCharts KPCplxIntertwinerEigenvalues

variable (s : ℝ) (N : ℕ)

abbrev harmonicBand : Submodule ℂ (PrincipalSeries s) :=
  (Finset.range (N + 1)).sup (harmonicKType s)

theorem harmonicBand_finite :
    Module.Finite ℂ (harmonicBand s N) := by
  have h (I : Finset ℕ) : Module.Finite ℂ ↥(I.sup (harmonicKType s)) := by
    induction I using Finset.induction_on with
    | empty =>
      rw [Finset.sup_empty]
      infer_instance
    | @insert i I hi ih =>
      let : Module.Finite ℂ (harmonicKType s i) :=
        KPCplxHarmonicIntertwinerSpectrum.harmonicKType_finite s i
      let : Module.Finite ℂ ↥(I.sup (harmonicKType s)) := ih
      rw [Finset.sup_insert]
      infer_instance
  exact h _

def harmonicBandEvaluation :
    harmonicBand s N →ₗ[ℂ] (KPCplxCharacterHaar.ComplexGL2 → ℂ) :=
  (principalSeriesSubmodule s).subtype.comp (harmonicBand s N).subtype

end DedekindZetaZeroFree.KPLiteralScalarArchIndependentSlices

namespace DedekindZetaZeroFree.KPLiteralScalarArchUniformBands
open KPCplxPrincipalSeriesCharts KPCplxIntertwinerEigenvalues
open KPLiteralScalarArchIndependentSlices

theorem invariant_subspace_le_band (s : ℝ)
    (U : Submodule ℂ (PrincipalSeries s)) [FiniteDimensional ℂ U]
    (hU : IsKInvariant s U) :
    U ≤ harmonicBand s (Module.finrank ℂ U) := by
  intro f hf
  let := principalSeries_t2 s
  let :=
    (show WithSeminorms (chartSeminorm s) from ⟨rfl⟩).continuousSMul
  obtain ⟨μ, hhaar, hprob⟩ := KPCplxHarmonicExtraction.exists_su2_probability_haar
  obtain ⟨a, hint, havg, htype, hlim⟩ :=
    KPCplxHarmonicExtraction.character_average_harmonic_expansion s μ hhaar hprob f
  have horbit : Submodule.span ℂ (Set.range (fun k : compactSubgroup => KPCplxPrincipalSeriesCharts.pi s k f)) ≤ U := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    exact hU k f hf
  have haU (ℓ : ℕ) : a ℓ ∈ U := by
    have h' := closure_mono horbit (KPCplxHarmonicExtraction.character_average_mem_orbit_closure
      s μ hhaar hprob ℓ f (a ℓ) (hint ℓ) (havg ℓ))
    rwa [U.closed_of_finiteDimensional.closure_eq] at h'
  have hbound (ℓ : ℕ) (hne : a ℓ ≠ 0) : ℓ < Module.finrank ℂ U := by
    have ht := harmonicKType_multiplicity_one s ℓ
    have hn : U ⊓ harmonicKType s ℓ ≠ ⊥ := by
      intro he
      have hm : a ℓ ∈ U ⊓ harmonicKType s ℓ := ⟨haU ℓ, htype ℓ⟩
      rw [he] at hm
      exact hne (by exact hm)
    have hle : harmonicKType s ℓ ≤ U := by
      rw [← ((ht.2.2.1 (U ⊓ harmonicKType s ℓ) inf_le_right (fun k v hv => ⟨hU k v hv.1, ht.1 k v hv.2⟩)).resolve_left hn)]
      exact inf_le_left
    have hd := Submodule.finrank_mono hle
    rw [ht.2.1] at hd
    omega
  have hzero (ℓ : ℕ) (hℓ : Module.finrank ℂ U ≤ ℓ) : a ℓ = 0 := by
    by_contra hn
    exact (not_lt.mpr hℓ) (hbound ℓ hn)
  have hsum (N : ℕ) (hN : Module.finrank ℂ U ≤ N) :
      (∑ ℓ ∈ Finset.range N, a ℓ) = ∑ ℓ ∈ Finset.range (Module.finrank ℂ U), a ℓ := by
    symm
    apply Finset.sum_subset (Finset.range_mono hN)
    intro ℓ hℓ hnot
    exact hzero ℓ (by simpa using hnot)
  have hevent : (fun N => ∑ ℓ ∈ Finset.range N, a ℓ) =ᶠ[Filter.atTop]
      (fun _ : ℕ => ∑ ℓ ∈ Finset.range (Module.finrank ℂ U), a ℓ) := by
    filter_upwards [Filter.eventually_ge_atTop (Module.finrank ℂ U)] with N hN
    exact hsum N hN
  rw [← (tendsto_nhds_unique (tendsto_const_nhds.congr' hevent.symm) hlim)]
  apply Submodule.sum_mem
  intro ℓ hℓ
  exact (Finset.le_sup (Finset.mem_range_succ_iff.mpr
    (Nat.le_of_lt (Finset.mem_range.mp hℓ))) :
    harmonicKType s ℓ ≤ harmonicBand s (Module.finrank ℂ U)) (htype ℓ)

end DedekindZetaZeroFree.KPLiteralScalarArchUniformBands

namespace DedekindZetaZeroFree.KPLiteralScalarArchCoefficientGeneration
open KPLiteralScalarArchIndependentSlices

section

variable {ι X : Type*} [Fintype ι] (S : ι → Submodule ℂ (X → ℂ))

def tensorEvaluation :
    PiTensorProduct ℂ (fun i => S i) →ₗ[ℂ] ((ι → X) → ℂ) :=
  PiTensorProduct.lift
    ((MultilinearMap.mkPiAlgebra ℂ ι ((ι → X) → ℂ)).compLinearMap
      (fun i =>
        { toFun := fun f a => f.val (a i)
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }))

@[simp] theorem tensorEvaluation_pure (f : ∀ i, S i) (a : ι → X) :
    tensorEvaluation S (PiTensorProduct.tprod ℂ f) a = ∏ i, (f i).val (a i) := by
  simp [tensorEvaluation]

private theorem product_span_eq_range :
    Submodule.span ℂ (Set.range (fun f : ∀ i, S i => fun a => ∏ i, (f i).val (a i))) =
      (tensorEvaluation S).range := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨f, rfl⟩
    exact ⟨PiTensorProduct.tprod ℂ f, funext (tensorEvaluation_pure S f)⟩
  · rintro h ⟨t, rfl⟩
    induction t using PiTensorProduct.induction_on with
    | smul_tprod c f =>
      rw [map_smul]
      apply Submodule.smul_mem
      exact Submodule.subset_span ⟨f, (funext (tensorEvaluation_pure S f)).symm⟩
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

theorem uniform_pure_sampling [∀ i, FiniteDimensional ℂ (S i)] :
    ∃ (n : ℕ) (p : Fin n → (ι → X)) (c : Fin n → ℂ) (f : Fin n → ∀ i, S i),
      ∀ h ∈ Submodule.span ℂ (Set.range
        (fun f : ∀ i, S i => fun a => ∏ i, (f i).val (a i))),
        ∀ a, h a = ∑ j, c j * h (p j) * ∏ i, (f j i).val (a i) := by
  let R : Submodule ℂ ((ι → X) → ℂ) := Submodule.span ℂ (Set.range
    (fun f : ∀ i, S i => fun a => ∏ i, (f i).val (a i)))
  have hfin : Module.Finite ℂ R := by
    rw [show R = (tensorEvaluation S).range from product_span_eq_range S]
    infer_instance
  let := hfin
  obtain ⟨m, p, b, hb⟩ := finite_interpolation R
  have hx (i : Fin m) : ∃ d : (∀ j, S j) →₀ ℂ,
      d.sum (fun f c => c • (fun a => ∏ j, (f j).val (a j))) = (b i).val :=
    Finsupp.mem_span_range_iff_exists_finsupp.mp (b i).property
  choose d hd using hx
  let J := (i : Fin m) × (d i).support
  let E := Fintype.equivFin J
  refine ⟨Fintype.card J, fun j => p (E.symm j).1,
    fun j => d (E.symm j).1 (E.symm j).2.val,
    fun j => (E.symm j).2.val, ?_⟩
  intro h hh a
  have hbase := hb (⟨h, hh⟩ : R) a
  change h a = _ at hbase
  rw [hbase]
  have he (i : Fin m) : (b i).val a =
      ∑ f ∈ (d i).support, d i f * ∏ j, (f j).val (a j) := by
    simpa only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using (congrFun (hd i) a).symm
  simp_rw [he, Finset.mul_sum]
  have hs : (∑ i : Fin m, ∑ f ∈ (d i).support,
      h (p i) * (d i f * ∏ j, (f j).val (a j))) =
      ∑ j : J, d j.1 j.2.val * h (p j.1) * ∏ i, (j.2.val i).val (a i) := by
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_attach]
    apply Finset.sum_congr rfl
    intro f _
    ring
  rw [hs]
  exact Fintype.sum_equiv E _ _ (fun j => (congrArg (fun u : J => d u.1 u.2.val * h (p u.1) *
      ∏ i, (u.2.val i).val (a i)) (E.symm_apply_apply j)).symm)

end

open KPCplxPrincipalSeriesCharts KPCplxIntertwinerEigenvalues

theorem harmonic_band_uniform_sampling
    {ι : Type*} [Fintype ι] (N : ι → ℕ) :
    ∃ (n : ℕ) (p : Fin n → (ι → KPCplxCharacterHaar.ComplexGL2))
      (c : Fin n → ℂ) (f : Fin n → ι → KPLiteralTensor.harmonicPlus),
      ∀ h : (ι → KPCplxCharacterHaar.ComplexGL2) → ℂ,
        h ∈ Submodule.span ℂ (Set.range
          (fun f : ∀ i, (harmonicBandEvaluation positiveParameter (N i)).range =>
            fun a => ∏ i, (f i).val (a i))) →
        ∀ a, h a = ∑ j, c j * h (p j) * ∏ i, (f j i).val (a i) := by
  let : ∀ i, Module.Finite ℂ (harmonicBand positiveParameter (N i)) :=
    fun i => harmonicBand_finite _ _
  obtain ⟨n, p, c, f, hp⟩ := uniform_pure_sampling
    (fun i => (harmonicBandEvaluation positiveParameter (N i)).range)
  choose b hb using fun j i => (f j i).property
  have hle (i : ι) : harmonicBand positiveParameter (N i) ≤
      KPLiteralTensor.harmonicPlus := by
    apply Finset.sup_le
    intro k _
    exact le_iSup _ k
  refine ⟨n, p, c, fun j i => ⟨(b j i).val, hle i (b j i).property⟩, ?_⟩
  intro h hh a
  rw [hp h hh a]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  exact (congrFun (hb j i) (a i)).symm

theorem harmonic_family_sampling
    {ι Y : Type*} [Fintype ι] [DecidableEq ι] (N : ι → ℕ)
    (h : Y → (ι → KPCplxCharacterHaar.ComplexGL2) → ℂ)
    (hh : ∀ y i a, (fun x => h y (Function.update a i x)) ∈
      (harmonicBandEvaluation positiveParameter (N i)).range) :
    ∃ (n : ℕ) (p : Fin n → (ι → KPCplxCharacterHaar.ComplexGL2))
      (c : Fin n → ℂ) (f : Fin n → ι → KPLiteralTensor.harmonicPlus),
      ∀ y a, h y a = ∑ j, c j * h y (p j) * ∏ i, (f j i).val (a i) := by
  let : ∀ i, Module.Finite ℂ (harmonicBand positiveParameter (N i)) :=
    fun i => harmonicBand_finite _ _
  obtain ⟨n, p, c, f, hp⟩ := harmonic_band_uniform_sampling N
  exact ⟨n, p, c, f, fun y => hp (h y)
    (independent_slices_mem_product_span _ (h y) (hh y))⟩

end DedekindZetaZeroFree.KPLiteralScalarArchCoefficientGeneration

end
