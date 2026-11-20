module

public import Mathlib
public import RoughRegime.LiftTranslation


@[expose] public section

/-!
# Unbounded square-integrable coordinates in factorial lifts

These lemmas replace pointwise boundedness by genuine `MemLp _ 2` assumptions.
The finite coordinate expansion and the unused-index argument follow the
mathematical construction in the supplied RoughRegime/UpperCovariance.lean;
all integrability here is proved for unbounded independent observations.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

namespace NearlyMinimax.LiftL2

export RoughRegime.UpperCovariance (kernelSum kernelStatistic centeredKernelExpansion)
open RoughRegime.LiftTranslation (embeddingsWithRangeEquiv)

set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

abbrev Kernel (p k : ℕ) := MultilinearMap ℝ (fun _ : Fin k => Fin p → ℝ) ℝ
abbrev KernelMap (p k : ℕ) := ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin p → ℝ) ℝ

/-- Independent finite-dimensional observations with measurable coordinates
and coordinatewise finite second moments. -/
structure IndependentL2 {n p : ℕ} (μ : Measure Ω) (X : Fin n → Ω → Fin p → ℝ) : Prop where
  indep : iIndepFun X μ
  meas : ∀ j, Measurable (X j)
  l2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ

/-- Independently and identically distributed `L²` observations. -/
structure IidL2 {n p : ℕ} (μ : Measure Ω) (X : Fin n → Ω → Fin p → ℝ)
    : Prop extends IndependentL2 μ X where
  ident : ∀ i j, IdentDistrib (X i) (X j) μ μ

variable {n p r t R : ℕ}

theorem IndependentL2.precomp {n p k : ℕ} {X : Fin n → Ω → Fin p → ℝ}
    (hX : IndependentL2 μ X) (e : Fin k ↪ Fin n) : IndependentL2 μ (X ∘ e) :=
  ⟨hX.indep.precomp (g := e) e.injective, fun i => hX.meas (e i), fun i => hX.l2 (e i)⟩


variable [IsProbabilityMeasure μ]

theorem IndependentL2.center {X : Fin n → Ω → Fin p → ℝ}
    (hX : IndependentL2 μ X) (m : Fin p → ℝ) : IndependentL2 μ (fun j ω => X j ω - m) :=
  ⟨hX.indep.comp (fun _ v => v - m) (fun _ => measurable_id.sub_const m),
    fun j => (hX.meas j).sub_const m, fun j a => (hX.l2 j a).sub (memLp_const (m a))⟩

theorem IndependentL2.of_pi
    {F : Fin n → Ω → Fin p → ℝ} (hF : ∀ i, Measurable (F i))
    (h2 : ∀ i a, MemLp (fun ω => F i ω a) 2 μ) :
    IndependentL2 (Measure.pi (fun _ => μ)) (fun i z => F i (z i)) :=
  ⟨iIndepFun_pi (fun i => (hF i).aemeasurable), fun i => (hF i).comp (measurable_pi_apply i),
    fun i a => (h2 i a).comp_measurePreserving (measurePreserving_eval _ i)⟩

theorem IidL2.of_pi {F : Ω → Fin p → ℝ}
    (hF : Measurable F) (h2 : ∀ a, MemLp (fun ω => F ω a) 2 μ) :
    IidL2 (Measure.pi (fun _ : Fin n => μ)) (fun i z => F (z i)) := by
  have hp (i : Fin n) := measurePreserving_eval (fun _ : Fin n => μ) i
  refine ⟨IndependentL2.of_pi (fun _ => hF) (fun _ => h2), fun i j => ?_⟩
  exact (show IdentDistrib _ _ _ _ from
    ⟨(hp i).aemeasurable, (hp j).aemeasurable, (hp i).map_eq.trans (hp j).map_eq.symm⟩).comp hF

section
variable {ι : Type*} [DecidableEq ι] {Y : ι → Ω → ℝ}
    (hind : iIndepFun Y μ) (hmeas : ∀ i, Measurable (Y i))
include hind hmeas

/-- Integrable independent factors have an integrable finite product. -/
theorem independent_finset_product_integrable
    (hint : ∀ i, Integrable (Y i) μ) (s : Finset ι) :
    Integrable (fun ω => ∏ i ∈ s, Y i ω) μ := by

  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hs : Integrable (∏ j ∈ s, Y j) μ := by rwa [Finset.prod_fn]
    simpa only [Finset.prod_fn, Pi.mul_def, Finset.prod_insert hi] using
      (hind.indepFun_finsetProd_of_notMem hmeas hi).symm.integrable_mul (hint i) hs

/-- The product of independent `L²` factors remains in `L²`. Independence
prevents the need for higher moments as the number of factors grows. -/
theorem independent_finset_product_memLp_two
    (hL2 : ∀ i, MemLp (Y i) 2 μ) (s : Finset ι) :
    MemLp (fun ω => ∏ i ∈ s, Y i ω) 2 μ := by
  apply (memLp_two_iff_integrable_sq
    (Finset.measurable_prod s (fun i _ => hmeas i)).aestronglyMeasurable).2
  have hsqind : iIndepFun (fun i ω => Y i ω ^ 2) μ :=
    hind.comp (fun _ => fun y : ℝ => y ^ 2) (fun _ => measurable_id.pow_const 2)
  have hsq := independent_finset_product_integrable hsqind
    (fun i => (hmeas i).pow_const 2) (fun i => (hL2 i).integrable_sq) s
  simpa only [Finset.prod_pow] using hsq

end

/-- A coordinate monomial uses one square-integrable coordinate from each
of distinct independent observations. -/
theorem coordinate_monomial_memLp_two (e : Fin r ↪ Fin n) (σ : Fin r → Fin p)
    (X : Fin n → Ω → Fin p → ℝ) (hX : IndependentL2 μ X) :
    MemLp (fun ω => ∏ i, X (e i) ω (σ i)) 2 μ := by
  have heind := hX.indep.precomp e.injective
  have hcoord :=
    heind.comp (fun i => fun v : Fin p → ℝ => v (σ i))
      (fun i => measurable_pi_apply (σ i))
  exact independent_finset_product_memLp_two hcoord
    (fun i => (measurable_pi_apply (σ i)).comp (hX.meas (e i)))
    (fun i => hX.l2 (e i) (σ i)) Finset.univ

omit [IsProbabilityMeasure μ] in
/-- Group coordinate factors by their observation index before using independence. -/
theorem coordinate_product_integral_fiberwise
    {A : Type*} [Fintype A]
    (s : A → Fin n) (σ : A → Fin p) (X : Fin n → Ω → Fin p → ℝ)
    (hind : iIndepFun X μ) (hmeas : ∀ j, Measurable (X j)) :
    (∫ ω, ∏ i, X (s i) ω (σ i) ∂μ) =
      ∏ j : Fin n, ∫ ω, ∏ i : A with s i = j, X j ω (σ i) ∂μ := by
  classical
  let F : Fin n → (Fin p → ℝ) → ℝ := fun j v => ∏ i : A with s i = j, v (σ i)
  have hF : ∀ j, Measurable (F j) := fun j =>
    Finset.measurable_prod _ (fun i _ => measurable_pi_apply (σ i))
  calc
    _ = ∫ ω, ∏ j, F j (X j ω) ∂μ := by
      congr with ω
      rw [← Finset.prod_fiberwise Finset.univ s (fun i => X (s i) ω (σ i))]
      exact Finset.prod_congr rfl fun j _ => Finset.prod_congr rfl fun i hi => by
        rw [(Finset.mem_filter.mp hi).2]
    _ = _ := hind.integral_fun_prod_comp (fun j => (hmeas j).aemeasurable)
      (fun j => (hF j).aestronglyMeasurable)

/-- A centered coordinate used at just one observation slot annihilates the
whole expectation. Pair integrability is provided by the previous theorem. -/
theorem coordinate_product_integral_eq_zero
    {A : Type*} [Fintype A]
    (s : A → Fin n) (σ : A → Fin p) (X : Fin n → Ω → Fin p → ℝ)
    (hind : iIndepFun X μ) (hmeas : ∀ j, Measurable (X j))
    (hmean : ∀ j a, ∫ ω, X j ω a ∂μ = 0)
    (k : A) (hk : ∀ i, s i = s k → i = k) :
    (∫ ω, ∏ i, X (s i) ω (σ i) ∂μ) = 0 := by
  classical
  rw [coordinate_product_integral_fiberwise s σ X hind hmeas]
  apply Finset.prod_eq_zero (Finset.mem_univ (s k))
  have hfilter : (Finset.univ.filter (fun i : A => s i = s k)) = {k} := by
    grind
  rw [hfilter]
  simpa using hmean (s k) (σ k)

/-- Finite coordinate expansion of any multilinear map. -/
theorem multilinear_coordinate_expansion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : MultilinearMap ℝ (fun _ : ι => Fin p → ℝ) ℝ)
    (v : ι → Fin p → ℝ) :
    H v = ∑ σ : ι → Fin p,
      H (fun i => Pi.single (σ i) 1) * ∏ i, v i (σ i) := by
  classical
  have hv : v = fun i => ∑ a : Fin p, v i a • (Pi.single a (1 : ℝ) : Fin p → ℝ) := by
    funext i a
    simp [Pi.single_apply]
  calc
    H v = H (fun i => ∑ a : Fin p, v i a • (Pi.single a (1 : ℝ) : Fin p → ℝ)) := congrArg H hv
    _ = ∑ σ : ι → Fin p, H (fun i => v i (σ i) • (Pi.single (σ i) (1 : ℝ) : Fin p → ℝ)) := H.map_sum _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro σ _
      simp [H.map_smul_univ] <;> linarith

/-- A multilinear kernel applied to distinct independent `L²` observations
is itself square integrable, with no pointwise bound on the observations. -/
theorem multilinear_kernel_memLp_two (H : Kernel p r)
    (e : Fin r ↪ Fin n) (X : Fin n → Ω → Fin p → ℝ)
    (hX : IndependentL2 μ X) :
    MemLp (fun ω => H (fun i => X (e i) ω)) 2 μ := by
  have hexp : (fun ω => H (fun i => X (e i) ω)) =
      fun ω => ∑ σ : Fin r → Fin p,
        H (fun i => Pi.single (σ i) 1) * ∏ i, X (e i) ω (σ i) := by
    funext ω
    exact multilinear_coordinate_expansion H _
  rw [hexp]
  exact memLp_finsetSum Finset.univ (fun σ _ =>
    (coordinate_monomial_memLp_two e σ X hX).const_mul _)

omit [IsProbabilityMeasure μ] in
private theorem integral_multilinear_coordinates {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : MultilinearMap ℝ (fun _ : ι => Fin p → ℝ) ℝ) (X : ι → Ω → Fin p → ℝ)
    (hX : ∀ σ : ι → Fin p, Integrable (fun ω => ∏ i, X i ω (σ i)) μ) :
    (∫ ω, H (fun i => X i ω) ∂μ) =
      ∑ σ : ι → Fin p, H (fun i => Pi.single (σ i) 1) * ∫ ω, ∏ i, X i ω (σ i) ∂μ := by
  simp_rw [fun ω => multilinear_coordinate_expansion H (fun i => X i ω)]
  rw [integral_finsetSum _ (fun σ _ => (hX σ).const_mul _)]
  simp_rw [integral_const_mul]

section
variable (H : Kernel p r) (G : Kernel p t)

/-- Expand a product of two kernels by treating it as one multilinear map on the disjoint slots. -/
private theorem integral_pair_coordinates
    (X : Fin r → Ω → Fin p → ℝ) (Y : Fin t → Ω → Fin p → ℝ)
    (hX : ∀ σ : Fin r → Fin p, MemLp (fun ω => ∏ i, X i ω (σ i)) 2 μ)
    (hY : ∀ σ : Fin t → Fin p, MemLp (fun ω => ∏ i, Y i ω (σ i)) 2 μ) :
    (∫ ω, H (fun i => X i ω) * G (fun i => Y i ω) ∂μ) =
      ∑ σ : Fin r ⊕ Fin t → Fin p,
        (H (fun i => Pi.single (σ (.inl i)) 1) * G (fun i => Pi.single (σ (.inr i)) 1)) *
          ∫ ω, ∏ i, Sum.elim X Y i ω (σ i) ∂μ := by
  let L := (TensorProduct.lid ℝ ℝ).toLinearMap.compMultilinearMap (H.domCoprod G)
  have h (σ : Fin r ⊕ Fin t → Fin p) : Integrable (fun ω => ∏ i, Sum.elim X Y i ω (σ i)) μ := by
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr]
    exact (hX (σ ∘ Sum.inl)).integrable_mul (hY (σ ∘ Sum.inr))
  simpa only [L, LinearMap.compMultilinearMap_apply, MultilinearMap.domCoprod_apply,
    LinearEquiv.coe_toLinearMap, TensorProduct.lid_tmul, smul_eq_mul, Sum.elim_inl, Sum.elim_inr] using
    integral_multilinear_coordinates L (Sum.elim X Y) h

theorem multilinear_kernel_pair_integral_eq_zero_left
    (e : Fin r ↪ Fin n) (f : Fin t ↪ Fin n)
    (X : Fin n → Ω → Fin p → ℝ) (hX : IndependentL2 μ X)
    (hmean : ∀ j a, ∫ ω, X j ω a ∂μ = 0)
    (k : Fin r) (hk : e k ∉ Set.range f) :
    (∫ ω, H (fun i => X (e i) ω) * G (fun i => X (f i) ω) ∂μ) = 0 := by
  rw [integral_pair_coordinates H G _ _ (fun σ => coordinate_monomial_memLp_two e σ X hX)
    (fun σ => coordinate_monomial_memLp_two f σ X hX)]
  apply Finset.sum_eq_zero
  intro σ _
  have he (i) : Sum.elim (fun j => X (e j)) (fun j => X (f j)) i = X (Sum.elim e f i) := by
    cases i <;> rfl
  simp_rw [he]
  rw [coordinate_product_integral_eq_zero (Sum.elim e f) σ X hX.indep hX.meas hmean (.inl k), mul_zero]
  grind

/-- Range inequality suffices for orthogonality, even at different kernel orders. -/
theorem multilinear_kernel_pair_integral_eq_zero
    (e : Fin r ↪ Fin n) (f : Fin t ↪ Fin n)
    (X : Fin n → Ω → Fin p → ℝ) (hX : IndependentL2 μ X)
    (hmean : ∀ j a, ∫ ω, X j ω a ∂μ = 0)
    (hef : Set.range e ≠ Set.range f) :
    (∫ ω, H (fun i => X (e i) ω) * G (fun i => X (f i) ω) ∂μ) = 0 := by
  rcases (show ¬ (Set.range e ⊆ Set.range f ∧ Set.range f ⊆ Set.range e) from
    fun h => hef (Set.Subset.antisymm h.1 h.2)) |> not_and_or.mp with h | h
  · obtain ⟨_, ⟨k, rfl⟩, hk⟩ := Set.not_subset.mp h
    exact multilinear_kernel_pair_integral_eq_zero_left H G e f X hX hmean k hk
  · obtain ⟨_, ⟨k, rfl⟩, hk⟩ := Set.not_subset.mp h
    simpa only [mul_comm] using multilinear_kernel_pair_integral_eq_zero_left G H f e X hX hmean k hk

end

/-- Every positive-order multilinear kernel is centered under independent,
coordinatewise centered observations. -/
theorem multilinear_kernel_integral_eq_zero (hr : 0 < r)
    (H : Kernel p r)
    (e : Fin r ↪ Fin n) (X : Fin n → Ω → Fin p → ℝ)
    (hX : IndependentL2 μ X)
    (hmean : ∀ j a, ∫ ω, X j ω a ∂μ = 0) :
    (∫ ω, H (fun i => X (e i) ω) ∂μ) = 0 := by
  rw [integral_multilinear_coordinates H (fun i => X (e i))
    (fun σ => (coordinate_monomial_memLp_two e σ X hX).integrable (by norm_num))]
  exact Finset.sum_eq_zero fun σ _ => by
    rw [coordinate_product_integral_eq_zero e σ X hX.indep hX.meas hmean ⟨0, hr⟩
      (fun _ h => e.injective h), mul_zero]

/-- Distinct-observation kernel sums are genuinely square integrable. -/
theorem kernelSum_memLp_two (H : Kernel p r)
    (X : Fin n → Ω → Fin p → ℝ) (hX : IndependentL2 μ X) :
    MemLp (kernelSum H X) 2 μ :=
  memLp_finsetSum Finset.univ (fun e _ => multilinear_kernel_memLp_two H e X hX)

section
variable (hr : 0 < r)
include hr

/-- Positive-order kernel sums have mean zero. -/
theorem kernelSum_integral_eq_zero
    (H : Kernel p r)
    (X : Fin n → Ω → Fin p → ℝ) (hX : IndependentL2 μ X)
    (hmean : ∀ j a, ∫ ω, X j ω a ∂μ = 0) :
    (∫ ω, kernelSum H X ω ∂μ) = 0 := by
  unfold kernelSum
  rw [integral_finsetSum]
  · exact Finset.sum_eq_zero (fun e _ => multilinear_kernel_integral_eq_zero
      hr H e X hX hmean)
  · exact fun e _ => (multilinear_kernel_memLp_two H e X hX).integrable
      (by norm_num)

/-- Exact covariance expansion into the pairs with equal observation ranges.
This is the probabilistic foundation of the factorial-lift variance identity. -/
theorem kernelSum_covariance_same_range (ht : 0 < t)
    (H : Kernel p r)
    (G : Kernel p t)
    (X : Fin n → Ω → Fin p → ℝ) (hX : IndependentL2 μ X)
    (hmean : ∀ j a, ∫ ω, X j ω a ∂μ = 0) :
    covariance (kernelSum H X) (kernelSum G X) μ =
      ∑ e : Fin r ↪ Fin n, ∑ f : Fin t ↪ Fin n with Set.range f.toFun = Set.range e.toFun,
        ∫ ω, H (fun i => X (e i) ω) * G (fun i => X (f i) ω) ∂μ := by
  unfold kernelSum
  rw [covariance_fun_sum_fun_sum (fun e => multilinear_kernel_memLp_two H e X hX)
    (fun f => multilinear_kernel_memLp_two G f X hX)]
  apply Finset.sum_congr rfl
  intro e _
  simp_rw [covariance, multilinear_kernel_integral_eq_zero hr H _ X hX hmean,
    multilinear_kernel_integral_eq_zero ht G _ X hX hmean, sub_zero]
  symm
  exact Finset.sum_subset (Finset.filter_subset _ _) fun f _ hf =>
    multilinear_kernel_pair_integral_eq_zero H G e f X hX hmean (by simpa [ne_comm] using hf)

end

/-- Exactly `r!` ordered distinct tuples represent one observation set. -/
private lemma card_same_range_embeddings (e : Fin r ↪ Fin n) :
    Fintype.card {f : Fin r ↪ Fin n // Set.range f.toFun = Set.range e.toFun} = r.factorial := by
  classical
  calc
    _ = Fintype.card (Fin r ≃ Set.range e) := Fintype.card_congr (embeddingsWithRangeEquiv _).symm
    _ = _ := by rw [Fintype.card_equiv e.toEquivRange, Fintype.card_fin]

omit [IsProbabilityMeasure μ] in
/-- Independent identically distributed observations give the same diagonal
kernel integral for every injective tuple. -/
lemma multilinear_pair_integral_identDistrib
    (H G : KernelMap p r)
    (e f : Fin r ↪ Fin n) (X : Fin n → Ω → Fin p → ℝ)
    (hind : iIndepFun X μ) (hid : ∀ i j, IdentDistrib (X i) (X j) μ μ) :
    (∫ ω, H (fun i => X (e i) ω) * G (fun i => X (e i) ω) ∂μ) =
      ∫ ω, H (fun i => X (f i) ω) * G (fun i => X (f i) ω) ∂μ := by
  have h := IdentDistrib.pi (fun i => hid (e i) (f i))
    (hind.precomp e.injective) (hind.precomp f.injective)
  exact (h.comp (H.cont.mul G.cont).measurable).integral_eq

omit [IsProbabilityMeasure μ] in
lemma multilinear_pair_integral_same_range
    (H G : KernelMap p r)
    (hsym : ∀ (σ : Equiv.Perm (Fin r)) v, G (fun i => v (σ i)) = G v)
    (e f e₀ : Fin r ↪ Fin n) (X : Fin n → Ω → Fin p → ℝ)
    (hind : iIndepFun X μ) (hid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hef : Set.range f = Set.range e) :
    (∫ ω, H (fun i => X (e i) ω) * G (fun i => X (f i) ω) ∂μ) =
      ∫ ω, H (fun i => X (e₀ i) ω) * G (fun i => X (e₀ i) ω) ∂μ := by
  let a := (embeddingsWithRangeEquiv (Set.range e)).symm ⟨f, hef⟩
  have hf : a.toEmbedding.trans (.subtype _) = f :=
    congrArg Subtype.val ((embeddingsWithRangeEquiv (Set.range e)).apply_symm_apply ⟨f, hef⟩)
  have h (ω : Ω) := hsym (a.trans e.toEquivRange.symm) (fun i => X (e i) ω)
  have h' (ω : Ω) : G (fun i => X (f i) ω) = G (fun i => X (e i) ω) := by
    rw [← h ω, ← hf]
    congr 1
    ext i j
    exact congrArg (fun x : Set.range e => X x.val ω j) (e.toEquivRange.apply_symm_apply (a i)).symm
  simp_rw [h']
  exact multilinear_pair_integral_identDistrib H G e e₀ X hind hid

section
variable (hr : 0 < r)
include hr

/-- The exact factorial covariance of the unnormalized kernel sum, for
square-integrable unbounded i.i.d. observations. -/
theorem kernelSum_covariance
    (H G : KernelMap p r)
    (hsym : ∀ (σ : Equiv.Perm (Fin r)) v, G (fun i => v (σ i)) = G v)
    (e₀ : Fin r ↪ Fin n) (X : Fin n → Ω → Fin p → ℝ)
    (hX : IidL2 μ X)
    (hmean : ∀ j a, ∫ ω, X j ω a ∂μ = 0) :
    covariance (kernelSum H.toMultilinearMap X) (kernelSum G.toMultilinearMap X) μ =
      (n.descFactorial r : ℝ) * (r.factorial : ℝ) *
        ∫ ω, H (fun i => X (e₀ i) ω) * G (fun i => X (e₀ i) ω) ∂μ := by

  rw [kernelSum_covariance_same_range hr hr H.toMultilinearMap G.toMultilinearMap X hX.toIndependentL2 hmean]
  let J := ∫ ω, H (fun i => X (e₀ i) ω) * G (fun i => X (e₀ i) ω) ∂μ
  have hs (e : Fin r ↪ Fin n) :
      (∑ f : Fin r ↪ Fin n with Set.range f.toFun = Set.range e.toFun,
        ∫ ω, H (fun i => X (e i) ω) * G (fun i => X (f i) ω) ∂μ) = (r.factorial : ℝ) * J := by
    trans ∑ f : Fin r ↪ Fin n with Set.range f.toFun = Set.range e.toFun, J
    · exact Finset.sum_congr rfl fun f hf =>
        multilinear_pair_integral_same_range H G hsym e f e₀ X hX.indep hX.ident (Finset.mem_filter.mp hf).2
    · rw [Finset.sum_const, nsmul_eq_mul, ← Fintype.card_subtype, card_same_range_embeddings e]
  simp_rw [ContinuousMultilinearMap.coe_coe, hs]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_embedding_eq, Fintype.card_fin]
  ring

/-- Kernel sums of different positive orders are exactly orthogonal. -/
theorem kernelSum_covariance_different_orders (ht : 0 < t) (hrt : r ≠ t)
    (H : Kernel p r)
    (G : Kernel p t)
    (X : Fin n → Ω → Fin p → ℝ) (hX : IndependentL2 μ X)
    (hmean : ∀ j a, ∫ ω, X j ω a ∂μ = 0) :
    covariance (kernelSum H X) (kernelSum G X) μ = 0 := by
  rw [kernelSum_covariance_same_range hr ht H G X hX hmean]
  refine Finset.sum_eq_zero fun e _ => Finset.sum_eq_zero fun f hf => ?_
  have h := Fintype.card_congr (e.toEquivRange.trans
    ((Set.equivOfEq (Finset.mem_filter.mp hf).2.symm).trans f.toEquivRange.symm))
  exact (hrt (by simpa using h)).elim

end

/-- Exact variance of one centered symmetric factorial-lift term, with finite
second moments and no pointwise boundedness restriction. -/
theorem kernelStatistic_variance (hr : 0 < r) (hrn : r ≤ n)
    (H : KernelMap p r)
    (hsym : ∀ (σ : Equiv.Perm (Fin r)) v, H (fun i => v (σ i)) = H v)
    (X : Fin n → Ω → Fin p → ℝ) (hX : IidL2 μ X)
    (hmean : ∀ j a, ∫ ω, X j ω a ∂μ = 0) :
    variance (kernelStatistic H X) μ =
      (((r.factorial : ℝ) * (n.descFactorial r : ℝ))⁻¹) *
        ∫ ω, H (fun i => X (Fin.castLEEmb hrn i) ω) ^ 2 ∂μ := by
  unfold kernelStatistic
  rw [variance_const_mul, ← covariance_self
    (kernelSum_memLp_two H.toMultilinearMap X hX.toIndependentL2).aemeasurable,
    kernelSum_covariance hr H H hsym (Fin.castLEEmb hrn) X hX hmean]
  have hfac : (r.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  grind

theorem kernelStatistic_memLp_two
    (H : KernelMap p r)
    (X : Fin n → Ω → Fin p → ℝ) (hX : IndependentL2 μ X) :
    MemLp (kernelStatistic H X) 2 μ :=
  (kernelSum_memLp_two H.toMultilinearMap X hX).const_mul _

theorem centeredKernelExpansion_memLp_two (c : ℝ)
    (H : (r : Fin R) → KernelMap p (r.val + 1))
    (X : Fin n → Ω → Fin p → ℝ) (hX : IndependentL2 μ X) :
    MemLp (centeredKernelExpansion c H X) 2 μ :=
  (memLp_const c).add (memLp_finsetSum Finset.univ (fun r _ =>
    kernelStatistic_memLp_two (H r) X hX))

theorem kernelStatistic_integral_eq_zero (hr : 0 < r)
    (H : KernelMap p r)
    (X : Fin n → Ω → Fin p → ℝ) (hX : IndependentL2 μ X)
    (hmean : ∀ j a, ∫ ω, X j ω a ∂μ = 0) :
    (∫ ω, kernelStatistic H X ω ∂μ) = 0 := by
  unfold kernelStatistic
  rw [integral_const_mul,
    kernelSum_integral_eq_zero hr H.toMultilinearMap X hX hmean, mul_zero]

section
variable (c : ℝ)
    (H : (r : Fin R) → KernelMap p (r.val + 1))

theorem centeredKernelExpansion_expectation
    (X : Fin n → Ω → Fin p → ℝ) (hX : IndependentL2 μ X)
    (hmean : ∀ j a, ∫ ω, X j ω a ∂μ = 0) :
    (∫ ω, centeredKernelExpansion c H X ω ∂μ) = c := by
  unfold centeredKernelExpansion
  have hi (r : Fin R) (_ : r ∈ Finset.univ) := (kernelStatistic_memLp_two (H r) X hX).integrable
    (by norm_num)
  rw [integral_add (integrable_const _) (integrable_finsetSum _ hi), integral_finsetSum _ hi]
  simp [fun r : Fin R => kernelStatistic_integral_eq_zero (Nat.succ_pos r.val) (H r) X hX hmean]

/-- Exact centered Taylor variance series under the original paper's finite
second-moment hypothesis, without restricting the responses to a bounded set. -/
theorem centeredKernelExpansion_variance
    (hsym : ∀ r (σ : Equiv.Perm (Fin (r.val + 1))) v,
      H r (fun i => v (σ i)) = H r v)
    (X : Fin n → Ω → Fin p → ℝ) (hR : R ≤ n)
    (hX : IidL2 μ X)
    (hmean : ∀ j a, ∫ ω, X j ω a ∂μ = 0) :
    variance (centeredKernelExpansion c H X) μ =
      ∑ r : Fin R, (((r.val + 1).factorial : ℝ) *
        (n.descFactorial (r.val + 1) : ℝ))⁻¹ *
        ∫ ω, H r (fun i => X
          (Fin.castLEEmb ((Nat.succ_le_of_lt r.isLt).trans hR) i) ω) ^ 2 ∂μ := by
  have hstats (r : Fin R) := kernelStatistic_memLp_two (H r) X hX.toIndependentL2
  have hsum :=
    memLp_finsetSum Finset.univ (fun r _ => hstats r)
  unfold centeredKernelExpansion
  rw [variance_const_add hsum.aestronglyMeasurable c, variance_fun_sum hstats]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_eq_single r]
  · rw [covariance_self (hstats r).aemeasurable]
    exact kernelStatistic_variance (by omega)
      ((Nat.succ_le_of_lt r.isLt).trans hR) (H r) (hsym r) X hX hmean
  · intro t _ htr
    unfold kernelStatistic
    rw [covariance_const_mul_left, covariance_const_mul_right]
    have hrt : r.val + 1 ≠ t.val + 1 := by
      intro h <;> omega
    rw [kernelSum_covariance_different_orders (by omega) (by omega) hrt
      (H r).toMultilinearMap (H t).toMultilinearMap X hX.toIndependentL2 hmean]
    ring
  tauto

end

/-- Centering preserves all the actual probability and moment hypotheses. -/
theorem centerObservations_l2 (X : Fin n → Ω → Fin p → ℝ) (m : Fin p → ℝ)
    (hX : IidL2 μ X)
    (hmean : ∀ j a, ∫ ω, X j ω a ∂μ = m a) :
    IidL2 μ (fun j ω => X j ω - m) ∧ (∀ j a, ∫ ω, X j ω a - m a ∂μ = 0) := by
  refine ⟨⟨hX.toIndependentL2.center m, fun i j => (hX.ident i j).comp (measurable_id.sub_const m)⟩,
    fun j a => ?_⟩
  simp [integral_sub ((hX.l2 j a).integrable (by norm_num)) (integrable_const (m a)), integral_const, hmean]

omit [MeasurableSpace Ω] in
/-- The supplied coefficient lift is the centered Taylor expansion. This
uses only the imported algebraic lift identity, which has no boundedness premise. -/
theorem polynomialLift_centering_l2
    (F : MvPolynomial (Fin p) ℝ) (X : Fin n → Ω → Fin p → ℝ) (m : Fin p → ℝ)
    (hdeg : F.totalDegree ≤ R) (hRn : R ≤ n) :
    RoughRegime.Upper.polynomialLift F X =
      centeredKernelExpansion (MvPolynomial.eval m F)
        (fun r : Fin R => iteratedFDeriv ℝ (r.val + 1) (fun x => MvPolynomial.eval x F) m)
        (fun j ω => X j ω - m) :=
  RoughRegime.LiftTranslation.polynomialLift_eq_centeredDerivativeLift F X m hdeg hRn

/-- Centering independently in each slot is an L² contraction. The mixed
inner product of the centered and original kernels equals the centered energy:
in each slot, the centered coordinate is orthogonal to a constant. -/
theorem independent_centering_square_le_l2
    (H : KernelMap p r) (X : Fin r → Ω → Fin p → ℝ) (hX : IndependentL2 μ X)
    (m : Fin p → ℝ) (hmean : ∀ i a, ∫ ω, X i ω a ∂μ = m a) :
    (∫ ω, H (fun i => X i ω - m) ^ 2 ∂μ) ≤ ∫ ω, H (fun i => X i ω) ^ 2 ∂μ := by
  let Y (i : Fin r) (ω : Ω) := X i ω - m
  have hY : IndependentL2 μ Y := hX.center m
  let F (Z : Fin r → Ω → Fin p → ℝ) (ω : Ω) := H (fun i => Z i ω)
  have hF {Z} (hZ : IndependentL2 μ Z) : MemLp (F Z) 2 μ :=
    multilinear_kernel_memLp_two H.toMultilinearMap (.refl _) Z hZ
  have hm (i a) : ∫ ω, Y i ω a ∂μ = 0 := by
    simp [Y, integral_sub ((hX.l2 i a).integrable (by norm_num)) (integrable_const _), hmean]
  have hcoordinate (i a b) :
      (∫ ω, Y i ω a * Y i ω b ∂μ) = ∫ ω, Y i ω a * X i ω b ∂μ := by
    change (∫ ω, Y i ω a * (X i ω b - m b) ∂μ) = _
    simp only [mul_sub]
    have h : Integrable (fun ω => Y i ω a * X i ω b) μ :=
      (hY.l2 i a).integrable_mul (hX.l2 i b)
    rw [integral_sub h (((hY.l2 i a).integrable (by norm_num)).mul_const (m b)),
      integral_mul_const, hm, zero_mul, sub_zero]
  have hfactor (B : (Fin p → ℝ) → (Fin p → ℝ)) (hB : Measurable B) (σ : Fin r ⊕ Fin r → Fin p) :
      (∫ ω, ∏ i, Sum.elim Y (fun i ω => B (X i ω)) i ω (σ i) ∂μ) =
        ∏ i, ∫ ω, Y i ω (σ (.inl i)) * B (X i ω) (σ (.inr i)) ∂μ := by
    let g (i : Fin r) (v : Fin p → ℝ) := (v - m) (σ (.inl i)) * B v (σ (.inr i))
    have hg (i : Fin r) : Measurable (g i) := by dsimp [g]; fun_prop
    simpa only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, ← Finset.prod_mul_distrib] using
      hX.indep.integral_fun_prod_comp (fun i => (hX.meas i).aemeasurable)
        (fun i => (hg i).aestronglyMeasurable)
  have hP {Z : Fin r → Ω → Fin p → ℝ} (hZ : IndependentL2 μ Z) σ :=
    coordinate_monomial_memLp_two (.refl _) σ Z hZ
  have hexp Z (hZ : IndependentL2 μ Z) :=
    integral_pair_coordinates H.toMultilinearMap H.toMultilinearMap Y Z (hP hY) (hP hZ)
  have hcross : (∫ ω, F Y ω * F X ω ∂μ) = ∫ ω, F Y ω ^ 2 ∂μ := by
    simp_rw [F, pow_two, ← ContinuousMultilinearMap.coe_coe, hexp X hX, hexp Y hY]
    apply Finset.sum_congr rfl
    intro σ _
    congr 1
    have hx := hfactor id measurable_id σ
    simp only [id_eq] at hx
    rw [hx, hfactor (· - m) (measurable_id.sub_const m) σ]
    exact Finset.prod_congr rfl fun i _ => (hcoordinate i _ _).symm
  have hf := (hF hX).integrable_sq
  have hg := (hF hY).integrable_sq
  have h := integral_mono (((hF hY).integrable_mul (hF hX)).const_mul 2) (hf.add hg)
    (fun ω => by
      change 2 * (F Y ω * F X ω) ≤ F X ω ^ 2 + F Y ω ^ 2
      nlinarith only [sq_nonneg (F X ω - F Y ω)])
  change (∫ ω, 2 * (F Y ω * F X ω) ∂μ) ≤ (∫ ω, F X ω ^ 2 + F Y ω ^ 2 ∂μ) at h
  rw [integral_const_mul, hcross, integral_add hf hg] at h
  change (∫ ω, F Y ω ^ 2 ∂μ) ≤ _
  linarith only [h]

section
variable (F : MvPolynomial (Fin p) ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (m : Fin p → ℝ)
    (hdeg : F.totalDegree ≤ R) (hRn : R ≤ n)
include m hdeg hRn

/-- The actual coefficient lift is square integrable under coordinatewise `L²`. -/
theorem polynomialLift_memLp_two_l2
    (hX : IndependentL2 μ X) :
    MemLp (RoughRegime.Upper.polynomialLift F X) 2 μ := by
  rw [polynomialLift_centering_l2 F X m hdeg hRn]
  exact centeredKernelExpansion_memLp_two _ _ _ (hX.center m)

/-- The coefficient lift is unbiased at the actual population mean. -/
theorem polynomialLift_expectation_l2
    (hX : IidL2 μ X)
    (hmean : ∀ j a, ∫ ω, X j ω a ∂μ = m a) :
    (∫ ω, RoughRegime.Upper.polynomialLift F X ω ∂μ) = MvPolynomial.eval m F := by
  obtain ⟨hX0, hzero⟩ := centerObservations_l2 X m hX hmean
  rw [polynomialLift_centering_l2 F X m hdeg hRn]
  exact centeredKernelExpansion_expectation _ _ _ hX0.toIndependentL2 hzero

end

/-- A positive lower bound on each available observation count bounds the
whole descending factorial. -/
theorem descFactorial_lower_bound {n R k : ℕ} (hRn : R ≤ n) (hkR : k ≤ R)
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (hΛn : Λ ≤ (n : ℝ) - R + 1) :
    Λ ^ k ≤ (n.descFactorial k : ℝ) := by
  have hkn : k ≤ n + 1 := by omega
  have hcast : ((n + 1 - k : ℕ) : ℝ) = (n : ℝ) + 1 - k := by
    rw [Nat.cast_sub hkn, Nat.cast_add, Nat.cast_one]
  have hRk : (k : ℝ) ≤ R := by exact_mod_cast hkR
  have hbase : Λ ≤ ((n + 1 - k : ℕ) : ℝ) := by rw [hcast]; linarith
  calc
    Λ ^ k ≤ (((n + 1 - k : ℕ) : ℝ)) ^ k := pow_le_pow_left₀ hΛ hbase k
    _ ≤ (n.descFactorial k : ℝ) := by exact_mod_cast Nat.pow_sub_le_descFactorial n k

/-- The factorial variance series and the centering contraction apply to an
arbitrary symmetric Taylor coefficient collection, including one obtained by
spatial integration. The right side consists of actual uncentered kernels. -/
theorem centered_expansion_variance_le_raw_power
    (c : ℝ) (H : (r : Fin R) → KernelMap p (r.val + 1))
    (hsym : ∀ r (σ : Equiv.Perm (Fin (r.val + 1))) v,
      H r (fun i => v (σ i)) = H r v)
    (X : Fin n → Ω → Fin p → ℝ) (m : Fin p → ℝ) (hR : R ≤ n)
    (hX : IidL2 μ X)
    (hmean : ∀ j a, ∫ ω, X j ω a ∂μ = m a)
    (Λ : ℝ) (hΛ : 0 < Λ) (hΛn : Λ ≤ (n : ℝ) - R + 1) :
    variance (centeredKernelExpansion c H (fun j ω => X j ω - m)) μ ≤
      ∑ r : Fin R, (((r.val + 1).factorial : ℝ) * Λ ^ (r.val + 1))⁻¹ *
        ∫ ω, H r (fun i => X
          (Fin.castLEEmb ((Nat.succ_le_of_lt r.isLt).trans hR) i) ω) ^ 2 ∂μ := by
  obtain ⟨hX0, hzero⟩ := centerObservations_l2 X m
    hX hmean
  rw [centeredKernelExpansion_variance c H hsym _ hR hX0 hzero]
  apply Finset.sum_le_sum
  intro r _
  let e := Fin.castLEEmb ((Nat.succ_le_of_lt r.isLt).trans hR)
  have hc := independent_centering_square_le_l2 (H r)
    (X ∘ e) (hX.toIndependentL2.precomp e) m
    (fun i a => hmean (e i) a)
  have hb := descFactorial_lower_bound hR (Nat.succ_le_of_lt r.isLt) hΛ.le hΛn
  exact (mul_le_mul_of_nonneg_left hc (by positivity)).trans
    (mul_le_mul_of_nonneg_right
      (inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left hb (by positivity)))
      (integral_nonneg fun _ => sq_nonneg _))

end NearlyMinimax.LiftL2




