module

public import Mathlib
public import RoughRegime.LiftTranslation
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-!
# Unbounded square-integrable coordinates in factorial lifts

These lemmas replace pointwise boundedness by genuine `MemLp _ 2` assumptions.
The finite coordinate expansion and the unused-index argument follow the
mathematical construction in the supplied RoughRegime/UpperCovariance.lean;
all integrability here is proved for unbounded independent observations.
-/

𝚵

namespace NearlyMinimax.LiftL2


𝛒

𝗃 𝖏 ∀ i, Measurable $ ἀ i
𝗇 𝖛 𝘄
𝗃 𝔉₁ fun ω => ἀ
𝗃 𝔐₁ MemLp ἀ 2 μ
section

variable [IsProbabilityMeasure μ]
    {ι }
    [DecidableEq ι]
    {Y : ι → 𝖛}
    (hind : iIndepFun Y μ)
    (hmeas : 𝖏 Y)

include hind hmeas

𝗇 𝔰 fun ω => ∏ i ∈ s, Y i ω
𝗇 𝔇₁ ∏ j ∈ s, Y j ω
𝗇 𝔱 𝔉₁ 𝔇₁
/-- Integrable independent factors have an integrable finite product. -/
theorem independent_finset_product_integrable
    (hint : ∀ i, Integrable (Y i) μ) s :
    Integrable 𝔰 μ := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hpfun : ∏ j ∈ s, Y j = 𝔱 := by
      funext ω
      simp
    have hprod := (hind.indepFun_finsetProd_of_notMem hmeas hi).symm.integrable_mul
      (hint i) 𝖤₄
    rw [hpfun] at hprod
    have hp : Y i * 𝔱 =
         fun ω => Y i ω * 𝔇₁ := 𝖦₄
    rw [hp] at hprod
    simpa only [Finset.prod_insert hi] using hprod

/-- The product of independent `L²` factors remains in `L²`. Independence
prevents the need for higher moments as the number of factors grows. -/
theorem independent_finset_product_memLp_two
    (hL2 : ∀ i, MemLp (Y i) 2 μ) s :
    𝔐₁ 𝔰 := by
  apply (memLp_two_iff_integrable_sq
    (Finset.measurable_prod s fun i _ => hmeas i ).aestronglyMeasurable).2
  have hsqind : iIndepFun (fun i ω => Y i ω ^ 2) μ :=
    hind.comp (fun _ => fun y => y ^ 2) fun _ => measurable_id.pow_const 2
  have hsq := independent_finset_product_integrable hsqind
    (fun i => (hmeas i).pow_const 2) (fun i => (hL2 i).integrable_sq) s
  simpa only [Finset.prod_pow] using hsq

end

𝗇 𝖇 X j ω a
𝗇 𝔄 ∀ j a, MemLp 𝔉₁ 𝖇 2 μ
𝗇 𝔈₁ 𝗓
𝗇 𝔅 Fin n → Ω → 𝔈₁
𝗇 𝔈 ∀ j, Measurable $ X j
𝗃 𝔊₁ ∫ ω, ἀ ∂μ
𝗇 𝔉 ∀ j a, 𝔊₁ 𝖇 = 0
𝗇 𝔐 𝚖₁
𝗇 𝔑 𝔈₁
𝗇 𝔔 iIndepFun X μ
𝗃 𝖍 ἀ $ e i
𝗇 𝔗 ∏ i, 𝖍 X ω (σ i)
𝗇 𝔙 Fin t ↪ Fin n
𝗇 𝔡 Fin r → Fin p
𝗇 𝔲 X j ω
𝗇 𝔴 coordinate_monomial_memLp_two e σ X hind hmeas hL2
𝗃 𝖎 ἀ $ σ i
𝗇 𝖒 Fin t → Fin p
𝗇 𝖓 Filter.Eventually.of_forall 𝔉₁ rfl
𝗃 𝔑₁ X (ἀ i) ω
𝗃 𝔒₁ fun i => ἀ
section

variable [IsProbabilityMeasure μ]

/-- A coordinate monomial uses one square-integrable coordinate from each
of distinct independent observations. -/
theorem coordinate_monomial_memLp_two
    {n p r } (e : 𝔐) (σ : 𝔡)
    (X : 𝔅) (hind : 𝔔)
    (hmeas : 𝔈)
    (hL2 : 𝔄) :
    MemLp 𝔉₁ 𝔗 2 μ := by
  have heind := hind.precomp e.injective
  have hcoord :=
    heind.comp (fun i => fun v => 𝖎 v)
       fun i => 𝖎 measurable_pi_apply
  exact independent_finset_product_memLp_two hcoord
    (fun i => (𝖎 measurable_pi_apply).comp 𝖍 hmeas)
    (fun i => 𝖍 hL2 $ σ i ) Finset.univ

𝗇 𝔭 ∏ i, 𝔑₁ f (τ i)
/-- Products of two coordinate monomials are integrable even when their
observation index sets overlap: each observation contributes at most twice. -/
theorem coordinate_monomial_pair_integrable
    (e : 𝔐) (f : 𝔙)
    (σ : 𝔡) (τ : 𝖒)
    (X : 𝔅) (hind : 𝔔)
    (hmeas : 𝔈)
    (hL2 : 𝔄) :
    Integrable (fun ω => 𝔗 *
      𝔭) μ := ((𝔴).integrable_mul
      $ coordinate_monomial_memLp_two f τ X hind hmeas hL2 ).congr
    𝖓

𝗇 𝔜 𝔑₁ s $ σ i
𝗇 𝕲 ∫ ω, ∏ i, 𝔜 ∂μ
/-- Group coordinate factors by their observation index before using independence. -/
theorem coordinate_product_integral_fiberwise
    [Fintype A]
    (s : A → Fin n) (σ : A → Fin p) (X : 𝔅)
    (hind : 𝔔) (hmeas : 𝔈) :
    𝕲 =
      ∏ j : Fin n, ∫ ω, ∏ i : A with s i = j, X j ω (σ i) ∂μ := by
  classical
  let F : Fin n → 𝔑 → ℝ := fun j v => ∏ i : A with s i = j, 𝖎 v
  have hF : ∀ j, Measurable $ F j := fun j =>
    Finset.measurable_prod _ fun i _ => 𝖎 measurable_pi_apply
  have hfind := hind.comp F hF
  have hfun : (fun ω => ∏ i, 𝔜) =
       fun ω => ∏ j, F j 𝔲 := by
    funext ω
    rw [← Finset.prod_fiberwise Finset.univ s
      𝔒₁ 𝔜]
    apply Finset.prod_congr rfl
    intro j _
    apply Finset.prod_congr rfl
    simp_all
  rw [hfun]
  exact hfind.integral_fun_prod_eq_prod_integral
     fun j => ((hF j).comp $ hmeas j ).aestronglyMeasurable

/-- A centered coordinate used at just one observation slot annihilates the
whole expectation. Pair integrability is provided by the previous theorem. -/
theorem coordinate_product_integral_eq_zero
    [Fintype A]
    (s : A → Fin n) (σ : A → Fin p) (X : 𝔅)
    (hind : 𝔔) (hmeas : 𝔈)
    (hmean : 𝔉)
    k (hk : ∀ i, s i = s k → i = k) :
    𝕲 = 0 := by
  classical
  rw [coordinate_product_integral_fiberwise s σ X hind hmeas]
  apply Finset.prod_eq_zero $ Finset.mem_univ $ s k
  have hfilter : Finset.univ.filter fun i => s i = s k = {k} := by
    grind
  rw [hfilter]
  simpa using hmean (s k) $ σ k

/-- Coordinate products of two distinct-index tuples are orthogonal if one
tuple contains an observation absent from the other. -/
theorem coordinate_monomial_pair_integral_eq_zero
    (e : 𝔐) (f : 𝔙)
    (σ : 𝔡) (τ : 𝖒)
    (X : 𝔅) (hind : 𝔔)
    (hmeas : 𝔈)
    (hmean : 𝔉)
    k (hk : e k ∉ Set.range f) :
     ∫ ω, 𝔗 * 𝔭 ∂μ = 0 := by
  have h := coordinate_product_integral_eq_zero (Sum.elim e f) (Sum.elim σ τ)
    X hind hmeas hmean (Sum.inl k) $ by
      simp_all
  simp_all

end

𝗇 𝔇 fun _ : Fin r => 𝔈₁
𝗇 𝔤 H fun i => 𝖎 Pi.single 1
𝗇 𝔥 fun i => ∑ a : Fin p, v i a • Pi.single a 1
𝗇 𝕮 MultilinearMap ℝ 𝔇 ℝ
𝗇 𝖜 𝘿
/-- Finite coordinate expansion of any multilinear map. -/
theorem multilinear_coordinate_expansion
    (H : 𝕮)
    v :
    H v = ∑ σ : 𝔡,
      𝔤 * ∏ i, v i (σ i) := by
  classical
  have hv : v = 𝔥 := by
    funext i a
    simp [Pi.single_apply]
  calc
    H v = H 𝔥 := congrArg H hv
    _ = ∑ σ : 𝔡, H fun i => v i (σ i) • 𝖎 Pi.single 1 := H.map_sum _
    𝖜 := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [H.map_smul_univ]
      ring

𝗇 𝔊 fun i => 𝖍 X ω
𝗇 𝖔 fun ω => H 𝔊
/-- A multilinear kernel applied to distinct independent `L²` observations
is itself square integrable, with no pointwise bound on the observations. -/
theorem multilinear_kernel_memLp_two [IsProbabilityMeasure μ]
    (H : 𝕮)
    (e : 𝔐) (X : 𝔅)
    (hind : 𝔔) (hmeas : 𝔈)
    (hL2 : 𝔄) :
    𝔐₁ 𝖔 := by
  have hexp : 𝖔 =
      fun ω => ∑ σ : 𝔡,
        𝔤 * 𝔗 := by
    funext ω
    exact multilinear_coordinate_expansion H _
  rw [hexp]
  exact memLp_finsetSum Finset.univ fun σ _ =>
    (𝔴).const_mul _

𝗇 𝔏 fun i => 𝔑₁ f
𝗇 𝔵 multilinear_kernel_memLp_two H e X hind hmeas hL2
𝗃 𝔞₁ fun _ : Fin ἀ => 𝔑
𝗇 𝔷 MultilinearMap ℝ 𝔞₁ t ℝ
/-- Two such kernels have an integrable product, including all possible
index overlaps. This discharges the integrability needed to expand covariance. -/
theorem multilinear_kernel_pair_integrable [IsProbabilityMeasure μ]

    (H : 𝕮)
    (G : 𝔷)
    (e : 𝔐) (f : 𝔙)
    (X : 𝔅) (hind : 𝔔)
    (hmeas : 𝔈)
    (hL2 : 𝔄) :
    Integrable (fun ω => H 𝔊 * G 𝔏) μ := ((𝔵).integrable_mul
      $ multilinear_kernel_memLp_two G f X hind hmeas hL2 ).congr
    𝖓

𝗃 𝔓₁ fun i => 𝖍 ἀ
/-- The product of two multilinear kernels expands into coordinate products. -/
theorem multilinear_pair_coordinate_expansion
    (H : 𝕮)
    (G : 𝔷)
    (e : 𝔐) (f : 𝔙) (v : Fin n → 𝔑) :
    H 𝔓₁ v * G (fun i => v $ f i ) =
      ∑ σ : 𝔡, ∑ τ : 𝖒,
        (𝔤 * G fun i => Pi.single (τ i) 1 ) *
        ((∏ i, 𝖍 v (σ i)) * ∏ i, v (f i) (τ i) ) := by
  classical
  rw [multilinear_coordinate_expansion H, multilinear_coordinate_expansion G,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro τ _
  ring

𝗇 𝔶 (coordinate_monomial_pair_integrable e f σ τ X hind hmeas hL2).const_mul _
𝗃 𝔘₁ ∫ ω, H 𝔊 * G ἀ ∂μ
𝗇 𝕭 𝔘₁ 𝔏
𝗇 𝖗 fun j => 𝔲
/-- Exact orthogonality of degenerate kernels on different observation sets,
with genuine finite second moments in place of pointwise boundedness. -/
theorem multilinear_kernel_pair_integral_eq_zero_left [IsProbabilityMeasure μ]

    (H : 𝕮)
    (G : 𝔷)
    (e : 𝔐) (f : 𝔙)
    (X : 𝔅) (hind : 𝔔)
    (hmeas : 𝔈)
    (hL2 : 𝔄)
    (hmean : 𝔉)
    k (hk : e k ∉ Set.range f) :
    𝕭 = 0 := by
  classical
  have hexp ω := multilinear_pair_coordinate_expansion H G e f 𝖗
  simp_rw [hexp]
  rw [integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro σ _
    rw [integral_finsetSum]
    · apply Finset.sum_eq_zero
      intro τ _
      rw [integral_const_mul,
        coordinate_monomial_pair_integral_eq_zero e f σ τ X hind hmeas hmean k hk,
        mul_zero]
    · intro τ _
      exact 𝔶
  · intro σ _
    exact integrable_finsetSum _ fun τ _ =>
      𝔶

𝗃 𝔍₁ ἀ H G e f X hind hmeas hL2
/-- Range inequality suffices for orthogonality, even at different kernel orders. -/
theorem multilinear_kernel_pair_integral_eq_zero [IsProbabilityMeasure μ]

    (H : 𝕮)
    (G : 𝔷)
    (e : 𝔐) (f : 𝔙)
    (X : 𝔅) (hind : 𝔔)
    (hmeas : 𝔈)
    (hL2 : 𝔄)
    (hmean : 𝔉)
    (hef : Set.range e ≠ Set.range f) :
    𝕭 = 0 := by
  classical
  by_cases hsub : Set.range e ⊆ Set.range f
  · obtain ⟨j, hj, hje⟩ := Set.not_subset.mp fun h => hef $ Set.Subset.antisymm hsub h
    obtain ⟨k, rfl⟩ := hj
    simpa only [mul_comm] using
      multilinear_kernel_pair_integral_eq_zero_left G H f e X hind hmeas hL2 hmean k hje
  · obtain ⟨j, hj, hjf⟩ := Set.not_subset.mp hsub
    obtain ⟨k, rfl⟩ := hj
    exact 𝔍₁ multilinear_kernel_pair_integral_eq_zero_left hmean k hjf

𝗇 𝕳 0 < r
/-- Every positive-order multilinear kernel is centered under independent,
coordinatewise centered observations. -/
theorem multilinear_kernel_integral_eq_zero [IsProbabilityMeasure μ]
    (hr : 𝕳)
    (H : 𝕮)
    (e : 𝔐) (X : 𝔅)
    (hind : 𝔔) (hmeas : 𝔈)
    (hL2 : 𝔄)
    (hmean : 𝔉) :
     ∫ ω, H 𝔊 ∂μ = 0 := by
  have hexp ω := multilinear_coordinate_expansion H 𝔊
  simp_rw [hexp]
  rw [integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro σ _
    rw [integral_const_mul,
      coordinate_product_integral_eq_zero e σ X hind hmeas hmean ⟨0, hr⟩
         fun i hi => e.injective hi , mul_zero]
  · intro σ _
    exact ((𝔴).integrable
      𝖠₄ ).const_mul _

/-- Ordered distinct-observation kernel sum. -/
def kernelSum
    (H : 𝕮)
    (X : 𝔅) : 𝖛 :=
  fun ω => ∑ e : 𝔐, H 𝔊

𝗇 𝔮 Set.range e.toFun = Set.range f.toFun
𝗃 𝔙₁ kernelSum ἀ X
𝗇 𝕴 𝔙₁ H
𝗃 𝖑 ∫ ω, ἀ ω ∂μ
𝗇 𝖘 covariance 𝕴 𝔙₁ G μ
section

variable [IsProbabilityMeasure μ]

/-- Distinct-observation kernel sums are genuinely square integrable. -/
theorem kernelSum_memLp_two
    (H : 𝕮)
    (X : 𝔅) (hind : 𝔔)
    (hmeas : 𝔈)
    (hL2 : 𝔄) :
    𝔐₁ 𝕴 :=
  memLp_finsetSum Finset.univ fun e _ => 𝔵

/-- Positive-order kernel sums have mean zero. -/
theorem kernelSum_integral_eq_zero
    (hr : 𝕳)
    (H : 𝕮)
    (X : 𝔅) (hind : 𝔔)
    (hmeas : 𝔈)
    (hL2 : 𝔄)
    (hmean : 𝔉) :
    𝖑 𝕴 = 0 := by
  unfold kernelSum
  rw [integral_finsetSum]
  · exact Finset.sum_eq_zero fun e _ => multilinear_kernel_integral_eq_zero
      hr H e X hind hmeas hL2 hmean
  · exact fun e _ => (𝔵).integrable
      𝖠₄

𝗇 𝔳 fun f _ => 𝔍₁ multilinear_kernel_pair_integrable
/-- Exact covariance expansion into the pairs with equal observation ranges.
This is the probabilistic foundation of the factorial-lift variance identity. -/
theorem kernelSum_covariance_same_range
    (hr : 𝕳) (ht : 𝘁₁)
    (H : 𝕮)
    (G : 𝔷)
    (X : 𝔅) (hind : 𝔔)
    (hmeas : 𝔈)
    (hL2 : 𝔄)
    (hmean : 𝔉) :
    𝖘 =
      ∑ e : 𝔐, ∑ f : 𝔙 with 𝔮,
        𝕭 := by
  classical
  unfold covariance
  rw [kernelSum_integral_eq_zero hr H X hind hmeas hL2 hmean,
    kernelSum_integral_eq_zero ht G X hind hmeas hL2 hmean]
  simp
  unfold kernelSum
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro e _
    rw [integral_finsetSum]
    · symm
      apply Finset.sum_subset $ Finset.filter_subset ..
      intro f _ hf
      exact 𝔍₁ multilinear_kernel_pair_integral_eq_zero hmean $ by simpa using hf
    · exact 𝔳
  · exact fun e _ => integrable_finsetSum _ 𝔳

end

𝗇 𝔧 Equiv.Perm $ Fin r
/-- Equal observation ranges differ by a permutation of the kernel slots. -/
theorem same_range_exists_perm (e f : 𝔐)
    (hef : Set.range f = Set.range e) :
    ∃ σ : 𝔧, ∀ i, 𝖎 e = f i := by
  let σ := (Equiv.ofInjective f f.injective).trans
    $ (Set.equivOfEq hef).trans (Equiv.ofInjective e e.injective).symm
  refine ⟨σ, fun i => ?_⟩
  exact Equiv.apply_ofInjective_symm e.injective _

𝗇 𝕵 Set.range f.toFun = Set.range e.toFun
section

variable (e : 𝔐)

theorem embedding_range_comp_perm
    (σ : 𝔧) : Set.range (σ.toEmbedding.trans e) = Set.range e := by
  simp

𝗇 𝖙 {f : 𝔐 // 𝕵}
/-- Exactly `r!` ordered distinct tuples represent one observation set. -/
theorem card_same_range_embeddings :
    Fintype.card 𝖙 = r.factorial := by
  classical
  let g : 𝔧 → 𝖙 :=
    fun σ => ⟨σ.toEmbedding.trans e, embedding_range_comp_perm e σ⟩
  have hg : Function.Bijective g := by
    constructor
    · intro σ τ h
      apply Equiv.ext
      intro i
      apply e.injective
      exact congrArg (fun f => f.val i) h
    · intro f
      obtain ⟨σ, hσ⟩ := same_range_exists_perm e f.val f.property
      refine ⟨σ, ?_⟩
      aesop
  rw [← Fintype.card_congr $ Equiv.ofBijective g hg , Fintype.card_perm, Fintype.card_fin]

theorem same_range_card_eq
    (f : 𝔙)
    (hef : Set.range e = Set.range f) : r = t := by
  have h := Fintype.card_congr $ (Equiv.ofInjective e e.injective).trans
    $ (Set.equivOfEq hef).trans (Equiv.ofInjective f f.injective).symm
  simpa using h

end

𝗇 𝔍 ∀ i j, IdentDistrib (X i) (X j) μ μ
𝗇 𝕰 ContinuousMultilinearMap ℝ 𝔇 ℝ
/-- Independent identically distributed observations give the same diagonal
kernel integral for every injective tuple. -/
theorem multilinear_pair_integral_identDistrib [IsProbabilityMeasure μ]

    (H G : 𝕰)
    (e f : 𝔐) (X : 𝔅)
    (hind : 𝔔) (hid : 𝔍) :
    𝔘₁ 𝔊 =
      ∫ ω, H 𝔏 * G 𝔏 ∂μ := by
  have h := IdentDistrib.pi (fun i => 𝖍 hid $ f i )
    (hind.precomp e.injective) $ hind.precomp f.injective
  exact (h.comp (H.cont.mul G.cont).measurable).integral_eq

𝗇 𝖈 fun i => 𝔑₁ e₀
𝗇 𝔖 ∫ ω, H 𝖈 * G 𝖈 ∂μ
𝗇 𝔛 fun i => 𝖎 v
𝗇 𝕶 ∀ (σ : 𝔧) v, G 𝔛 = G v
theorem multilinear_pair_integral_same_range [IsProbabilityMeasure μ]

    (H G : 𝕰)
    (hsym : 𝕶)
    (e f e₀ : 𝔐) (X : 𝔅)
    (hind : 𝔔) (hid : 𝔍)
    (hef : Set.range f = Set.range e) :
    𝕭 =
      𝔖 := by
  obtain ⟨σ, hσ⟩ := same_range_exists_perm e f hef
  have hG ω : G 𝔏 = G 𝔊 := by
    calc
      G 𝔏 = G fun i => X 𝖎 e ω :=
        congrArg G $ funext fun i => congrArg 𝖗 (hσ i).symm
      𝖜 := hsym σ 𝔊
  simp_rw [hG]
  exact multilinear_pair_integral_identDistrib H G e e₀ X hind hid

/-- The exact factorial covariance of the unnormalized kernel sum, for
square-integrable unbounded i.i.d. observations. -/
theorem kernelSum_covariance [IsProbabilityMeasure μ]
    (hr : 𝕳)
    (H G : 𝕰)
    (hsym : 𝕶)
    (e₀ : 𝔐) (X : 𝔅)
    (hind : 𝔔) (hmeas : 𝔈)
    (hid : 𝔍)
    (hL2 : 𝔄)
    (hmean : 𝔉) :
    covariance 𝔙₁ H.toMultilinearMap 𝔙₁ G.toMultilinearMap μ =
       n.descFactorial r * r.factorial *
        𝔖 := by
  rw [kernelSum_covariance_same_range hr hr H.toMultilinearMap G.toMultilinearMap
    X hind hmeas hL2 hmean]
  let J := 𝔖
  have hs (e : 𝔐) :
       ∑ f : 𝔐 with 𝔮,
        𝕭 =
      r.factorial * J := by
    have hfilterEq : Finset.univ.filter (fun f =>
        𝔮) =
        Finset.univ.filter fun f : 𝔐 =>
        𝕵 := by
      grind
    rw [hfilterEq]
    calc
      _ = ∑ f : 𝔐 with 𝕵, J := by
        apply Finset.sum_congr rfl
        intro f hf
        exact multilinear_pair_integral_same_range H G hsym e f e₀ X hind hid
          (Finset.mem_filter.mp hf).2
      𝖜 := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [← Fintype.card_subtype, card_same_range_embeddings e]
  change ∑ e : 𝔐,
    ∑ f : 𝔐 with 𝔮,
      𝕭 = _
  simp_rw [hs]
  simp
  ring

/-- Kernel sums of different positive orders are exactly orthogonal. -/
theorem kernelSum_covariance_different_orders [IsProbabilityMeasure μ]
    (hr : 𝕳) (ht : 𝘁₁) (hrt : r ≠ t)
    (H : 𝕮)
    (G : 𝔷)
    (X : 𝔅) (hind : 𝔔)
    (hmeas : 𝔈)
    (hL2 : 𝔄)
    (hmean : 𝔉) :
    𝖘 = 0 := by
  rw [kernelSum_covariance_same_range hr ht H G X hind hmeas hL2 hmean]
  apply Finset.sum_eq_zero
  intro e _
  have hfilter : Finset.univ.filter (fun f : 𝔙 =>
      𝔮) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro f hf
    exact hrt $ same_range_card_eq e f (Finset.mem_filter.mp hf).2
  simp_all

𝗃 𝔟₁ (ἀ : ℝ)
𝗃 𝔣₁ (n.descFactorial ἀ : ℝ)
/-- The normalization appearing in the centered Taylor lift. -/
def kernelStatistic
    (H : 𝕰)
    (X : 𝔅) : 𝖛 :=
  fun ω => (𝔟₁ r.factorial * 𝔣₁ r)⁻¹ *
    𝔙₁ H.toMultilinearMap ω

𝗇 𝖕 kernelStatistic H X
𝗃 𝔔₁ fun i => X (Fin.castLEEmb ἀ i) ω
/-- Exact variance of one centered symmetric factorial-lift term, with finite
second moments and no pointwise boundedness restriction. -/
theorem kernelStatistic_variance [IsProbabilityMeasure μ]
    (hr : 𝕳) hrn
    (H : 𝕰)
    (hsym : ∀ (σ : 𝔧) v, H 𝔛 = H v)
    (X : 𝔅) (hind : 𝔔)
    (hmeas : 𝔈)
    (hid : 𝔍)
    (hL2 : 𝔄)
    (hmean : 𝔉) :
    variance 𝖕 μ =
       (r.factorial * 𝔣₁ r)⁻¹ *
        ∫ ω, H 𝔔₁ hrn ^ 2 ∂μ := by
  unfold kernelStatistic
  rw [variance_const_mul, ← covariance_self
    (kernelSum_memLp_two H.toMultilinearMap X hind hmeas hL2).aemeasurable,
    kernelSum_covariance hr H H hsym (Fin.castLEEmb hrn) X hind hmeas hid hL2 hmean]
  field_simp

𝗇 𝔒 𝗙₁
𝗇 𝕬 (r : Fin R) → ContinuousMultilinearMap ℝ 𝔞₁ 𝔒 ℝ
𝗇 𝖝 kernelStatistic (H r) X ω
/-- The finite centered-kernel expansion of a polynomial lift. -/
def centeredKernelExpansion (c : ℝ)
    (H : 𝕬)
    (X : 𝔅) : 𝖛 :=
  fun ω => c + ∑ r, 𝖝

𝗇 𝔓 ∀ j a, 𝔊₁ 𝖇 = m a
𝗇 𝔨 hind.comp (fun _ => fun v => v - m) fun _ => measurable_id.sub_const m
𝗇 𝔄₁ memLp_const $ m a
𝗇 𝔪 fun j a => (hL2 j a).sub 𝔄₁
𝗇 𝖉 (𝔒).factorial
𝗇 𝕯 (𝖉 * 𝔣₁ 𝔒)⁻¹
𝗇 𝕻 fun j ω => 𝔲 - m
𝗇 𝕼 fun j => (hmeas j).sub_const m
𝗇 𝖊 X i ω
𝗃 𝔤₁ fun ἀ => 𝖊 - m
section

variable [IsProbabilityMeasure μ]

theorem kernelStatistic_memLp_two
    (H : 𝕰)
    (X : 𝔅) (hind : 𝔔)
    (hmeas : 𝔈)
    (hL2 : 𝔄) :
    𝔐₁ 𝖕 :=
  (kernelSum_memLp_two H.toMultilinearMap X hind hmeas hL2).const_mul _

𝗇 𝔢 kernelStatistic_memLp_two (H r) X hind hmeas hL2
𝗇 𝕹 centeredKernelExpansion c H X
𝗇 𝕺 memLp_finsetSum Finset.univ fun r _ => 𝔢
theorem centeredKernelExpansion_memLp_two
    (c : ℝ)
    (H : 𝕬)
    (X : 𝔅) (hind : 𝔔)
    (hmeas : 𝔈)
    (hL2 : 𝔄) :
    𝔐₁ 𝕹 :=
  (memLp_const c).add 𝕺

theorem kernelStatistic_integral_eq_zero
    (hr : 𝕳)
    (H : 𝕰)
    (X : 𝔅) (hind : 𝔔)
    (hmeas : 𝔈)
    (hL2 : 𝔄)
    (hmean : 𝔉) :
     ∫ ω, 𝖕 ω ∂μ = 0 := by
  unfold kernelStatistic
  rw [integral_const_mul,
    kernelSum_integral_eq_zero hr H.toMultilinearMap X hind hmeas hL2 hmean, mul_zero]

theorem centeredKernelExpansion_expectation
    (c : ℝ)
    (H : 𝕬)
    (X : 𝔅) (hind : 𝔔)
    (hmeas : 𝔈)
    (hL2 : 𝔄)
    (hmean : 𝔉) :
    𝖑 𝕹 = c := by
  unfold centeredKernelExpansion
  have hs :=
    (𝕺).integrable 𝖠₄
  rw [integral_add (integrable_const c) hs, integral_const,
    integral_finsetSum Finset.univ fun r _ =>
      (𝔢).integrable 𝖠₄ ]
  have hz : ∑ r : Fin R, 𝔊₁ 𝖝 = 0 :=
    Finset.sum_eq_zero fun r _ => kernelStatistic_integral_eq_zero
      (Nat.succ_pos r.val) (H r) X hind hmeas hL2 hmean
  simpa

𝗇 𝖃 (Nat.succ_le_of_lt r.isLt).trans hR
/-- Exact centered Taylor variance series under the original paper's finite
second-moment hypothesis, without restricting the responses to a bounded set. -/
theorem centeredKernelExpansion_variance
    (c : ℝ)
    (H : 𝕬)
    (hsym : ∀ r (σ : Equiv.Perm $ Fin 𝔒 ) v,
      H r 𝔛 = H r v)
    (X : 𝔅) hR
    (hind : 𝔔) (hmeas : 𝔈)
    (hid : 𝔍)
    (hL2 : 𝔄)
    (hmean : 𝔉) :
    variance 𝕹 μ =
      ∑ r : Fin R, 𝕯 *
        ∫ ω, H r 𝔔₁ 𝖃 ^ 2 ∂μ := by
  have hstats r := 𝔢
  have hsum :=
    memLp_finsetSum Finset.univ fun r _ => hstats r
  unfold centeredKernelExpansion
  rw [variance_const_add hsum.aestronglyMeasurable c, variance_fun_sum hstats]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_eq_single r]
  · rw [covariance_self (hstats r).aemeasurable]
    exact kernelStatistic_variance  𝖡₃ 
      𝖃 (H r) (hsym r) X hind hmeas hid hL2 hmean
  · intro t _ htr
    unfold kernelStatistic
    rw [covariance_const_mul_left, covariance_const_mul_right]
    have hrt : 𝔒 ≠ t.val + 1 := by
      omega
    rw [kernelSum_covariance_different_orders  𝖡₃   𝖡₃  hrt
      (H r).toMultilinearMap (H t).toMultilinearMap X hind hmeas hL2 hmean]
    ring
  simp

𝗇 𝖄 fun ω => 𝔲 - m
/-- Centering preserves all the actual probability and moment hypotheses. -/
theorem centerObservations_l2
    (X : 𝔅) m
    (hind : 𝔔) (hmeas : 𝔈)
    (hid : 𝔍)
    (hL2 : 𝔄)
    (hmean : 𝔓) :
    iIndepFun 𝕻 μ ∧
      (∀ j, Measurable 𝖄) ∧
      (∀ i j, IdentDistrib 𝔤₁ ω 𝖄 μ μ) ∧
      (∀ j a, MemLp (fun ω => 𝖇 - m a) 2 μ) ∧
       ∀ j a, ∫ ω, 𝖇 - m a ∂μ = 0 := by
  refine ⟨ 𝔨,
    𝕼,
    fun i j => (hid i j).comp $ measurable_id.sub_const m ,
    𝔪, ?_⟩
  intro j a
  rw [integral_sub ((hL2 j a).integrable 𝖠₄ ) $ integrable_const $ m a ,
    integral_const, hmean]
  simp

end

𝗇 𝔣 𝘣₁
𝗇 𝔩 𝙩₁
𝗇 𝔯 RoughRegime.Upper.polynomialLift F X
𝗇 𝕽 F.totalDegree ≤ R
𝗇 𝖞 R ≤ n
𝗇 𝔅₁ iteratedFDeriv ℝ 𝔒 𝔣 m
𝗃 𝔖₁ ἀ F X m hdeg hRn
/-- The supplied coefficient lift is the centered Taylor expansion. This
uses only the imported algebraic lift identity, which has no boundedness premise. -/
theorem polynomialLift_centering_l2
    (F : 𝔩) (X : 𝔅) m
    (hdeg : 𝕽) (hRn : 𝖞) :
    𝔯 =
      centeredKernelExpansion (MvPolynomial.eval m F)
        (fun r : Fin R => 𝔅₁)
        𝕻 := by
  rw [𝔖₁ RoughRegime.LiftTranslation.polynomialLift_eq_centeredDerivativeLift]
  rfl

𝗃 𝖌 fun _ => ἀ
𝗇 𝔎 Measure.pi 𝖌 μ
𝗇 𝖋 (Nat.succ_le_of_lt r.isLt).trans hRn
𝗇 𝔞 X (Fin.castLEEmb 𝖋 i) ω
𝗃 𝖐 ∀ a, MemLp (fun ω => ἀ ω a) 2 μ
𝗇 𝔟 𝖐 X
𝗇 𝔠 ∀ a, ∫ ω, X ω a ∂μ = m a
𝗇 𝕷 Ω → 𝔑
𝗇 𝕸 fun i => (hm i).aemeasurable
𝗇 𝕾 𝔖₁ polynomialLift_centering_l2
𝗇 𝕿 fun ω => 𝖊 a
𝗇 𝖚 centerObservations_l2 X m hind hmeas hid hL2 hmean
𝗃 𝔚₁ Fin r → ἀ
𝗃 𝔛₁ fun i => (hm ἀ).comp $ measurable_pi_apply i
section

variable [IsProbabilityMeasure μ]

/-- Original `lem:U6` exact variance identity for the actual unbiased polynomial
lift on unbounded i.i.d. `L²` features. -/
theorem polynomialLift_variance_l2
    (F : 𝔩)
    (X : 𝔅) (m : 𝔑)
    (hdeg : 𝕽) hRn
    (hind : 𝔔) (hmeas : 𝔈)
    (hid : 𝔍)
    (hL2 : 𝔄)
    (hmean : 𝔓) :
    variance 𝔯 μ =
      ∑ r : Fin R, 𝕯 *
        ∫ ω, (𝔅₁
           fun i => 𝔞 - m ) ^ 2 ∂μ := by
  obtain ⟨hi, hm, hid', hlp, hzero⟩ := 𝖚
  rw [𝕾]
  apply centeredKernelExpansion_variance _ _ ?_ _ hRn hi hm hid' hlp hzero
  intro r σ v
  exact (AnalyticOnNhd.eval_mvPolynomial F).analyticOn.iteratedFDeriv_comp_perm v σ

𝗇 𝖟 𝔑 →L[ℝ] ℝ
/-- Coordinatewise `L²` gives an integrable vector with the coordinate means. -/
theorem vector_integral_of_coordinate_moments
    (X : 𝕷) m
    (hL2 : 𝔟)
    (hmean : 𝔠) :
    Integrable X μ ∧ 𝖑 X = m := by
  have hi := integrable_pi_iff.mpr fun a =>
    (hL2 a).integrable 𝖠₄
  refine ⟨hi, ?_⟩
  funext a
  exact ((ContinuousLinearMap.proj a : 𝖟).integral_comp_comm hi).symm.trans $ hmean a

𝗇 𝖖 L $ X ω
/-- Subtracting the mean contracts the scalar `L²` norm of every linear functional. -/
theorem linear_centering_square_le_l2
    (X : 𝕷) (hm : Measurable X)
    (hL2 : 𝔟)
    m (hmean : 𝔠)
    (L : 𝖟) :
     ∫ ω, L (X ω - m) ^ 2 ∂μ ≤ ∫ ω, 𝖖 ^ 2 ∂μ := by
  obtain ⟨hi, hvector⟩ := vector_integral_of_coordinate_moments X m hL2 hmean
  have hLX : Measurable 𝔉₁ 𝖖 := L.continuous.measurable.comp hm
  have hml : 𝔊₁ 𝖖 = L m := by
    rw [L.integral_comp_comm hi, hvector]
  have hv := variance_le_expectation_sq (μ := μ) hLX.aestronglyMeasurable
  rw [variance_eq_integral hLX.aemeasurable, hml] at hv
  simpa

𝗃 𝔎₁ ∀ i a, MemLp (fun ω => ἀ i ω a) 2 μ
/-- Independent copies of possibly different coordinatewise `L²` vectors have
an integrable squared multilinear kernel. -/
theorem product_kernel_square_integrable_l2
    (H : 𝕰)
    (A : 𝔚₁ 𝕷) (hm : 𝖏 A)
    (hL2 : 𝔎₁ A) :
    Integrable (fun ω => H (fun i => A i $ ω i ) ^ 2)
      𝔎 := by
  let X : Fin r → 𝔚₁ Ω → 𝔑 := fun i ω => A i $ ω i
  have hmeas : 𝖏 X := 𝔛₁ i
  have hlp : ∀ i a, MemLp 𝕿 2 𝔎 := by
    intro i a
    exact (hL2 i a).comp_measurePreserving $ measurePreserving_eval 𝖌 μ i
  exact (multilinear_kernel_memLp_two H.toMultilinearMap (Function.Embedding.refl _) X
    (iIndepFun_pi 𝕸) hmeas hlp).integrable_sq

𝗇 𝔚 Fin 𝘜₂
𝗃 𝔏₁ fun _ : 𝔚 => ἀ
𝗇 𝖅 MeasurableEquiv.piFinSuccAbove 𝔏₁ Ω 0
𝗇 𝖆 measurePreserving_piFinSuccAbove 𝔏₁ μ 0
theorem integral_pi_succ_l2
    (f : (𝔚 → Ω) → ℝ) (hf : Integrable f 𝔎) :
     ∫ x, f x ∂ 𝔎 =
      ∫ x, ∫ y, f (Fin.cons x y) ∂ 𝔎 ∂μ := by
  let e := 𝖅
  have he := 𝖆
  rw [← (he.symm e).integral_comp' f]
  change ∫ x, (f ∘ e.symm) x ∂μ.prod 𝔎 = _
  rw [integral_prod _ $ (he.symm e).integrable_comp_of_integrable hf ]
  aesop

theorem kernel_cons_square_integrable_l2
    (H : ContinuousMultilinearMap ℝ 𝔏₁ 𝔑 ℝ)
    (A B : 𝕷) (hA : Measurable A) (hB : Measurable B)
    (hL2A : 𝖐 A)
    (hL2B : 𝖐 B) :
    Integrable (fun xy =>
      H (Fin.cons (A xy.1) fun j => B $ xy.2 j ) ^ 2)
      $ μ.prod 𝔎 := by
  let C : 𝔚 → 𝕷 := Fin.cons A 𝖌 B
  have hC : 𝖏 C := by
    intro i
    cases i using Fin.cases <;> simp [C, hA, hB]
  have hlpC : 𝔎₁ C := by
    intro i a
    cases i using Fin.cases
    all_goals bound
  let e := 𝖅
  have he := 𝖆
  have hf' := (he.symm e).integrable_comp_of_integrable $ product_kernel_square_integrable_l2 H C hC hlpC
  apply hf'.congr
  exact Filter.Eventually.of_forall fun xy => by
    apply congrArg fun z => z ^ 2
    apply congrArg H
    funext i
    cases i using Fin.cases <;> simp [C, e]

end

𝗇 𝔘 fun j => Y $ y j
𝗃 𝔠₁ H (Fin.cons (ἀ x) 𝔘) ^ 2
𝗇 𝖀 𝔠₁ Y
𝗇 𝖁 𝔠₁ X
𝗃 𝔗₁ _ = ∫ x, ∫ y, ἀ ∂ 𝔎 ∂μ
𝗃 𝔜₁ fun j => X $ ἀ j
𝗃 𝔡₁ ∫ y, ∫ x, ἀ ∂μ ∂ 𝔎
/-- Centering each slot of an independent multilinear kernel contracts its
squared norm. Only finite second moments are required. -/
theorem multilinear_iid_centering_square_le_l2 [MeasurableSpace Ω]
    μ [IsProbabilityMeasure μ]
    (H : 𝕰)
    (X : 𝕷) (hm : Measurable X)
    (hL2 : 𝔟)
    m (hmean : 𝔠) :
     ∫ ω, H (fun j => X (ω j) - m) ^ 2 ∂ 𝔎 ≤
      ∫ ω, H 𝔜₁ ω ^ 2 ∂ 𝔎 := by
  induction r with
  | zero =>
    apply le_of_eq
    congr 1
    funext ω
    congr 2
    funext j
    exact Fin.elim0 j
  | succ r ih =>
    let Y := fun ω => X ω - m
    have hY : Measurable Y := hm.sub measurable_const
    have hYlp := fun a =>
      (hL2 a).sub 𝔄₁
    have hc := kernel_cons_square_integrable_l2 H Y Y hY hY hYlp hYlp
    have hmix := kernel_cons_square_integrable_l2 H X Y hm hY hL2 hYlp
    have hu := kernel_cons_square_integrable_l2 H X X hm hm hL2 hL2
    have hiUncenter := product_kernel_square_integrable_l2 H 𝖌 X 𝖌 hm 𝖌 hL2
    calc
      𝔗₁ 𝖀 := by
        rw [integral_pi_succ_l2 _ $ product_kernel_square_integrable_l2 H 𝖌 Y 𝖌 hY 𝖌 hYlp ]
        congr 1
        funext x
        congr 1
        funext y
        congr 2
        funext j
        cases j using Fin.cases <;> simp
      _ = 𝔡₁ 𝖀 := integral_integral_swap hc
      _ ≤ 𝔡₁ 𝖁 := by
        apply integral_mono_ae hc.integral_prod_right hmix.integral_prod_right
        exact Filter.Eventually.of_forall fun y => by
          let L :=
            (ContinuousMultilinearMap.apply ℝ 𝖌 𝔑 ℝ
              𝔘).comp H.curryLeft
          simpa only [L, ContinuousLinearMap.comp_apply,
            ContinuousMultilinearMap.apply_apply, ContinuousMultilinearMap.curryLeft_apply]
            using linear_centering_square_le_l2 X hm hL2 m hmean L
      𝔗₁ 𝖁 := (integral_integral_swap hmix).symm
      _ ≤ ∫ x, ∫ y, H (Fin.cons (X x) 𝔜₁ y) ^ 2
          ∂ 𝔎 ∂μ := by
        apply integral_mono_ae hmix.integral_prod_left hu.integral_prod_left
        exact Filter.Eventually.of_forall fun x => by
          simpa only [ContinuousMultilinearMap.curryLeft_apply] using ih $ H.curryLeft $ X x
      𝖜 := by
        rw [integral_pi_succ_l2 _ hiUncenter]
        congr 1
        funext x
        congr 1
        funext y
        congr 2
        funext j
        cases j using Fin.cases <;> simp


𝗇 𝔦 ∫ ω, H 𝔤₁ i ^ 2 ∂μ
𝗇 𝔫 fun i => X j $ ω i
𝗇 𝔬 ∫ ω, H 𝔒₁ 𝖊 ^ 2 ∂μ
/-- The `L²` contraction transfers from independent product copies to actual
i.i.d. observations on an arbitrary probability space. -/
theorem independent_centering_square_le_l2 [MeasurableSpace Ω]
    μ [IsProbabilityMeasure μ]
    (H : 𝕰)
    (X : 𝔚₁ 𝕷) (hm : 𝖏 X)
    (hind : 𝔔) (hid : 𝔍)
    (hL2 : ∀ i a, 𝔐₁ 𝕿)
    m (hmean : ∀ i a, ∫ ω, 𝖊 a ∂μ = m a) :
    𝔦 ≤ 𝔬 := by
  by_cases hr : r = 0
  · subst r
    apply le_of_eq
    congr 1
    funext ω
    congr 2
    funext i
    exact Fin.elim0 i
  · let j : Fin r := ⟨0, Nat.pos_of_ne_zero hr⟩
    have hcopy : Measurable fun ω : 𝔚₁ Ω => 𝔫 :=
      measurable_pi_iff.mpr 𝔛₁ j
    have hjoint :=
      measurable_pi_iff.mpr hm
    have hjointLaw : IdentDistrib (fun ω => 𝔒₁ 𝖊)
        𝔉₁ 𝔫 μ 𝔎 := by
      refine ⟨hjoint.aemeasurable, hcopy.aemeasurable, ?_⟩
      rw [hind.map_fun_eq_pi_map 𝕸,
        Measure.pi_map_pi fun _ => (hm j).aemeasurable ]
      congr 1
      funext i
      exact (hid i j).map_eq
    have hc : Measurable fun v : 𝔚₁ 𝔑 => H (fun i => v i - m) ^ 2 :=
      (H.coe_continuous.measurable.comp
        $ measurable_pi_iff.mpr fun i => (measurable_pi_apply i).sub measurable_const ).pow_const 2
    have hcEq : 𝔦 =
        ∫ ω, H (fun i => X j (ω i) - m) ^ 2 ∂ 𝔎 := by
      simpa only [Function.comp_def] using (hjointLaw.comp hc).integral_eq
    have huEq : 𝔬 =
        ∫ ω, H 𝔫 ^ 2 ∂ 𝔎 := by
      simpa only [Function.comp_def] using (hjointLaw.comp $ H.coe_continuous.measurable.pow_const 2 ).integral_eq
    rw [hcEq, huEq]
    exact multilinear_iid_centering_square_le_l2 μ H (X j) (hm j) (hL2 j) m $ hmean j


/-- The actual coefficient lift is square integrable under coordinatewise `L²`. -/
theorem polynomialLift_memLp_two_l2 [IsProbabilityMeasure μ]
    (F : 𝔩)
    (X : 𝔅) (m : 𝔑)
    (hdeg : 𝕽) (hRn : 𝖞)
    (hind : 𝔔) (hmeas : 𝔈)
    (hL2 : 𝔄) :
    𝔐₁ 𝔯 := by
  rw [𝕾]
  exact centeredKernelExpansion_memLp_two _ _ _
    𝔨
    𝕼
    𝔪

/-- The coefficient lift is unbiased at the actual population mean. -/
theorem polynomialLift_expectation_l2 [IsProbabilityMeasure μ]
    (F : 𝔩)
    (X : 𝔅) (m : 𝔑)
    (hdeg : 𝕽) (hRn : 𝖞)
    (hind : 𝔔) (hmeas : 𝔈)
    (hid : 𝔍)
    (hL2 : 𝔄)
    (hmean : 𝔓) :
     ∫ ω, RoughRegime.Upper.polynomialLift F X ω ∂μ = MvPolynomial.eval m F := by
  obtain ⟨hi, hm, _, hlp, hzero⟩ := 𝖚
  rw [𝕾]
  exact centeredKernelExpansion_expectation _ _ _ hi hm hlp hzero

𝗇 𝕱 ∫ ω, 𝔅₁ 𝔒₁ 𝔞 ^ 2 ∂μ
𝗃 𝔢₁ fun i a => 𝖍 ἀ a
/-- Original U6 comparison with the true descending-factorial denominators. -/
theorem polynomialLift_variance_le_raw_l2 [IsProbabilityMeasure μ]
    (F : 𝔩)
    (X : 𝔅) (m : 𝔑)
    (hdeg : 𝕽) hRn
    (hind : 𝔔) (hmeas : 𝔈)
    (hid : 𝔍)
    (hL2 : 𝔄)
    (hmean : 𝔓) :
    variance 𝔯 μ ≤
      ∑ r : Fin R, 𝕯 *
        𝕱 := by
  rw [𝔖₁ polynomialLift_variance_l2 hind hmeas hid hL2 hmean]
  apply Finset.sum_le_sum
  intro r _
  apply mul_le_mul_of_nonneg_left _ 𝖠₃
  let e := Fin.castLEEmb 𝖋
  exact independent_centering_square_le_l2 μ _ 𝔓₁ X
    𝔓₁ hmeas (hind.precomp e.injective)
    (fun i j => 𝖍 hid $ e j ) 𝔢₁ hL2 m
    𝔢₁ hmean

𝗇 𝖂 (𝗉 - k : ℕ)
/-- A positive lower bound on each available observation count bounds the
whole descending factorial. -/
theorem descFactorial_lower_bound {n R k : ℕ} (hRn : 𝖞) (hkR : k ≤ R)
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (hΛn : Λ ≤ n - R + 1) :
    Λ ^ k ≤ n.descFactorial k := by
  have hkn : k ≤ 𝗉 := 𝖡₃
  have hcast : 𝔟₁ 𝖂 = 𝗉 - k := by
    simp_all
  have hRk : 𝔟₁ k ≤ R := by exact_mod_cast hkR
  calc
    Λ ^ k ≤ 𝖂 ^ k := pow_le_pow_left₀ hΛ  𝖡₄  k
    _ ≤ n.descFactorial k := by exact_mod_cast Nat.pow_sub_le_descFactorial n k

/-- The denominator comparison in U6 for every `0 < Λ ≤ n - degree + 1`. -/
theorem polynomialLift_variance_le_raw_power_l2 [IsProbabilityMeasure μ]
    {n p R : ℕ} F
    (X : 𝔅) m
    (hdeg : 𝕽) hRn
    (hind : 𝔔) (hmeas : 𝔈)
    (hid : 𝔍)
    (hL2 : 𝔄)
    (hmean : 𝔓)
    Λ (hΛ : 𝖠₂) (hΛn : Λ ≤ 𝔟₁ n - R + 1) :
    variance 𝔯 μ ≤
      ∑ r : Fin R, (𝖉 * Λ ^ 𝔒)⁻¹ *
        𝕱 := by
  apply (𝔖₁ polynomialLift_variance_le_raw_l2 hind hmeas hid hL2 hmean).trans
  apply Finset.sum_le_sum
  intro r _
  apply mul_le_mul_of_nonneg_right _ $ integral_nonneg 𝖸
  have hb := descFactorial_lower_bound hRn (Nat.succ_le_of_lt r.isLt) hΛ.le hΛn
  have hfac : 0 < 𝖉 := 𝖠₃
  bound
