module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
public import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.Topology.MetricSpace.Antilipschitz
public import Mathlib.Tactic

/-!
# Fredholm alternative, finite-rank completion (Lemma 7.2) and the fixed complement (Lemma 7.3)

The paper invokes the Fredholm alternative for operators of the form identity plus compact
(External theorem on compact operators). We use its spectral form from Mathlib and the
ascending-kernel Riesz argument, for an operator `I + C` with `C` compact on a Banach space over `ℝ` or `ℂ`:

* `finiteDimensional_ker_one_add`: `ker (I + C)` is finite-dimensional;
* `injective_iff_surjective_one_add`: `I + C` is injective iff it is surjective
  (the range direction from Mathlib, the kernel direction by a Riesz chain argument);
* `exists_complement_range_one_add`: there is a subspace of dimension `dim ker (I + C)` meeting
  `ran (I + C)` only in `0` (the half of "index zero" used in the paper).

With these:

* `finite_rank_completion` / `finite_rank_completion_isUnit` (**Lemma 7.2**): on a Hilbert space
  `H = H₀ ⊕ H₀ᗮ`, if `A = I + C` is injective on `H₀`, there is a finite-rank `F : H₀ᗮ → H` with
  `A + F Π₁` invertible;
* `finite_rank_completion_basis` (**Lemma 7.2**, second sentence): given Hilbert bases of `H` and
  `H₀ᗮ`, `F` can be taken as `∑_r ⟪u_r, ·⟫ v_r` with finite basis combinations `u_r`, `v_r`;
* `exists_fixed_complement` (**Lemma 7.3**, abstract form): for a norm-continuous family
  `Ĵ_E : H₀ → H` with `Ĵ_{E₀}` injective and `Ĵ_{E₀} Π₀ + Π₁ − I` compact, there is a fixed
  `R = inclusion + finite rank` such that `𝔅_E = Ĵ_E Π₀ + R Π₁` is invertible near `E₀`, with
  norm-continuous inverse; `exists_fixed_complement_basis` gives `R` with finite basis input and
  output vectors.

In the paper `H₀ = 𝓗_{≤0}`, `H₀ᗮ = 𝓗_+` and `Ĵ_E` is the normalized conormal transmutation; its
compactness property (Lemma 6.13) is a hypothesis here.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open Filter Topology

section Banach

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- A compact operator cannot map a norm-bounded sequence to a sequence with pairwise distances
at least `1/2`. -/
lemma IsCompactOperator.not_separated {C : X →L[𝕜] X} (hC : IsCompactOperator C)
    {u : ℕ → X} (hu : ∀ n, ‖u n‖ ≤ 1) (hsep : ∀ m n, m < n → 1 / 2 ≤ ‖C (u n) - C (u m)‖) :
    False := by
  obtain ⟨K, hK, hsub⟩ := hC.image_closedBall_subset_compact 1
  obtain ⟨y, -, φ, hφ, hlim⟩ := hK.tendsto_subseq fun n => hsub ⟨u n, by simpa using hu n, rfl⟩
  have hc := hlim.cauchySeq
  rw [Metric.cauchySeq_iff'] at hc
  obtain ⟨N, hN⟩ := hc (1 / 2) (by norm_num)
  have h1 := hN (N + 1) (by omega)
  rw [dist_eq_norm] at h1
  have := hsep (φ N) (φ (N + 1)) (hφ (by omega))
  exact h1.not_ge this

/-- Riesz chain argument, increasing version. -/
lemma not_strictMono_chain {C : X →L[𝕜] X} (hC : IsCompactOperator C)
    (N : ℕ → Submodule 𝕜 X) (hcl : ∀ n, IsClosed (N n : Set X))
    (hlt : ∀ n, N n < N (n + 1)) (hmap : ∀ n, ∀ x ∈ N (n + 1), x + C x ∈ N n) : False := by
  have hmono  := monotone_nat_of_le_succ fun n => (hlt n).le
  have hx : ∀ n, ∃ x ∈ N (n + 1), ‖x‖ = 1 ∧ ∀ y ∈ N n, 1 / 2 ≤ ‖x - y‖ := by
    intro n
    obtain ⟨z, hzn, hz⟩ := SetLike.exists_of_lt (hlt n)
    let F  := (N n).comap (N (n + 1)).subtype
    have hFc : IsClosed (F : Set (N (n + 1))) := (hcl n).preimage continuous_subtype_val
    obtain ⟨x, -, hx1, hxF⟩ := riesz_lemma_of_lt_one hFc ⟨⟨z, hzn⟩, hz⟩ (r := 1 / 2) (by norm_num)
    refine ⟨x, x.2, hx1, fun y hy => ?_⟩
    have := hxF ⟨y, (hlt n).le hy⟩ hy
    exact this
  choose u huN hu1 husep using hx
  refine IsCompactOperator.not_separated hC (u := u) ((by grind)) fun m n hmn => ?_
  have hmem : (u n + C (u n)) - (u m + C (u m)) + u m ∈ N n := by
    refine add_mem (sub_mem (hmap n _ (huN n)) (hmono ((by omega))
      (hmap m _ (huN m)))) (hmono ((by omega)) (huN m))
  have := husep n _ hmem
  rw [norm_sub_rev]
  convert this using 2
  abel

section Fredholm

variable [CompleteSpace X]

/-- **Fredholm alternative**, injective implies surjective: if `C` is compact and `I + C` is
injective, then `I + C` is surjective. -/
theorem surjective_of_injective_one_add {C : X →L[𝕜] X} (hC : IsCompactOperator C)
    (hinj : Function.Injective ⇑((1 : X →L[𝕜] X) + C)) :
    Function.Surjective ⇑((1 : X →L[𝕜] X) + C) := by
  rcases IsCompactOperator.hasEigenvalue_or_mem_resolventSet (T := -C) hC.neg (one_ne_zero : (1 : 𝕜) ≠ 0) with h | h
  · obtain ⟨v, hv, hne⟩ := h.exists_hasEigenvector
    have he : -C v = v := by simpa using Module.End.mem_eigenspace_iff.mp hv
    exact False.elim (hne (hinj ((show v + C v = 0 from (eq_neg_iff_add_eq_zero.mp he.symm)).trans (map_zero (1 + C)).symm)))
  · rw [spectrum.mem_resolventSet_iff] at h
    exact (ContinuousLinearMap.isUnit_iff_bijective.mp (by simpa using h)).2

omit [CompleteSpace X] in
/-- **Fredholm alternative**, surjective implies injective: if `C` is compact and `I + C` is
surjective, then `I + C` is injective. -/
theorem injective_of_surjective_one_add {C : X →L[𝕜] X} (hC : IsCompactOperator C)
    (hsurj : Function.Surjective ⇑((1 : X →L[𝕜] X) + C)) :
    Function.Injective ⇑((1 : X →L[𝕜] X) + C) := by
  set T : X →L[𝕜] X := 1 + C with hTdef
  rw [injective_iff_map_eq_zero]
  by_contra hne
  push_neg at hne
  obtain ⟨x₁, hx₁, hx₁0⟩ := hne
  have hsurjn : ∀ n : ℕ, Function.Surjective (T ^ n : X →L[𝕜] X) := fun n => by
    rw [FunLike.coe_pow_eq_iterate]
    exact hsurj.iterate n
  refine not_strictMono_chain hC (fun n => LinearMap.ker ((T ^ n : X →L[𝕜] X) : X →ₗ[𝕜] X))
    (fun n => (T ^ n).isClosed_ker) (fun n => ?_) (fun n => ?_)
  · refine lt_of_le_of_ne ?_ ?_
    · intro x hx
      simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hx ⊢
      simp [pow_succ', hx]
    · intro heq
      obtain ⟨z, hz⟩ := hsurjn n x₁
      have hmem : z ∈ LinearMap.ker ((T ^ (n + 1) : X →L[𝕜] X) : X →ₗ[𝕜] X) := by
        simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
        simp [pow_succ', hz, hx₁]
      rw [← heq] at hmem
      exact hx₁0 (hz ▸ hmem)
  · simp [LinearMap.mem_ker, pow_succ, hTdef]

/-- **Fredholm alternative**: for compact `C`, `I + C` is injective iff it is surjective. -/
theorem injective_iff_surjective_one_add {C : X →L[𝕜] X} (hC : IsCompactOperator C) :
    Function.Injective ⇑((1 : X →L[𝕜] X) + C) ↔ Function.Surjective ⇑((1 : X →L[𝕜] X) + C) :=
  ⟨surjective_of_injective_one_add hC, injective_of_surjective_one_add hC⟩

omit [CompleteSpace X] in
/-- A compact operator acting by a nonzero scalar on a closed subspace forces
that subspace to be finite dimensional. -/
lemma finiteDimensional_of_compact_scalar {C : X →L[𝕜] X} (hC : IsCompactOperator C)
    {K : Submodule 𝕜 X} (hK : IsClosed (K : Set X)) {μ : 𝕜} (hμ : μ ≠ 0)
    (he : ∀ v : K, C v = μ • (v : X)) : FiniteDimensional 𝕜 K := by
  have hc : IsCompactOperator (fun v : K => μ⁻¹ • C v) := (hC.comp_clm K.subtypeL).smul _
  simp_rw [he, inv_smul_smul₀ hμ] at hc
  exact FiniteDimensional.of_isCompactOperator_id (hc.codRestrict (fun v => v.2) hK)

omit [CompleteSpace X] in
/-- The kernel of `I + C` is finite-dimensional when `C` is compact. -/
theorem finiteDimensional_ker_one_add {C : X →L[𝕜] X} (hC : IsCompactOperator C) :
    FiniteDimensional 𝕜 (LinearMap.ker (((1 : X →L[𝕜] X) + C : X →L[𝕜] X) : X →ₗ[𝕜] X)) := by
  apply finiteDimensional_of_compact_scalar hC (1 + C).isClosed_ker (neg_ne_zero.mpr (one_ne_zero : (1 : 𝕜) ≠ 0))
  exact fun v => (eq_neg_of_add_eq_zero_right (show (v : X) + C v = 0 from v.2)).trans (neg_one_smul 𝕜 (v : X)).symm

end Fredholm

section FiniteRank

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- A bounded operator with finite-dimensional range is compact. -/
theorem isCompactOperator_of_finiteDimensional_range (F : X →L[𝕜] Y)
    [FiniteDimensional 𝕜 (LinearMap.range (F : X →ₗ[𝕜] Y))] : IsCompactOperator F := by
  let V := LinearMap.range F.toLinearMap
  exact (isCompactOperator_of_locallyCompactSpace_dom (F.codRestrict V (LinearMap.mem_range_self _))).clm_comp V.subtypeL

end FiniteRank

section Codim

variable [CompleteSpace X]

/-- A surjective linear map from a larger finite-dimensional space. -/
lemma exists_surjective_of_finrank_le {K Q : Type*} [AddCommGroup K] [Module 𝕜 K]
    [AddCommGroup Q] [Module 𝕜 Q] [FiniteDimensional 𝕜 K] [FiniteDimensional 𝕜 Q]
    (h : Module.finrank 𝕜 Q ≤ Module.finrank 𝕜 K) :
    ∃ L : K →ₗ[𝕜] Q, Function.Surjective L := by
  obtain ⟨f, hf⟩ := finrank_le_iff_exists_linearMap.mp h
  obtain ⟨g, hg⟩ := f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hf)
  exact ⟨g, fun x => ⟨f x, LinearMap.congr_fun hg x⟩⟩

omit [CompleteSpace X] in
/-- If the range of `I + C` together with a finite-dimensional `Q` spans everything, then
`dim Q ≥ dim ker (I + C)`. -/
lemma finrank_ker_le_of_sup_eq_top {C : X →L[𝕜] X} (hC : IsCompactOperator C)
    (Q : Submodule 𝕜 X) [FiniteDimensional 𝕜 Q]
    (htop : LinearMap.range (((1 : X →L[𝕜] X) + C : X →L[𝕜] X) : X →ₗ[𝕜] X) ⊔ Q = ⊤) :
    haveI := finiteDimensional_ker_one_add hC
    Module.finrank 𝕜 (LinearMap.ker (((1 : X →L[𝕜] X) + C : X →L[𝕜] X) : X →ₗ[𝕜] X)) ≤
      Module.finrank 𝕜 Q := by
  haveI := finiteDimensional_ker_one_add hC
  set A : X →L[𝕜] X := 1 + C with hAdef
  set K := LinearMap.ker (A : X →ₗ[𝕜] X)
  by_contra hlt
  push_neg at hlt
  obtain ⟨P, hP⟩ := Submodule.ClosedComplemented.of_finiteDimensional K
  obtain ⟨L, hL⟩ := exists_surjective_of_finrank_le (K := K) (Q := Q) hlt.le
  -- a nonzero element of the kernel of `L`
  obtain ⟨k₁, hk₁L, hk₁0⟩ : ∃ k₁ ∈ LinearMap.ker L, k₁ ≠ 0 := by
    have hrn := LinearMap.finrank_range_add_finrank_ker L
    have hr : Module.finrank 𝕜 (LinearMap.range L) ≤ Module.finrank 𝕜 Q :=
      Submodule.finrank_le _
    
    refine Submodule.exists_mem_ne_zero_of_ne_bot (Submodule.one_le_finrank_iff.1 ?_)
    omega
  let Lc  := LinearMap.toContinuousLinearMap L
  let F  := Q.subtypeL ∘L Lc ∘L P
  have hFrange : FiniteDimensional 𝕜 (LinearMap.range (F : X →ₗ[𝕜] X)) := by
    refine Submodule.finiteDimensional_of_le (S₂ := Q) ?_
    rintro _ ⟨x, rfl⟩
    exact (Lc (P x)).2
  
  have hKA : ∀ k ∈ K, A k = 0 := fun k hk => hk
  have hsurj : Function.Surjective ((1 : X →L[𝕜] X) + (C + F)) := by
    intro h
    have hh : h ∈ LinearMap.range (A : X →ₗ[𝕜] X) ⊔ Q := htop ▸ Submodule.mem_top
    obtain ⟨_, ⟨x, rfl⟩, q, hq, rfl⟩ := Submodule.mem_sup.1 hh
    obtain ⟨k₀, hk₀⟩ := hL ⟨q, hq⟩
    refine ⟨x - (P x) + k₀, ?_⟩
    have h1 : (1 : X →L[𝕜] X) + (C + F) = A + F := by rw [hAdef, add_assoc]
    rw [h1, ContinuousLinearMap.add_apply]
    have hA : A (x - (P x : X) + (k₀ : X)) = A x := by
      simp
    have hF : F (x - (P x : X) + (k₀ : X)) = q := by
      simp only [F, ContinuousLinearMap.comp_apply, map_add, map_sub]
      have hPx  := hP (P x)
      have hPk  := hP k₀
      simp [hPx, hPk, sub_self, Lc, hk₀]
    simp [hA, hF]
  have hinj := injective_of_surjective_one_add (hC.add (isCompactOperator_of_finiteDimensional_range F)) hsurj
  apply hk₁0
  have : (1 + (C + F)) k₁ = (1 + (C + F)) 0 := by
    have h1 : (1 : X →L[𝕜] X) + (C + F) = A + F := by rw [hAdef, add_assoc]
    rw [h1, map_zero, ContinuousLinearMap.add_apply, hKA _ k₁.2, zero_add]
    simp only [F, ContinuousLinearMap.comp_apply, hP k₁]
    simp [Lc, LinearMap.mem_ker.1 hk₁L]
  exact Subtype.ext (hinj this)

omit [CompleteSpace X] in
/-- The range of `I + C` has codimension at least `dim ker (I + C)`: there is a subspace `Q`
of dimension `dim ker (I + C)` meeting the range only in `0`. -/
theorem exists_complement_range_one_add {C : X →L[𝕜] X} (hC : IsCompactOperator C) :
    haveI := finiteDimensional_ker_one_add hC
    ∃ Q : Submodule 𝕜 X, FiniteDimensional 𝕜 Q ∧
      Module.finrank 𝕜 Q =
        Module.finrank 𝕜 (LinearMap.ker (((1 : X →L[𝕜] X) + C : X →L[𝕜] X) : X →ₗ[𝕜] X)) ∧
      Disjoint Q (LinearMap.range (((1 : X →L[𝕜] X) + C : X →L[𝕜] X) : X →ₗ[𝕜] X)) := by
  haveI := finiteDimensional_ker_one_add hC
  set k := Module.finrank 𝕜 (LinearMap.ker ((1 + C : X →L[𝕜] X) : X →ₗ[𝕜] X))
  set Rg := LinearMap.range ((1 + C : X →L[𝕜] X) : X →ₗ[𝕜] X)
  suffices h : ∀ n ≤ k, ∃ Q : Submodule 𝕜 X, FiniteDimensional 𝕜 Q ∧
      Module.finrank 𝕜 Q = n ∧ Disjoint Q Rg from h k le_rfl
  intro n
  induction n with
  | zero => exact fun _ => ⟨⊥, inferInstance, finrank_bot _ _, disjoint_bot_left⟩
  | succ n ih =>
    intro hn
    obtain ⟨Q, hQf, hQn, hQd⟩ := ih (by omega)
    by_cases htop : Rg ⊔ Q = ⊤
    · have := finrank_ker_le_of_sup_eq_top hC Q htop
      omega
    · obtain ⟨y, -, hy⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr htop)
      have hd := Submodule.disjoint_span_singleton_of_notMem hy
      have hyQ : y ∉ Q := fun h => hy (Submodule.mem_sup_right h)
      have hy0 : y ≠ 0 := fun h => hyQ (h ▸ Q.zero_mem)
      refine ⟨Q ⊔ Submodule.span 𝕜 {y}, inferInstance, ?_,
        (hQd.symm.disjoint_sup_right_of_disjoint_sup_left hd).symm⟩
      have hr := Submodule.finrank_sup_add_finrank_inf_eq Q (Submodule.span 𝕜 {y})
      rw [(Submodule.disjoint_span_singleton_of_notMem hyQ).eq_bot, finrank_bot, add_zero, finrank_span_singleton hy0, hQn] at hr
      exact hr

end Codim

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- **Lemma 7.2 (finite-rank completion).** Let `H = H₀ ⊕ H₀ᗮ` be a Hilbert space and
`A = I + C` with `C` compact. If `A` is injective on `H₀`, there is a finite-rank bounded
`F : H₀ᗮ → H` such that `A + F Π₁` is bijective, where `Π₁` is the orthogonal projection onto
`H₀ᗮ`. -/
theorem finite_rank_completion {C : H →L[𝕜] H} (hC : IsCompactOperator C)
    (H₀ : Submodule 𝕜 H) [H₀.HasOrthogonalProjection]
    (hinj : ∀ x ∈ H₀, x + C x = 0 → x = 0) :
    ∃ F : H₀ᗮ →L[𝕜] H, FiniteDimensional 𝕜 (LinearMap.range (F : H₀ᗮ →ₗ[𝕜] H)) ∧
      Function.Bijective ⇑((1 : H →L[𝕜] H) + C + F ∘L H₀ᗮ.orthogonalProjection) := by
  haveI := finiteDimensional_ker_one_add hC
  set A : H →L[𝕜] H := 1 + C with hAdef
  set K := LinearMap.ker (A : H →ₗ[𝕜] H) with hKdef
  obtain ⟨Q, hQf, hQk, hQd⟩ := exists_complement_range_one_add hC
  set P₁ : H →L[𝕜] H₀ᗮ := H₀ᗮ.orthogonalProjection
  have hKA : ∀ k ∈ K, k + C k = 0 := fun k hk => (LinearMap.mem_ker.1 hk)
  -- `Π₁` is injective on the kernel
  have hP₁inj : Function.Injective ((P₁ : H →ₗ[𝕜] H₀ᗮ) ∘ₗ K.subtype) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro k hk
    rw [LinearMap.mem_ker, LinearMap.comp_apply] at hk
    
    have := hinj _ (by
      have := (Submodule.orthogonalProjection_eq_zero_iff ).1 hk
      rwa [Submodule.orthogonal_orthogonal] at this) (hKA _ k.2)
    simp [Subtype.ext_iff, this]
  set M : Submodule 𝕜 H₀ᗮ := LinearMap.range (P₁ ∘ₗ K.subtype) with hMdef
  
  let e : M ≃ₗ[𝕜] Q := LinearEquiv.ofFinrankEq _ _ (by rw [(LinearMap.finrank_range_of_inj hP₁inj), hQk])
  let Lc  := LinearMap.toContinuousLinearMap (e : M →ₗ[𝕜] Q)
  let F  := Q.subtypeL ∘L Lc ∘L M.orthogonalProjection
  have hFQ : ∀ y, F y ∈ Q := fun y => (Lc _).2
  
  refine ⟨F, (by
    refine Submodule.finiteDimensional_of_le (S₂ := Q) ?_
    rintro _ ⟨x, rfl⟩
    exact hFQ x), ?_⟩
  have hFP : FiniteDimensional 𝕜 (LinearMap.range ((F ∘L P₁ : H →L[𝕜] H) : H →ₗ[𝕜] H)) := by
    refine Submodule.finiteDimensional_of_le (S₂ := Q) ?_
    rintro _ ⟨x, rfl⟩
    exact hFQ _
  
  
  have hinj' : Function.Injective ⇑(1 + C + F ∘L P₁) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply] at hx
    have hAx  := eq_neg_of_add_eq_zero_left hx
    have hAx0 : A x = 0 := by
      refine Submodule.disjoint_def.1 hQd (A x) ?_ ⟨x, rfl⟩
      simp [*]
    have hxK  := hAx0
    have hF0 : F (P₁ x) = 0 := by rw [← neg_eq_zero, ← hAx, hAx0]
    have hPM : P₁ x ∈ M := ⟨⟨x, hxK⟩, rfl⟩
    have hPx  :=
      Submodule.orthogonalProjection_mem_subspace_eq_self (K := M) ⟨P₁ x, hPM⟩
    have hP0 : P₁ x = 0 := by
      have h1 : (e ⟨P₁ x, hPM⟩ : H) = 0 := by
        simpa [F, Lc, hPx] using hF0
      have h2 : e ⟨P₁ x, hPM⟩ = 0 := Subtype.ext h1
      have h3 := h2
      simpa using congrArg Subtype.val h3
    
    refine hinj x ?_ (hKA x hxK)
    have := (Submodule.orthogonalProjection_eq_zero_iff ).1 hP0
    rwa [Submodule.orthogonal_orthogonal] at this
  refine ⟨hinj', ?_⟩
  rw [(add_assoc _ _ _)] at hinj' ⊢
  exact surjective_of_injective_one_add (hC.add (isCompactOperator_of_finiteDimensional_range _)) hinj'

/-- **Lemma 7.2**, stated with invertibility in the operator algebra: `A + F Π₁` is a unit. -/
theorem finite_rank_completion_isUnit {C : H →L[𝕜] H} (hC : IsCompactOperator C)
    (H₀ : Submodule 𝕜 H) [H₀.HasOrthogonalProjection]
    (hinj : ∀ x ∈ H₀, x + C x = 0 → x = 0) :
    ∃ F : H₀ᗮ →L[𝕜] H, FiniteDimensional 𝕜 (LinearMap.range (F : H₀ᗮ →ₗ[𝕜] H)) ∧
      IsUnit ((1 : H →L[𝕜] H) + C + F ∘L H₀ᗮ.orthogonalProjection) := by
  obtain ⟨F, hF, hbij⟩ := finite_rank_completion hC H₀ hinj
  exact ⟨F, hF, ContinuousLinearMap.isUnit_iff_bijective.mpr hbij⟩

section

variable (H₀ : Submodule 𝕜 H) [H₀.HasOrthogonalProjection]

/-- Invertibility at `E₀` of `Ĵ_E Π₀ + R Π₁` propagates to a neighbourhood of `E₀`, with
norm-continuous inverse. -/
lemma isUnit_nhds_of_isUnit
    {J : ℝ → (H₀ →L[𝕜] H)} (hJ : Continuous J) {E₀ : ℝ} (R : H₀ᗮ →L[𝕜] H)
    (hunit : IsUnit (J E₀ ∘L H₀.orthogonalProjection + R ∘L H₀ᗮ.orthogonalProjection)) :
    ∃ U ∈ 𝓝 E₀,
      (∀ E ∈ U, IsUnit (J E ∘L H₀.orthogonalProjection + R ∘L H₀ᗮ.orthogonalProjection)) ∧
      ContinuousOn (fun E => Ring.inverse
        (J E ∘L H₀.orthogonalProjection + R ∘L H₀ᗮ.orthogonalProjection)) U := by
  set B : ℝ → (H →L[𝕜] H) :=
    fun E => J E ∘L H₀.orthogonalProjection + R ∘L H₀ᗮ.orthogonalProjection with hBdef
  
  refine ⟨B ⁻¹' {x | IsUnit x}, (Units.isOpen.preimage (by
    fun_prop)).mem_nhds hunit, fun E hE => hE, ?_⟩
  intro E hE
  obtain ⟨u, hu⟩ := hE
  have := NormedRing.inverse_continuousAt u
  rw [hu] at this
  fun_prop

omit [CompleteSpace H] in
/-- In the setting of Lemma 7.3, write `Ĵ_{E₀} Π₀ + Π₁ = I + C`. Then `I + C` is injective on
`H₀` and `Ĵ_{E₀} Π₀ + (ι + F) Π₁ = I + C + F Π₁` for every `F`. -/
lemma fixed_complement_aux
    (J₀ : H₀ →L[𝕜] H) (hinj : Function.Injective J₀) :
    (∀ x ∈ H₀, x + (J₀ ∘L H₀.orthogonalProjection +
      Submodule.subtypeL H₀ᗮ ∘L H₀ᗮ.orthogonalProjection - (1 : H →L[𝕜] H)) x = 0 → x = 0) ∧
    ∀ F : H₀ᗮ →L[𝕜] H, J₀ ∘L H₀.orthogonalProjection +
        (Submodule.subtypeL H₀ᗮ + F) ∘L H₀ᗮ.orthogonalProjection =
      (1 : H →L[𝕜] H) + (J₀ ∘L H₀.orthogonalProjection +
        Submodule.subtypeL H₀ᗮ ∘L H₀ᗮ.orthogonalProjection - (1 : H →L[𝕜] H)) +
        F ∘L H₀ᗮ.orthogonalProjection := by
  refine ⟨fun x hx h0 => ?_, fun F => ?_⟩
  · have hP₁  :=
      Submodule.orthogonalProjection_eq_zero_iff.2
        (Submodule.le_orthogonal_orthogonal H₀ hx)
    have hP₀  :=
      Submodule.orthogonalProjection_mem_subspace_eq_self (K := H₀) ⟨x, hx⟩
    simp [hP₁, hP₀, add_sub_cancel] at h0
    have := hinj (h0.trans (map_zero J₀).symm)
    exact congrArg Subtype.val this
  · simp only [ContinuousLinearMap.add_comp]
    abel

end

/-- A finite-rank bounded operator between Hilbert spaces is a finite sum of rank-one operators
`z ↦ ⟪u_r, z⟫ v_r`. -/
lemma exists_eq_sum_rankOne {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y]
    [CompleteSpace Y] (F : Y →L[𝕜] H) [FiniteDimensional 𝕜 (LinearMap.range (F : Y →ₗ[𝕜] H))] :
    ∃ (d : ℕ) (u : Fin d → Y) (v : Fin d → H),
      F = ∑ r, InnerProductSpace.rankOne 𝕜 (v r) (u r) := by
  set V := LinearMap.range (F : Y →ₗ[𝕜] H)
  let e := stdOrthonormalBasis 𝕜 V
  refine ⟨_, fun r => ContinuousLinearMap.adjoint F (e r), fun r => (e r), ?_⟩
  ext z
  
  have := congrArg Subtype.val (e.sum_repr' (⟨F z, LinearMap.mem_range_self _ z⟩ : V))
  simp only [Submodule.coe_sum, Submodule.coe_smul] at this
  rw [ContinuousLinearMap.sum_apply]
  simp [ContinuousLinearMap.adjoint_inner_left]
  conv_lhs => rw [← this]
  rfl

omit [CompleteSpace H] in
/-- Joint continuity of the rank-one operator `(x, y) ↦ ⟪y, ·⟫ x`. -/
lemma continuous_rankOne {Y Z : Type*} [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y]
    [TopologicalSpace Z] {f : Z → H} {g : Z → Y} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun z => InnerProductSpace.rankOne 𝕜 (f z) (g z) := by
  simp [InnerProductSpace.rankOne_def']
  refine Continuous.clm_comp ?_ ((innerSL 𝕜 (E := Y)).continuous.comp hg)
  exact (ContinuousLinearMap.toSpanSingletonCLE  (E := H)).continuous.comp hf

variable {ι ι₁ : Type*}

/-- **Lemma 7.2, basis refinement.** If `H` and `H₀ᗮ` carry Hilbert bases `b`, `b₁`, the
finite-rank correction can be taken of the form `F z = ∑_r ⟪u_r, z⟫ v_r` with every `u_r` a finite
linear combination of the `b₁ i` and every `v_r` a finite linear combination of the `b i`. -/
theorem finite_rank_completion_basis {C : H →L[𝕜] H} (hC : IsCompactOperator C)
    (H₀ : Submodule 𝕜 H) [H₀.HasOrthogonalProjection]
    (hinj : ∀ x ∈ H₀, x + C x = 0 → x = 0)
    (b : HilbertBasis ι 𝕜 H) (b₁ : HilbertBasis ι₁ 𝕜 H₀ᗮ) :
    ∃ (d : ℕ) (u : Fin d → H₀ᗮ) (v : Fin d → H),
      (∀ r, u r ∈ Submodule.span 𝕜 (Set.range b₁)) ∧
      (∀ r, v r ∈ Submodule.span 𝕜 (Set.range b)) ∧
      IsUnit ((1 : H →L[𝕜] H) + C +
        (∑ r, InnerProductSpace.rankOne 𝕜 (v r) (u r)) ∘L H₀ᗮ.orthogonalProjection) := by
  obtain ⟨F, hF, hunit⟩ := finite_rank_completion_isUnit hC H₀ hinj
  obtain ⟨d, u, v, rfl⟩ := exists_eq_sum_rankOne F
  set P₁ : H →L[𝕜] H₀ᗮ := H₀ᗮ.orthogonalProjection
  let Φ : (Fin d → H₀ᗮ) × (Fin d → H) → (H →L[𝕜] H) := fun p =>
    1 + C + (∑ r, InnerProductSpace.rankOne 𝕜 (p.2 r) (p.1 r)) ∘L P₁
  have hΦ : Continuous Φ := by
    refine continuous_const.add ?_
    refine ((ContinuousLinearMap.compL 𝕜 H H₀ᗮ H).flip P₁).continuous.comp ?_
    refine continuous_finset_sum _ fun r _ => ?_
    exact continuous_rankOne ((continuous_apply r).comp continuous_snd)
      ((by fun_prop))
  
  have hdense : Dense ((Set.univ.pi fun _ : Fin d => (Submodule.span 𝕜 (Set.range b₁) : Set H₀ᗮ))
      ×ˢ (Set.univ.pi fun _ : Fin d => (Submodule.span 𝕜 (Set.range b) : Set H))) := by
    refine Dense.prod (dense_pi _ fun _ _ => ?_) (dense_pi _ fun _ _ => ?_)
    · exact Submodule.dense_iff_topologicalClosure_eq_top.2 b₁.dense_span
    · exact Submodule.dense_iff_topologicalClosure_eq_top.2 b.dense_span
  obtain ⟨⟨u', v'⟩, hmem, hD⟩ := hdense.inter_open_nonempty _ (Units.isOpen.preimage hΦ) ⟨(u, v), hunit⟩
  simp at hD
  exact ⟨d, u', v', hD.1, hD.2, hmem⟩

/-- **Lemma 7.3**, with finite basis input and output vectors: given Hilbert bases `b` of `H`
and `b₁` of `H₀ᗮ`, the fixed map can be taken as `R z = z + ∑_r ⟪u_r, z⟫ v_r` with finite basis
combinations `u_r`, `v_r`. -/
theorem exists_fixed_complement_basis (H₀ : Submodule 𝕜 H) [H₀.HasOrthogonalProjection]
    {J : ℝ → (H₀ →L[𝕜] H)} (hJ : Continuous J) {E₀ : ℝ}
    (hcpt : IsCompactOperator (J E₀ ∘L H₀.orthogonalProjection +
      Submodule.subtypeL H₀ᗮ ∘L H₀ᗮ.orthogonalProjection - (1 : H →L[𝕜] H)))
    (hinj : Function.Injective (J E₀))
    (b : HilbertBasis ι 𝕜 H) (b₁ : HilbertBasis ι₁ 𝕜 H₀ᗮ) :
    ∃ (d : ℕ) (u : Fin d → H₀ᗮ) (v : Fin d → H),
      (∀ r, u r ∈ Submodule.span 𝕜 (Set.range b₁)) ∧
      (∀ r, v r ∈ Submodule.span 𝕜 (Set.range b)) ∧
      ∃ U ∈ 𝓝 E₀,
        (∀ E ∈ U, IsUnit (J E ∘L H₀.orthogonalProjection +
          (Submodule.subtypeL H₀ᗮ + ∑ r, InnerProductSpace.rankOne 𝕜 (v r) (u r)) ∘L
            H₀ᗮ.orthogonalProjection)) ∧
        ContinuousOn (fun E => Ring.inverse (J E ∘L H₀.orthogonalProjection +
          (Submodule.subtypeL H₀ᗮ + ∑ r, InnerProductSpace.rankOne 𝕜 (v r) (u r)) ∘L
            H₀ᗮ.orthogonalProjection)) U := by
  obtain ⟨hinj', heq⟩ := fixed_complement_aux H₀ (J E₀) hinj
  obtain ⟨d, u, v, hu, hv, hunit⟩ := finite_rank_completion_basis hcpt H₀ hinj' b b₁
  exact ⟨d, u, v, hu, hv, isUnit_nhds_of_isUnit H₀ hJ _ (by rw [heq]; exact hunit)⟩

end Hilbert

end Banach

end PolyaNeumann
