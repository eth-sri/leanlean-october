module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.Normed.Operator.Compact
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
(External theorem on compact operators). We use Mathlib's compact-operator spectral theorem
for the injective case, and split off the finite-dimensional kernel for the converse:

* `finiteDimensional_ker_one_add`: `ker (I + C)` is finite-dimensional;
* Fredholm alternative: `I + C` is injective iff it is surjective on a Banach space over `ℝ` or `ℂ`;
* `exists_complement_range_one_add`: there is a subspace of dimension `dim ker (I + C)` meeting
  `ran (I + C)` only in `0` (the half of "index zero" used in the paper).

With these:

* `finite_rank_completion` / `finite_rank_completion_isUnit` (**Lemma 7.2**): on a Hilbert space
  `H = H₀ ⊕ H₀ᗮ`, if `A = I + C` is injective on `H₀`, there is a finite-rank `F : H₀ᗮ → H` with
  `A + F Π₁` invertible;
* `finite_rank_completion_basis`: the output vectors of `F = ∑_r ⟪u_r, ·⟫ v_r` can be chosen
  in the finite span of the given Hilbert basis of `H`;
* `exists_fixed_complement_basis`: for a continuous family `Ĵ_E`, the same complement is
  invertible for all energies near `E₀`.

In the paper `H₀ = 𝓗_{≤0}`, `H₀ᗮ = 𝓗_+` and `Ĵ_E` is the normalized conormal transmutation; its
compactness property (Lemma 6.13) is a hypothesis here.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open Filter Topology

section Banach

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

section Fredholm

variable [CompleteSpace X]

/-- The injective case of the Fredholm alternative at the spectral parameter `-1`. -/
theorem surjective_of_injective_one_add {C : X →L[𝕜] X} (hC : IsCompactOperator C)
    (hinj : Function.Injective ⇑((1 : X →L[𝕜] X) + C)) :
    Function.Surjective ⇑((1 : X →L[𝕜] X) + C) := by
  have hn : (-1 : 𝕜) ∉ spectrum 𝕜 C := by
    intro hs
    obtain ⟨x, hx⟩ := ((hC.hasEigenvalue_iff_mem_spectrum (by simp)).2 hs).exists_hasEigenvector
    exact hx.2 (hinj (by simp [show C x = (-1 : 𝕜) • x from hx.apply_eq_smul]))
  have hu := spectrum.notMem_iff.mp hn
  rw [map_neg, map_one, ← neg_add', IsUnit.neg_iff] at hu
  exact (ContinuousLinearMap.isUnit_iff_bijective.mp hu).2

omit [CompleteSpace X] in
/-- The kernel of `I + C` is finite-dimensional when `C` is compact. -/
theorem finiteDimensional_ker_one_add {C : X →L[𝕜] X} (hC : IsCompactOperator C) :
    FiniteDimensional 𝕜 (LinearMap.ker (((1 : X →L[𝕜] X) + C : X →L[𝕜] X) : X →ₗ[𝕜] X)) := by
  let K := LinearMap.ker (((1 : X →L[𝕜] X) + C : X →L[𝕜] X) : X →ₗ[𝕜] X)
  have hK : ∀ x : K, (-C) x ∈ K := by
    intro x
    have hx : (x : X) + C x = 0 := x.2
    rw [ContinuousLinearMap.neg_apply, ← eq_neg_of_add_eq_zero_left hx]
    assumption
  apply FiniteDimensional.of_isCompactOperator_id
  convert (hC.neg.comp_clm K.subtypeL).codRestrict hK ((1 + C).isClosed_ker) using 1
  ext x
  have hx := x.2
  exact eq_neg_of_add_eq_zero_left hx

/-- A surjective compact perturbation of the identity splits along its finite-dimensional
kernel. The bounded right inverse is itself a compact perturbation of the identity, so it
is surjective by the injective case of the Fredholm alternative. -/
theorem injective_of_surjective_one_add {C : X →L[𝕜] X} (hC : IsCompactOperator C)
    (hsurj : Function.Surjective ⇑((1 : X →L[𝕜] X) + C)) :
    Function.Injective ⇑((1 : X →L[𝕜] X) + C) := by
  let A := 1 + C
  haveI : FiniteDimensional 𝕜 A.ker := finiteDimensional_ker_one_add hC
  obtain ⟨Q, hQc, hQ⟩ := (Submodule.ClosedComplemented.of_finiteDimensional A.ker).exists_isClosed_isCompl
  haveI : CompleteSpace Q := hQc.completeSpace_coe
  let f := A ∘L Q.subtypeL
  have hi := (injective_iff_map_eq_zero f).2 fun x hx =>
    Subtype.ext (Submodule.disjoint_def.mp hQ.disjoint _ hx x.property)
  have hs : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := hsurj y
    have hxmem : x ∈ A.ker ⊔ Q := hQ.sup_eq_top ▸ Submodule.mem_top
    obtain ⟨k, hk, q, hq, rfl⟩ := Submodule.mem_sup.mp hxmem
    refine ⟨⟨q, hq⟩, ?_⟩
    change A (k + q) = y at hx
    simpa [f, show A k = 0 from hk] using hx
  let e := ContinuousLinearEquiv.ofBijective f (LinearMap.ker_eq_bot.mpr hi)
    (LinearMap.range_eq_top.mpr hs)
  let B := Q.subtypeL ∘L e.symm.toContinuousLinearMap
  have hAB : Function.LeftInverse A B := e.apply_symm_apply
  have hB : B = 1 + -(C ∘L B) := by
    ext x
    have h := hAB x
    change B x + C (B x) = x at h
    simpa [sub_eq_add_neg] using eq_sub_of_add_eq h
  have hBs := surjective_of_injective_one_add (hC.comp_clm B).neg
    (show Function.Injective ⇑((1 : X →L[𝕜] X) + -(C ∘L B)) from hB ▸ hAB.injective)
  exact (hAB.rightInverse_of_surjective (hB.symm ▸ hBs)).injective

end Fredholm

section FiniteRank

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- A bounded operator with finite-dimensional range is compact. -/
theorem isCompactOperator_of_finiteDimensional_range (F : X →L[𝕜] Y)
    [FiniteDimensional 𝕜 (LinearMap.range (F : X →ₗ[𝕜] Y))] : IsCompactOperator F :=
  (isCompactOperator_of_locallyCompactSpace_dom (F.codRestrict F.range
    (LinearMap.mem_range_self _))).clm_comp F.range.subtypeL

end FiniteRank

section Codim

variable [CompleteSpace X]

/-- A surjective linear map from a larger finite-dimensional space. -/
lemma exists_surjective_of_finrank_le {K Q : Type*} [AddCommGroup K] [Module 𝕜 K]
    [AddCommGroup Q] [Module 𝕜 Q] [FiniteDimensional 𝕜 K] [FiniteDimensional 𝕜 Q]
    (h : Module.finrank 𝕜 Q ≤ Module.finrank 𝕜 K) :
    ∃ L : K →ₗ[𝕜] Q, Function.Surjective L := by
  obtain ⟨L, hL⟩ := finrank_le_iff_exists_linearMap.mp h
  exact ⟨L.leftInverse, (show Function.LeftInverse L.leftInverse L from
    L.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr hL)).surjective⟩

/-- If the range of `I + C` together with a finite-dimensional `Q` spans everything, then
`dim Q ≥ dim ker (I + C)`. -/
lemma finrank_ker_le_of_sup_eq_top {C : X →L[𝕜] X} (hC : IsCompactOperator C)
    (Q : Submodule 𝕜 X) [FiniteDimensional 𝕜 Q]
    (htop : LinearMap.range (((1 : X →L[𝕜] X) + C : X →L[𝕜] X) : X →ₗ[𝕜] X) ⊔ Q = ⊤) :
    haveI := finiteDimensional_ker_one_add hC
    Module.finrank 𝕜 (LinearMap.ker (((1 : X →L[𝕜] X) + C : X →L[𝕜] X) : X →ₗ[𝕜] X)) ≤
      Module.finrank 𝕜 Q := by
  haveI := finiteDimensional_ker_one_add hC
  set A : X →L[𝕜] X := (1 : X →L[𝕜] X) + C with hAdef
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
    have hpos : 0 < Module.finrank 𝕜 (LinearMap.ker L) := by omega
    exact Submodule.exists_mem_ne_zero_of_ne_bot (Submodule.one_le_finrank_iff.1 hpos)
  let Lc := LinearMap.toContinuousLinearMap L
  let F := Q.subtypeL ∘L Lc ∘L P
  have hFrange : FiniteDimensional 𝕜 (LinearMap.range (F : X →ₗ[𝕜] X)) := by
    refine Submodule.finiteDimensional_of_le (S₂ := Q) ?_
    rintro _ ⟨x, rfl⟩
    exact (Lc (P x)).2
  have hFc :=
    hC.add (isCompactOperator_of_finiteDimensional_range F)
  have hKA : ∀ k ∈ K, A k = 0 := fun k hk => hk
  have hsurj : Function.Surjective ((1 : X →L[𝕜] X) + (C + F)) := by
    intro h
    have hh : h ∈ LinearMap.range (A : X →ₗ[𝕜] X) ⊔ Q := htop ▸ Submodule.mem_top
    obtain ⟨_, ⟨x, rfl⟩, q, hq, rfl⟩ := Submodule.mem_sup.1 hh
    obtain ⟨k₀, hk₀⟩ := hL ⟨q, hq⟩
    refine ⟨x - (P x : X) + (k₀ : X), ?_⟩
    have h1 : (1 : X →L[𝕜] X) + (C + F) = A + F := by rw [add_assoc]
    rw [h1, ContinuousLinearMap.add_apply]
    have hA : A (x - (P x : X) + (k₀ : X)) = A x := by
      simp
    have hF : F (x - (P x : X) + (k₀ : X)) = q := by
      simp  [F, map_add, map_sub]
      have hPx : P (P x : X) = P x := hP (P x)
      have hPk : P (k₀ : X) = k₀ := hP k₀
      rw [hPx, hPk, sub_self, zero_add]
      simp [Lc, hk₀]
    rw [hA, hF]
    rfl
  have hinj := injective_of_surjective_one_add hFc hsurj
  apply hk₁0
  have : ((1 : X →L[𝕜] X) + (C + F)) (k₁ : X) = ((1 : X →L[𝕜] X) + (C + F)) 0 := by
    have h1 : (1 : X →L[𝕜] X) + (C + F) = A + F := by rw [hAdef, add_assoc]
    rw [h1, map_zero, ContinuousLinearMap.add_apply, hKA _ k₁.2, zero_add]
    simp only [F, ContinuousLinearMap.comp_apply, hP k₁]
    simp [Lc, LinearMap.mem_ker.1 hk₁L]
  exact Subtype.ext (hinj this)

/-- The range of `I + C` has codimension at least `dim ker (I + C)`: there is a subspace `Q`
of dimension `dim ker (I + C)` meeting the range only in `0`. -/
theorem exists_complement_range_one_add {C : X →L[𝕜] X} (hC : IsCompactOperator C) :
    haveI := finiteDimensional_ker_one_add hC
    ∃ Q : Submodule 𝕜 X, FiniteDimensional 𝕜 Q ∧
      Module.finrank 𝕜 Q =
        Module.finrank 𝕜 (LinearMap.ker (((1 : X →L[𝕜] X) + C : X →L[𝕜] X) : X →ₗ[𝕜] X)) ∧
      Disjoint Q (LinearMap.range (((1 : X →L[𝕜] X) + C : X →L[𝕜] X) : X →ₗ[𝕜] X)) := by
  haveI := finiteDimensional_ker_one_add hC
  let A := 1 + C
  obtain ⟨P, hP⟩ := A.range.exists_isCompl
  have hrank : Module.rank 𝕜 A.ker ≤ Module.rank 𝕜 P := by
    by_contra! hlt
    haveI := Module.rank_lt_aleph0_iff.mp (hlt.trans (Module.rank_lt_aleph0 𝕜 A.ker))
    have h := finrank_ker_le_of_sup_eq_top hC P hP.sup_eq_top
    change Module.finrank 𝕜 A.ker ≤ Module.finrank 𝕜 P at h
    rw [← Module.finrank_eq_rank, ← Module.finrank_eq_rank, Nat.cast_lt] at hlt
    omega
  obtain ⟨L, hL⟩ := rank_le_iff_exists_linearMap.mp hrank
  let f := P.subtype ∘ₗ L
  refine ⟨f.range, inferInstance, (LinearEquiv.ofInjective f (Subtype.val_injective.comp hL)).symm.finrank_eq,
    hP.disjoint.symm.mono_left ?_⟩
  rintro _ ⟨x, rfl⟩
  exact (L x).property

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
  set A : H →L[𝕜] H := (1 : H →L[𝕜] H) + C with hAdef
  set K := LinearMap.ker (A : H →ₗ[𝕜] H) with hKdef
  obtain ⟨Q, hQf, hQk, hQd⟩ := exists_complement_range_one_add hC
  set P₁ : H →L[𝕜] H₀ᗮ := H₀ᗮ.orthogonalProjection
  have hKA : ∀ k ∈ K, k + C k = 0 := fun k hk => hk
  -- `Π₁` is injective on the kernel
  have hP₁inj : Function.Injective ((P₁ : H →ₗ[𝕜] H₀ᗮ) ∘ₗ K.subtype) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro k hk
    rw [LinearMap.mem_ker] at hk
    have h0 : (k : H) ∈ H₀ := by
      have := (Submodule.orthogonalProjection_eq_zero_iff (K := H₀ᗮ)).1 hk
      rwa [Submodule.orthogonal_orthogonal] at this
    have := hinj _ h0 (hKA _ k.2)
    simp [Subtype.ext_iff, this]
  set M : Submodule 𝕜 H₀ᗮ := LinearMap.range ((P₁ : H →ₗ[𝕜] H₀ᗮ) ∘ₗ K.subtype) with hMdef
  have hMk := LinearMap.finrank_range_of_inj hP₁inj
  let e : M ≃ₗ[𝕜] Q := LinearEquiv.ofFinrankEq _ _ (by aesop)
  let Lc := LinearMap.toContinuousLinearMap (e : M →ₗ[𝕜] Q)
  let F := Q.subtypeL ∘L Lc ∘L M.orthogonalProjection
  have hFQ : ∀ y, F y ∈ Q := fun y => (Lc _).2
  have hFrange : FiniteDimensional 𝕜 (LinearMap.range (F : H₀ᗮ →ₗ[𝕜] H)) := by
    refine Submodule.finiteDimensional_of_le (S₂ := Q) ?_
    rintro _ ⟨x, rfl⟩
    tauto
  refine ⟨F, hFrange, ?_⟩
  have hFP : FiniteDimensional 𝕜 (LinearMap.range ((F ∘L P₁ : H →L[𝕜] H) : H →ₗ[𝕜] H)) := by
    refine Submodule.finiteDimensional_of_le (S₂ := Q) ?_
    rintro _ ⟨x, rfl⟩
    tauto
  have hcpt : IsCompactOperator (C + F ∘L P₁) :=
    hC.add (isCompactOperator_of_finiteDimensional_range _)
  have heq : (1 : H →L[𝕜] H) + C + F ∘L P₁ = (1 : H →L[𝕜] H) + (C + F ∘L P₁) := add_assoc _ _ _
  have hinj' : Function.Injective ⇑((1 : H →L[𝕜] H) + C + F ∘L P₁) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    rw [ContinuousLinearMap.add_apply] at hx
    have hAx : A x = -F (P₁ x) := eq_neg_of_add_eq_zero_left hx
    have hAx0 : A x = 0 := by
      refine Submodule.disjoint_def.1 hQd (A x) ?_ ⟨x, rfl⟩
      rw [hAx]
      exact Q.neg_mem (hFQ _)
    have hxK : x ∈ K := hAx0
    have hF0 : F (P₁ x) = 0 := by rw [← neg_eq_zero, ← hAx, hAx0]
    have hPM : P₁ x ∈ M := ⟨⟨x, hxK⟩, rfl⟩
    have hPx : M.orthogonalProjection (P₁ x) = ⟨P₁ x, hPM⟩ :=
      Submodule.orthogonalProjection_mem_subspace_eq_self (K := M) ⟨P₁ x, hPM⟩
    have hP0 : P₁ x = 0 := by
      have h1 : (e ⟨P₁ x, hPM⟩ : H) = 0 := by
        simpa [F, Lc, hPx] using hF0
      have h2 : e ⟨P₁ x, hPM⟩ = 0 := Subtype.ext h1
      have h3 : (⟨P₁ x, hPM⟩ : M) = 0 := by simpa using h2
      simpa using congrArg Subtype.val h3
    have h0 : x ∈ H₀ := by
      have := (Submodule.orthogonalProjection_eq_zero_iff (K := H₀ᗮ)).1 hP0
      rwa [Submodule.orthogonal_orthogonal] at this
    exact hinj x h0 (hKA x hxK)
  refine ⟨hinj', ?_⟩
  rw [heq] at hinj' ⊢
  exact surjective_of_injective_one_add hcpt hinj'

/-- A bijective bounded operator on a Banach space is a unit of the operator algebra. -/
lemma isUnit_of_bijective (f : H →L[𝕜] H) (hf : Function.Bijective f) : IsUnit f :=
  ContinuousLinearMap.isUnit_iff_bijective.mpr hf

/-- **Lemma 7.2**, stated with invertibility in the operator algebra: `A + F Π₁` is a unit. -/
theorem finite_rank_completion_isUnit {C : H →L[𝕜] H} (hC : IsCompactOperator C)
    (H₀ : Submodule 𝕜 H) [H₀.HasOrthogonalProjection]
    (hinj : ∀ x ∈ H₀, x + C x = 0 → x = 0) :
    ∃ F : H₀ᗮ →L[𝕜] H, FiniteDimensional 𝕜 (LinearMap.range (F : H₀ᗮ →ₗ[𝕜] H)) ∧
      IsUnit ((1 : H →L[𝕜] H) + C + F ∘L H₀ᗮ.orthogonalProjection) := by
  obtain ⟨F, hF, hbij⟩ := finite_rank_completion hC H₀ hinj
  exact ⟨F, hF, isUnit_of_bijective _ hbij⟩

omit [CompleteSpace H] in
/-- In the setting of Lemma 7.3, write `Ĵ_{E₀} Π₀ + Π₁ = I + C`. Then `I + C` is injective on
`H₀` and `Ĵ_{E₀} Π₀ + (ι + F) Π₁ = I + C + F Π₁` for every `F`. -/
lemma fixed_complement_aux (H₀ : Submodule 𝕜 H) [H₀.HasOrthogonalProjection]
    (J₀ : H₀ →L[𝕜] H) (hinj : Function.Injective J₀) :
    (∀ x ∈ H₀, x + (J₀ ∘L H₀.orthogonalProjection +
      Submodule.subtypeL H₀ᗮ ∘L H₀ᗮ.orthogonalProjection - (1 : H →L[𝕜] H)) x = 0 → x = 0) ∧
    ∀ F : H₀ᗮ →L[𝕜] H, J₀ ∘L H₀.orthogonalProjection +
        (Submodule.subtypeL H₀ᗮ + F) ∘L H₀ᗮ.orthogonalProjection =
      (1 : H →L[𝕜] H) + (J₀ ∘L H₀.orthogonalProjection +
        Submodule.subtypeL H₀ᗮ ∘L H₀ᗮ.orthogonalProjection - (1 : H →L[𝕜] H)) +
        F ∘L H₀ᗮ.orthogonalProjection := by
  refine ⟨fun x hx h0 => ?_, fun F => ?_⟩
  · have hP₁ :=
      (Submodule.orthogonalProjection_eq_zero_iff (K := H₀ᗮ)).2
        (Submodule.le_orthogonal_orthogonal H₀ hx)
    have hP₀ :=
      Submodule.orthogonalProjection_mem_subspace_eq_self (K := H₀) ⟨x, hx⟩
    simp  [hP₁, hP₀, map_zero, add_zero, add_sub_cancel] at h0
    have := hinj (h0.trans (map_zero J₀).symm)
    simp_all
  · simp only [ContinuousLinearMap.add_comp]
    abel

/-- A finite-rank bounded operator between Hilbert spaces is a finite sum of rank-one operators
`z ↦ ⟪u_r, z⟫ v_r`. -/
lemma exists_eq_sum_rankOne {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y]
    [CompleteSpace Y] (F : Y →L[𝕜] H) [FiniteDimensional 𝕜 (LinearMap.range (F : Y →ₗ[𝕜] H))] :
    ∃ (d : ℕ) (u : Fin d → Y) (v : Fin d → H),
      F = ∑ r, InnerProductSpace.rankOne 𝕜 (v r) (u r) := by
  set V := LinearMap.range (F : Y →ₗ[𝕜] H)
  let e := stdOrthonormalBasis 𝕜 V
  refine ⟨_, fun r => ContinuousLinearMap.adjoint F (e r), fun r => (e r : H), ?_⟩
  ext z
  have hz := e.sum_repr' (⟨F z, LinearMap.mem_range_self _ z⟩ : V)
  have := congrArg Subtype.val hz
  simp  [Submodule.coe_sum] at this
  rw [ContinuousLinearMap.sum_apply]
  simp  [ContinuousLinearMap.adjoint_inner_left]
  tauto

omit [CompleteSpace H] in
/-- Joint continuity of the rank-one operator `(x, y) ↦ ⟪y, ·⟫ x`. -/
lemma continuous_rankOne {Y Z : Type*} [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y]
    [TopologicalSpace Z] {f : Z → H} {g : Z → Y} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun z => InnerProductSpace.rankOne 𝕜 (f z) (g z) := by exact_mod_cast Continuous.clm_comp (Continuous.comp (ContinuousLinearEquiv.continuous ContinuousLinearMap.toSpanSingletonCLE) hf) (Continuous.comp (ContinuousLinearMap.continuous (innerSL 𝕜)) hg)

variable {ι : Type*}

/-- Finite-rank completion with output vectors in the finite span of a Hilbert basis.
Only the output vectors require finite support in the Fourier application. -/
theorem finite_rank_completion_basis {C : H →L[𝕜] H} (hC : IsCompactOperator C)
    (H₀ : Submodule 𝕜 H) [H₀.HasOrthogonalProjection]
    (hinj : ∀ x ∈ H₀, x + C x = 0 → x = 0) (b : HilbertBasis ι 𝕜 H) :
    ∃ (d : ℕ) (u : Fin d → H₀ᗮ) (v : Fin d → H),
      (∀ r, v r ∈ Submodule.span 𝕜 (Set.range b)) ∧
      IsUnit ((1 : H →L[𝕜] H) + C +
        (∑ r, InnerProductSpace.rankOne 𝕜 (v r) (u r)) ∘L H₀ᗮ.orthogonalProjection) := by
  obtain ⟨F, hF, hunit⟩ := finite_rank_completion_isUnit hC H₀ hinj
  obtain ⟨d, u, v, rfl⟩ := exists_eq_sum_rankOne F
  let P := H₀ᗮ.orthogonalProjection
  let Φ (x : Fin d → H) := (1 : H →L[𝕜] H) + C +
    (∑ r, InnerProductSpace.rankOne 𝕜 (x r) (u r)) ∘L P
  have hΦ : Continuous Φ :=
    continuous_const.add ((continuous_finset_sum _ fun r _ =>
      continuous_rankOne (continuous_apply r) continuous_const).clm_comp continuous_const)
  have hdense : Dense (Set.univ.pi fun _ : Fin d => (Submodule.span 𝕜 (Set.range b) : Set H)) :=
    dense_pi _ fun _ _ => (Submodule.dense_iff_topologicalClosure_eq_top).2 b.dense_span
  obtain ⟨v', hmem, hD⟩ := hdense.inter_open_nonempty _ (Units.isOpen.preimage hΦ) ⟨v, hunit⟩
  exact ⟨d, u, v', by simpa using hD, hmem⟩

/-- The fixed completion is still invertible near the reference energy. -/
theorem exists_fixed_complement_basis (H₀ : Submodule 𝕜 H) [H₀.HasOrthogonalProjection]
    {J : ℝ → (H₀ →L[𝕜] H)} (hJ : Continuous J) {E₀ : ℝ}
    (hcpt : IsCompactOperator (J E₀ ∘L H₀.orthogonalProjection +
      Submodule.subtypeL H₀ᗮ ∘L H₀ᗮ.orthogonalProjection - (1 : H →L[𝕜] H)))
    (hinj : Function.Injective (J E₀)) (b : HilbertBasis ι 𝕜 H) :
    ∃ (d : ℕ) (u : Fin d → H₀ᗮ) (v : Fin d → H),
      (∀ r, v r ∈ Submodule.span 𝕜 (Set.range b)) ∧
      ∀ᶠ E in 𝓝 E₀, IsUnit (J E ∘L H₀.orthogonalProjection +
        (Submodule.subtypeL H₀ᗮ + ∑ r, InnerProductSpace.rankOne 𝕜 (v r) (u r)) ∘L
          H₀ᗮ.orthogonalProjection) := by
  obtain ⟨hinj', heq⟩ := fixed_complement_aux H₀ (J E₀) hinj
  obtain ⟨d, u, v, hv, hunit⟩ := finite_rank_completion_basis hcpt H₀ hinj' b
  let B (E : ℝ) := J E ∘L H₀.orthogonalProjection +
    (Submodule.subtypeL H₀ᗮ + ∑ r, InnerProductSpace.rankOne 𝕜 (v r) (u r)) ∘L H₀ᗮ.orthogonalProjection
  have hB : Continuous B := by fun_prop
  have hB₀ : IsUnit (B E₀) := by simpa only [B, heq] using hunit
  exact ⟨d, u, v, hv, hB.continuousAt (Units.isOpen.mem_nhds hB₀)⟩

end Hilbert

end Banach

end PolyaNeumann
