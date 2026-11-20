module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.Tame.DeformedTestSupportAndReverseIntegralSymmetry

@[expose] public section

section
noncomputable section
namespace DedekindZetaZeroFree.KPTameTransposeKernelUnfoldingRaw.HigherShellCancellation
open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPTameJacquetTestDuality KPLocalExceptionalConstruction

variable (F : Type) [Field F] [NumberField F] (q : HeightOneSpectrum (𝓞 F)) (π : (LocalField F q)ˣ)

local notation "LocalCompletion" => LocalField F q

private theorem ball_add_subgroup (r : ℕ) :
    ∃ A : AddSubgroup LocalCompletion, (A : Set LocalCompletion) = expandingBall F q π r := by
  let a := ((π ^ r : LocalCompletionˣ) : LocalCompletion)⁻¹
  refine ⟨((valuation LocalCompletion).integer.toAddSubgroup.map
    (AddMonoidHom.mulLeft a)), ?_⟩
  ext x
  constructor
  · rintro ⟨y, hy, h⟩
    exact ⟨⟨y, hy⟩, h.symm⟩
  · rintro ⟨u, h⟩
    exact ⟨u, u.property, h.symm⟩

private theorem ball_mono
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt LocalCompletion
      (valuation LocalCompletion (π : LocalCompletion)) = WithZero.exp (-1 : ℤ))
    {r s : ℕ} (hrs : r ≤ s) : expandingBall F q π r ⊆ expandingBall F q π s := by
  let valuation₀ := valuation LocalCompletion
  have hv : valuation₀ π ≤ 1 := by
    apply (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt LocalCompletion).toOrderIso.le_iff_le.mp
    change IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt LocalCompletion
      (valuation₀ π) ≤
      IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt LocalCompletion 1
    rw [hπ, map_one]
    norm_num
  rintro x ⟨u, rfl⟩
  refine ⟨⟨π ^ (s-r) * u, (valuation₀).integer.mul_mem ((valuation₀).integer.pow_mem ((Valuation.mem_integer_iff _ _).mpr hv) _) u.property⟩, ?_⟩
  change ((π : LocalCompletion)^r)⁻¹ * u = ((π : LocalCompletion)^s)⁻¹ * ((π : LocalCompletion)^(s-r) * u)
  have he : (π : LocalCompletion) ^ s = (π : LocalCompletion) ^ r * (π : LocalCompletion) ^ (s-r) := by
    rw [← pow_add, Nat.add_sub_of_le hrs]
  rw [he, mul_inv_rev]
  field_simp

private theorem ball_measurable (r : ℕ) : MeasurableSet (expandingBall F q π r) := by apply @DedekindZetaZeroFree.KPTameJacquetBruhatTests.Stabilization.TameStableWhittakerIntegrals.ball_measurable <;> assumption

theorem exists_conductor_one_translation
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt LocalCompletion
      (valuation LocalCompletion (π : LocalCompletion)) = WithZero.exp (-1 : ℤ))
    (ψ : Multiplicative LocalCompletion →* ℂˣ)
    (hconductor : HasConductorIntegers F q ψ) :
    ∃ t ∈ expandingBall F q π 1, ψ (Multiplicative.ofAdd (-t)) ≠ 1 := by
  let valuation₀ := valuation LocalCompletion
  have hv : valuation₀ π < 1 := by
    apply (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt LocalCompletion).toOrderIso.lt_iff_lt.mp
    change IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt LocalCompletion
      (valuation₀ π) <
      IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt LocalCompletion 1
    rw [hπ, map_one]
    norm_num
  have hni : (π : LocalCompletion)⁻¹ ∉ (valuation₀).integer := by
    rw [Valuation.mem_integer_iff, map_inv₀]
    exact not_le.mpr (one_lt_inv₀ ((Valuation.pos_iff (valuation₀)).mpr π.ne_zero) |>.mpr hv)
  have hw := mt (hconductor (π⁻¹)).mp hni
  push Not at hw
  obtain ⟨o, ho⟩ := hw
  refine ⟨-(o * π⁻¹), ?_, ?_⟩
  · refine ⟨-o, ?_⟩
    simp [expandingBall, mul_comm]
  · simpa using ho

theorem integral_zero_of_translation
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt LocalCompletion
      (valuation LocalCompletion (π : LocalCompletion)) = WithZero.exp (-1 : ℤ))
    (μ : Measure LocalCompletion) [μ.IsAddHaarMeasure]
    (ψ : Multiplicative LocalCompletion →* ℂˣ)
    (t : LocalCompletion) (htball : t ∈ expandingBall F q π 1)
    (ht : ψ (Multiplicative.ofAdd (-t)) ≠ 1)
    (φ : LocalCompletion → ℂ) (r : ℕ) (hr : 2 ≤ r)
    (hφ : ∀ x ∈ expandingBall F q π r \ expandingBall F q π (r-1),
      φ (x+t) = φ x) :
    (∫ x in expandingBall F q π r \ expandingBall F q π (r-1),
      φ x * (ψ (Multiplicative.ofAdd (-x)) : ℂ) ∂μ) = 0 := by
  let shell := expandingBall F q π r \ expandingBall F q π (r-1)
  let g := fun x : LocalCompletion => φ x * (ψ (Multiplicative.ofAdd (-x)) : ℂ)
  have hball : ∀ s : ℕ, 1 ≤ s → ∀ x : LocalCompletion,
      x+t ∈ expandingBall F q π s ↔ x ∈ expandingBall F q π s := by
    intro s hs x
    obtain ⟨A, hA⟩ := ball_add_subgroup F q π s
    rw [← hA]
    refine A.add_mem_cancel_right ?_
    rw [← SetLike.mem_coe, hA]
    exact ball_mono F q π hπ hs htball
  have hset : ∀ x, x+t ∈ shell ↔ x ∈ shell := fun x => and_congr (hball r (by omega) x) (not_congr (hball (r-1) (by omega) x))
  let c := (ψ (Multiplicative.ofAdd (-t)) : ℂ)
  have hg : ∀ x ∈ shell, g (x+t) = c * g x := by
    intro x hx
    change φ (x+t) * (ψ (Multiplicative.ofAdd (-(x+t))) : ℂ) =
      (ψ (Multiplicative.ofAdd (-t)) : ℂ) * (φ x * (ψ (Multiplicative.ofAdd (-x)) : ℂ))
    rw [hφ x hx, neg_add, ofAdd_add, map_mul, Units.val_mul]
    ring
  have hind : ∀ x, shell.indicator g (x+t) = c * shell.indicator g x := by
    intro x
    by_cases hx : x ∈ shell
    · simp only [Set.indicator_of_mem hx, Set.indicator_of_mem ((hset x).mpr hx), hg x hx]
    · simp only [Set.indicator_of_notMem hx, Set.indicator_of_notMem (mt (hset x).mp hx), mul_zero]
  have he := integral_add_right_eq_self (shell.indicator g) t (μ := μ)
  simp_rw [hind] at he
  rw [integral_const_mul, integral_indicator ((ball_measurable F q π r).diff (ball_measurable F q π (r-1)))] at he
  have hz : (c-1) * (∫ x in shell, g x ∂μ) = 0 := by
    linear_combination he
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr (fun h => ht (Units.ext h)))

end DedekindZetaZeroFree.KPTameTransposeKernelUnfoldingRaw.HigherShellCancellation

end

end
