module
public import GuthMaynard.NativeSource.GuthMaynard.ClassicalDetector
public import GuthMaynard.NativeSource.GuthMaynard.ClassicalLargeValues
public import GuthMaynard.NativeSource.GuthMaynard.BetaDependence
public import Mathlib.Analysis.Complex.PhragmenLindelof

@[expose] public section

open Complex Finset Set Topology
open scoped BigOperators

namespace GuthMaynard.NativeMoment

open Filter Asymptotics PhragmenLindelof

/-- A Dirichlet polynomial on an arbitrary finite positive support. -/
noncomputable def finiteDirichletSeries
    (S : Finset ℕ) (a : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑ n ∈ S, a n * (n : ℂ) ^ (-s)

/-- The coefficient mass used to bound a finite Dirichlet polynomial in the
closed right half-plane. -/
noncomputable def finiteDirichletMass (S : Finset ℕ) (a : ℕ → ℂ) : ℝ :=
  ∑ n ∈ S, ‖a n‖

theorem norm_finiteDirichletSeries_le_mass
    (S : Finset ℕ) (a : ℕ → ℂ) (s : ℂ)
    (hS : ∀ n ∈ S, 0 < n) (hs : 0 ≤ s.re) :
    ‖finiteDirichletSeries S a s‖ ≤ finiteDirichletMass S a := by
  unfold finiteDirichletSeries finiteDirichletMass
  calc
    ‖∑ n ∈ S, a n * (n : ℂ) ^ (-s)‖ ≤
        ∑ n ∈ S, ‖a n * (n : ℂ) ^ (-s)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ S, ‖a n‖ := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul, Complex.norm_natCast_cpow_of_pos (hS n hn)]
      exact mul_le_of_le_one_right (norm_nonneg _) <|
        Real.rpow_le_one_of_one_le_of_nonpos
          (by exact_mod_cast (hS n hn)) (by simp [hs])

theorem differentiable_finiteDirichletSeries_add
    (S : Finset ℕ) (a : ℕ → ℂ) (z : ℂ) (hS : ∀ n ∈ S, 0 < n) :
    Differentiable ℂ (fun w : ℂ => finiteDirichletSeries S a (z + w)) := by
  intro w
  apply AnalyticAt.differentiableAt
  unfold finiteDirichletSeries
  have hEq :
      (fun u : ℂ => ∑ n ∈ S, a n * (n : ℂ) ^ (-(z + u))) =
        ∑ n ∈ S, fun u : ℂ => a n * (n : ℂ) ^ (-(z + u)) := by
    funext u
    simp
  rw [hEq]
  apply Finset.analyticAt_sum
  intro n hn
  have hnPos : 0 < n := hS n hn
  have hpow : AnalyticAt ℂ (fun u : ℂ => (n : ℂ) ^ (-(z + u))) w :=
    analyticAt_const.cpow ((analyticAt_const.add analyticAt_id).neg)
      (Complex.natCast_mem_slitPlane.mpr hnPos.ne')
  exact analyticAt_const.mul hpow

/-- Rational localization of a finite Dirichlet polynomial. -/
noncomputable def localizedFiniteDirichlet
    (S : Finset ℕ) (a : ℕ → ℂ) (k : ℕ) (z : ℂ) (H : ℝ) (w : ℂ) : ℂ :=
  (((H : ℂ) / (H + w)) ^ k) * finiteDirichletSeries S a (z + w)

theorem localizedFiniteDirichlet_le_mass
    (S : Finset ℕ) (a : ℕ → ℂ) (k : ℕ) (z w : ℂ) (H : ℝ)
    (hS : ∀ n ∈ S, 0 < n) (hH : 0 < H) (hz : 0 ≤ z.re) (hw : 0 ≤ w.re) :
    ‖localizedFiniteDirichlet S a k z H w‖ ≤ finiteDirichletMass S a := by
  rw [localizedFiniteDirichlet, norm_mul]
  calc
    ‖((H : ℂ) / (H + w)) ^ k‖ * ‖finiteDirichletSeries S a (z + w)‖ ≤
        1 * finiteDirichletMass S a := by
      gcongr
      · exact localizer_norm_le_one k H hH w hw
      · exact norm_finiteDirichletSeries_le_mass S a (z + w) hS (by simp; linarith)
    _ = finiteDirichletMass S a := one_mul _

theorem localizedFiniteDirichlet_halfPlane_bound
    (S : Finset ℕ) (a : ℕ → ℂ) (k : ℕ) (z : ℂ) (H C : ℝ)
    (hS : ∀ n ∈ S, 0 < n) (hH : 0 < H) (hz : 0 ≤ z.re)
    (hBoundary : ∀ y : ℝ,
      ‖localizedFiniteDirichlet S a k z H (y * I)‖ ≤ C)
    (w : ℂ) (hw : 0 ≤ w.re) :
    ‖localizedFiniteDirichlet S a k z H w‖ ≤ C := by
  apply PhragmenLindelof.right_half_plane_of_bounded_on_real
      (f := localizedFiniteDirichlet S a k z H)
  · exact (by
      unfold localizedFiniteDirichlet
      apply DifferentiableOn.diffContOnCl
      intro u hu
      have hne : (H : ℂ) + u ≠ 0 := by
        intro h
        have hre := congrArg Complex.re h
        simp only [add_re, ofReal_re, zero_re] at hre
        rw [closure_setOfPred_lt_re] at hu
        change 0 ≤ u.re at hu
        linarith
      exact ((((differentiableAt_const (c := (H : ℂ))).div
        ((differentiableAt_const (c := (H : ℂ))).add differentiableAt_id) hne).pow k).mul
          (differentiable_finiteDirichletSeries_add S a z hS u)).differentiableWithinAt)
  · refine ⟨1, by norm_num, 0, ?_⟩
    apply Asymptotics.IsBigO.of_bound (finiteDirichletMass S a)
    have hopen : ∀ᶠ u in (Bornology.cobounded ℂ ⊓ Filter.principal {u : ℂ | 0 < u.re}),
        0 < u.re := Filter.le_principal_iff.mp inf_le_right
    filter_upwards [hopen] with u hu
    simp only [zero_mul, Real.exp_zero, norm_one, mul_one]
    exact localizedFiniteDirichlet_le_mass S a k z u H hS hH hz hu.le
  · refine ⟨finiteDirichletMass S a, ?_⟩
    rw [eventually_map]
    exact Filter.eventually_atTop.mpr ⟨0, fun x hx =>
      localizedFiniteDirichlet_le_mass S a k z x H hS hH hz (by simpa using hx)⟩
  · exact hBoundary
  · exact hw

/-- A large value to the right of a fixed vertical line produces a comparably
large value on that line after a controlled ordinate displacement. -/
theorem exists_nearby_large_value_finiteDirichlet
    (S : Finset ℕ) (coeff : ℕ → ℂ) (k : ℕ) (z : ℂ) (H R A a : ℝ)
    (hS : ∀ n ∈ S, 0 < n) (hH : 0 < H) (hR : 0 < R) (hA : 0 < A)
    (hz : 0 ≤ z.re) (ha : 0 ≤ a)
    (hLarge : A ≤ ‖finiteDirichletSeries S coeff (z + a)‖)
    (hFactor : 3 / 4 < ‖((H : ℂ) / (H + (a : ℂ))) ^ k‖)
    (hExterior : finiteDirichletMass S coeff * (H / R) ^ k < (3 / 4) * A) :
    ∃ y : ℝ, |y| ≤ R ∧
      (3 / 4) * A ≤ ‖finiteDirichletSeries S coeff (z + y * I)‖ := by
  by_contra! hNo
  have hBoundary : ∀ y : ℝ,
      ‖localizedFiniteDirichlet S coeff k z H (y * I)‖ ≤ (3 / 4) * A := by
    intro y
    rw [localizedFiniteDirichlet, norm_mul]
    by_cases hy : |y| ≤ R
    · calc
        ‖((H : ℂ) / (H + (y : ℂ) * I)) ^ k‖ *
            ‖finiteDirichletSeries S coeff (z + (y : ℂ) * I)‖ ≤
            1 * ((3 / 4) * A) := by
          gcongr
          · exact localizer_norm_le_one k H hH (y * I) (by simp)
          · exact (hNo y hy).le
        _ = (3 / 4) * A := one_mul _
    · have hyR : R ≤ |y| := le_of_lt (lt_of_not_ge hy)
      calc
        ‖((H : ℂ) / (H + (y : ℂ) * I)) ^ k‖ *
            ‖finiteDirichletSeries S coeff (z + (y : ℂ) * I)‖ ≤
            (H / R) ^ k * finiteDirichletMass S coeff := by
          gcongr
          · exact localizer_norm_boundary_le k H R y hH hR hyR
          · exact norm_finiteDirichletSeries_le_mass S coeff
              (z + y * I) hS (by simp [hz])
        _ = finiteDirichletMass S coeff * (H / R) ^ k := by ring
        _ ≤ (3 / 4) * A := hExterior.le
  have hPL := localizedFiniteDirichlet_halfPlane_bound
    S coeff k z H ((3 / 4) * A) hS hH hz hBoundary (a : ℂ) (by simpa using ha)
  rw [localizedFiniteDirichlet, norm_mul] at hPL
  have hStrict : (3 / 4) * A <
      ‖((H : ℂ) / (H + (a : ℂ))) ^ k‖ *
        ‖finiteDirichletSeries S coeff (z + a)‖ := by
    calc
      (3 / 4) * A < ‖((H : ℂ) / (H + (a : ℂ))) ^ k‖ * A := by gcongr
      _ ≤ ‖((H : ℂ) / (H + (a : ℂ))) ^ k‖ *
          ‖finiteDirichletSeries S coeff (z + a)‖ := by gcongr
  exact (not_lt_of_ge hPL) hStrict

/-- The actual support of the nonconstant sharp zeta--Möbius convolution. -/
noncomputable def sharpMollifiedTailSupport (A X : ℕ) : Finset ℕ :=
  Ioc X (A * X)

/-- The finite analytic tail to which exact beta removal is applied. -/
noncomputable def sharpMollifiedTail (A X : ℕ) (s : ℂ) : ℂ :=
  finiteDirichletSeries (sharpMollifiedTailSupport A X)
    (sharpMollifiedCoeff A X) s

theorem sharpMollifiedTail_apply (A X : ℕ) (s : ℂ) :
    sharpMollifiedTail A X s =
      ∑ n ∈ Ioc X (A * X),
        sharpMollifiedCoeff A X n * (n : ℂ) ^ (-s) := rfl

theorem sharpMollifiedTailSupport_pos (A X n : ℕ)
    (hn : n ∈ sharpMollifiedTailSupport A X) : 0 < n := by
  rw [sharpMollifiedTailSupport, Finset.mem_Ioc] at hn
  omega

/-- A crude polynomial coefficient-mass bound, sufficient for rational
localization. The sharper divisor estimate is retained for large-values
normalization after localization. -/
theorem sharpMollifiedTail_mass_le_sq (A X : ℕ) :
    finiteDirichletMass (sharpMollifiedTailSupport A X)
        (sharpMollifiedCoeff A X) ≤ (A * X : ℝ) ^ 2 := by
  unfold finiteDirichletMass
  calc
    (∑ n ∈ sharpMollifiedTailSupport A X, ‖sharpMollifiedCoeff A X n‖) ≤
        ∑ _n ∈ sharpMollifiedTailSupport A X, (A * X : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      calc
        ‖sharpMollifiedCoeff A X n‖ ≤ (n.divisors.card : ℝ) :=
          norm_sharpMollifiedCoeff_le_divisors_card A X n
        _ ≤ (n : ℝ) := by exact_mod_cast Nat.card_divisors_le_self n
        _ ≤ (A * X : ℝ) := by
          exact_mod_cast (Finset.mem_Ioc.mp hn).2
    _ = ((sharpMollifiedTailSupport A X).card : ℝ) * (A * X : ℝ) := by simp
    _ ≤ (A * X : ℝ) * (A * X : ℝ) := by
      gcongr
      have hCard := Finset.card_le_card (show sharpMollifiedTailSupport A X ⊆
          Finset.Icc 1 (A * X) by
            intro n hn
            rw [sharpMollifiedTailSupport, Finset.mem_Ioc] at hn
            exact Finset.mem_Icc.mpr ⟨by omega, hn.2⟩)
      have hCard' : (sharpMollifiedTailSupport A X).card ≤ A * X := by
        simpa using hCard
      exact_mod_cast hCard'
    _ = (A * X : ℝ) ^ 2 := by ring

/-- Fixed-line coefficients of the sharp mollified tail. -/
noncomputable def sharpMollifiedLineCoeff
    (A X : ℕ) (σ : ℝ) (n : ℕ) : ℂ :=
  sharpMollifiedCoeff A X n * (n : ℂ) ^ (-(σ : ℂ))

theorem sharpMollifiedLineCoeff_term (A X n : ℕ) (σ t : ℝ) (hn : 0 < n) :
    sharpMollifiedLineCoeff A X σ n * (n : ℂ) ^ (-(t : ℂ) * I) =
      sharpMollifiedCoeff A X n *
        (n : ℂ) ^ (-((σ : ℂ) + I * (t : ℂ))) := by
  rw [sharpMollifiedLineCoeff, mul_assoc,
    ← Complex.cpow_add _ _ (by exact_mod_cast hn.ne')]
  congr 2
  ring

theorem sharpMollifiedTail_eq_wideDirichletPoly
    (A X : ℕ) (σ t : ℝ) :
    sharpMollifiedTail A X ((σ : ℂ) + I * (t : ℂ)) =
      wideDirichletPoly X (Nat.clog 2 A) (sharpMollifiedLineCoeff A X σ) t := by
  have hCover : A ≤ 2 ^ Nat.clog 2 A :=
    (Nat.clog_le_iff_le_pow Nat.one_lt_two).mp le_rfl
  have hSubset : Finset.Ioc X (A * X) ⊆
      Finset.Ioc X (2 ^ Nat.clog 2 A * X) := by
    intro n hn
    rw [Finset.mem_Ioc] at hn ⊢
    exact ⟨hn.1, hn.2.trans (Nat.mul_le_mul_right X hCover)⟩
  rw [sharpMollifiedTail_apply, wideDirichletPoly]
  have hExtend :
      (∑ n ∈ Finset.Ioc X (A * X),
          sharpMollifiedLineCoeff A X σ n * (n : ℂ) ^ (-(t : ℂ) * I)) =
        ∑ n ∈ Finset.Ioc X (2 ^ Nat.clog 2 A * X),
          sharpMollifiedLineCoeff A X σ n * (n : ℂ) ^ (-(t : ℂ) * I) := by
    apply Finset.sum_subset hSubset
    intro n hnBig hnSmall
    have hnAX : A * X < n := by
      rw [Finset.mem_Ioc] at hnBig
      by_contra h
      exact hnSmall (Finset.mem_Ioc.mpr ⟨hnBig.1, Nat.le_of_not_gt h⟩)
    rw [sharpMollifiedLineCoeff,
      sharpMollifiedCoeff_eq_zero_of_mul_lt A X n hnAX]
    simp
  rw [← hExtend]
  apply Finset.sum_congr rfl
  intro n hn
  exact (sharpMollifiedLineCoeff_term A X n σ t
    (lt_of_le_of_lt (Nat.zero_le X) (Finset.mem_Ioc.mp hn).1)).symm

/-- One dyadic block of the fixed-line sharp tail carries at least its average
share. The block count is the genuine ceiling base-two logarithm of `A`. -/
theorem exists_sharpMollified_large_dyadic_block
    (A X : ℕ) (σ t V : ℝ) (hA : 1 < A)
    (hLarge : V ≤ ‖sharpMollifiedTail A X ((σ : ℂ) + I * (t : ℂ))‖) :
    ∃ r ∈ Finset.range (Nat.clog 2 A),
      V / Nat.clog 2 A ≤
        ‖dirichletPoly (2 ^ r * X) (sharpMollifiedLineCoeff A X σ) t‖ := by
  have hk : 0 < Nat.clog 2 A := Nat.clog_pos Nat.one_lt_two hA
  apply exists_large_dyadic_block X (Nat.clog 2 A)
    (sharpMollifiedLineCoeff A X σ) t V hk
  rw [← sharpMollifiedTail_eq_wideDirichletPoly A X σ t]
  exact hLarge

/-- Simultaneous selection of one beta-shifted dyadic witness, preserving the
full multiplicity weight up to the explicit scale and local-bin factors. -/
theorem finite_shifted_dyadic_witness_extraction {α : Type*} [DecidableEq α]
    (S : Finset α) (weight : α → ℕ) (ordinate : α → ℝ)
    (k L : ℕ) (H : ℝ) (large : ℕ → ℝ → Prop) (inInterval : ℝ → Prop)
    (hS : S.Nonempty)
    (hEach : ∀ x ∈ S, ∃ t : ℝ, |ordinate x - t| ≤ H ∧
      inInterval t ∧ ∃ r ∈ Finset.range k, large r t)
    (hLocal : ∀ z : ℤ,
      ∑ x ∈ S.filter
        (fun y => (z : ℝ) ≤ ordinate y ∧ ordinate y < (z : ℝ) + 1),
        weight x ≤ L) :
    ∃ r ∈ Finset.range k, ∃ W : Finset ℝ,
      IsSeparated 1 W ∧
      (∀ t ∈ W, large r t) ∧
      (∀ t ∈ W, inInterval t) ∧
      ∑ x ∈ S, weight x ≤
        2 * k * ((2 * ⌈H⌉₊ + 1) * L) * W.card := by
  classical
  let shift (x : α) : ℝ :=
    if hx : x ∈ S then Classical.choose (hEach x hx) else ordinate x
  have hShiftSpec : ∀ x ∈ S,
      |ordinate x - shift x| ≤ H ∧ inInterval (shift x) ∧
        ∃ r ∈ Finset.range k, large r (shift x) := by
    intro x hx
    dsimp [shift]
    rw [dite_eq_left hx]
    exact Classical.choose_spec (hEach x hx)
  let scale (x : α) : ℕ :=
    if hx : x ∈ S then Classical.choose (hShiftSpec x hx).2.2 else 0
  have hScaleSpec : ∀ x ∈ S,
      scale x ∈ Finset.range k ∧ large (scale x) (shift x) := by
    intro x hx
    dsimp [scale]
    rw [dite_eq_left hx]
    exact Classical.choose_spec (hShiftSpec x hx).2.2
  have hFiberLocal : ∀ r ∈ Finset.range k, ∀ z : ℤ,
      ∑ t ∈ ((S.filter (fun x => scale x = r)).image shift).filter
          (fun u => (z : ℝ) ≤ u ∧ u < (z : ℝ) + 1),
        ∑ x ∈ (S.filter (fun y => scale y = r)).filter
          (fun y => shift y = t), weight x ≤ (2 * ⌈H⌉₊ + 1) * L := by
    intro r hr z
    apply shifted_bin_weight_le_of_unit_bin_weight
      (S.filter (fun x => scale x = r)) weight ordinate shift H L
    · intro x hx
      exact (hShiftSpec x (Finset.mem_filter.mp hx).1).1
    · intro q
      apply le_trans (Finset.sum_le_sum_of_subset ?_) (hLocal q)
      intro x hx
      rw [Finset.mem_filter] at hx ⊢
      exact ⟨(Finset.mem_filter.mp hx.1).1, hx.2⟩
  obtain ⟨r, hr, W, hSep, hLarge, hInterval, hWeight⟩ :=
    finite_weighted_extract_separated S (Finset.range k) weight scale
      (fun _r x => shift x) large inInterval ((2 * ⌈H⌉₊ + 1) * L)
      hS (fun x hx => (hScaleSpec x hx).1) hFiberLocal
      (fun r hr x hx hxr => by simpa [hxr] using (hScaleSpec x hx).2)
      (fun r hr x hx hxr => by simpa using (hShiftSpec x hx).2.1)
  refine ⟨r, hr, W, hSep, hLarge, hInterval, ?_⟩
  simpa using hWeight

/-- Natural-number cap for the Jensen unit-bin multiplicity estimate. -/
noncomputable def classicalLocalMultiplicityCap (T : ℝ) : ℕ :=
  ⌈Real.log ((100 * T ^ (3 : ℝ)) / (0.6 : ℝ)) /
      Real.log ((7 / 4 : ℝ) / (8 / 5 : ℝ))⌉₊

theorem zeroUnitBin_multiplicity_le_cap (σ T : ℝ) (z : ℤ)
    (hσ : 1 / 2 ≤ σ) (hT : 8 ≤ T) :
    ∑ ρ ∈ zeroUnitBin σ T z, analyticVanishingOrder riemannZeta ρ ≤
      classicalLocalMultiplicityCap T := by
  have hJensen := zeroUnitBin_multiplicity_le_jensen σ T z hσ hT
  have hCeil :
      Real.log ((100 * T ^ (3 : ℝ)) / (0.6 : ℝ)) /
          Real.log ((7 / 4 : ℝ) / (8 / 5 : ℝ)) ≤
        (classicalLocalMultiplicityCap T : ℝ) := by
    exact Nat.le_ceil _
  exact_mod_cast hJensen.trans hCeil

/-- Coefficients normalized to unit size on one chosen dyadic block. -/
noncomputable def normalizedSharpMollifiedLineCoeff
    (A X N : ℕ) (σ ε C : ℝ) (n : ℕ) : ℂ :=
  sharpMollifiedLineCoeff A X σ n /
    ((C * (2 * N : ℝ) ^ ε * (N : ℝ) ^ (-σ) : ℝ) : ℂ)

theorem norm_normalizedSharpMollifiedLineCoeff_le_one
    (A X N n : ℕ) (σ ε C : ℝ) (hN : 0 < N) (hσ : 0 ≤ σ)
    (hε : 0 ≤ ε) (hC : 0 < C)
    (hCoeff : ∀ m : ℕ, 0 < m →
      ‖sharpMollifiedCoeff A X m‖ ≤ C * (m : ℝ) ^ ε)
    (hn : n ∈ dyadicInterval N) :
    ‖normalizedSharpMollifiedLineCoeff A X N σ ε C n‖ ≤ 1 := by
  have hnData := Finset.mem_Ioc.mp hn
  have hnPos : 0 < n := lt_of_le_of_lt (Nat.zero_le N) hnData.1
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hnUpper : (n : ℝ) ≤ 2 * N := by exact_mod_cast hnData.2
  have hnLower : (N : ℝ) ≤ n := by exact_mod_cast hnData.1.le
  have hPowCoeff : (n : ℝ) ^ ε ≤ (2 * N : ℝ) ^ ε :=
    Real.rpow_le_rpow (by positivity) hnUpper hε
  have hWeight : (n : ℝ) ^ (-σ) ≤ (N : ℝ) ^ (-σ) :=
    Real.rpow_le_rpow_of_nonpos hNreal hnLower (by linarith)
  have hLine : ‖sharpMollifiedLineCoeff A X σ n‖ ≤
      C * (2 * N : ℝ) ^ ε * (N : ℝ) ^ (-σ) := by
    rw [sharpMollifiedLineCoeff, norm_mul,
      Complex.norm_natCast_cpow_of_pos hnPos]
    exact mul_le_mul (hCoeff n hnPos) hWeight
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      (mul_nonneg hC.le (Real.rpow_nonneg (by positivity) _)) |>.trans <| by
        gcongr
  have hScalePos : 0 < C * (2 * N : ℝ) ^ ε * (N : ℝ) ^ (-σ) := by positivity
  rw [normalizedSharpMollifiedLineCoeff, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hScalePos]
  exact (div_le_one hScalePos).mpr hLine

theorem dirichletPoly_normalizedSharpMollifiedLineCoeff
    (A X N : ℕ) (σ ε C t : ℝ) :
    dirichletPoly N (normalizedSharpMollifiedLineCoeff A X N σ ε C) t =
      dirichletPoly N (sharpMollifiedLineCoeff A X σ) t /
        ((C * (2 * N : ℝ) ^ ε * (N : ℝ) ^ (-σ) : ℝ) : ℂ) := by
  unfold dirichletPoly normalizedSharpMollifiedLineCoeff
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n _
  rw [div_mul_eq_mul_div]

