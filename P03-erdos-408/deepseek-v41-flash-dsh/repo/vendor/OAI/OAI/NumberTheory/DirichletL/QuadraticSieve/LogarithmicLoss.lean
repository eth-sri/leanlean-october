module

public import OAI.NumberTheory.DirichletL.QuadraticSieve.SelectedExponents

@[expose] public section

namespace OAI

noncomputable section














namespace CanonicalQuadraticSieve

theorem lifting_annular_scale_bounds (j : Fin 7) : 1≤(2:ℝ)^j.val ∧ (2:ℝ)^j.val≤64 := by
  refine ⟨one_le_pow₀ (by norm_num),?_⟩
  have hj : j.val≤6 := by omega
  have hh := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hj
  norm_num at hh
  exact hh

theorem HasSieveExponent.lifted_annular_selected {α : ℝ} (hexp : HasSieveExponent α)
    (hα1 : 1≤α) (hα2 : α≤2) (η : ℝ) (hη : 0<η) (hη1 : η≤1)
    (l A : ℕ) (hl : 4≤η*l) (hA : 4≤η*A) :
    ∃ C : ℝ, 0<C ∧ ∀ (M N : ℝ),
      1≤M → 28≤N → N^(2-1/α)≤M →
      1≤selectedPoissonK fixedCutoffBase M N η →
      ∀ (j : Fin 7) (q : ℝ), 1≤q → q≤7 →
      ∀ (a : idealRange N → ℂ), CoefficientOnShell N (N/q) a →
      annularHighEnergy ((2:ℝ)^j.val*M) N (selectedPoissonK fixedCutoffBase M N η) a ≤
        C*(M*N)^(260*η)*M*∑J,‖a J‖^2 := by
  have hc0 : 0<fixedCutoffBase := lt_of_lt_of_le (by norm_num) fixedCutoffBase_bounds.1
  obtain ⟨C,hC,hann⟩ := hexp.annular_selected_bound hα1 hα2 η hη hη1 l A hl hA
    (21952*fixedCutoffBase) (by linarith [fixedCutoffBase_bounds.1])
  refine ⟨C*64^(260*η)*64,by positivity,?_⟩
  intro M N hM hN hthreshold hK j q hq hq7 a ha
  let r : ℝ := (2:ℝ)^j.val
  have hr := lifting_annular_scale_bounds j
  have hM0 : 0<M := by linarith
  have hN0 : 0<N := by linarith
  have hq0 : 0<q := by linarith
  have hr0 : 0<r := by dsimp [r]; positivity
  have hNq : 4≤N/q := (le_div_iff₀ hq0).mpr (by nlinarith)
  have hNqN : N/q≤N := div_le_self hN0.le hq
  have hβ : 0≤2-1/α := by
    have hfrac : 1/α≤1 := (div_le_one (by linarith : 0<α)).mpr hα1
    linarith
  have hth : (N/q)^(2-1/α)≤r*M := by
    calc
      _ ≤ N^(2-1/α) := Real.rpow_le_rpow (by positivity) hNqN hβ
      _ ≤ M := hthreshold
      _ ≤ r*M := by nlinarith [hr.1]
  let c := cutoffRescaleCoefficient fixedCutoffBase η r q
  have hc := cutoffRescaleCoefficient_bounds fixedCutoffBase η r q hc0.le hη.le hη1 hr.1 hr.2 hq hq7
  have hk := selectedPoissonK_rescale fixedCutoffBase M N η r q hM0 hN0 hr0 hq0
  have hh := hann c (r*M) (N/q) hc.1 hc.2 (by nlinarith [hr.1]) hNq hth
    (by simpa only [c,hk] using hK) (coefficientAtScale N (N/q) a)
    (coefficientAtScale_shell N (N/q) a ha)
  dsimp only [c] at hh
  rw [hk,←annularHighEnergy_coefficientAtScale (r*M) N (N/q)
    (selectedPoissonK fixedCutoffBase M N η) a (fun J hJ => (ha J hJ).2),
    ←coefficientAtScale_energy N (N/q) a (fun J hJ => (ha J hJ).2)] at hh
  have hp : ((r*M)*(N/q))^(260*η)≤64^(260*η)*(M*N)^(260*η) := by
    calc
      _ ≤ (64*(M*N))^(260*η) := by
        apply Real.rpow_le_rpow (by positivity) _ (by positivity)
        calc
          (r*M)*(N/q) ≤ (64*M)*N := by gcongr; exact hr.2
          _ = _ := by ring
      _ = _ := Real.mul_rpow (by norm_num) (by positivity)

  apply hh.trans
  calc
    _ ≤ C*(64^(260*η)*(M*N)^(260*η))*(64*M)*∑J,‖a J‖^2 := by
      gcongr
      exact hr.2
    _ = _ := by ring

theorem HasSieveExponent.ball_selected_high {α : ℝ} (hexp : HasSieveExponent α)
    (hα1 : 1≤α) (hα2 : α≤2) (η : ℝ) (hη : 0<η) (hη1 : η≤1)
    (l A : ℕ) (hl : 4≤η*l) (hA : 4≤η*A) :
    ∃ C : ℝ, 0<C ∧ ∀ (M N : ℝ),
      1≤M → 28≤N → N^(2-1/α)≤M →
      1≤selectedPoissonK fixedCutoffBase M N η →
      ∀ (a : idealRange N → ℂ), CoefficientOnShell N N a →
      ballQuadraticEnergy M N a ≤
        (sieveNorm (selectedPoissonK fixedCutoffBase M N η) N+
          C*(M*N)^(260*η)*M)*∑J,‖a J‖^2 := by
  obtain ⟨C,hC,hann⟩ := hexp.lifted_annular_selected hα1 hα2 η hη hη1 l A hl hA
  refine ⟨14*C,by positivity,?_⟩
  intro M N hM hN hthreshold hK a ha
  have hf (j : Fin 7) := hann M N hM hN hthreshold hK j 1 (by norm_num) (by norm_num)
    (liftingFreeCoefficient N a) (by simpa only [div_one] using liftingFreeCoefficient_shell N N a ha)
  have hd (j : Fin 7) := hann M N hM hN hthreshold hK j 7 (by norm_num) (by norm_num)
    (liftingDividedCoefficient N a) (liftingDividedCoefficient_shell N N a ha)
  have hsf := Finset.sum_le_sum (fun j (_ : j∈(Finset.univ : Finset (Fin 7))) => hf j)
  have hsd := Finset.sum_le_sum (fun j (_ : j∈(Finset.univ : Finset (Fin 7))) => hd j)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] at hsf hsd
  have he := liftingCoefficient_energy N a
  have hb := ballQuadraticEnergy_lifted_annuli M N (selectedPoissonK fixedCutoffBase M N η)
    (by linarith) a
  calc
    _ ≤ sieveNorm (selectedPoissonK fixedCutoffBase M N η) N*(∑J,‖a J‖^2)+
      2*(7*(C*(M*N)^(260*η)*M*∑J,‖liftingFreeCoefficient N a J‖^2)+
        7*(C*(M*N)^(260*η)*M*∑J,‖liftingDividedCoefficient N a J‖^2)) := by linarith
    _ = _ := by
      calc
        _ = sieveNorm (selectedPoissonK fixedCutoffBase M N η) N*(∑J,‖a J‖^2)+
          (14*C)*(M*N)^(260*η)*M*((∑J,‖liftingFreeCoefficient N a J‖^2)+
            (∑J,‖liftingDividedCoefficient N a J‖^2)) := by ring
        _ = _ := by rw [he]; ring

theorem HasSieveExponent.low_threshold {α : ℝ} (hexp : HasSieveExponent α)
    (hα : 1≤α) (hα2 : α≤2) (η : ℝ) (hη : 0<η) (hη1 : η≤1)
    (c : ℝ) (hc : 4≤c) :
    ∃ C : ℝ, 0<C ∧ ∀ M N : ℝ, 1≤M → 1≤N → N^(2-1/α)≤M → M≤N^2 →
      sieveNorm (selectedPoissonK c M N η) N≤C*(M*N)^(6*η)*M := by
  obtain ⟨C,hC,hrev⟩ := hexp.reverse η hη
  have hc0 : 0<c := by linarith
  refine ⟨C*c^η*(1+c^α),by positivity,?_⟩
  intro M N hM hN hthreshold hupper
  have hM0 : 0<M := by linarith
  have hN0 : 0<N := by linarith
  have hP : 1≤M*N := by nlinarith
  have hP0 : 0<M*N := by positivity
  have hNM := improved_threshold_ge_column α N M hα hN hthreshold
  have hNP : N≤M*N := by nlinarith
  have hK := (selectedPoisson_bounds c M N η hc hM hN hupper hη.le).2.1
  have hKP := (selectedPoisson_upper c c M N η hc le_rfl hM hN hη.le hη1).2.2
  have hprod : selectedPoissonK c M N η*N≤c*(M*N)^4 := by
    calc
      _ ≤ (c*(M*N)^3)*(M*N) := by gcongr
      _ = _ := by ring
  have hsmall : (selectedPoissonK c M N η*N)^η≤c^η*(M*N)^(4*η) := by
    calc
      _ ≤ (c*(M*N)^4)^η := Real.rpow_le_rpow (by positivity) hprod hη.le
      _ = _ := by
        rw [Real.mul_rpow hc0.le (by positivity)]
        congr 1
        rw [←Real.rpow_natCast,←Real.rpow_mul hP0.le]
        norm_num
  have hmain : (selectedPoissonK c M N η)^α≤c^α*(M*N)^(2*η)*M := by
    apply (improved_threshold_low α c η N M (by linarith) hc0 hN0 hM0 hthreshold).trans
    have hp : (M*N)^(η*α)≤(M*N)^(2*η) := Real.rpow_le_rpow_of_exponent_le hP (by nlinarith)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hc0.le _))
      hNM hN0.le (by positivity)
  have hR : 1≤(M*N)^(2*η) := Real.one_le_rpow hP (by positivity)
  have hsum : N+(selectedPoissonK c M N η)^α≤(1+c^α)*(M*N)^(2*η)*M := by
    calc
      _ ≤ M+c^α*(M*N)^(2*η)*M := add_le_add hNM hmain
      _ ≤ (M*N)^(2*η)*M+c^α*(M*N)^(2*η)*M := by
        exact add_le_add (le_mul_of_one_le_left hM0.le hR) le_rfl
      _ = _ := by ring
  have hpowers : (M*N)^(4*η)*(M*N)^(2*η)=(M*N)^(6*η) := by
    rw [←Real.rpow_add hP0]
    congr 1
    ring
  calc
    _ ≤ C*(selectedPoissonK c M N η*N)^η*(N+(selectedPoissonK c M N η)^α) := hrev _ _ hK hN
    _ ≤ C*(c^η*(M*N)^(4*η))*((1+c^α)*(M*N)^(2*η)*M) := by gcongr
    _ = C*c^η*(1+c^α)*((M*N)^(4*η)*(M*N)^(2*η))*M := by ring
    _ = _ := by rw [hpowers]

end CanonicalQuadraticSieve

namespace SecondPassArithmetic

theorem normLogBin_le_log_upper (x Y : ℝ) (hx : 0<x) (hxy : x≤Y) (hY : 1≤Y) :
    (normLogBin x:ℝ)≤Real.log Y := by
  have hh : (normLogBin x:ℝ)≤normLogBin Y := by exact_mod_cast normLogBin_mono hx hxy
  exact hh.trans (Nat.floor_le (Real.log_nonneg hY))

end SecondPassArithmetic

namespace CanonicalQuadraticSieve

theorem sieveNorm_small_columns (M N : ℝ) (hM : 1≤M) (hN : 1≤N) (hN28 : N≤28) :
    sieveNorm M N≤785*QuadraticInitialBound.initialSieveConstant*M := by
  have hceil : (⌈N⌉₊:ℝ)≤28 := by
    exact_mod_cast (Nat.ceil_le.mpr hN28 : ⌈N⌉₊≤28)
  have hs : (⌈N⌉₊:ℝ)^2≤784 := by
    nlinarith [Nat.cast_nonneg (α:=ℝ) ⌈N⌉₊]
  have hc := QuadraticInitialBound.initialSieveConstant_pos
  have hb := sieveNorm_initial M N hM hN
  have ht : M+(⌈N⌉₊:ℝ)^2≤785*M := by linarith
  calc
    _ ≤ QuadraticInitialBound.initialSieveConstant*(M+(⌈N⌉₊:ℝ)^2) := hb
    _ ≤ QuadraticInitialBound.initialSieveConstant*(785*M) := mul_le_mul_of_nonneg_left ht hc.le
    _ = _ := by ring

theorem HasSieveExponent.shell_threshold {α : ℝ} (hexp : HasSieveExponent α)
    (hα1 : 1≤α) (hα2 : α≤2) :
    ∀ρ : ℝ, 0<ρ → ∃C : ℝ, 0<C ∧ ∀M N : ℝ,
      1≤M → 1≤N → N^(2-1/α)≤M →
      ∀a : idealRange N → ℂ, CoefficientOnShell N N a →
      ballQuadraticEnergy M N a≤C*(M*N)^ρ*M*∑J,‖a J‖^2 := by
  intro ρ hρ
  let η := min 1 (ρ/600)
  have hη : 0<η := lt_min (by norm_num) (by positivity)
  have hη1 : η≤1 := min_le_left _ _
  have hηρ : η≤ρ/600 := min_le_right _ _
  have h6 : 6*η≤ρ := by linarith only [hηρ,hη]
  have h260 : 260*η≤ρ := by linarith only [hηρ,hη]
  obtain ⟨l,hl⟩ := exists_nat_gt (4/η)
  have horder : 4≤η*l := by
    have hh := (div_lt_iff₀ hη).mp hl
    nlinarith only [hh]
  obtain ⟨CH,hCH,hhigh⟩ := hexp.ball_selected_high hα1 hα2 η hη hη1 l l horder horder
  obtain ⟨CL,hCL,hlow⟩ := hexp.low_threshold hα1 hα2 η hη hη1 fixedCutoffBase fixedCutoffBase_bounds.1
  let I := QuadraticInitialBound.initialSieveConstant
  have hI : 0<I := QuadraticInitialBound.initialSieveConstant_pos
  let C := 790*I+CL+CH
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro M N hM hN hthreshold a ha
  have hP : 1≤M*N := by nlinarith only [hM,hN]
  have hPρ : 1≤(M*N)^ρ := Real.one_le_rpow hP hρ.le
  have hE : 0≤∑J,‖a J‖^2 := by positivity
  have hM0 : 0≤M := le_trans zero_le_one hM
  have hscale {x y : ℝ} (hxy : x≤y) :
      x*M*∑J,‖a J‖^2 ≤ y*M*∑J,‖a J‖^2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hxy hM0) hE
  have hmatrix : ballQuadraticEnergy M N a≤sieveNorm M N*∑J,‖a J‖^2 :=
    FiniteSieveOperator.energy_bound (matrix M N) a
  by_cases hlarge : N^2≤M
  · have hb := sieveNorm_large_rows M N hM hN hlarge
    calc
      _ ≤ (5*I*M)*∑J,‖a J‖^2 := hmatrix.trans (mul_le_mul_of_nonneg_right hb hE)
      _ = (5*I)*1*M*∑J,‖a J‖^2 := by ring
      _ ≤ _ := hscale (mul_le_mul
        (show 5*I≤C by dsimp [C]; linarith only [hI,hCL,hCH])
        hPρ zero_le_one hC.le)
  by_cases hsmall : N≤28
  · have hb := sieveNorm_small_columns M N hM hN hsmall
    calc
      _ ≤ (785*I*M)*∑J,‖a J‖^2 := hmatrix.trans (mul_le_mul_of_nonneg_right hb hE)
      _ = (785*I)*1*M*∑J,‖a J‖^2 := by ring
      _ ≤ _ := hscale (mul_le_mul
        (show 785*I≤C by dsimp [C]; linarith only [hI,hCL,hCH])
        hPρ zero_le_one hC.le)
  have hupper : M≤N^2 := le_of_not_ge hlarge
  have hK := (selectedPoisson_bounds fixedCutoffBase M N η fixedCutoffBase_bounds.1 hM hN hupper hη.le).2.1
  have hb := hhigh M N hM (by linarith only [hsmall]) hthreshold hK a ha
  have hlb := hlow M N hM hN hthreshold hupper
  have hp6 : (M*N)^(6*η)≤(M*N)^ρ := Real.rpow_le_rpow_of_exponent_le hP h6
  have hp260 : (M*N)^(260*η)≤(M*N)^ρ := Real.rpow_le_rpow_of_exponent_le hP h260
  calc
    _ ≤ (sieveNorm (selectedPoissonK fixedCutoffBase M N η) N+CH*(M*N)^(260*η)*M)*∑J,‖a J‖^2 := hb
    _ ≤ (CL*(M*N)^(6*η)*M+CH*(M*N)^(260*η)*M)*∑J,‖a J‖^2 :=
      mul_le_mul_of_nonneg_right (add_le_add hlb le_rfl) hE
    _ ≤ (CL*(M*N)^ρ*M+CH*(M*N)^ρ*M)*∑J,‖a J‖^2 :=
      mul_le_mul_of_nonneg_right (add_le_add
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp6 hCL.le) hM0)
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp260 hCH.le) hM0)) hE
    _ = (CL+CH)*(M*N)^ρ*M*∑J,‖a J‖^2 := by ring
    _ ≤ _ := hscale (mul_le_mul_of_nonneg_right
      (show CL+CH≤C by dsimp [C]; linarith only [hI])
      (Real.rpow_nonneg (by positivity) _))

theorem HasSieveExponent.improve {α : ℝ} (hexp : HasSieveExponent α)
    (hα1 : 1≤α) (hα2 : α≤2) : HasSieveExponent (2-1/α) := by
  have hα : 0<α := by linarith
  have hfrac : 1/α≤1 := (div_le_one hα).mpr hα1
  have hpos : 0≤1/α := by positivity
  apply hasSieveExponent_of_shell_threshold (2-1/α) (by linarith) (by linarith)
  exact hexp.shell_threshold hα1 hα2



theorem hasSieveExponent_one : HasSieveExponent 1 :=
  hasSieveExponent_one_of_improvement (fun _α hα hα2 h => h.improve hα.le hα2)

theorem sieveNorm_sharp :
    ∀ ε : ℝ, 0<ε → ∃ C : ℝ, 0<C ∧ ∀ M N : ℝ, 1≤M → 1≤N →
      sieveNorm M N≤C*(M*N)^ε*(M+N) := by
  simpa only [HasSieveExponent,Real.rpow_one] using hasSieveExponent_one

end CanonicalQuadraticSieve

namespace SecondPassArithmetic

end SecondPassArithmetic

end

end OAI
