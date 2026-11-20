module

public import OAI.NumberTheory.DirichletL.Reflection.OriginalBranchSum
public import OAI.NumberTheory.DirichletL.Reflection.LiteralNormalized
public import OAI.NumberTheory.DirichletL.Reflection.InactiveEnergy
public import OAI.NumberTheory.DirichletL.Reflection.CountBudget
public import OAI.NumberTheory.DirichletL.Reflection.BudgetData

public import OAI.NumberTheory.DirichletL.Reflection.SectorData

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v

set_option maxHeartbeats 1000000 in
theorem original_sector_retained_budget_uniform_degree
    (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (ρ : ℝ) (hρ : 0<ρ) (η : ℝ) (hηpos : 0<η)
    (κ δ Lscale Lpool : ℝ) (hκ : 0<κ) (hδL : 0≤δ+Lscale) (_hLpool : 0≤Lpool) :
    ∃ (degree : ℕ), ∀ {Nlevel a c₀ : Eis} {mode : Bool}
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (_hNlevel : (9:Eis)*c₀∣Nlevel)
    (_hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀-1)
    (_hac : IsCoprime a c₀),
    ∃ (C Z₀ : ℝ), 0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ], ∀ (J I F B R Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hF : F≠0) (_hB : B≠0) (_hR : R≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J (B*F*R)=rowMaskPart I (B*F*R) →
    ∀ (A : Finset (FreeReflection.pool J (B*F*R) Q₀))
      (rb : OriginalReflectionBudget I F B R Z₀ η ε δ Lscale),
      let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (familyRawScale G s rb.X rb.QK rb.QP)⁻¹≤rb.Z^Lscale →
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤rb.Z^Lpool → κ+ρ*Lpool≤rb.cstar/16 →
    ForSectorRows (σ := σ) Nlevel G s hc₀ fun rows Pset S hrows E =>
    ForDyadicWeights rows Pset rb.QK rb.QP fun θ r aw =>
      (∑ K : rows,‖∑' u : Eisˣ,∑ i∈retainedDyads (familyRawScale G s rb.X rb.QK rb.QP) (16*rb.Z^δ),
        literalDyadicRow G K.val (hrows K.val K.property) S j Pset
          (E.completion K) s hc₀ u i W θ rb.X r aw‖^2)≤
        C*(1+‖θ‖)^degree*rb.Z^(rb.F₀-3*rb.cstar/16-rb.O₀/2) := by
  obtain ⟨degree,huniform⟩ := sector_normalized_literal_energy_uniform_degree ε hε lo hi hlo W hWs hW η hηpos
  refine ⟨degree*2,?_⟩
  intro Nlevel a c₀ mode s hc₀ hNlevel hbase hac
  obtain ⟨C₀,Cs,Zs,hC₀,hCs,hZs,henergy⟩ := huniform (N:=Nlevel) (a:=a) (c:=c₀) (mode:=mode) s hc₀
  obtain ⟨Zb,Cb,hZb,hCb,hbranch⟩ := original_surviving_energy_sum s hc₀ ρ hρ 1 (1/2) η
    (by norm_num) (by norm_num) hηpos
  let Kc := (Real.exp (Real.log 2/2+Real.log 2))^2*(6*Cs)
  have hKc : 0<Kc := by positivity
  let C := Kc*Cb*C₀^2+1
  have hC : 0<C := by dsimp [C]; positivity
  obtain ⟨Cd,hCd,hcount⟩ := retained_count_budget κ δ Lscale hκ hδL
  refine ⟨36*C*Cd,max Zs Zb,by positivity,hZs.trans_le (le_max_left _ _),?_⟩
  intro σ _ J I F B R Q₀ hJ hI hF hB hR hpower hmask A rb
  dsimp only
  intro hscap hpool hsmall rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar θ r aw hqk hqp hKr hPr hr haw
  let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
  let j := fun b : A => completedLocalExponent J F b.val.val
  have hpair := (poolPrimeFamily J (B*F*R) Q₀).restrict_pairwise (poolPrimeFamily_pairwise J (B*F*R) Q₀) A
  have hj : ∀ b : A,j b<6 := by intro b;exact Nat.mod_lt _ (by norm_num)
  have hzpos : 0<rb.Z := zero_lt_one.trans (hZs.trans_le ((le_max_left _ _).trans rb.scale_ge))
  let Dset := retainedDyads (familyRawScale G s rb.X rb.QK rb.QP) (16*rb.Z^δ)
  have hb := retained_sum_energy Dset (fun u i (K : rows) =>
    literalDyadicRow G K.val (hrows K.val K.property) S j Pset (E.completion K) s hc₀ u i W θ rb.X r aw) (C*(1+‖θ‖)^(degree*2)*(Ideal.absNorm (∏ b,G.ideal b):ℝ)^ρ*rb.Z^(rb.F₀-rb.cstar/4-rb.O₀/2)) (fun u i hi => by
    have hs := henergy rb.Z ((le_max_left _ _).trans rb.scale_ge) G j hNlevel hbase hac hpair hGN hGchar hj
      rows Pset S hrows E hrowcop hprod hScop hSN hSchar u i rb.X θ rb.QK rb.QP r aw rb.X_pos hqk hqp hKr hPr hr haw
    have hb := hbranch J I F B R Q₀ hJ hI hF hB hR hpower hmask A (actualCuspColumn E.referenceArithmetic s hc₀ u i.1)
      rb.Z rb.F₀ rb.N rb.V rb.M rb.z₀ rb.margin rb.cstar rb.O₀ rb.H rb.za rb.Nstar rb.hhat rb.d δ rb.π rb.Ck rb.CO rb.CH rb.Cf rb.X rb.QK rb.QP ε Lscale rb.Lrow rb.Lslot i
      ((le_max_right _ _).trans rb.scale_ge) rb.Ck_pos rb.CO_pos rb.CH_pos rb.Cf_pos rb.X_pos rb.QK_pos rb.QP_pos rb.row_upper rb.powerful_lower rb.residual_lower rb.factor_upper rb.residual_error rb.width_error rb.margins rb.total_width rb.shifted_width rb.factor_width rb.shift_le
      (by simpa only [one_mul] using rb.row_log) (by simpa only [one_div,mul_comm,mul_inv_rev,div_eq_mul_inv,one_mul] using rb.slot_log)
      rb.source_log rb.row_nonneg rb.powerful_nonneg rb.slot_nonneg rb.slot_le rb.saving_pos rb.margin_le rb.perturbation_le rb.eta_le rb.delta_le rb.overhead_le hε.le
      (by simpa only [one_mul] using rb.row_cap) (by simpa only [one_div,mul_comm,mul_inv_rev,div_eq_mul_inv,one_mul] using rb.slot_cap)
      rb.fixed_error rb.loss_budget hscap hi
    dsimp only at hs hb
    rw [←rb.row_log,←rb.slot_log,←rb.source_log] at hs
    simp_rw [←Finset.mul_sum] at hs
    apply hs.trans
    calc
      _ ≤ Kc*(Cb*(Ideal.absNorm (∏ b,G.ideal b):ℝ)^ρ*rb.Z^(rb.F₀-rb.cstar/4-rb.O₀/2))*(C₀*(1+‖θ‖)^degree)^2 := by
        convert mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb hKc.le)
          (sq_nonneg (C₀*(1+‖θ‖)^degree)) using 1 <;> dsimp only [Kc,G,j] <;> ring
      _ = (Kc*Cb*C₀^2)*(1+‖θ‖)^(degree*2)*(Ideal.absNorm (∏ b,G.ideal b):ℝ)^ρ*rb.Z^(rb.F₀-rb.cstar/4-rb.O₀/2) := by ring
      _ ≤ _ := by dsimp only [C]; gcongr; linarith)
  have hcounted := hcount rb.Z (familyRawScale G s rb.X rb.QK rb.QP) (le_of_lt (lt_of_lt_of_le hZs ((le_max_left _ _).trans rb.scale_ge))) hscap
  have h := retained_budget_le (C := 36*C) (e := rb.F₀-rb.cstar/4-rb.O₀/2)
    (hZs.le.trans ((le_max_left _ _).trans rb.scale_ge)) (by positivity) hCd.le
    (U := (1+‖θ‖)^(degree*2)) (by positivity) (Nat.cast_nonneg _) hρ.le hcounted hpool
    (e' := rb.F₀-3*rb.cstar/16-rb.O₀/2) (by nlinarith only [hsmall])
  refine hb.trans ?_
  convert h using 1 <;> dsimp only [Dset] <;> ring

end
end SevenEighths.InverseReflectedPhase

end OAI
