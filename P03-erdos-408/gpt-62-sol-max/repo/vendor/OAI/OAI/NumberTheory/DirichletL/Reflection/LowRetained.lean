module

public import OAI.NumberTheory.DirichletL.Reflection.InactiveEnergy
public import OAI.NumberTheory.DirichletL.Reflection.SectorData
public import OAI.NumberTheory.DirichletL.Reflection.LowBranchSum
public import OAI.NumberTheory.DirichletL.Reflection.LiteralNormalized

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section

local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel a c₀ : Eis} {mode : Bool}

set_option maxHeartbeats 850000 in
theorem original_low_sector_retained_energy
    (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (hNlevel : (9:Eis)*c₀∣Nlevel)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀-1)
    (hac : IsCoprime a c₀) (ρ : ℝ) (hρ : 0<ρ) (η : ℝ) (hηpos : 0<η) :
    ∃ (degree : ℕ) (C Z₀ : ℝ), 0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ], ∀ (J I F Q Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hQ : Q≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J Q=rowMaskPart I Q →
    ∀ (A : Finset (FreeReflection.pool J Q Q₀))
      {δ Lscale : ℝ}
      (rb : LowReflectionBudget I Q Z₀ η ε δ Lscale id (· / 2)),
      let G := (poolPrimeFamily J Q Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (familyRawScale G s rb.X rb.QK rb.QP)⁻¹≤rb.Z^Lscale →
    ForSectorRows (σ := σ) Nlevel G s hc₀ fun rows Pset S hrows E =>
    ForDyadicWeights rows Pset rb.QK rb.QP fun θ r aw =>
      (∑ K : rows,‖∑' u : Eisˣ,∑ i∈retainedDyads (familyRawScale G s rb.X rb.QK rb.QP) (16*rb.Z^δ),
        literalDyadicRow G K.val (hrows K.val K.property) S j Pset
          (E.completion K) s hc₀ u i W θ rb.X r aw‖^2)≤
        C*((retainedDyads (familyRawScale G s rb.X rb.QK rb.QP) (16*rb.Z^δ)).card:ℝ)^2*(1+‖θ‖)^degree*(Ideal.absNorm (∏ b,G.ideal b):ℝ)^ρ*rb.Z^((5/6-2*rb.d)+200*η+rb.π-rb.O₀/2) := by
  obtain ⟨degree, h⟩ := sector_normalized_literal_energy_uniform_degree ε hε lo hi hlo W hWs hW η hηpos
  obtain ⟨C₀,Cs,Zs,hC₀,hCs,hZs,henergy⟩ := h (N := Nlevel) s hc₀
  obtain ⟨Zb,Cb,hZb,hCb,hbranch⟩ := original_surviving_low_energy_sum s hc₀ ρ hρ 1 (1/2) η
    (by norm_num) (by norm_num) hηpos
  let Kc := (Real.exp (Real.log 2/2+Real.log 2))^2*(6*Cs)
  have hKc : 0<Kc := by dsimp [Kc];positivity
  let C := Kc*Cb*C₀^2+1
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨degree*2,36*C,max Zs Zb,by positivity,hZs.trans_le (le_max_left _ _),?_⟩
  intro σ _ J I F Q Q₀ hJ hI hQ hpower hmask A δ Lscale rb
  dsimp only
  intro hscap rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar θ r aw hqk hqp hKr hPr hr haw
  let G := (poolPrimeFamily J Q Q₀).restrict A
  let j := fun b : A => completedLocalExponent J F b.val.val
  have hpair := (poolPrimeFamily J Q Q₀).restrict_pairwise (poolPrimeFamily_pairwise J Q Q₀) A
  have hj : ∀ b : A,j b<6 := by intro b;exact Nat.mod_lt _ (by norm_num)
  have hzpos : 0<rb.Z := zero_lt_one.trans (hZs.trans_le ((le_max_left _ _).trans rb.scale_ge))
  let Dset := retainedDyads (familyRawScale G s rb.X rb.QK rb.QP) (16*rb.Z^δ)
  have hb := retained_sum_energy Dset (fun u i (K : rows) =>
    literalDyadicRow G K.val (hrows K.val K.property) S j Pset (E.completion K) s hc₀ u i W θ rb.X r aw) (C*(1+‖θ‖)^(degree*2)*(Ideal.absNorm (∏ b,G.ideal b):ℝ)^ρ*rb.Z^((5/6-2*rb.d)+200*η+rb.π-rb.O₀/2)) (fun u i hi => by
    have hs := henergy rb.Z ((le_max_left _ _).trans rb.scale_ge) G j hNlevel hbase hac hpair hGN hGchar hj
      rows Pset S hrows E hrowcop hprod hScop hSN hSchar u i rb.X θ rb.QK rb.QP r aw rb.X_pos hqk hqp hKr hPr hr haw
    let rb' : LowReflectionBudget I Q Zb η ε δ Lscale (1 * ·) ((1/2:ℝ) * ·) := {
      rb with
      scale_ge := (le_max_right _ _).trans rb.scale_ge
      row_log := by simpa only [id, one_mul] using rb.row_log
      slot_log := by simpa only [div_eq_mul_inv, one_mul, mul_comm] using rb.slot_log
      row_cap := by simpa only [id, one_mul] using rb.row_cap
      slot_cap := by simpa only [div_eq_mul_inv, one_mul, mul_comm] using rb.slot_cap }
    have hb := hbranch J I F Q Q₀ hJ hI hQ hpower hmask A (actualCuspColumn E.referenceArithmetic s hc₀ u i.1)  rb' i hε.le hscap hi
    dsimp only [rb'] at hs hb
    have hrow : rb.H = Real.logb rb.Z rb.QK := rb.row_log
    have hslot : rb.za = Real.logb rb.Z (rb.QP / 2) := rb.slot_log
    rw [←hrow,←hslot,←rb.source_log] at hs
    simp_rw [←Finset.mul_sum] at hs
    apply hs.trans
    calc
      _ ≤ Kc*(Cb*(Ideal.absNorm (∏ b,G.ideal b):ℝ)^ρ*rb.Z^((5/6-2*rb.d)+200*η+rb.π-rb.O₀/2))*(C₀*(1+‖θ‖)^degree)^2 := by
        convert mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb hKc.le)
          (sq_nonneg (C₀*(1+‖θ‖)^degree)) using 1 <;> dsimp only [Kc,G,j] <;> ring
      _ = (Kc*Cb*C₀^2)*(1+‖θ‖)^(degree*2)*(Ideal.absNorm (∏ b,G.ideal b):ℝ)^ρ*rb.Z^((5/6-2*rb.d)+200*η+rb.π-rb.O₀/2)  := by rw [mul_pow,←pow_mul]; ring
      _ ≤ _ := by dsimp only [C]; gcongr; linarith)
  exact hb.trans_eq (by ring)

end
end SevenEighths.InverseReflectedPhase

end OAI
