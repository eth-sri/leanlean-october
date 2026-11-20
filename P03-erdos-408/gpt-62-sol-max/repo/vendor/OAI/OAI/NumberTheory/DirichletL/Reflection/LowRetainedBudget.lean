module

public import OAI.NumberTheory.DirichletL.Reflection.LowRetained
public import OAI.NumberTheory.DirichletL.Reflection.CountBudget

public import OAI.NumberTheory.DirichletL.Reflection.SectorData

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel a c₀ : Eis} {mode : Bool}

theorem original_low_sector_retained_budget
    (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (hNlevel : (9:Eis)*c₀∣Nlevel)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀-1)
    (hac : IsCoprime a c₀) (ρ : ℝ) (hρ : 0<ρ) (η : ℝ) (hηpos : 0<η)
    (κ δ Lscale Lpool : ℝ) (hκ : 0<κ) (hδL : 0≤δ+Lscale) (_hLpool : 0≤Lpool) :
    ∃ (degree : ℕ) (C Z₀ : ℝ), 0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ], ∀ (J I F Q Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hQ : Q≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J Q=rowMaskPart I Q →
    ∀ (A : Finset (FreeReflection.pool J Q Q₀))
      (rb : LowReflectionBudget I Q Z₀ η ε δ Lscale id (· / 2)),
      let G := (poolPrimeFamily J Q Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (familyRawScale G s rb.X rb.QK rb.QP)⁻¹≤rb.Z^Lscale →
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤rb.Z^Lpool →
    ForSectorRows (σ := σ) Nlevel G s hc₀ fun rows Pset S hrows E =>
    ForDyadicWeights rows Pset rb.QK rb.QP fun θ r aw =>
      (∑ K : rows,‖∑' u : Eisˣ,∑ i∈retainedDyads (familyRawScale G s rb.X rb.QK rb.QP) (16*rb.Z^δ),
        literalDyadicRow G K.val (hrows K.val K.property) S j Pset
          (E.completion K) s hc₀ u i W θ rb.X r aw‖^2)≤
        C*(1+‖θ‖)^degree*rb.Z^((5/6-2*rb.d)+200*η+rb.π+κ+ρ*Lpool-rb.O₀/2) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,henergy⟩ := original_low_sector_retained_energy
    (Nlevel:=Nlevel) ε hε lo hi hlo W hWs hW s hc₀ hNlevel hbase hac ρ hρ η hηpos
  obtain ⟨Cd,hCd,hcount⟩ := retained_count_budget κ δ Lscale hκ hδL
  refine ⟨degree,C*Cd,Z₀,mul_pos hC hCd,hZ₀,?_⟩
  intro σ _ J I F Q Q₀ hJ hI hQ hpower hmask A rb
  dsimp only
  intro hscap hpool rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar θ r aw hqk hqp hKr hPr hr haw
  let G := (poolPrimeFamily J Q Q₀).restrict A
  have hz' : 1<rb.Z := lt_of_lt_of_le hZ₀ rb.scale_ge
  have hs := henergy J I F Q Q₀ hJ hI hQ hpower hmask A rb hscap
    rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar θ r aw hqk hqp hKr hPr hr haw
  have hcounted := hcount rb.Z (familyRawScale G s rb.X rb.QK rb.QP) hz'.le hscap
  exact hs.trans (retained_budget_le hz'.le hC.le hCd.le (by positivity)
    (Nat.cast_nonneg _) hρ.le hcounted hpool (by nlinarith))

end
end SevenEighths.InverseReflectedPhase

end OAI
