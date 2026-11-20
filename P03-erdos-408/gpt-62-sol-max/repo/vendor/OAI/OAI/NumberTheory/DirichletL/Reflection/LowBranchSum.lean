module

public import OAI.NumberTheory.DirichletL.Reflection.LowExponent
public import OAI.NumberTheory.DirichletL.Reflection.RetainedCaps
public import OAI.NumberTheory.DirichletL.Reflection.BranchCount

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {a c₀ : Eis} {mode : Bool}

theorem original_surviving_low_energy_sum
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (ρ : ℝ) (hρ : 0<ρ) (kK kP η : ℝ) (hkK : 0<kK) (hkP : 0<kP) (hηpos : 0<η) :
    ∃ Z₀ C : ℝ, 1<Z₀ ∧ 0<C ∧
    ∀ (J I F Q Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hQ : Q≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J Q=rowMaskPart I Q →
    ∀ (A : Finset (FreeReflection.pool J Q Q₀))
      (column : Ideal Eis→Ideal Eis→ℂ)
      {ε δ Lscale : ℝ}
      (rb : LowReflectionBudget I Q Z₀ η ε δ Lscale (kK * ·) (kP * ·)) (i : ℕ×ℕ×ℕ),
      0 ≤ ε →
      let G := (poolPrimeFamily J Q Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (familyRawScale G s rb.X rb.QK rb.QP)⁻¹≤rb.Z^Lscale →
      i∈retainedDyads (familyRawScale G s rb.X rb.QK rb.QP) (16*rb.Z^δ) →
      let branches := survivingFrozenBranches G j column (reflectedNDyad i.2.2) (reflectedBDyad i.2.1)
      ((branches.card:ℝ)*∑ e∈branches,
        rb.Z^(InverseTerminalWidths.reflectedExponent 0 rb.H (normWidth rb.Z (frozenExtracted G j e 0))
          (normWidth rb.Z (frozenExtracted G j e 2)) rb.za
          (Real.logb rb.Z (((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted G j e 1)))
          (Real.logb rb.Z (((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted G j e 2)))
          (ramifiedWidth rb.Z i.1) (terminalDualWidth rb.Z rb.H rb.za rb.Nstar G.ideal j e)+
          ε*(rb.H+Real.logb rb.Z (((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted G j e 1))+
            Real.logb rb.Z (((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted G j e 2))+rb.za)+η/2))≤
        C*(Ideal.absNorm (∏ b,G.ideal b):ℝ)^ρ*rb.Z^((5/6-2*rb.d)+200*η+rb.π-rb.O₀/2) := by
  obtain ⟨Z₀,hZ₀,hsave⟩ := original_surviving_low_exponent s hc₀ kK kP η hkK hkP hηpos
  obtain ⟨C,hC,hcount⟩ := surviving_branch_count_small_power ρ hρ
  refine ⟨Z₀,C,hZ₀,hC,?_⟩
  intro J I F Q Q₀ hJ hI hQ hpower hmask A column ε δ Lscale rb i hε
  dsimp only
  intro hscap hret
  let G := (poolPrimeFamily J Q Q₀).restrict A
  let j := fun b : A => completedLocalExponent J F b.val.val
  let branches := survivingFrozenBranches G j column (reflectedNDyad i.2.2) (reflectedBDyad i.2.1)
  have hcbr := hcount G ((poolPrimeFamily J Q Q₀).restrict_pairwise
    (poolPrimeFamily_pairwise J Q Q₀) A) j column (reflectedNDyad i.2.2) (reflectedBDyad i.2.1)
  have hz' : 1<rb.Z := lt_of_lt_of_le hZ₀ rb.scale_ge
  have hb (e : A→Fin 3) (he : e∈branches) := hsave J I F Q Q₀ hJ hI hQ hpower hmask A e column rb i hε hscap hret he
  calc
    _ ≤ (branches.card:ℝ)*∑ _e∈branches,rb.Z^((5/6-2*rb.d)+200*η+rb.π-rb.O₀/2) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro e he
      apply Real.rpow_le_rpow_of_exponent_le hz'.le
      have hh := hb e he
      dsimp only at hh
      linarith
    _ = ((branches.card:ℝ)^2)*rb.Z^((5/6-2*rb.d)+200*η+rb.π-rb.O₀/2) := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcbr (Real.rpow_nonneg (lt_trans zero_lt_one hz').le _)
end
end SevenEighths.InverseReflectedPhase

end OAI
