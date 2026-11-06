module

public import OAI.NumberTheory.DirichletL.Reflection.SumMeasure

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
universe u v
variable {Ω : Type*} [MeasurableSpace Ω] {N a c : ActualEisensteinCubic.O} {mode : Bool}

theorem bounded_column_hybrid_energy_extracted_type_uniform (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {φ : Type u} [Fintype φ], ∀ X Y B L : ℝ, 1 ≤ X → 1 ≤ L →
    ∀ (F : PrimeFamily φ), Pairwise (Function.onFun IsCoprime F.ideal) →
    ∀ (jF : φ → ℕ) (e : φ → Fin 3) (A : Ideal ActualEisensteinCubic.O → Ideal ActualEisensteinCubic.O → ℂ),
      (∀ n b, ‖A n b‖ ≤ 1) →
    ∀ (rows nset bset Pset : Finset (Ideal ActualEisensteinCubic.O)) (aP : Ideal ActualEisensteinCubic.O → ℂ),
      (∀ K ∈ rows, Admissible K ∧ (Ideal.absNorm K:ℝ) ≤ X) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n:ℝ) ≤ Y) →
      (∀ b ∈ bset, primaryGenerator b ≠ 0 ∧ (Ideal.absNorm b:ℝ) ≤ B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ) ≤ 2*L) →
      (∀ P ∈ Pset, ‖aP P‖ ≤ 1) →
      let Yq := extractedDualScale (frozenExtracted F jF e 1) Y
      let Bq := extractedDualScale (frozenExtracted F jF e 2) B
      (∑ K ∈ rows, ‖hybridRow Pset nset bset aP
        (frozenBranchColumn F jF e A) K‖^2) ≤
      (frozenBranchScale F jF e)^2*
        (C*(X*Yq*Bq*L)^ε*(X+Yq*Bq)*Bq*(Yq+L+(Yq*L)^(2/3:ℝ))) := by
  obtain ⟨C,hC,he⟩ := hybridRow_energy ε hε
  refine ⟨C,hC,?_⟩
  intro φ _ X Y B L hX hL F hF jF e A hA rows nset bset Pset aP hrows hn hb hP ha
  let D1 := frozenExtracted F jF e 1
  let D2 := frozenExtracted F jF e 2
  let Yq := extractedDualScale D1 Y
  let Bq := extractedDualScale D2 B
  have hD1 : D1 ≠ 0 := frozenExtracted_ne_zero F jF e 1
  have hD2 : D2 ≠ 0 := frozenExtracted_ne_zero F jF e 2
  have hnq : ∀ n ∈ quotientSupport D1 nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n:ℝ) ≤ Yq := by
    intro n hn'
    exact ⟨quotientSupport_cubic_admissible D1 hD1 nset (by grind) n hn',
      (quotientSupport_norm_div D1 hD1 nset Y (by grind) n hn').trans (le_max_right _ _)⟩
  have hbq : ∀ b ∈ quotientSupport D2 bset, primaryGenerator b ≠ 0 ∧ (Ideal.absNorm b:ℝ) ≤ Bq := by
    intro b hb'
    have hsource := hb (D2*b) ((mem_quotientSupport D2 b hD2 bset).mp hb')
    rw [primaryGenerator_mul] at hsource
    exact ⟨(mul_ne_zero_iff.mp hsource.1).2,
      (quotientSupport_norm_div D2 hD2 bset B (fun b h => (hb b h).2) b hb').trans (le_max_right _ _)⟩
  have hacoeff : ∀ P ∈ Pset, ‖aP P*extractedSlotFactor D1 D2 P‖ ≤ 1 := by
    intro P hP'
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (by grind)).trans (extractedSlotFactor_norm_le_one D1 D2 P)
  have hcolumn :=
    extractedFrozenColumn_norm_le_one F jF e A hA
  have hh := he X Yq Bq L hX (le_max_left _ _) (le_max_left _ _) hL rows
    (quotientSupport D1 nset) (quotientSupport D2 bset) Pset
    (fun P => aP P*extractedSlotFactor D1 D2 P)
    (extractedFrozenColumn F jF e A)
    hrows hnq hbq hP hacoeff (fun n _ b _ => hcolumn n b)
  apply le_trans (Finset.sum_le_sum (fun K hK => ?_))
    ((by rw [← Finset.mul_sum]; nlinarith) :
      (∑ K ∈ rows, (frozenBranchScale F jF e)^2*
        ‖hybridRow Pset (quotientSupport D1 nset) (quotientSupport D2 bset)
          (fun P => aP P*extractedSlotFactor D1 D2 P)
          (extractedFrozenColumn F jF e A) K‖^2) ≤ _)
  rw [hybridRow_frozen_extraction F hF jF e _ nset bset Pset
    (fun n h => (hn n h).1.2) (fun b h => (hb b h).1) aP K (by grind)
    (fun P h => (hP P h).1.2)]
  have hp := frozenBranchScale_pos F jF e
  have hs := extractedRowFactor_norm_le_one D1 D2 K
  have hs2 : ‖extractedRowFactor D1 D2 K‖^2 ≤ 1 := by
    have h0 := norm_nonneg (extractedRowFactor D1 D2 K)
    nlinarith
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp,mul_pow]
  change (frozenBranchScale F jF e)^2*‖extractedRowFactor D1 D2 K‖^2* _ ≤ _
  calc
    _ ≤ ((frozenBranchScale F jF e)^2*1)*_ := by gcongr
    _ = _ := by linarith

theorem actual_weighted_reflected_branch_energy_type_uniform (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ], ∀ (X Y B L : ℝ), 1 ≤ X → 1 ≤ Y → 1 ≤ B → 1 ≤ L →
    ∀ (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
      (hc : c ≠ 0), (9:ActualEisensteinCubic.O)*c ∣ N →
      (if mode then ConcretePrimeRowBridge.goodLambda^2 ∣ a-1 else ConcretePrimeRowBridge.goodLambda^2 ∣ c-1) → IsCoprime a c →
      Pairwise (Function.onFun IsCoprime F.ideal) →
      (∀ f, IsCoprime (Ideal.span {N}) (F.ideal f)) →
      (∀ f, ringChar (ActualEisensteinCubic.O ⧸ F.ideal f) ≠ 2) → (∀ f, jF f < 6) →
    ∀ {ι : Type*} [Fintype ι] (G0 : PrimeFamily ι)
      (D0 : ControlledStratumArithmetic G0.generator N a c mode)
      (u : ActualEisensteinCubic.Oˣ) (m : ℕ) (rows nset bset Pset : Finset (Ideal ActualEisensteinCubic.O))
      (S : Ideal ActualEisensteinCubic.O → PrimeFamily σ)
      (r aw : Ideal ActualEisensteinCubic.O → ℂ) (w : Ideal ActualEisensteinCubic.O → Ideal ActualEisensteinCubic.O → ℂ),
      (∀ K ∈ rows, Admissible K ∧ (Ideal.absNorm K:ℝ) ≤ X) →
      (∀ K ∈ rows, (∀ f, IsCoprime (F.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K) →
      (∀ P ∈ Pset, (∏ i, (S P).ideal i) = P) →
      (∀ P ∈ Pset, Pairwise (Function.onFun IsCoprime (F.sum (S P)).ideal)) →
      (∀ P ∈ Pset, ∀ i, IsCoprime (Ideal.span {N}) ((F.sum (S P)).ideal i)) →
      (∀ P ∈ Pset, ∀ i, ringChar (ActualEisensteinCubic.O ⧸ (F.sum (S P)).ideal i) ≠ 2) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n:ℝ) ≤ Y) →
      (∀ b ∈ bset, primaryGenerator b ≠ 0 ∧ (Ideal.absNorm b:ℝ) ≤ B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ) ≤ 2*L) →
      (∀ K ∈ rows, ‖r K‖ ≤ 1) → (∀ P ∈ Pset, ‖aw P‖ ≤ 1) → (∀ n b, ‖w n b‖ ≤ 1) →
      let Yq := extractedDualScale (frozenExtracted F jF e 1) Y
      let Bq := extractedDualScale (frozenExtracted F jF e 2) B
      (∑ K ∈ rows, ‖weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
        (actualCuspColumn D0 s hc u m) r aw w u m Pset nset bset K‖^2) ≤
      (frozenBranchScale F jF e)^2*
        (C*(X*Yq*Bq*L)^ε*(X+Yq*Bq)*Bq*(Yq+L+(Yq*L)^(2/3:ℝ))) := by
  obtain ⟨C,hC,he⟩ := bounded_column_hybrid_energy_extracted_type_uniform  ε hε
  refine ⟨C,hC,?_⟩
  intro φ σ _ _ X Y B L hX _hY _hB hL F jF e s hc hN hbase hac hF hNF hcharF hj
    ι _ G0 D0 u m rows nset bset Pset S r aw w hrows hrowcop _hproducts hScop hSN hSchar hn hb hP hr haw hw
  have hfrozen :=
    actualFrozenPhase_norm_le_one F jF D0.fixedFactor (D0.fixedFactor_norm hN G0.generator_product_primary hbase).le
      s hc hN hbase hac hF hNF hcharF hj u m
  have hrow (K : Ideal ActualEisensteinCubic.O) (hK : K ∈ rows) : ‖actualRowPhaseExtension F jF s u m K‖ ≤ 1 := by
    rw [actualRowPhaseExtension,dite_eq_left (hrows K hK).1]
    exact actualRowPhase_norm_le_one F K (hrows K hK).1 jF s hc hN hbase hac hF
      (hrowcop K hK).1 hNF (hrowcop K hK).2 hcharF u m
  have hslot (P : Ideal ActualEisensteinCubic.O) (hP : P ∈ Pset) : ‖actualSlotPhase F (S P) jF s u m*aw P‖ ≤ 1 := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (two_block_phase_bounds F (S P) jF s hc hN hbase hac (hScop P hP) (hSN P hP) (hSchar P hP) u m).2).trans
      (haw P hP)
  have hcol := actualCuspWeightedColumn_norm_le_one G0 D0 s hc u m w hw
  apply le_trans (Finset.sum_le_sum (fun K hK => ?_))
    (he X Y B L hX hL F hF jF e (fun n b => actualCuspColumn D0 s hc u m n b*w n b) hcol
      rows nset bset Pset (fun P => actualSlotPhase F (S P) jF s u m*aw P) hrows hn hb hP hslot)
  have hphase : ‖(-1:ℂ)^(Fintype.card σ)*actualFrozenPhase F jF D0.fixedFactor s u m*
      actualRowPhaseExtension F jF s u m K*r K‖ ≤ 1 := by
    simp only [norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      ((mul_le_of_le_one_left (norm_nonneg _) hfrozen).trans (hrow K hK))).trans (hr K hK)
  have hphase0 := norm_nonneg ((-1:ℂ)^(Fintype.card σ)*actualFrozenPhase F jF D0.fixedFactor s u m*
      actualRowPhaseExtension F jF s u m K*r K)
  have hs : ‖(-1:ℂ)^(Fintype.card σ)*actualFrozenPhase F jF D0.fixedFactor s u m*
      actualRowPhaseExtension F jF s u m K*r K‖^2 ≤ 1 := by nlinarith
  rw [weightedReflectedBranchHybridRow,norm_mul,mul_pow]
  nlinarith

end
end SevenEighths.InverseReflectedPhase

end OAI
