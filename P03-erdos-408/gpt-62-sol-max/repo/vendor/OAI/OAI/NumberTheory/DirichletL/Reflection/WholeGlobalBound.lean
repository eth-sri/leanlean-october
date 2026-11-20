module

public import OAI.NumberTheory.DirichletL.Reflection.FullEnergyBasic
public import OAI.NumberTheory.DirichletL.Reflection.GlobalEnergy

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v

universe u
variable {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ]
variable {N a c₀ : Eis} {mode : Bool} [Fintype (Eis ⧸ Ideal.span {N^2})]

/-- The whole-row estimate, before fixing the admissible row and slot families. -/
abbrev WholeGlobalBound (σ : Type v) [Fintype σ] (G : PrimeFamily φ) (j : φ → ℕ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀ ≠ 0)
    (W : ℝ → ℂ) (X QK QP : ℝ) (B : ℝ → ℝ) : Prop :=
  ∀ (rows Pset : Finset (Ideal Eis)) (S : Ideal Eis → PrimeFamily σ)
    (hrows : ∀ K ∈ rows, Admissible K),
    WithSectorFamilies N G rows Pset S <|
    ∃ D : ∀ K : rows, ∀ P : Pset, IsCoprime K.val P.val →
      ControlledStratumArithmetic (G.reflected K.val (hrows K.val K.property) (S P.val)).generator N a c₀ mode,
    ForDyadicWeights rows Pset QK QP fun θ r aw =>
      (∑ K : rows, ‖literalWholeRow G K.val (hrows K.val K.property) S j Pset
        (D K) s hc₀ W θ X r aw‖ ^ 2) ≤ B θ

def wholeGlobalConstant (N : Eis) [Fintype (Eis ⧸ Ideal.span {N^2})]
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (Cm Ct : ℝ) : ℝ :=
  let Cshape := ‖fixedRadialCoefficientScalar‖ * ‖s.stratumShapeFactor c₀‖
  let cusp := 27 * (sourceCuspScale s.index)^2 * (Ideal.absNorm (Ideal.span {c₀}) : ℝ)^2
  (Fintype.card (Eis ⧸ Ideal.span {N^2}) : ℝ)^3 *
    ((2*Cshape^2*Cm+1) + 2*(6*Cshape*Ct+1)^2*cusp^4+1) + 1

lemma wholeGlobalConstant_pos
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) {Cm Ct : ℝ} (hCm : 0 ≤ Cm) :
    0 < wholeGlobalConstant N s Cm Ct := by
  unfold wholeGlobalConstant
  positivity

set_option maxHeartbeats 600000 in
/-- Sum the per-sector main and tail bounds for an arbitrary target budget. -/
theorem wholeGlobalBound_of_retained (G : PrimeFamily φ) (j : φ → ℕ)
    (hj : ∀ b, j b < 6) (hpair : Pairwise (Function.onFun IsCoprime G.ideal))
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀ ≠ 0)
    (hNlevel : (9 : Eis) * c₀ ∣ N)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀-1)
    (hac : IsCoprime a c₀) {W : ℝ → ℂ} {X T QK QP U V : ℝ} {Adecay degree degreeTail : ℕ} {Cm₀ Ct₀ : ℝ}
    (hX : 0 < X) (hT : 0 < T) (hQK : 0 < QK) (hQP : 0 < QP)
    (hU : 0 ≤ U) (hpow : V ≤ U) (hCm₀ : 0 ≤ Cm₀) (hCt₀ : 0 ≤ Ct₀)
    (hTailProfiles : WholeRowTailBound.{u,v} W Adecay degreeTail Ct₀)
    (hsize : ∀ rows Pset : Finset (Ideal Eis), 1 ≤ QK → 2 ≤ QP →
      (∀ K ∈ rows, K ≠ 0 ∧ (Ideal.absNorm K : ℝ) ≤ QK) →
      (∀ P ∈ Pset, P ≠ 0 ∧ (Ideal.absNorm P : ℝ) ≤ QP) →
      (rows.card:ℝ)*(Pset.card*((Ideal.absNorm (∏ i,G.ideal i):ℝ)*QK*QP)*
        T^(-(Adecay:ℝ))*(familyRawScale G s X QK QP^2)⁻¹)^2 ≤
        (27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c₀}):ℝ)^2)^4 * V)
    (hmain : ForSectorRows (σ := σ) N G s hc₀ fun rows Pset S hrows E =>
      ForDyadicWeights rows Pset QK QP fun θ r aw =>
        (∑ K : rows, ‖∑' u : Eisˣ, ∑ i ∈ retainedDyads (familyRawScale G s X QK QP) (16*T),
          literalDyadicRow G K.val (hrows K.val K.property) S j Pset (E.completion K) s hc₀ u i W θ X r aw‖^2) ≤
          Cm₀ * ((1+‖θ‖)^degree*U)) :
    WholeGlobalBound (N := N) σ G j s hc₀ W X QK QP fun θ =>
      wholeGlobalConstant N s Cm₀ Ct₀ * (1+‖θ‖)^(max degree (degreeTail*2)) * U := by
  intro rows Pset S hrows hGN hGchar hrowcop hprod hScop hSN hSchar
  obtain ⟨D,hD⟩ := exists_global_sector_completion G rows Pset S hrows s hc₀ hNlevel hbase hac hpair hGN
    hrowcop hprod hScop (fun P hP b => hSN P hP (Sum.inr b))
  refine ⟨D,?_⟩
  intro θ r aw hqk hqp hKr hPr hr haw
  let Cshape := ‖fixedRadialCoefficientScalar‖*‖s.stratumShapeFactor c₀‖
  let Ct := 6*Cshape*Ct₀+1
  let Cm := 2*Cshape^2*Cm₀+1
  let cusp := 27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c₀}):ℝ)^2
  let deg := max degree (degreeTail*2)
  let C := Cm+2*Ct^2*cusp^4+1
  have hCm : 0≤Cm := by dsimp [Cm]; positivity
  have hC : 0<C := by dsimp [C]; positivity
  let q := (Fintype.card (Eis⧸Ideal.span {N^2}):ℝ)
  have hq : 0≤q := Nat.cast_nonneg _
  have hs := literal_global_sector_energy G rows Pset S hrows j D s hc₀ W θ X r aw
    (C*(1+‖θ‖)^deg*U) (by
      intro r₀ p₀
      obtain ⟨E,hE⟩ := hD r₀ p₀
      refine ⟨E,hE,?_⟩
      let rows' := fullRaySector N rows r₀
      let Pset' := fullRaySector N Pset p₀
      have hK {K} (hK : K ∈ rows') := (Finset.mem_filter.mp hK).1
      have hP {P} (hP : P ∈ Pset') := (Finset.mem_filter.mp hP).1
      have hKr' K (h : K ∈ rows') := hKr K (hK h)
      have hPr' P (h : P ∈ Pset') := hPr P (hP h)
      have hretained := whole_sector_energy_of_retained (j := j) E hNlevel hbase hGchar
        (fun P h => hSchar P (hP h)) (fun P h => hprod P (hP h))
        hj hTailProfiles hCt₀ hX hT
        hQK hQP (fun K h => (hKr' K h).2) (fun P h => ⟨(hPr' P h).1,(hPr' P h).2.2⟩)
        r aw (fun K h => hr K (hK h)) (fun P h => haw P (hP h))
        (Cm := Cm₀) (U := (1+‖θ‖)^degree*U) (by positivity)
        (fun rr aa hrr haa => hmain rows' Pset' S (fun K h => hrows K (hK h)) E hGN hGchar
          (fun K h => hrowcop K (hK h)) (fun P h => hprod P (hP h))
          (fun P h => hScop P (hP h)) (fun P h => hSN P (hP h)) (fun P h => hSchar P (hP h))
          θ rr aa hqk hqp hKr' hPr' hrr haa)
      have hSize := hsize rows' Pset' hqk hqp
        (fun K h => ⟨(hrows K (hK h)).1,(hKr' K h).2⟩)
        (fun P h => ⟨(hPr' P h).1.1.ne_zero,(hPr' P h).2.2⟩)
      have htail := hSize.trans (mul_le_mul_of_nonneg_left hpow (by positivity))
      refine hretained.trans ?_
      convert main_add_tail_le (w := 1+‖θ‖) (d := degree) (e := degreeTail) (Ct := Ct)
          hCm (by linarith only [norm_nonneg θ]) hU htail using 1 <;>
        dsimp only [C,Ct,Cm,Cshape,deg,cusp] <;> ring)
  refine hs.trans ?_
  change q^3*(C*(1+‖θ‖)^deg*U)≤(q^3*C+1)*(1+‖θ‖)^deg*U
  nlinarith only [mul_nonneg (pow_nonneg (by positivity : 0 ≤ 1+‖θ‖) deg) hU]

end
end SevenEighths.InverseReflectedPhase

end OAI
