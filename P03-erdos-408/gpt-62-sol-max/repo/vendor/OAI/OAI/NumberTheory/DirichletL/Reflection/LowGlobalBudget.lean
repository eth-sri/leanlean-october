module

public import OAI.NumberTheory.DirichletL.Reflection.GlobalEnergy
public import OAI.NumberTheory.DirichletL.Reflection.SectorData
public import OAI.NumberTheory.DirichletL.Reflection.ActualSizeCaps
public import OAI.NumberTheory.DirichletL.Reflection.LowRetainedBudget
public import OAI.NumberTheory.DirichletL.Reflection.WholeGlobalBound

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel a c₀ : Eis} {mode : Bool}

set_option maxHeartbeats 600000 in
theorem original_low_global_full_budget
    [Fintype (Eis⧸Ideal.span {Nlevel^2})]
    (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (hNlevel : (9:Eis)*c₀∣Nlevel)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀-1)
    (hac : IsCoprime a c₀) (ρ : ℝ) (hρ : 0<ρ) (η : ℝ) (hηpos : 0<η)
    (κ δ Lscale Lpool : ℝ) (hκ : 0<κ) (hδL : 0≤δ+Lscale) (hLpool : 0≤Lpool)
    (Lcap saving : ℝ) (hδ : 0<δ) :
    ∃ (degree : ℕ) (C Z₀ : ℝ), 0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ], ∀ (J I F Q Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hQ : Q≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J Q=rowMaskPart I Q →
    ∀ (A : Finset (FreeReflection.pool J Q Q₀))
      (rb : LowReflectionBudget I Q Z₀ η ε δ Lscale id (· / 2)),
      rb.X⁻¹≤rb.Z^Lcap → rb.QK≤rb.Z^Lcap → rb.QP≤rb.Z^Lcap → -saving≤(5/6-2*rb.d)+200*η+rb.π+κ+ρ*Lpool-rb.O₀/2 →
      let G := (poolPrimeFamily J Q Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤rb.Z^Lcap →
      (familyRawScale G s rb.X rb.QK rb.QP)⁻¹≤rb.Z^Lscale →
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤rb.Z^Lpool →
    WholeGlobalBound (N := Nlevel) σ G j s hc₀ W rb.X rb.QK rb.QP
      fun θ => C*(1+‖θ‖)^degree*rb.Z^((5/6-2*rb.d)+200*η+rb.π+κ+ρ*Lpool-rb.O₀/2) := by
  obtain ⟨Adecay,hTailSize⟩ := actual_finite_source_tail_budget_uniform_degree Lcap δ saving hδ
  obtain ⟨degree,Cm₀,Z₀,hCm₀,hZ₀,henergy⟩ := original_low_sector_retained_budget
    (Nlevel:=Nlevel) ε hε lo hi hlo W hWs hW s hc₀ hNlevel hbase hac ρ hρ η hηpos
    κ δ Lscale Lpool hκ hδL hLpool
  obtain ⟨degreeTail,Ct₀,hCt₀,hTailProfiles⟩ := original_family_whole_tail_uniform_degree lo hi hlo Adecay W hWs hW
  refine ⟨max degree (degreeTail*2),wholeGlobalConstant Nlevel s Cm₀ Ct₀,max Z₀ 128,
    wholeGlobalConstant_pos s hCm₀.le,hZ₀.trans_le (le_max_left _ _),?_⟩
  intro σ _ J I F Q Q₀ hJ hI hQ hpower hmask A rb hXi hKcap hPcap hexp
  dsimp only
  intro hFcap hscap hpool
  let G := (poolPrimeFamily J Q Q₀).restrict A
  let j := fun b : A => completedLocalExponent J F b.val.val
  have hpair := (poolPrimeFamily J Q Q₀).restrict_pairwise (poolPrimeFamily_pairwise J Q Q₀) A
  have hz1 : 1≤rb.Z := hZ₀.le.trans ((le_max_left _ _).trans rb.scale_ge)
  have h128 : 128≤rb.Z := (le_max_right _ _).trans rb.scale_ge
  apply wholeGlobalBound_of_retained G j (fun b => Nat.mod_lt _ (by decide)) hpair s hc₀ hNlevel hbase hac
    rb.X_pos (Real.rpow_pos_of_pos (zero_lt_one.trans_le hz1) δ) rb.QK_pos rb.QP_pos
    (by positivity) (Real.rpow_le_rpow_of_exponent_le hz1 hexp)
    hCm₀.le hCt₀.le hTailProfiles
  · intro rows Pset hqk hqp hr hp
    exact hTailSize s G rows Pset rb.Z rb.X rb.QK rb.QP h128 rb.X_pos hqk (by linarith) hr hp hFcap hKcap hPcap hXi
  · simpa only [mul_assoc,LowReflectionBudget.lowerThreshold] using
      henergy J I F Q Q₀ hJ hI hQ hpower hmask A (rb.lowerThreshold (le_max_left _ _)) hscap hpool

end
end SevenEighths.InverseReflectedPhase

end OAI
