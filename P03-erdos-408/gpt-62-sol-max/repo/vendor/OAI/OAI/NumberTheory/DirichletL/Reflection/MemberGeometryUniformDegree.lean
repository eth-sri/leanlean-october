module

public import OAI.NumberTheory.DirichletL.Reflection.MemberEnergySpec
public import OAI.FiniteMajorant
public import OAI.NumberTheory.DirichletL.Reflection.OriginalBranchSum
public import OAI.NumberTheory.DirichletL.Reflection.LiteralNormalized
public import OAI.NumberTheory.DirichletL.Reflection.InactiveEnergy
public import OAI.NumberTheory.DirichletL.Reflection.CountBudget
public import OAI.NumberTheory.DirichletL.Reflection.FullEnergyBasic
public import OAI.NumberTheory.DirichletL.Reflection.ActualSizeCaps
public import OAI.NumberTheory.DirichletL.Reflection.GlobalEnergy
public import OAI.NumberTheory.DirichletL.Reflection.TupleMembers
public import OAI.NumberTheory.DirichletL.Reflection.SectorData
public import OAI.NumberTheory.DirichletL.Reflection.WholeGlobalBound
public import OAI.NumberTheory.DirichletL.Reflection.RetainedBudgetUniformDegree
public import OAI.NumberTheory.DirichletL.Reflection.WholeTail

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section

local notation "Eis" => ActualEisensteinCubic.O
universe v

set_option maxHeartbeats 650000 in
theorem original_member_geometry_uniform_uniform_degree
    (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (ρ : ℝ) (hρ : 0<ρ) (η : ℝ) (hηpos : 0<η)
    (κ δ Lscale Lpool : ℝ) (hκ : 0<κ) (hδL : 0≤δ+Lscale) (hLpool : 0≤Lpool)
    (Lcap saving : ℝ) (hδ : 0<δ) :
    ∃ (degree : ℕ), ∀ {Nlevel : Eis}, ∀
    {γ : Type*} [Fintype γ] (a c₀ : γ→Eis) (mode : γ→Bool)
    [Fintype (Eis⧸Ideal.span {Nlevel^2})]
    (s : ∀ i,FixedCuspShape (ControlledStratumArithmetic.fixedCusp (a i) (c₀ i) (mode i))) (hc₀ : ∀ i,c₀ i≠0)
    (_hNlevel : ∀ i,(9:Eis)*c₀ i∣Nlevel)
    (_hbase : ∀ i,if mode i then ConcretePrimeRowBridge.goodLambda^2∣a i-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀ i-1)
    (_hac : ∀ i,IsCoprime (a i) (c₀ i)),
    ∃ (C Z₀ : ℝ), 0<C ∧ 1<Z₀ ∧
    ∀ i : γ,
      let a := a i
      let c₀ := c₀ i
      let mode := mode i
      let s := s i
      let hc₀ := hc₀ i
    ∀ {σ : Type v} [Fintype σ] [DecidableEq σ], ∀ (J I F B R Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hF : F≠0) (_hB : B≠0) (_hR : R≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J (B*F*R)=rowMaskPart I (B*F*R) →
    ∀ (A : Finset (FreeReflection.pool J (B*F*R) Q₀))
      (rb : CappedReflectionBudget I F B R Z₀ η ε δ Lscale Lcap saving),
      let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤rb.Z^Lcap →
      (familyRawScale G s rb.X rb.QK rb.QP)⁻¹≤rb.Z^Lscale →
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤rb.Z^Lpool → κ+ρ*Lpool≤rb.cstar/16 →
    ∀ (rows : Finset (Ideal Eis)) (tuples : Finset (σ→Ideal Eis)) (hne : tuples.Nonempty)
      (hmax : ∀ p∈tuples,∀ i,(p i).IsMaximal)
      (hgood : ∀ p∈tuples,∀ i,ConcretePrimeRowBridge.goodLambda∉p i)
      (hinj : Set.InjOn slotTupleProduct (↑tuples : Set (σ→Ideal Eis))),
      ∀ (hrows : ∀ K∈rows,Admissible K),
      MemberTupleEnergy (N:=Nlevel) G rows hrows tuples hne hmax hgood hinj s hc₀ j W
        rb.X rb.QK rb.QP (fun θ => C*(1+‖θ‖)^degree*rb.Z^(rb.F₀-3*rb.cstar/16-rb.O₀/2)) := by
  obtain ⟨Adecay,hTailSize⟩ := actual_finite_source_tail_budget_uniform_degree Lcap δ saving hδ
  obtain ⟨degree,hu⟩ := original_sector_retained_budget_uniform_degree
    ε hε lo hi hlo W hWs hW ρ hρ η hηpos κ δ Lscale Lpool hκ hδL hLpool
  obtain ⟨degreeTail,Ct₀,hCt₀,hTailProfiles⟩ := original_family_whole_tail_uniform_degree lo hi hlo Adecay W hWs hW
  refine ⟨max degree (degreeTail*2),?_⟩
  intro Nlevel γ _ a c₀ mode _ s hc₀ hNlevel hbase hac
  choose Cm Zmin hCm hZmin henergy using
    fun i => hu (Nlevel:=Nlevel) (a:=a i) (c₀:=c₀ i) (mode:=mode i)
      (s i) (hc₀ i) (hNlevel i) (hbase i) (hac i)
  obtain ⟨C,hC,hCoefficient⟩ := exists_real_majorant 0 (fun i => wholeGlobalConstant Nlevel (s i) (Cm i) Ct₀)
  obtain ⟨Z₀,hZ₀,hThreshold⟩ := exists_real_majorant 1 (fun i => max (Zmin i) 128)
  refine ⟨C,Z₀,hC,hZ₀,?_⟩
  intro i
  dsimp only
  intro σ _ _ J I F B R Q₀ hJ hI hF hB hR hpower hmask A rb
    hFcap hscap hpool hsmall rows tuples hne hmax hgood hinj hrows hGN hGchar hrowcop hprod hScop hSN hSchar
  let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
  let j := fun b : A => completedLocalExponent J F b.val.val
  have hpair := (poolPrimeFamily J (B*F*R) Q₀).restrict_pairwise (poolPrimeFamily_pairwise J (B*F*R) Q₀) A
  have h128 := (le_max_right (Zmin i) (128:ℝ)).trans ((hThreshold i).trans rb.scale_ge)
  have hZi := (le_max_left (Zmin i) (128:ℝ)).trans (hThreshold i)
  have hz1 := hZ₀.le.trans rb.scale_ge
  have hzp := zero_lt_one.trans_le hz1
  have hh := wholeGlobalBound_of_retained (σ:=σ) G j (fun b => Nat.mod_lt _ (by decide)) hpair
    (s i) (hc₀ i) (hNlevel i) (hbase i) (hac i) rb.X_pos (Real.rpow_pos_of_pos hzp δ) rb.QK_pos rb.QP_pos
    (Real.rpow_nonneg hzp.le _) (Real.rpow_le_rpow_of_exponent_le hz1 rb.target_lower)
    (hCm i).le hCt₀.le hTailProfiles
    (fun rows Pset hqk hqp hr hp => hTailSize (s i) G rows Pset rb.Z rb.X rb.QK rb.QP
      h128 rb.X_pos hqk (by linarith) hr hp hFcap rb.row_scale_cap rb.slot_scale_cap rb.source_cap)
    (by simpa only [mul_assoc,OriginalReflectionBudget.lowerThreshold] using
      henergy i J I F B R Q₀ hJ hI hF hB hR hpower hmask A (rb.toOriginalReflectionBudget.lowerThreshold hZi) hscap hpool hsmall)
  obtain ⟨D,hD⟩ := hh rows (tuples.image slotTupleProduct) (tuplePrimeFamily tuples hne hmax hgood)
    hrows hGN hGchar hrowcop hprod hScop hSN hSchar
  refine ⟨D,?_⟩
  intro θ r aw hqk hqp hKr hPr hr haw
  have he := hD θ r (slotProductCoefficient tuples aw) hqk hqp hKr hPr hr
    (fun P hP => slotProductCoefficient_norm tuples hinj aw haw P hP)
  refine (le_of_eq ?_).trans (he.trans ?_)
  · refine Finset.sum_congr rfl (fun K _ => ?_)
    congr 2
    exact (literalWholeRow_eq_member_tuples tuples hmax hgood G K.val (hrows K.val K.property)
      hne hinj (D K) (s i) (hc₀ i) j W θ rb.X r aw).symm
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hCoefficient i) (by positivity)) (Real.rpow_nonneg hzp.le _)

end
end SevenEighths.InverseReflectedPhase

end OAI
