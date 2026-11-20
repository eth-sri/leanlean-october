module
public import OAI.NumberTheory.DirichletL.Reflection.SectorData
public import OAI.NumberTheory.DirichletL.Reflection.CanonicalDyads
public import OAI.NumberTheory.DirichletL.Reflection.CanonicalEnergyUniformDegree

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve CanonicalRowCompletion InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v

theorem canonical_dyadic_geometry_uniform_uniform_degree
    (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (L cstar η : ℝ)
    (hL : 0≤L) (hcstar : 0<cstar) (hη : 0<η) (hη1 : η≤1) (hηc : η≤cstar/100000) :
    ∃ (degree : ℕ), ∀ {Nlevel : Eis}, ∀
    {γ : Type*} [Fintype γ] (a c₀ : γ→Eis) (mode : γ→Bool)
    [Fintype (Eis⧸Ideal.span {Nlevel^2})]
    (s : ∀ i,FixedCuspShape (ControlledStratumArithmetic.fixedCusp (a i) (c₀ i) (mode i))) (hc₀ : ∀ i,c₀ i≠0)
    (_hNlevel : ∀ i,(9:Eis)*c₀ i∣Nlevel)
    (_hbase : ∀ i,if mode i then ConcretePrimeRowBridge.goodLambda^2∣a i-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀ i-1)
    (_hac : ∀ i,IsCoprime (a i) (c₀ i))
    (B : Ideal Eis) (_hB : B≠0),
    ∃ (C Z₀ : ℝ),0<C ∧ 1<Z₀ ∧
    ∀ g : γ,∀ {σ : Type v} [Fintype σ] [DecidableEq σ],∀ (J F R Q₀ : Ideal Eis)
      (_hJ : J≠0) (_hF : F≠0) (_hR : R≠0),
    ∀ (A : Finset (FreeReflection.pool J (B*F*R) Q₀))
      (Z N V M z₀ margin O₀ hhat d : ℝ),
      Z₀≤Z → 0≤N → 0≤M → M≤L → V≤L → z₀≤L → hhat≤L →
      (Ideal.absNorm F:ℝ)≤Z^V → (Ideal.absNorm R:ℝ)≤Z^L →
      0≤O₀ → O₀≤M → Z^O₀≤(Ideal.absNorm (rowPowerfulPart J):ℝ) →
      CanonicalMargins (N+V) M (normWidth Z R) z₀ margin → cstar/2≤margin →
      V≤d → hhat≤d+η → d≤cstar/200 →
    ∀ (parents rows : Finset (Ideal Eis)),
      (∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤Z^M) →
      rows⊆originalResidualRows parents J (B*F*R) →
      (∀ P∈fixedBadPrimes,P∣B*F*R) →
      let Hrow := Z^M/((Ideal.absNorm (rowPowerfulPart J):ℝ)*(Ideal.absNorm (rowMaskPart J (B*F*R)):ℝ))
      let Hslot := Z^z₀
      let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
      let jF := fun b : A => completedLocalExponent J F b.val.val
    ∀ (tuples : Finset (σ→Ideal Eis))
      (hmax : ∀ p∈tuples,∀ i,(p i).IsMaximal)
      (hgood : ∀ p∈tuples,∀ i,ConcretePrimeRowBridge.goodLambda∉p i)
      (_hinj : Set.InjOn slotTupleProduct (↑tuples : Set (σ→Ideal Eis)))
      (hrows : ∀ K∈rows,Admissible K),
      WithMemberPrimes Nlevel G rows (memberTupleFamily tuples hmax hgood) <|
      (∀ p∈tuples,CubicSieve.Admissible (slotTupleProduct p) ∧ (Ideal.absNorm (slotTupleProduct p):ℝ)≤Hslot) →
    ∃ D : ∀ i : Fin (columnDyadicLength Hrow+1),∀ j : Fin (columnDyadicLength Hslot+1),
      CellCompletion (N:=Nlevel) (a:=a g) (c:=c₀ g) (mode:=mode g) G rows hrows tuples hmax hgood Hrow Hslot i j,
    ∀ (θ : ℝ) (r : Ideal Eis→ℂ) (aw : (σ→Ideal Eis)→ℂ),
      (∀ K∈rows,‖r K‖≤1) → (∀ p∈tuples,‖aw p‖≤1) →
      (∑ K : rows,‖∑ p : tuples,
        dyadicPhysicalTerm G rows hrows tuples hmax hgood Hrow Hslot D (s g) (hc₀ g) jF W θ (Z^(N-3*hhat)) r aw K p‖^2)≤
        (columnDyadicLength Hrow+1:ℝ)*(columnDyadicLength Hslot+1:ℝ)^2*
          (C*(1+‖θ‖)^degree*Z^(N+V-3*cstar/16-O₀/2)) := by
  obtain ⟨degree,hu⟩ := canonical_member_geometry_uniform_uniform_degree lo hi hlo W hWs hW L cstar η hL hcstar hη hη1 hηc
  refine ⟨degree,?_⟩
  intro Nlevel γ _ a c₀ mode _ s hc₀ hNlevel hbase hac B hB
  obtain ⟨C,Z₀,hC,hZ₀,he⟩ := hu a c₀ mode s hc₀ hNlevel hbase hac B hB
  refine ⟨C,Z₀,hC,hZ₀,?_⟩
  intro g σ _ _ J F R Q₀ hJ hF hR A Z N V M z₀ margin O₀ hhat d hZ hN hM hMc hVc hzc hhc
    hFn hRn hO hOM hOn hinv hmargin hVd hhd hd parents rows hparents hsub hbad
  dsimp only
  intro tuples hmax hgood hinj hrows hGN hGchar hrowcop hpair hPN hPchar hPnorm
  let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
  let jF := fun b : A => completedLocalExponent J F b.val.val
  have hzp : 0<Z := zero_lt_one.trans ((lt_of_lt_of_le hZ₀ hZ))
  refine original_dyadic_energy_transfer (Nlevel:=Nlevel) G parents rows J (B*F*R) (Z^M) (Z^z₀)
    hparents hsub hbad tuples hmax hgood hinj hrows (s g) (hc₀ g) jF W (Z^(N-3*hhat))
    (fun θ => C*(1+‖θ‖)^degree*Z^(N+V-3*cstar/16-O₀/2))
    (by intro θ; positivity) ?_ hGN hGchar hrowcop hpair hPN hPchar hPnorm
  intro I hI0 hIn hpow hmask Urow Uslot hKlower hUrow hKupper hUslot hPupper Rc Tc hTc hm hg hti hRi
  exact he g J I F R Q₀ hJ hI0 hF hR hpow hmask A
    Z N V M z₀ margin O₀ hhat d Urow Uslot hZ hN hM hMc hVc hzc hhc hIn hFn hRn hO hOM
    (by rw [← hpow]; exact hOn) hKlower hUrow hKupper hUslot hPupper hinv hmargin hVd hhd hd Rc Tc hTc hm hg hti hRi

end
end SevenEighths.InverseReflectedPhase

end OAI
