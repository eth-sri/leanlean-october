module
public import OAI.NumberTheory.DirichletL.Reflection.CanonicalDyads
public import OAI.NumberTheory.DirichletL.Reflection.CanonicalEnergyUniformDegree
import WeylPort.Analytic.RealLaplace

public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
local notation "Eis" => ActualEisensteinCubic.O
universe v

theorem canonical_dyadic_geometry_uniform_uniform_degree
    (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (L cstar η : ℝ)
    (hL : 0≤L) (hcstar : 0< cstar) (hη : 0<η) (hη1 : η≤1) (hηc : η≤ cstar/100000) :
    ∃ (degree : ℕ), ∀ {Nlevel : Eis}, ∀
    {γ : Type*} [Fintype γ] (a c₀ : γ→ Eis) (mode : γ→ Bool)
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
      (Ideal.absNorm F:ℝ)≤Z ^V → (Ideal.absNorm R:ℝ)≤Z ^L →
      0≤O₀ → O₀≤M → Z ^O₀≤(Ideal.absNorm (rowPowerfulPart J):ℝ) →
      CanonicalMargins (N+V) M (normWidth Z R) z₀ margin → cstar/2≤ margin →
      V≤d → hhat≤d+η → d≤ cstar/200 →
    ∀ (parents rows : Finset (Ideal Eis)),
      (∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤Z ^M) →
      rows⊆originalResidualRows parents J (B*F*R) →
      (∀ P∈fixedBadPrimes,P∣B*F*R) →
      let Hrow := Z ^M/((Ideal.absNorm (rowPowerfulPart J):ℝ)*(Ideal.absNorm (rowMaskPart J (B*F*R)):ℝ))
      let Hslot := Z ^z₀
      let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
      let jF := fun b : A => completedLocalExponent J F b.val.val
    ∀ (tuples : Finset (σ→ Ideal Eis))
      (hmax : ∀ p∈tuples,∀ i,(p i).IsMaximal)
      (hgood : ∀ p∈tuples,∀ i,ConcretePrimeRowBridge.goodLambda∉p i)
      (_hinj : Set.InjOn slotTupleProduct (↑tuples : Set (σ→ Ideal Eis)))
      (hrows : ∀ K∈rows,Admissible K),
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ p : tuples,Pairwise (Function.onFun IsCoprime (G.sum (memberTupleFamily tuples hmax hgood p)).ideal)) →
      (∀ p : tuples,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (memberTupleFamily tuples hmax hgood p)).ideal b)) →
      (∀ p : tuples,∀ b,ringChar (Eis⧸(G.sum (memberTupleFamily tuples hmax hgood p)).ideal b)≠2) →
      (∀ p∈tuples,CubicSieve.Admissible (slotTupleProduct p) ∧ (Ideal.absNorm (slotTupleProduct p):ℝ)≤Hslot) →
    ∃ D : ∀ i : Fin (columnDyadicLength Hrow+1),∀ j : Fin (columnDyadicLength Hslot+1),
      CellCompletion (N:=Nlevel) (a:=a g) (c:=c₀ g) (mode:=mode g) G rows hrows tuples hmax hgood Hrow Hslot i j,
    ∀ (θ : ℝ) (r : Ideal Eis→ℂ) (aw : (σ→ Ideal Eis)→ℂ),
      (∀ K∈rows,‖r K‖≤1) → (∀ p∈tuples,‖aw p‖≤1) →
      (∑ K : rows,‖∑ p : tuples,
        dyadicPhysicalTerm G rows hrows tuples hmax hgood Hrow Hslot D (s g) (hc₀ g) jF W θ (Z ^(N-3*hhat)) r aw K p‖^2)≤
        (columnDyadicLength Hrow+1:ℝ)*(columnDyadicLength Hslot+1:ℝ)^2*
          (C*(1+‖θ‖)^degree*Z ^(N+V-3*cstar/16-O₀/2)) := by
  obtain ⟨degree,hu⟩ := canonical_member_geometry_uniform_uniform_degree lo hi hlo W hWs hW L cstar η hL hcstar hη hη1 hηc
  pm_3287
  intro tuples hmax hgood hinj hrows hGN hGchar hrowcop hpair hPN hPchar hPnorm
  let Hrow := Z ^M/((Ideal.absNorm (rowPowerfulPart J):ℝ)*(Ideal.absNorm (rowMaskPart J (B*F*R)):ℝ))
  let Hslot := Z ^z₀
  pm_3298
  pm_8620 jF b b.val.val
  pm_148 hz hZ₀ hZ hzp
  have hrowNorm : ∀ K∈rows,1≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤Hrow :=
    fun K hK => original_residual_norm_bounds parents J (B*F*R) hbad (Z ^M) hparents K (hsub hK)
  pm_311
  apply physical_dyad_selection_energy G rows hrows tuples hmax hgood Hrow Hslot
    (s g) (hc₀ g) jF W (Z ^(N-3*hhat)) (fun θ => C*(1+‖θ‖)^degree*Z ^(N+V-3*cstar/16-O₀/2))
    (fun θ => by positivity)
  pm_189
  have hti : Set.InjOn slotTupleProduct (↑Tc : Set (σ→ Ideal Eis)) :=
    hinj.mono (activeTupleDyad_subset tuples Hslot j)
  pm_222
  have hKlower : (2*divisorDyadicScale i.val)/2≤(Ideal.absNorm (rowResidualPart I (B*F*R)):ℝ) := by
    pm_6965
  have hKupper : 2*divisorDyadicScale i.val≤2*Z ^M := by
    have hres : (Ideal.absNorm (rowResidualPart I (B*F*R)):ℝ)≤(Ideal.absNorm I:ℝ) := by
      rw [rowResidualPart_norm I (B*F*R) hI0]
      apply div_le_self (Nat.cast_nonneg _)
      exact one_le_mul_of_one_le_of_one_le
        (QuadraticMainBoundary.norm_one_le (rowPowerfulPart_ne_zero I))
        (QuadraticMainBoundary.norm_one_le (squarefreeMaskPart_ne_zero (rowSimplePart I) (B*F*R)))
    have hs := hKlower.trans (hres.trans hIn)
    linarith
  have hPupper : (2*divisorDyadicScale j.val)/2≤Z ^z₀ := by
    convert activeTupleDyad_scale_le tuples Hslot htupleNorm j hj using 1 ; dsimp [Hslot] ; ring
  let S := tuplePrimeFamily Tc hTc hm hg
  have hScop : ∀ P∈Tc.image slotTupleProduct,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal) := by
    pm_535 hpair
  have hSN : ∀ P∈Tc.image slotTupleProduct,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b) := by
    pm_535 hPN
  have hSchar : ∀ P∈Tc.image slotTupleProduct,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2 := by
    pm_535 hPchar
  obtain ⟨D,hD⟩ := he g J I F R Q₀ hJ hI0 hF hR hpow.symm hmask.symm A
    Z N V M z₀ margin O₀ hhat d (2*divisorDyadicScale i.val) (2*divisorDyadicScale j.val)
    hZ hN hM hMc hVc hzc hhc hIn hFn hRn hO hOM (by rw [hpow];exact hOn) hKlower
    (by linarith [divisorDyadicScale_ge_one i.val]) hKupper
    (by linarith [divisorDyadicScale_ge_one j.val]) hPupper hinv hmargin hVd hhd hd
    Rc Tc hTc hm hg hti hRi hGN hGchar
    (fun K hK => hrowcop K (divisorDyadicBin_subset rows Hrow i hK))
    (tuplePrimeFamily_product Tc hTc hm hg) hScop hSN hSchar
  pm_217
  have hb := hD θ r aw (by linarith [divisorDyadicScale_ge_one i.val])
    (by linarith [divisorDyadicScale_ge_one j.val])
    (fun K hK => by convert hKr K hK using 1 ; ring_nf)
    (by
      pm_67 P hP p hp Finset.mem_image.mp
      pm_6476
      convert hPr p hp using 1 ; ring_nf)
    (fun K hK => hr K (divisorDyadicBin_subset rows Hrow i hK))
    (fun p hp => haw p (activeTupleDyad_subset tuples Hslot j hp))
  exact hb
end SevenEighths.InverseReflectedPhase

end OAI
