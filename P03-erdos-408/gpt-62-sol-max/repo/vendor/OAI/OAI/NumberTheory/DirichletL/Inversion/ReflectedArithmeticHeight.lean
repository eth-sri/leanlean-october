module

public import OAI.IdealNorm
public import OAI.NumberTheory.DirichletL.Reflection.PhysicalIntegral
public import OAI.NumberTheory.DirichletL.Reflection.WeightedMeasurable
public import OAI.NumberTheory.DirichletL.Reflection.DyadicTail
public import OAI.NumberTheory.DirichletL.Inversion.KernelSourceUniform

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedArithmeticHeight
open scoped Classical BigOperators ContDiff
open MeasureTheory FourierBridge InverseKernelSourceUniform CompletedDyadic ActualEisensteinCubic
open CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment InverseReflectedPhase
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe u v

theorem weighted_finite_physical_row_branch_measure_arithmetic_uniform
    (a₀ b₀ : ℝ) (ha₀ : 0<a₀) (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ)
    (hM : ∀ i, 0≤M i) (hwindows : ∀ i y, windows i y≠0 → |y|≤M i)
    (W : ℝ→ℂ) (hWsupport : Function.support W ⊆ Set.Icc a₀ b₀)
    (hW : ContDiff ℝ ∞ W) (J : ℕ) :
    ∃ (U : ℝ→ℂ) (degree : ℕ) (C₀ : ℝ), 0≤C₀ ∧ HasCompactSupport U ∧ ContDiff ℝ ∞ U ∧
      ∀ {N a c : Eis} {mode : Bool}, ∀ {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ], ∀ (F : PrimeFamily φ)
        (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
        (unit : Eisˣ) (m : ℕ) (θ X QK QP Qn Qb : ℝ),
        0<X → 0<QK → 0<QP → 0<Qn → 0<Qb →
      let R := kernelCenter (actualKernelCoefficient F s m X) QK QP Qn Qb
      (∀ (K : Ideal Eis) (hK : Admissible K) (S : Ideal Eis→PrimeFamily σ) (jF : φ→ℕ)
        (Pset nset bset : Finset (Ideal Eis))
        (D : ∀ P : Pset, IsCoprime K P.val →
          ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode),
        (∀ P ∈ Pset, (∏ i, (S P).ideal i)=P) → (∀ n ∈ nset, n≠0) → (∀ b ∈ bset, b≠0) →
        ∀ (r₀ aw₀ : Ideal Eis→ℂ) (w₀ : Ideal Eis→Ideal Eis→ℂ),
        ∀ {ι : Type*} [Fintype ι] (G0 : PrimeFamily ι)
          (D0 : ControlledStratumArithmetic G0.generator N a c mode),
        (∀ P : Pset, IsCoprime K P.val → Pairwise (Function.onFun IsCoprime (F.reflected K hK (S P.val)).ideal)) →
        (∀ P hp, (D P hp).fixedFactor=D0.fixedFactor) →
        (∀ P hp u m n b, actualCuspColumn (D P hp) s hc u m n b=actualCuspColumn D0 s hc u m n b) →
        (∀ b ∈ bset, primaryGenerator b≠0) →
        weightedFinitePhysicalKernelRow F K hK S jF Pset nset bset D s hc unit m windows QK QP Qn Qb W θ X r₀ aw₀ w₀ =
        ((Real.exp (M 2/2+M 3)/(ramifiedScale 1 completedRamifiedStep m*Real.sqrt Qn*Qb)*smallScalar R:ℝ):ℂ)*
          ∫ t : ℝ, twistedDensity U W θ R t *
            (∑ e : φ→Fin 3, weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
              (actualCuspColumn D0 s hc unit m)
              (fun K => r₀ K*kernelCoordinateWeight (reciprocalKernelWindows windows M 0) (-2) QK t (Ideal.absNorm K:ℝ))
              (fun P => aw₀ P*kernelCoordinateWeight (reciprocalKernelWindows windows M 1) (-2) QP t (Ideal.absNorm P:ℝ))
              (fun n b => w₀ n b*kernelDualWeight (reciprocalKernelWindows windows M) Qn Qb t (Ideal.absNorm n:ℝ) (Ideal.absNorm b:ℝ)) unit m Pset nset bset K)) ∧
      Integrable (twistedDensity U W θ R) ∧
      Integrable (fun t : ℝ => (1+‖t‖)^J*‖twistedDensity U W θ R t‖) ∧
      (∫ t : ℝ, (1+‖t‖)^J*‖twistedDensity U W θ R t‖) ≤ C₀*(1+‖θ‖)^degree ∧
      (∀ t : ℝ, (1+‖t‖)^J*‖twistedDensity U W θ R t‖ ≤ C₀*(1+‖θ‖)^degree) := by
  obtain ⟨U,degree,C₀,hC₀,hUc,hUs,hsep⟩ := reflected_finite_source_uniform.{0}
    a₀ b₀ ha₀ windows M hM hwindows W hWsupport hW J
  refine ⟨U,degree,C₀,hC₀,hUc,hUs,?_⟩
  intro N a c mode φ σ _ _ F s hc unit m θ X QK QP Qn Qb hX hQK hQP hQn hQb
  have hr := ramifiedScale_pos 1 completedRamifiedStep (by norm_num)
    (lt_trans zero_lt_one completedRamifiedStep_gt_one) m
  obtain ⟨he,hi,hiJ,hm,hp⟩ := hsep θ (actualKernelCoefficient F s m X) QK QP Qn Qb
    (ramifiedScale 1 completedRamifiedStep m) (actualKernelCoefficient_pos F s hc m X hX)
    hQK hQP hQn hQb hr
  refine ⟨?_,hi,hiJ,hm,hp⟩
  intro K hK S jF Pset nset bset D hprod hn hb r₀ aw₀ w₀ ι _ G0 D0 hcop hκ hA hbgen
  have hnorm (I : Ideal Eis) (hI : I≠0) : (0:ℝ)<Ideal.absNorm I := by
    exact_mod_cast Ideal.absNorm_pos_of_ne_bot hI
  let T := CoprimeSourceIndex K Pset nset bset
  have hh := he (Finset.univ : Finset T)
    (fun x => r₀ K*aw₀ x.1.val.val*w₀ x.2.1.val x.2.2.val*
      actualMixedCoefficient F K hK (S x.1.val.val) jF (D x.1.val x.1.property) s hc unit m x.2.1.val x.2.2.val)
    (fun _ => (Ideal.absNorm K : ℝ)) (fun x => (Ideal.absNorm (∏ i, (S x.1.val.val).ideal i) : ℝ))
    (fun x => (Ideal.absNorm x.2.1.val : ℝ)) (fun x => (Ideal.absNorm x.2.2.val : ℝ))
    (fun x _ => ⟨hnorm _ hK.1, hnorm _ (Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne ((S x.1.val.val).ideal i))),
      hnorm _ (hn _ x.2.1.property), hnorm _ (hb _ x.2.2.property)⟩)
  convert hh using 1
  · simp only [weightedFinitePhysicalKernelRow,actualKernelSourceTerm_numeric,mul_assoc]
    rfl
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  dsimp only [T]
  congr 1
  rw [← weightedPhysicalReflectedRow_eq_branches F K hK S jF Pset nset bset hprod D hcop
    G0 D0 s hc hκ hA hbgen _ _ _ unit m, weightedPhysicalReflectedRow_eq_coprime_source]
  apply Finset.sum_congr rfl
  intro x _
  rw [hprod x.1.val.val x.1.val.property]
  ring

theorem literal_dyadic_tail_height_arithmetic_uniform (lo hi : ℝ) (hlo : 0<lo) (A : ℕ)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W) :
    ∃ (degree : ℕ) (C : ℝ), 0<C ∧
    ∀ {N a c : Eis} {mode : Bool}, ∀ {ι : Type u} [Fintype ι], ∀ (G : PrimeFamily ι) (D : ControlledStratumArithmetic G.generator N a c mode)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0),
      (9:Eis)*c∣N → (if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1) →
      (∀ i, ringChar (Eis⧸G.ideal i)≠2) →
    ∀ (j : ι→ℕ), (∀ i, j i<6) → ∀ (S : Finset ι) (u : Eisˣ) (θ X T : ℝ), 0<X → 0<T →
    ∀ cut : (ℕ×ℕ×ℕ)→Prop,
      (∀ i, cut i → 16*T≤rawDyadicCenter (literalRawScale G s X) i) →
      ‖∑' i : ℕ×ℕ×ℕ, if cut i then
        literalDyadicBlock G D s hc j S (CompletedHeight.normTwistedSource W θ) X u i else 0‖≤
        C*(1+‖θ‖)^degree*(Ideal.absNorm (∏ i,G.ideal i):ℝ)*T^(-(A:ℝ))*(literalRawScale G s X^2)⁻¹ := by
  obtain ⟨orders,C,hC,hbound⟩ := raw_kernel_tail lo hi completedRamifiedStep hlo completedRamifiedStep_gt_one A
  let V := vstarSchwartz W lo hi hlo hWs hW
  have hV  := Vstar_support W lo hi hWs
  obtain ⟨H,hH,hpoly⟩ := CompletedHeight.normTwistedSource_schwartz V lo hi hlo hV
  obtain ⟨degree,C₁,hC₁,hsemi⟩ := hpoly orders
  have hlink (θ : ℝ) : (H θ : ℝ→ℂ)=Vstar (CompletedHeight.normTwistedSource W θ) := by
    funext x
    rw [hH θ x]
    change FourierBridge.logPhase θ (Real.log x)*((Real.sqrt x:ℂ)*W x)=
      (Real.sqrt x:ℂ)*(FourierBridge.logPhase θ (Real.log x)*W x)
    ring
  have hHs (θ : ℝ) : Function.support (H θ : ℝ→ℂ)⊆Set.Icc lo hi := by
    intro x hx
    change H θ x≠0 at hx
    rw [hH θ x] at hx
    exact hV (CompletedHeight.normTwistedSource_support V θ hx)
  refine ⟨degree,C*C₁,mul_pos hC hC₁,?_⟩
  intro N a c mode ι _ G D s hc hN hbase hchar j hj S u θ X T hX hT cut hcut
  let scale := literalRawScale G s X
  have hs := literalRawScale_pos G s hc X hX
  obtain ⟨hn,hh⟩ := hbound (H θ) (hHs θ) scale 1 (Ideal.absNorm (∏ i,G.ideal i):ℝ) T
    hs (by norm_num) (Nat.cast_nonneg _) hT (literalRawCoefficient G D s hc j S u)
    (literalRawCoefficient_norm G D s hc hN hbase hchar j hj S u)
    (fun x => cut (rawDyadicLabel x)) (fun x hx => by
      have h := (le_div_iff₀ (by norm_num : (0:ℝ)<16)).mpr (by simpa only [mul_comm] using hcut _ hx)
      exact h.trans (rawDyadicCenter_lower scale hs.le x))
  rw [tsum_cut_dyadic _ cut hn.of_norm] at hh
  simp only [rawDualKernelTerm,hlink,literalDyadicBlock,literalRawSeries,one_pow,mul_one] at hh ⊢
  refine hh.trans ?_
  have hrest : 0≤(Ideal.absNorm (∏ i,G.ideal i):ℝ)*T^(-(A:ℝ))*(scale^2)⁻¹ := by positivity
  simpa only [←mul_assoc, scale] using mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hsemi θ) hC.le) hrest

end
end SevenEighths.InverseReflectedArithmeticHeight

end OAI
