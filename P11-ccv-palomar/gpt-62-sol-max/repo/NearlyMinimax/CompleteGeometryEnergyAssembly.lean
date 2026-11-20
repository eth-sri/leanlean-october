module

public import NearlyMinimax.HigherGeometryEnergyAssembly
public import NearlyMinimax.CompleteGeometryExteriorEnergy


@[expose] public section

/-! Finite full-count energy assembly for the genuine spatial envelope.
The canonical statistical construction supplies the higher block from its
actual cardinal, ordinary alias, pair alias and field integrals. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def completeGeometryDefectConstant (d q : ℕ) (B C a rho Cs : ℝ) : ℝ :=
  1+|completeGeometryRadialConstant d B a rho Cs|+
    4*|cardinalGeometryFactorialConstant d q B C a rho Cs|

def completeGeometryFieldConstant (d q : ℕ) (aD bD C a rho c0 Cs : ℝ) : ℝ :=
  1+4*|finePairFieldFactorialConstant d q aD bD C a rho c0 (3*Cs)|

def completeGeometryAliasConstant (d q : ℕ) (aD bD C a rho c0 K Cs Cord : ℝ) : ℝ :=
  1+4*|Cord|+4*|finePairSaddleAliasFactorialConstant d q aD bD C a rho c0 K (3*Cs)|

section
variable (d q : ℕ)

theorem completeGeometryDefectConstant_pos (B C a rho Cs : ℝ) :
    0 < completeGeometryDefectConstant d q B C a rho Cs := by
  unfold completeGeometryDefectConstant
  positivity

theorem completeGeometryFieldConstant_pos (aD bD C a rho c0 Cs : ℝ) :
    0 < completeGeometryFieldConstant d q aD bD C a rho c0 Cs := by
  unfold completeGeometryFieldConstant
  positivity

theorem completeGeometryAliasConstant_pos (aD bD C a rho c0 K Cs Cord : ℝ) :
    0 < completeGeometryAliasConstant d q aD bD C a rho c0 K Cs Cord := by
  unfold completeGeometryAliasConstant
  positivity

end

theorem four_component_raw_energy_algebra {mu Pdef Pal Plo A2 Ad Ao Ap Af : ℝ}
    (hmu : 0 ≤ mu) (hPd : 0 ≤ Pdef) (hPal : 0 ≤ Pal)
    (hPloPal : Plo ≤ Pal) (hAo : 0 ≤ Ao) (hAp : 0 ≤ Ap) (M : ℕ) :
    A2*Pdef+4*(Ad*Pdef+Ao*Pal*poissonCountWeight (Ao*mu) (M+1)+
      Ap*Plo*poissonCountWeight (Ap*mu) (M+1)+Af*Pdef) ≤
      3*((1+|A2|+4*|Ad|)+(1+4*|Af|))*Pdef+
      3*(1+4*|Ao|+4*|Ap|)*Pal*poissonCountWeight ((1+4*|Ao|+4*|Ap|)*mu) (M+1) := by
  let C6 := 1+4*|Ao|+4*|Ap|
  have hC6 : 0 ≤ C6 := by positivity
  have hAoC : Ao ≤ C6 := by
    grind
  have hApC : Ap ≤ C6 := by
    grind
  have hoW := poissonCountWeight_mono (mul_nonneg hAo hmu)
    (mul_le_mul_of_nonneg_right hAoC hmu) (M+1)
  have hpW := poissonCountWeight_mono (mul_nonneg hAp hmu)
    (mul_le_mul_of_nonneg_right hApC hmu) (M+1)
  have ho := mul_le_mul_of_nonneg_left hoW (mul_nonneg hAo hPal)
  have hpP := mul_le_mul_of_nonneg_left hPloPal hAp
  have hp := mul_le_mul hpP hpW (poissonCountWeight_nonneg (mul_nonneg hAp hmu) _)
    (mul_nonneg hAp hPal)
  have hcoef : 4*(Ao+Ap) ≤ 3*C6 := by
    grind
  have hAli := mul_le_mul_of_nonneg_right hcoef
    (mul_nonneg hPal (poissonCountWeight_nonneg (mul_nonneg hC6 hmu) (M+1)))
  have hDef : A2+4*Ad+4*Af ≤ 3*((1+|A2|+4*|Ad|)+(1+4*|Af|)) := by
    linarith only [le_abs_self A2,le_abs_self Ad,le_abs_self Af,
      abs_nonneg A2,abs_nonneg Ad,abs_nonneg Af]
  have hd := mul_le_mul_of_nonneg_right hDef hPd
  grind

section
variable {d : ℕ}

theorem SourceGeometry.envelope_refined_integral (S : SourceGeometry d)
    (Chi Bl : ℝ) (j : ℕ) (hj : 3+j ≤ S.D) :
    (∫ U, S.envelope Chi Bl (3+j) U ∂fullSpatialPatchDesign d (3+j)) =
      ∫ U, S.higherEnvelope U ∂fullSpatialPatchDesign d (3+j) := by
  rw [Nat.add_comm 3 j] at hj ⊢
  simp [envelope, hj]

theorem SourceGeometry.envelope_factorial_from_higher (S : SourceGeometry d) (hd : 0 < d)
    (n : ℕ) (hD : 3 ≤ S.D) (K Chi Bl Cs Cord tau : ℝ)
    (hN : 0 < S.N) (hCs : 0 ≤ Cs) (hmu : 0 ≤ S.mu) (hmu1 : S.mu ≤ 1)
    (hbd : 0 ≤ S.bd) (hbdB : S.bd ≤ S.bD)
    (hCord : 0 ≤ Cord)
    (hCal : 0 ≤ finePairSaddleAliasFactorialConstant d S.q S.aD S.bD S.C S.a S.rho S.c0 K (3*Cs))
    (htau : 0 ≤ tau)
    (hhigher : (∑ j ∈ Finset.range (S.D-2), poissonCountWeight (Cs*S.mu) (3+j) *
      ∫ U, S.higherEnvelope U ∂fullSpatialPatchDesign d (3+j)) ≤
      4*(cardinalGeometryFactorialConstant d S.q S.bD S.C S.a S.rho Cs*S.eta^4*S.N^(-(d : ℝ))*S.mu^2 +
        Cord*(S.eta^4*Real.exp (2*tau*S.M)*S.N^(4-(d : ℝ)))*poissonCountWeight (Cord*S.mu) (S.M+1) +
        finePairSaddleAliasFactorialConstant d S.q S.aD S.bD S.C S.a S.rho S.c0 K (3*Cs) *
          (S.eta^4*S.N^(4-(d : ℝ))) *
          poissonCountWeight (finePairSaddleAliasFactorialConstant d S.q S.aD S.bD S.C S.a S.rho S.c0 K (3*Cs)*S.mu) (S.M+1) +
        finePairFieldFactorialConstant d S.q S.aD S.bD S.C S.a S.rho S.c0 (3*Cs)*S.eta^4*S.mu^2*S.N^(-(d : ℝ)))) :
    (∑ r ∈ Finset.range (n+1), poissonCountWeight (Cs*S.mu) r *
      ∫ U, S.envelope Chi Bl r U
        ∂fullSpatialPatchDesign d r) ≤
      3*(completeGeometryDefectConstant d S.q S.bD S.C S.a S.rho Cs+
        completeGeometryFieldConstant d S.q S.aD S.bD S.C S.a S.rho S.c0 Cs)*S.eta^4*S.mu^2*S.N^(-(d : ℝ)) +
      3*completeGeometryAliasConstant d S.q S.aD S.bD S.C S.a S.rho S.c0 K Cs Cord*S.eta^4*
        (Real.exp (2*tau*S.M)*S.N^(4-(d : ℝ)))*
          poissonCountWeight (completeGeometryAliasConstant d S.q S.aD S.bD S.C S.a S.rho S.c0 K Cs Cord*S.mu) (S.M+1) +
      Real.exp (completeGeometryExteriorConstant d Cs Chi)*S.eta^4*(Bl+1)^2*
        poissonCountWeight (completeGeometryExteriorConstant d Cs Chi*S.mu) (S.D+1) := by
  let e := fun r => ∫ U, S.envelope Chi Bl r U
    ∂fullSpatialPatchDesign d r
  have he (r : ℕ) : 0 ≤ e r := integral_nonneg (S.envelope_nonneg Chi Bl r)
  have he0 : e 0=0 := by simp [e, envelope]
  have he1 : e 1=0 := by simp [e, envelope]
  have hp := S.envelope_pair_factorial_le Chi Bl Cs S.bD hd hN hCs hmu hbd hbdB
  have ht := S.envelope_exterior_factorial_le (n+1) (by omega) Chi Bl Cs hCs hmu hmu1
  have href : (∑ j ∈ Finset.range (S.D-2), poissonCountWeight (Cs*S.mu) (3+j)*e (3+j)) =
      ∑ j ∈ Finset.range (S.D-2), poissonCountWeight (Cs*S.mu) (3+j)*
        ∫ U, S.higherEnvelope U ∂fullSpatialPatchDesign d (3+j) := by
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [e]
    rw [S.envelope_refined_integral Chi Bl j (by grind)]
  have hblocks := finite_count_energy_from_blocks (mul_nonneg hCs hmu) n S.D (by omega)
    e he he0 he1 _ _ _ hp (href.le.trans hhigher) ht
  have hPloPal : S.eta^4*S.N^(4-(d : ℝ)) ≤ S.eta^4*Real.exp (2*tau*S.M)*S.N^(4-(d : ℝ)) := by
    have heone : 1 ≤ Real.exp (2*tau*S.M) := Real.one_le_exp (by positivity)
    have h := mul_le_mul_of_nonneg_left heone (by positivity : 0 ≤ S.eta^4*S.N^(4-(d : ℝ)))
    convert h using 1 <;> ring
  have ha := four_component_raw_energy_algebra hmu
    (by positivity : 0 ≤ S.eta^4*S.mu^2*S.N^(-(d : ℝ)))
    (by positivity : 0 ≤ S.eta^4*Real.exp (2*tau*S.M)*S.N^(4-(d : ℝ))) hPloPal hCord hCal S.M
    (A2 := completeGeometryRadialConstant d S.bD S.a S.rho Cs)
    (Ad := cardinalGeometryFactorialConstant d S.q S.bD S.C S.a S.rho Cs)
    (Af := finePairFieldFactorialConstant d S.q S.aD S.bD S.C S.a S.rho S.c0 (3*Cs))
  apply hblocks.trans
  have h := add_le_add_right ha
    (Real.exp (completeGeometryExteriorConstant d Cs Chi)*S.eta^4*(Bl+1)^2*
      poissonCountWeight (completeGeometryExteriorConstant d Cs Chi*S.mu) (S.D+1))
  convert h using 1 <;> (try dsimp [e,completeGeometryDefectConstant,completeGeometryFieldConstant,completeGeometryAliasConstant]) <;> ring

end

end NearlyMinimax
