module

public import OAI.NumberTheory.DirichletL.Energy.ReferenceScalarReserve

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyStageReserveBounded
open CenteredMomentEnergyState CenteredMomentNaturalRowSource CenteredMomentEnergyReferenceScalarReserve

theorem exists_bounded_separated_reference_reserve (rho ε Mcap Bmask bΦ:ℝ)
    (hrho:0<rho)(hε:0<ε)(hM:0≤Mcap)(hB:0≤Bmask):
    ∃d xi saving L C:ℝ,0<d ∧ 0<xi ∧ 0<saving ∧ 0<C ∧
      xi≤rho/100 ∧ Mcap+Bmask+xi≤L ∧ L≤Mcap+Bmask+rho/100 ∧
      ∀e:ℝ,0≤e → ∀Z:ℝ,1≤Z → ∀s:NaturalState Z Bmask bΦ,s.width≤Mcap →
      ∀(α:Type*)[Fintype α](w:α→ℝ),(∑i,w i)≤Mcap →
      (s.puncture.radical.absNorm:ℝ)^d*(
        Z^(s.width+e)+
        (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*
          (1+2*(L*Real.log Z))*Z^(s.width+e)+
        (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
          max 1 s.radial.scale*Z^(s.width/4)*(∏i,Z^(w i)))≤
        C*Z^(s.width+e+ε) :=by
  let d:=ε/(4*(Bmask+Mcap+2))
  let xi:=rho/100
  let saving:=2*Mcap+Bmask*d+2*Mcap*d+1
  let L:=Mcap+Bmask+xi
  have hd:0<d:=by positivity
  have hxi:0<xi:=by positivity
  have hsave:0<saving:=by dsimp only [saving];positivity
  have hL:0≤L:=by positivity
  have hmain:d*(Bmask+Mcap+2)≤ε:=by
    dsimp only [d]
    field_simp
    nlinarith
  have herror:Bmask*d+Mcap*(2*d)-2*saving+5*Mcap/4≤ε:=by
    dsimp only [saving]
    nlinarith [mul_nonneg hB hd.le,mul_nonneg hM hd.le]
  obtain ⟨C,hC,hledger⟩:=ledger_bound Mcap Bmask bΦ L d saving ε hM hL hd hmain herror
  refine ⟨d,xi,saving,L,C,hd,hxi,hsave,hC,le_rfl,le_rfl,le_rfl,?_⟩
  intro e he Z hZ s hwidth α _ w hw
  have hz:=zero_lt_one.trans_le hZ
  have hze:=Real.one_le_rpow hZ he
  have hp:Z^(s.width+e)≤Z^e*Z^(s.width+d):=by
    rw [←Real.rpow_add hz]
    exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  let A:ℝ:=(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*(1+2*(L*Real.log Z))
  let B:ℝ:=(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
          max 1 s.radial.scale*Z^(s.width/4)*(∏i,Z^(w i))
  have hlog:=Real.log_nonneg hZ
  have hA:0≤A:=by dsimp [A];positivity
  have hB0:0≤B:=by positivity
  have hb:B≤Z^e*B:=by nlinarith
  have hh:=add_le_add (add_le_add hp (mul_le_mul_of_nonneg_left hp hA)) hb
  calc
    _≤Z^e*((s.puncture.radical.absNorm:ℝ)^d*(Z^(s.width+d)+A*Z^(s.width+d)+B)):=by
      convert mul_le_mul_of_nonneg_left hh (by positivity : 0≤(s.puncture.radical.absNorm:ℝ)^d) using 1 <;> ring
    _≤Z^e*(C*Z^(s.width+ε)):=mul_le_mul_of_nonneg_left (hledger Z hZ s hwidth α w hw) (by positivity)
    _=C*Z^(s.width+e+ε):=by
      rw [mul_left_comm,←Real.rpow_add hz]
      congr 2 <;> ring

end SevenEighths.CenteredMomentEnergyStageReserveBounded

end

end OAI
