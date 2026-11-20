module

public import OAI.NumberTheory.DirichletL.Reflection.WholeTail
public import OAI.NumberTheory.DirichletL.Reflection.InactiveEnergy
public import OAI.NumberTheory.DirichletL.Reflection.SectorData

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic
open CanonicalQuadraticSieve InverseMoment
local notation "Eis" => ActualEisensteinCubic.O
noncomputable section

lemma norm_sq_le_retained (f g : ℂ) (E : ℝ) (hf : ‖f-g‖≤E) :
    ‖f‖^2≤2*‖g‖^2+2*E^2 := by
  have hh : ‖f‖≤‖g‖+E := by
    calc
      _ = ‖g+(f-g)‖ := by congr 1;ring
      _ ≤ ‖g‖+‖f-g‖ := norm_add_le _ _
      _ ≤ _ := add_le_add_right hf _
  have hsq := pow_le_pow_left₀ (norm_nonneg f) hh 2
  nlinarith [sq_nonneg (‖g‖-E)]

lemma row_energy_le_retained {α : Type*} (rows : Finset α) (f g : α→ℂ) (E : ℝ)
    (hE : 0≤E) (hf : ∀ k∈rows,‖f k-g k‖≤E) :
    (∑ k∈rows,‖f k‖^2)≤2*(∑ k∈rows,‖g k‖^2)+2*rows.card*E^2 := by
  calc
    _ ≤ ∑ k∈rows, (2*‖g k‖^2+2*E^2) := Finset.sum_le_sum (fun k hk => norm_sq_le_retained (f k) (g k) E (hf k hk))
    _ = _ := by simp only [Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_const,nsmul_eq_mul];ring

universe u v

/-- Insert the row and slot shape phases in the weights, and combine the
retained-row energy with a uniform estimate for the omitted dyads. -/
lemma whole_sector_energy_of_retained {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ]
    {N a c₀ : Eis} {mode : Bool}
    {G : PrimeFamily φ} {rows Pset : Finset (Ideal Eis)} {S : Ideal Eis → PrimeFamily σ}
    {hrows : ∀ K ∈ rows, Admissible K}
    {s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)} {hc₀ : c₀ ≠ 0}
    (E : SectorArithmetic (N:=N) G rows Pset S hrows s hc₀)
    (hN : (9:Eis)*c₀ ∣ N)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀-1)
    (hGchar : ∀ f, ringChar (Eis ⧸ G.ideal f) ≠ 2)
    (hSchar : ∀ P ∈ Pset, ∀ b, ringChar (Eis ⧸ (G.sum (S P)).ideal b) ≠ 2)
    (hprod : ∀ P ∈ Pset, (∏ b, (S P).ideal b) = P)
    {j : φ → ℕ} (hj : ∀ b, j b < 6)
    {W : ℝ → ℂ} {Adecay degreeTail : ℕ} {Ct : ℝ}
    (htail : WholeRowTailBound.{u,v} W Adecay degreeTail Ct) (hCt : 0 ≤ Ct)
    {θ X T QK QP : ℝ} (hX : 0 < X) (hT : 0 < T) (hQK : 0 < QK) (hQP : 0 < QP)
    (hKr : ∀ K ∈ rows, (Ideal.absNorm K:ℝ) ≤ QK)
    (hPr : ∀ P ∈ Pset, CubicSieve.Admissible P ∧ (Ideal.absNorm P:ℝ) ≤ QP)
    (r aw : Ideal Eis → ℂ) (hr : ∀ K ∈ rows, ‖r K‖ ≤ 1) (haw : ∀ P ∈ Pset, ‖aw P‖ ≤ 1)
    {Cm U : ℝ} (hU : 0 ≤ U)
    (hmain : ∀ (r aw : Ideal Eis → ℂ), (∀ K ∈ rows, ‖r K‖ ≤ 1) →
      (∀ P ∈ Pset, ‖aw P‖ ≤ 1) →
      (∑ K : rows, ‖∑' u : Eisˣ, ∑ i ∈ retainedDyads (familyRawScale G s X QK QP) (16*T),
        literalDyadicRow G K.val (hrows K.val K.property) S j Pset (E.completion K) s hc₀
          u i W θ X r aw‖^2) ≤ Cm * U) :
    let Cshape := ‖fixedRadialCoefficientScalar‖*‖s.stratumShapeFactor c₀‖
    let Et := (Pset.card:ℝ)*(6*Cshape*Ct+1)*(1+‖θ‖)^degreeTail*
      ((Ideal.absNorm (∏ b,G.ideal b):ℝ)*QK*QP)*T^(-(Adecay:ℝ))*(familyRawScale G s X QK QP^2)⁻¹
    (∑ K : rows, ‖literalWholeRow G K.val (hrows K.val K.property) S j Pset
      (E.completion K) s hc₀ W θ X r aw‖^2) ≤ (2*Cshape^2*Cm+1)*U + 2*rows.card*Et^2 := by
  dsimp only
  let Cshape := ‖fixedRadialCoefficientScalar‖*‖s.stratumShapeFactor c₀‖
  let rr := fun K => r K*shapeArgument (primaryGenerator K)
  let aa := fun P => aw P*shapeArgument (primaryGenerator P)
  let Φ := fixedRadialCoefficientScalar*s.stratumShapeFactor (c₀*primaryGenerator (∏ b,G.ideal b))
  let g := fun K : rows => ∑' u : Eisˣ, ∑ i ∈ retainedDyads (familyRawScale G s X QK QP) (16*T),
    literalDyadicRow G K.val (hrows K.val K.property) S j Pset (E.completion K) s hc₀ u i W θ X rr aa
  let f := fun K : rows =>
    literalWholeRow G K.val (hrows K.val K.property) S j Pset (E.completion K) s hc₀ W θ X r aw
  let V := (1+‖θ‖)^degreeTail*((Ideal.absNorm (∏ b,G.ideal b):ℝ)*QK*QP)*
    T^(-(Adecay:ℝ))*(familyRawScale G s X QK QP^2)⁻¹
  let Et := (Pset.card:ℝ)*(6*Cshape*Ct+1)*V
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hΦ : ‖Φ‖=Cshape := by
    dsimp only [Φ,Cshape]
    rw [norm_mul, stratumShapeFactor_frozen_norm]
  have hret : (∑ K, ‖g K‖^2) ≤ Cm * U :=
    hmain rr aa
      (fun K hK => by simpa only [rr,row_shape_weight_norm r K (hrows K hK)] using hr K hK)
      (fun P hP => by simpa only [aa,slot_shape_weight_norm aw P (hPr P hP).1] using haw P hP)
  have hrem (K : rows) : ‖f K-Φ*g K‖≤Et := by
    have hodd : ∀ P∈Pset,∀ b,ringChar (Eis⧸(G.reflected K.val (hrows K.val K.property) (S P)).ideal b)≠2 := by
      intro P hP b
      rcases b with b | b | b
      · exact hGchar b
      · exact ((hrows K.val K.property).2.2 b.val (Multiset.mem_toFinset.mp b.property)).2
      · exact hSchar P hP (Sum.inr b)
    have hh := htail G K.val (hrows K.val K.property) S j Pset (E.completion K) s hc₀ hN hbase
      hodd hj hprod (fun P hP => (hPr P hP).1) θ X T QK QP r aw hX hT hQK hQP
      (hKr K.val K.property) (fun P hP => (hPr P hP).2) (hr K.val K.property) haw
    refine hh.trans ?_
    change _ ≤ Et
    calc
      _ = Pset.card * (6*Cshape*Ct) * V := by dsimp only [Cshape,V]; ring
      _ ≤ Et := by dsimp only [Et]; gcongr; linarith only
  have hh := row_energy_le_retained (Finset.univ : Finset rows) f (fun K => Φ*g K) Et
    (by dsimp [Et,Cshape]; positivity) (fun K _ => hrem K)
  simp only [norm_mul,mul_pow,hΦ,←Finset.mul_sum,Finset.card_univ,Fintype.card_coe] at hh
  refine hh.trans ?_
  calc
    _ ≤ 2*(Cshape^2*(Cm*U)) + 2*rows.card*Et^2 := by gcongr
    _ ≤ _ := by
      have he : Et = (Pset.card:ℝ)*(6*Cshape*Ct+1)*(1+‖θ‖)^degreeTail*
        ((Ideal.absNorm (∏ b,G.ideal b):ℝ)*QK*QP)*T^(-(Adecay:ℝ))*(familyRawScale G s X QK QP^2)⁻¹ := by
        dsimp only [Et,V]
        ring
      rw [he]
      change 2 * (Cshape ^ 2 * (Cm * U)) + _ ≤ (2*Cshape^2*Cm+1)*U + _
      nlinarith only [hU]

/-- A squared tail obeys the same degree bound as the main term after doubling
its degree and paying the tail mass bound. -/
lemma main_add_tail_le {Cm Ct w Z c N b : ℝ} {d e : ℕ}
    (hCm : 0≤Cm) (hw : 1≤w) (hZ : 0≤Z) (ht : N*b^2≤c^4*Z) :
    Cm*(w^d*Z)+2*N*(Ct*w^e*b)^2 ≤ (Cm+2*Ct^2*c^4+1)*w^(max d (e*2))*Z := by
  have hm := pow_le_pow_right₀ hw (le_max_left d (e*2))
  have he := pow_le_pow_right₀ hw (le_max_right d (e*2))
  calc
    _ = Cm*w^d*Z+(2*Ct^2*w^(e*2))*(N*b^2) := by rw [pow_mul]; ring
    _ ≤ Cm*w^(max d (e*2))*Z+(2*Ct^2*w^(max d (e*2)))*(c^4*Z) := by
      refine add_le_add (by gcongr) ?_
      calc
        _ ≤ (2*Ct^2*w^(e*2))*(c^4*Z) := by gcongr
        _ ≤ _ := by gcongr
    _ ≤ _ := by nlinarith only [mul_nonneg (pow_nonneg (zero_le_one.trans hw) (max d (e*2))) hZ]

end
end SevenEighths.InverseReflectedPhase

end OAI
