module
public import OAI.NumberTheory.DirichletL.Descent.ShortReflectedEnergy

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve InverseTerminalWidths InverseReflectedPhase CompletedHeight
local notation "Eis"=>ActualEisensteinCubic.O
universe v

theorem short_harmonic_small_power (L e:ℝ) (hL:0≤L) (he:0<e):
    ∃C:ℝ,0<C ∧ ∀Z h:ℝ,1≤Z → 0≤h → h≤L →
      (256*(columnDyadicLength (Z^h)+1:ℝ))^2≤C*Z^e := by
  let a:=e/(2*(L+1))
  have ha:0<a:=by dsimp [a]; positivity
  let B:=256*(2+1/(a*Real.log 2))
  have hlog:0<Real.log 2:=Real.log_pos (by norm_num)
  have hB:0<B:=by dsimp [B]; positivity
  refine ⟨B^2,pow_pos hB _,?_⟩
  intro Z h hZ hh hhL
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hZh:1≤Z^h:=Real.one_le_rpow hZ hh
  have hb:=mul_le_mul_of_nonneg_left (columnDyadicLength_small_power a ha (Z^h) hZh)
    (by norm_num:(0:ℝ)≤256)
  have hs:(256*(columnDyadicLength (Z^h)+1:ℝ))^2≤B^2*Z^(h*a*2):=by
    calc
      _≤(B*(Z^h)^a)^2:=pow_le_pow_left₀ (by positivity) (by simpa [B,mul_assoc] using hb) 2
      _=B^2*Z^(h*a*2):=by rw [mul_pow,←Real.rpow_mul hz.le,←Real.rpow_mul_natCast hz.le (h*a) 2]; norm_num
  apply hs.trans
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg B)
  apply Real.rpow_le_rpow_of_exponent_le hZ
  have heq:a*(2*(L+1))=e:=by dsimp [a]; field_simp
  nlinarith

end SevenEighths.InverseMoment

end

end OAI
