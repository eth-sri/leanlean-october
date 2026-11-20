module

public import DedekindZetaZeroFree.Moments.Probes.PrincipalArithmeticEnlargement

@[expose] public section

open scoped NumberField Classical
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.PrincipalProbeConstruction
variable {F : Type} [Field F] [NumberField F]
private alias prime_eq := DedekindZetaZeroFree.SArithmeticData.OscillatoryIntegralStabilization.prime_eq
private alias continuous_cast_map := DedekindZetaZeroFree.SArithmeticData.OscillatoryIntegralStabilization.continuous_cast_map

private alias traceChar_cast := DedekindZetaZeroFree.SArithmeticData.OscillatoryIntegralStabilization.traceChar_cast

private alias char_eq := DedekindZetaZeroFree.QuadraticRawProduct.tensor_finiteCharacter_eq
private theorem phase_single (A : SArithmeticData F) (v : ↥A.Sf)
    (u : PoissonFinite.Space F A.Sf) (y : v.val.adicCompletion F) :
    PoissonS.finiteBallTraceCharacter F A.Sf
      (u * (Pi.single v y : PoissonFinite.Space F A.Sf)) =
      localFiniteCharacter F v.val (u v * y) := by
  rw [PoissonS.finiteBallTraceCharacter_apply, Finset.prod_eq_single v]
  · simp
  · intro w hw hne
    have hs : (Pi.single v y : PoissonFinite.Space F A.Sf) w = 0 := by
      simp [Pi.single_eq_of_ne hne]
    simp only [Pi.mul_apply, hs, mul_zero]
    exact AddChar.map_zero_eq_one _
  · intro hn
    exact False.elim (hn (Finset.mem_univ v))

set_option backward.isDefEq.respectTransparency false in
private theorem conductor_localFinite (A : SArithmeticData F) :
    PoissonS.TraceConductor F A.Sf (fun v => localFiniteCharacter F v.val) := by
  intro v y
  have hball' := Iff.of_eq (congrArg (fun E : Set (PoissonFinite.Space F A.Sf) =>
      (Pi.single v y : PoissonFinite.Space F A.Sf) ∈ E)
    (PoissonS.finiteBallAnnihilator_eq F A.Sf (fun _ => 0)))
  simp only [PoissonS.finiteBallAnnihilator, PoissonS.finiteBall,
    Set.mem_setOf_eq, sub_zero, neg_neg, neg_zero, zpow_zero] at hball'
  constructor
  · intro h
    have ha := hball'.mp (fun u hu => by
      rw [phase_single A v]
      apply h
      simpa [PoissonS.finiteBall] using hu v)
    simpa using ha v
  · intro h
    have ha := hball'.mpr (fun w => by
      by_cases hw : w = v
      · subst w
        simpa using h
      · simp only [Pi.single_eq_of_ne hw, norm_zero]
        exact le_of_lt (zpow_pos (by exact_mod_cast
          (Nat.zero_lt_of_lt (NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm w.val))) _))
    intro x hx
    let u : PoissonFinite.Space F A.Sf := Pi.single v x
    have hu : u ∈ PoissonS.finiteBall F A.Sf (fun _ => 0) := by
      intro w
      by_cases hw : w = v
      · subst w
        simpa [u] using hx
      · simp [u, Pi.single_eq_of_ne hw]
    simpa [phase_single A v, u] using (ha u hu)

theorem canonical_trace_conductor (A : SArithmeticData F) :
    PoissonS.TraceConductor F A.Sf
      (fun v => ResidueTrace.localTraceCharacter v.val) := by
  intro v y
  simpa only [char_eq] using (conductor_localFinite A) v y

end DedekindZetaZeroFree.PrincipalProbeConstruction
