module

public import DedekindZetaZeroFree.Moments.Probes.Poisson.Scales
public import DedekindZetaZeroFree.Moments.Reflected.RankOneExpansion
public import DedekindZetaZeroFree.Nonvanishing.Mellin.TripleMellinInitialEstimates

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative

open DedekindZetaZeroFree

noncomputable section

open scoped NumberField Classical

structure FixedData {F : Type} [Field F] [NumberField F]
    (S : SArithmeticData F) (η : RayClassCharacter F S.modulus) where
  recipe : PrincipalMellin.ActualRecipe S η
  rootAligned : MomentSources.RootAligned recipe
  source : MomentSources.SelectedMomentSource recipe

private theorem recipe_M_estimates {F : Type} [Field F] [NumberField F]
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    (R : PrincipalMellin.ActualRecipe S η) :
    DifferentiableOn ℂ R.W.M {z : ℂ | 0 < z.re} ∧
    (∀ (σ0 σ1 B : ℝ), 0 < σ0 → σ0 ≤ σ1 → 0 ≤ B →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Set.Icc σ0 σ1, ∀ τ : ℝ,
        ‖R.W.M ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤ C * (1 + |τ|) ^ (-B)) := by
  have hne : ∀ v, R.probe.finiteTrace v ≠ 1 := by
    intro v he
    obtain ⟨x, hx⟩ := R.probe.finiteTrace_ne_one R.A R.σ R.target R.traceBad v
    exact hx (by rw [he]; rfl)
  let w : NumberField.InfinitePlace F := Classical.choice inferInstance
  obtain ⟨dt, hdt, hdis, hsheet⟩ := probe_sheet_mellin_estimates F R.A
    R.probe.finiteTrace R.probe.continuousTrace R.probe.traceCompatible hne
    R.probe.additiveMeasure R.probe.multiplicativeMeasure
    R.probe.additiveHaar R.probe.multiplicativeHaar w
    R.probe.W0 R.probe.W1 R.probe.annular R.probe.compactSupport R.probe.supportUnits
  rcases hsheet with ⟨_, _, _, hM, hMd, _, _, _⟩
  exact ⟨hM, hMd⟩

namespace FixedData

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

def context : D.recipe.A.GeneralArithmeticContext D.recipe.σ D.recipe.target
    D.recipe.traceBad :=
  PrincipalMellinGrowth.recipeContext D.recipe

structure Row where

  toFrequency : CorrectionFactors.Frequency D.context

  isRep : ∃ h : toFrequency.u ≠ 0,
    (⟨toFrequency.u, h⟩ : ThetaReflectionData.Row D.recipe.A) ∈ D.recipe.probe.frequencies.reps

namespace Row

variable {D}

abbrev u (r : D.Row) : D.recipe.A.R := r.toFrequency.u

instance : Coe D.Row (CorrectionFactors.Frequency D.context) := ⟨Row.toFrequency⟩

abbrev generates (r : D.Row) := r.toFrequency.generates

theorem ext {r r' : D.Row} (h : r.toFrequency = r'.toFrequency) : r = r' := by
  cases r; cases r'; cases h; rfl

private theorem frequency_ext_of_u_ideal {f g : CorrectionFactors.Frequency D.context}
    (hu : f.u = g.u) (hI : f.ideal = g.ideal) : f = g := by
  obtain ⟨u, I, a, b, c⟩ := f
  obtain ⟨u', I', a', b', c'⟩ := g
  have hu' : u = u' := hu
  have hI' : I = I' := hI
  subst hu'
  subst hI'
  rfl

theorem u_injective : Function.Injective (Row.u (D := D)) := by
  intro r r' h
  have hu : r.toFrequency.u = r'.toFrequency.u := h
  have hI : r.toFrequency.ideal = r'.toFrequency.ideal := by
    apply D.recipe.A.exteriorIdealEquiv.injective
    apply Subtype.ext
    rw [D.recipe.A.exteriorIdealEquiv_apply, D.recipe.A.exteriorIdealEquiv_apply,
      ← r.toFrequency.generates.2, ← r'.toFrequency.generates.2]
    exact congrArg (fun x : D.recipe.A.R => Ideal.span {x}) hu
  exact ext (frequency_ext_of_u_ideal hu hI)

theorem u_mem_reps (r : D.Row) :
    ∃ h : r.u ≠ 0, (⟨r.u, h⟩ : ThetaReflectionData.Row D.recipe.A) ∈
      D.recipe.probe.frequencies.reps := r.isRep

theorem u_ne_zero (r : D.Row) : r.u ≠ 0 := r.isRep.choose

theorem u_unique {r r' : D.Row} (h : r.u = r'.u) : r = r' := u_injective h

end Row

section
variable (u : D.Row)
include u
def q   : ℝ :=
  (FiniteTransform.exteriorNorm D.recipe.A.R.toSubring u.u : ℝ)

def inducers   : FrequencyCharacterMasks.PrimitiveInducers u.toFrequency :=
  (MaskedHeckeMeromorphic.masked_hecke_meromorphic u.toFrequency).choose

def rowContinuation   (i : MaskedHeckeMeromorphic.Row) :
    MaskedHeckeMeromorphic.RowContinuation u.toFrequency (D.inducers u) i :=
  ((MaskedHeckeMeromorphic.masked_hecke_meromorphic u.toFrequency).choose_spec i).some

def omega   : Detector.PrimitiveFrequencyCharacter F :=
  (D.inducers u).minus

def LpsiRaw   (s : ℂ) : ℂ :=
  MaskedHeckeMeromorphic.incompleteL u.toFrequency MaskedHeckeMeromorphic.Row.plus s

def LlamRaw   (s : ℂ) : ℂ :=
  MaskedHeckeMeromorphic.incompleteL u.toFrequency MaskedHeckeMeromorphic.Row.minus s

def Lpsi   (s : ℂ) : ℂ :=
  MaskedHeckeMeromorphic.quotientRepresentative u.toFrequency (D.inducers u)
    MaskedHeckeMeromorphic.Row.plus (D.rowContinuation u .plus).J s

def Llam   (s : ℂ) : ℂ :=
  MaskedHeckeMeromorphic.quotientRepresentative u.toFrequency (D.inducers u)
    MaskedHeckeMeromorphic.Row.minus (D.rowContinuation u .minus).J s

abbrev rowDeletionSet   (i : MaskedHeckeMeromorphic.Row) :
    Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :=
  MaskedHeckeMeromorphic.deletionSet u.toFrequency i

theorem Lpsi_eq_raw   (s : ℂ) (hs : 1 < s.re) : D.Lpsi u s = D.LpsiRaw u s :=
  ((D.rowContinuation u .plus).regular_equality s hs).symm

theorem Llam_eq_raw   (s : ℂ) (hs : 1 < s.re) : D.Llam u s = D.LlamRaw u s :=
  ((D.rowContinuation u .minus).regular_equality s hs).symm

theorem Lpsi_eq_J_mask   (s : ℂ) :
    D.Lpsi u s = (D.rowContinuation u .plus).J s *
      Detector.finiteEulerDeletionMask F (D.rowDeletionSet u .plus)
        (fun p => (D.inducers u).plus.character p.asIdeal) s /
      (s - 1) ^ MaskedHeckeMeromorphic.poleIndicator (D.inducers u).plus := rfl

theorem Llam_eq_J_mask   (s : ℂ) :
    D.Llam u s = (D.rowContinuation u .minus).J s *
      Detector.finiteEulerDeletionMask F (D.rowDeletionSet u .minus)
        (fun p => (D.omega u).character p.asIdeal) s /
      (s - 1) ^ MaskedHeckeMeromorphic.poleIndicator (D.omega u) := rfl

private theorem row_analyticOnNhd (i : MaskedHeckeMeromorphic.Row) :
    AnalyticOnNhd ℂ (MaskedHeckeMeromorphic.quotientRepresentative u.toFrequency
      (D.inducers u) i (D.rowContinuation u i).J) ({s : ℂ | 0 < s.re} \ {1}) := by
  intro s hs
  exact ((D.rowContinuation u i).J_holomorphic s hs.1).mul
    ((D.rowContinuation u i).B_holomorphic s hs.1) |>.div
      ((analyticAt_id.sub analyticAt_const).pow _) (pow_ne_zero _ (sub_ne_zero.mpr hs.2))

theorem Lpsi_analyticOnNhd :
    AnalyticOnNhd ℂ (D.Lpsi u) ({s : ℂ | 0 < s.re} \ {1}) :=
  row_analyticOnNhd D u .plus

theorem Llam_analyticOnNhd :
    AnalyticOnNhd ℂ (D.Llam u) ({s : ℂ | 0 < s.re} \ {1}) :=
  row_analyticOnNhd D u .minus

end


def zetaS (s : ℂ) : ℂ := InitialSeparatedEuler.zetaS D.recipe.A s

def zetaSCont : ℂ → ℂ := D.recipe.L

def I (X Y Z : ℝ) : ℂ :=
  NormalizedProbe.probe D.recipe.A D.recipe.probe.coefficients D.recipe.probe.domain
    D.recipe.probe.W0 D.recipe.probe.W1 X Y Z

def Iscale (Z : ℝ) : ℂ := D.I (Scales.xScale Z) (Scales.yScale Z) Z

def M : ℂ → ℂ := D.recipe.W.M

def W1Hat : ℂ → ℂ := D.recipe.W.W1Hat

theorem M_one_sixth_ne_zero : D.M (1 / 6) ≠ 0 :=
  D.recipe.mellinWeight_ne_zero

theorem W1Hat_one_ne_zero : D.W1Hat 1 ≠ 0 :=
  D.recipe.realMellinWeight_ne_zero

theorem M_differentiableOn : DifferentiableOn ℂ D.M {z : ℂ | 0 < z.re} :=
  (recipe_M_estimates D.recipe).1

theorem M_vertical_decay (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (k : ℕ) :
    ∃ C : ℝ, ∀ z : ℂ, a ≤ z.re → z.re ≤ b →
      (1 + |z.im|) ^ k * ‖D.M z‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := (recipe_M_estimates D.recipe).2 a b (k : ℝ) ha hab (Nat.cast_nonneg k)
  refine ⟨C, fun z hza hzb => ?_⟩
  have h := hb z.re ⟨hza, hzb⟩ z.im
  rw [Complex.re_add_im] at h
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv] at h
  exact (le_div_iff₀' (by positivity)).mp h

theorem W1Hat_vertical_decay (a b : ℝ) (hab : a ≤ b) (k : ℕ) :
    ∃ C : ℝ, ∀ z : ℂ, a ≤ z.re → z.re ≤ b →
      (1 + |z.im|) ^ k * ‖D.W1Hat z‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := DedekindZetaZeroFree.PrincipalMellinComparison.principal_real_weight_rapid_strip_decay
    D.recipe a b (k : ℝ) (Nat.cast_nonneg k)
  refine ⟨C, fun z hza hzb => ?_⟩
  have hz : z ∈ DedekindZetaZeroFree.comparisonClosedStrip a b := ⟨hza, hzb⟩
  have h := hb z hz
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv] at h
  exact (le_div_iff₀' (by positivity)).mp h

end FixedData

end

end DedekindZetaZeroFree.Quantitative
