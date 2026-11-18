module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BracketSquares
public import HypoellipticAleksandrov.KineticAleksandrov.ClassicalInputs
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.HormanderBridgeTransfer

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Evolution
set_option autoImplicit false
open MeasureTheory Set HypoellipticAleksandrov
open scoped MatrixOrder

variable {n : ℕ}

/-- Spanning on a set implies spanning on any subset. -/
theorem lieAlgebraSpansOn_mono {k N : ℕ} {Ω Ω' : Set (PDE.Vec N)} (h : Ω' ⊆ Ω)
    {X : Fin (k + 1) → PDE.Vec N → PDE.Vec N} (hX : LieAlgebraSpansOn Ω X) :
    LieAlgebraSpansOn Ω' X :=
  fun x hx => hX x (h hx)

/-- **Proposition 2.1.**  Under the standing hypotheses of the evolution problem
(`B` smooth, symmetric, `lam I ≤ B ≤ Lam I`; `b` smooth with `ξ · Db ξ ≥ m`, `m > 0`), the
generators `X_0, X_1, …, X_d` of `Lop` are smooth on `ℝ^{1+2d}` and generate a Lie algebra
spanning every tangent space.  Valid also when `B` depends on `z`. -/
theorem hormander_hypotheses_transportedFields {lam Lam m : ℝ} {B : FullKineticCoefficient n}
    {b : PDE.Vec n → PDE.Vec n} (hlam : 0 < lam) (hB : IsSmoothFullKineticCoefficient B)
    (hell : HasEverywhereLoewnerBounds lam Lam B) (hb : IsSmoothDrift b) (hm : 0 < m)
    (hcoerc : HasUnitDirectionDriftCoercivity m b) (Ω : Set (EvolutionVec n)) :
    (∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (transportedFields B b i) Ω) ∧
      LieAlgebraSpansOn Ω (transportedFields B b) :=
  ⟨fun i => (contDiff_transportedFields (contDiff_sqrtCoeffAt_entry hlam hB hell) hb i).contDiffOn,
    lieAlgebraSpansOn_mono (Set.subset_univ Ω)
      (lieAlgebraSpansOn_transportedFields hlam hB hell hb hm hcoerc)⟩

/-- **Proposition 2.1 (bracket part).**  For `ε > 0`, the generators
`X_0, X_i, Y_l` of `L_ε` are smooth and their Lie algebra (indeed the generators themselves)
spans every tangent space of `ℝ^{1+2d}`.  Only `0 < lam`, the lower Loewner bound, `B` smooth
and `b` smooth are used (no drift coercivity is needed for `ε > 0`). -/
theorem hormander_hypotheses_regularizedFields {lam Lam ε : ℝ} {B : FullKineticCoefficient n}
    {b : PDE.Vec n → PDE.Vec n} (hlam : 0 < lam) (hB : IsSmoothFullKineticCoefficient B)
    (hell : HasEverywhereLoewnerBounds lam Lam B) (hb : IsSmoothDrift b) (hε : 0 < ε)
    (Ω : Set (EvolutionVec n)) :
    (∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (regularizedFields B b ε i) Ω) ∧
      LieAlgebraSpansOn Ω (regularizedFields B b ε) :=
  ⟨fun i =>
    (contDiff_regularizedFields (contDiff_sqrtCoeffAt_entry hlam hB hell) hb ε i).contDiffOn,
    lieAlgebraSpansOn_mono (Set.subset_univ Ω)
      (lieAlgebraSpansOn_regularizedFields hlam hell hε)⟩

set_option autoImplicit false

variable {n : ℕ}

/-- **Smooth representative** (Proposition 2.1).  Assuming Hörmander's theorem
`hH`, a locally integrable distributional solution `u` of `L_ε u = 0` (`ε > 0`) on an open
`U ⊆ KineticPoint n` has a representative `v`, smooth in packed coordinates on the preimage of `U`,
with `u = v` almost everywhere on `U`. -/
theorem exists_smooth_viscous_kinetic_representative
    (hH : HormanderHypoellipticityStatement) {lam Lam : ℝ}
    {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n} (hlam : 0 < lam)
    (hB_smooth : IsSmoothFullKineticCoefficient B)
    (hB_ell : HasEverywhereLoewnerBounds lam Lam B) (hb_smooth : IsSmoothDrift b)
    (U : Set (KineticPoint n)) (hU : IsOpen U) (ε : ℝ) (hε : 0 < ε) (u : KineticPoint n → ℝ)
    (hu : IsKineticWeakRegularizedSolution B b ε U u (fun _ => 0)) :
    ∃ v : KineticPoint n → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) (v ∘ evolutionHomeomorph n) (evolutionHomeomorph n ⁻¹' U) ∧
        u =ᵐ[volume.restrict U] v := by
  obtain ⟨hX, hspan⟩ :=
    hormander_hypotheses_regularizedFields hlam hB_smooth hB_ell hb_smooth hε
      (evolutionHomeomorph n ⁻¹' U)
  exact exists_kinetic_representative
    (hH ((evolutionHomeomorph n).continuous.isOpen_preimage U hU) _ _ _ _ hX hspan
      contDiffOn_const (hasWeakHormanderEquation_comp_regularizedFields hε.le hlam hB_smooth hB_ell hb_smooth hu (contDiffOn_const (c := 0))))

/-- **Smooth representative** (Proposition 2.1, Hörmander part).  Assuming the Hörmander
theorem `hH`, a locally integrable distributional solution `u` of `Lop u = 0` for the transported
operator on an open `U ⊆ KineticPoint n` has a representative `v`, smooth in packed coordinates
on the preimage of `U`, with `u = v` almost everywhere on `U`.  The bracket check uses `0 < m` and
unit-direction drift coercivity. -/
theorem exists_smooth_kinetic_representative
    (hH : HormanderHypoellipticityStatement) {lam Lam m : ℝ}
    {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n} (hlam : 0 < lam)
    (hB_smooth : IsSmoothFullKineticCoefficient B)
    (hB_ell : HasEverywhereLoewnerBounds lam Lam B) (hb_smooth : IsSmoothDrift b)
    (hm : 0 < m) (hb_coercive : HasUnitDirectionDriftCoercivity m b)
    (U : Set (KineticPoint n)) (hU : IsOpen U) (u : KineticPoint n → ℝ)
    (hu : IsKineticWeakTransportedSolution B b U u (fun _ => 0)) :
    ∃ v : KineticPoint n → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) (v ∘ evolutionHomeomorph n) (evolutionHomeomorph n ⁻¹' U) ∧
        u =ᵐ[volume.restrict U] v := by
  obtain ⟨hX, hspan⟩ :=
    hormander_hypotheses_transportedFields hlam hB_smooth hB_ell hb_smooth hm hb_coercive
      (evolutionHomeomorph n ⁻¹' U)
  exact exists_kinetic_representative
    (hH ((evolutionHomeomorph n).continuous.isOpen_preimage U hU) _ _ _ _ hX hspan
      contDiffOn_const (hasWeakHormanderEquation_comp_transportedFields hlam hB_smooth hB_ell hb_smooth hu (contDiffOn_const (c := 0))))

/-- Identification of a continuous candidate with a smooth representative: two functions that
are continuous in packed coordinates on the preimage of an open `U` and agree almost everywhere
on `U` agree at every point of `U`. -/
theorem eqOn_of_ae_eq_of_continuousOn_kinetic {U : Set (KineticPoint n)} (hU : IsOpen U)
    {v w : KineticPoint n → ℝ}
    (hv : ContinuousOn (v ∘ evolutionHomeomorph n) (evolutionHomeomorph n ⁻¹' U))
    (hw : ContinuousOn (w ∘ evolutionHomeomorph n) (evolutionHomeomorph n ⁻¹' U))
    (hae : v =ᵐ[volume.restrict U] w) : EqOn v w U := by
  intro x hx
  have := (Measure.eqOn_open_of_ae_eq (ae_eq_comp_evolutionHomeomorph_iff.2 hae) ((evolutionHomeomorph n).continuous.isOpen_preimage U hU) hv hw) (show (evolutionHomeomorph n).symm x ∈ evolutionHomeomorph n ⁻¹' U by simpa using hx)
  simpa using this

end HypoellipticAleksandrov.KineticAleksandrov.Evolution

