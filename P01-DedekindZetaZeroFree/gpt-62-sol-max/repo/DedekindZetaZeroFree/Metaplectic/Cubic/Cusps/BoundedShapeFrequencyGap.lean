module

public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.Lattices.DualBasisCoordinates
public import DedekindZetaZeroFree.Metaplectic.Kubota.GenuineCuspLinesAndUnitaryMonodromy

@[expose] public section

noncomputable section
open scoped Classical

namespace DedekindZetaZeroFree
namespace KPCuspFrequencyGap

abbrev Euclidean (d : ℕ) := EuclideanSpace ℂ (Fin d)

def coordinates (d : ℕ) : Euclidean d ≃ₗ[ℝ] (Fin d → ℂ) :=
  WithLp.linearEquiv 2 ℝ (Fin d → ℂ)

def shapeEnergy {d : ℕ} (b : KPCuspLogShape.hyperplane d) (ξ : Euclidean d) : ℝ :=
  ∑ i, Real.exp (2 * (b : Fin d → ℝ) i) * ‖coordinates d ξ i‖ ^ 2

def horizontalEnergy {d : ℕ} (t : ℝ) (b : KPCuspLogShape.hyperplane d)
    (ξ : Euclidean d) : ℝ :=
  4 * Real.pi ^ 2 * Real.exp (2 * t) * shapeEnergy b ξ


theorem uniform_shortest_frequency (d : ℕ) (L : Submodule ℤ (Euclidean d))
    [DiscreteTopology L] [IsZLattice ℝ L]
    (B : Set (KPCuspLogShape.hyperplane d)) (hB : IsCompact B) :
    ∃ c : ℝ, 0 < c ∧ ∀ b ∈ B, ∀ ξ : PoissonArch.dualLattice L,
      (ξ : Euclidean d) ≠ 0 → c ≤ shapeEnergy b ξ := by
  classical

  haveI : DiscreteTopology (PoissonArch.dualLattice L) := inferInstance
  have h0mem : ({0} : Set (PoissonArch.dualLattice L)) ∈ nhds (0 : PoissonArch.dualLattice L) :=
    (isOpen_discrete _).mem_nhds (Set.mem_singleton 0)
  obtain ⟨ε, hεpos, hε⟩ := Metric.mem_nhds_iff.mp h0mem
  have hnorm : ∀ ξ : PoissonArch.dualLattice L,
      (ξ : Euclidean d) ≠ 0 → ε ≤ ‖(ξ : Euclidean d)‖ := by
    intro ξ hξ
    by_contra hlt
    rw [not_le] at hlt
    have hmem : ξ ∈ Metric.ball (0 : PoissonArch.dualLattice L) ε := by
      rw [Metric.mem_ball, dist_eq_norm]
      simpa using hlt
    have h0 : ξ = 0 := by
      have := hε hmem
      simpa using this
    exact hξ (by simpa [h0])

  have hbound : ∀ i : Fin d, ∃ m : ℝ, ∀ b ∈ B, m ≤ (b : Fin d → ℝ) i := by
    intro i
    have hc : Continuous (fun b : KPCuspLogShape.hyperplane d => (b : Fin d → ℝ) i) :=
      (continuous_apply i).comp continuous_subtype_val
    obtain ⟨mm, hmm⟩ := (hB.image hc).bddBelow
    exact ⟨mm, fun b hb => hmm ⟨b, hb, rfl⟩⟩
  choose m hm using hbound
  set M : ℝ := ∑ i, |m i| with hM
  have hbge : ∀ b ∈ B, ∀ i, -M ≤ (b : Fin d → ℝ) i := by
    intro b hb i
    have h1 : m i ≤ (b : Fin d → ℝ) i := hm i b hb
    have h2 : -|m i| ≤ m i := neg_abs_le _
    have h3 : |m i| ≤ M := by
      rw [hM]
      exact Finset.single_le_sum (fun j _ => abs_nonneg (m j)) (Finset.mem_univ i)
    linarith
  refine ⟨Real.exp (-2 * M) * ε ^ 2, ?_, ?_⟩
  · have := Real.exp_pos (-2 * M)
    positivity
  · intro b hb ξ hξ
    have hsum : shapeEnergy b ξ =
        ∑ i, Real.exp (2 * (b : Fin d → ℝ) i) * ‖(ξ : Euclidean d) i‖ ^ 2 := rfl
    rw [hsum]
    calc Real.exp (-2 * M) * ε ^ 2
        ≤ Real.exp (-2 * M) * ‖(ξ : Euclidean d)‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          exact pow_le_pow_left₀ (le_of_lt hεpos) (hnorm ξ hξ) 2
      _ = Real.exp (-2 * M) * ∑ i, ‖(ξ : Euclidean d) i‖ ^ 2 := by
          rw [PiLp.norm_sq_eq_of_L2]
      _ = ∑ i, Real.exp (-2 * M) * ‖(ξ : Euclidean d) i‖ ^ 2 := by
          rw [Finset.mul_sum]
      _ ≤ ∑ i, Real.exp (2 * (b : Fin d → ℝ) i) * ‖(ξ : Euclidean d) i‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          apply Real.exp_le_exp.mpr
          have := hbge b hb i
          linarith

section Cusp
variable {F : Type} [Field F] [NumberField F]
variable {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable (S : Subgroup (KPCuspArithmetic.PGL2 F))
variable (D : KPCuspCharts.ParabolicData F S) (ρ : S →* rootsOfUnity 3 F)

def kernelEuclideanLattice : Submodule ℤ (Euclidean (KPCuspLogShape.dimension F)) :=
  ((KPCuspCharts.translationLattice F
    (KPCuspGenuineMonodromy.kernelLattice S D ρ)).toIntSubmodule).map
      ((coordinates (KPCuspLogShape.dimension F)).symm.toLinearMap.restrictScalars ℤ)

abbrev Frequency := PoissonArch.dualLattice (kernelEuclideanLattice S D ρ)

def fourierCharacter (ξ : Euclidean (KPCuspLogShape.dimension F))
    (y : KPCuspCharts.Horizontal F) : ℂ :=
  Complex.exp ((2 * Real.pi * inner ℝ ξ
    ((coordinates (KPCuspLogShape.dimension F)).symm y) : ℝ) * Complex.I)

 def exponentLinear (ξ : Euclidean (KPCuspLogShape.dimension F)) :
    KPCuspCharts.Horizontal F →L[ℝ] ℂ :=
  (Complex.ofRealCLM.comp ((innerSL ℝ ξ).comp ((coordinates _).symm.toLinearMap.toContinuousLinearMap))).smulRight ((2 * Real.pi : ℂ) * Complex.I)
private theorem exponent_apply (ξ : Euclidean (KPCuspLogShape.dimension F)) (y : KPCuspCharts.Horizontal F) :
    exponentLinear ξ y = (2 * Real.pi * inner ℝ ξ ((coordinates _).symm y) : ℝ) * Complex.I := by
  change ((inner ℝ ξ ((coordinates _).symm y) : ℝ) : ℂ) * ((2 * Real.pi : ℂ) * Complex.I) = _
  push_cast
  ring


 lemma fourierCharacter_add (ξ : Euclidean (KPCuspLogShape.dimension F))
    (x y : KPCuspCharts.Horizontal F) :
    fourierCharacter (F := F) ξ (x + y) =
      fourierCharacter (F := F) ξ x * fourierCharacter (F := F) ξ y := by
  unfold fourierCharacter
  rw [map_add, inner_add_right]
  rw [mul_add, Complex.ofReal_add, add_mul, Complex.exp_add]

 lemma fourierCharacter_translation (ξ : Frequency S D ρ) (v : KPCuspCharts.Horizontal F)
    (hv : v ∈ KPCuspCharts.translationLattice F
      (KPCuspGenuineMonodromy.kernelLattice S D ρ)) :
    fourierCharacter (F := F) (ξ : Euclidean (KPCuspLogShape.dimension F)) v = 1 := by
  obtain ⟨x, hx, hxv⟩ := AddSubgroup.mem_map.mp hv
  subst hxv
  set w := (coordinates (KPCuspLogShape.dimension F)).symm (KPCuspCharts.embedding F x) with hwdef
  have hw : w ∈ kernelEuclideanLattice S D ρ := by
    rw [kernelEuclideanLattice]
    exact Submodule.mem_map.mpr ⟨KPCuspCharts.embedding F x,
      AddSubgroup.mem_map.mpr ⟨x, hx, rfl⟩, rfl⟩
  have hmem : (ξ : Euclidean (KPCuspLogShape.dimension F)) ∈
      LinearMap.BilinForm.dualSubmodule (innerₗ (Euclidean (KPCuspLogShape.dimension F)))
        (kernelEuclideanLattice S D ρ) := ξ.property
  have hdual : inner ℝ (ξ : Euclidean (KPCuspLogShape.dimension F)) w ∈ (1 : Submodule ℤ ℝ) := by
    have h := (LinearMap.BilinForm.mem_dualSubmodule
      (B := innerₗ (Euclidean (KPCuspLogShape.dimension F)))).mp hmem w hw
    simpa using h
  obtain ⟨n, hn⟩ := Submodule.mem_one.mp hdual
  have hn' : (n : ℝ) = inner ℝ (ξ : Euclidean (KPCuspLogShape.dimension F)) w := hn
  have hmain : fourierCharacter (F := F) (ξ : Euclidean (KPCuspLogShape.dimension F))
      (KPCuspCharts.embedding F x) =
      Complex.exp ((n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) := by
    unfold fourierCharacter
    rw [← hn']
    congr 1
    push_cast
    ring
  rw [hmain, Complex.exp_int_mul_two_pi_mul_I]

def torusMode (ξ : Frequency S D ρ) :
    KPCuspGenuineMonodromy.KernelTorus S D ρ → ℂ :=
  Quotient.lift (fourierCharacter (F := F) (ξ : Euclidean (KPCuspLogShape.dimension F)))
    (by
      intro a b hab
      have hab' : -a + b ∈ KPCuspCharts.translationLattice F
          (KPCuspGenuineMonodromy.kernelLattice S D ρ) :=
        QuotientAddGroup.leftRel_apply.mp hab
      have hb : b = a + (-a + b) := by abel
      rw [hb, fourierCharacter_add, fourierCharacter_translation S D ρ ξ (-a + b) hab', mul_one])

def constantSections (V : Submodule ℂ ℂ) :
    Submodule ℂ (KPCuspGenuineMonodromy.KernelTorus S D ρ → ℂ) where
  carrier := {f | f ∈ KPCuspGenuineMonodromy.torusSections
    (ζ := ζ) (hζ := hζ) S D ρ V ∧ ∀ z, f z = f 0}
  zero_mem' := ⟨Submodule.zero_mem _, by intro z; simp⟩
  add_mem' := by
    intro f g hf hg
    exact ⟨Submodule.add_mem _ hf.1 hg.1,
      by intro z; rw [Pi.add_apply, Pi.add_apply, hf.2 z, hg.2 z]⟩
  smul_mem' := by
    intro a f hf
    exact ⟨Submodule.smul_mem _ a hf.1,
      by intro z; rw [Pi.smul_apply, Pi.smul_apply, hf.2 z]⟩

private theorem mode_lift (ξ : Frequency S D ρ) (y : KPCuspCharts.Horizontal F) :
    torusMode S D ρ ξ (QuotientAddGroup.mk y) = fourierCharacter ξ y := rfl

 def evalConstant (V : Submodule ℂ ℂ) : constantSections (ζ := ζ) (hζ := hζ) S D ρ V →ₗ[ℂ] ℂ where
  toFun f := f.val 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
private theorem eval_injective (V : Submodule ℂ ℂ) : Function.Injective (evalConstant (ζ := ζ) (hζ := hζ) S D ρ V) := by
  intro f g h
  apply Subtype.ext
  funext z
  exact (f.property.2 z).trans (h.trans (g.property.2 z).symm)
 def scalarAction (V : Submodule ℂ ℂ) : S →* (constantSections (ζ := ζ) (hζ := hζ) S D ρ V ≃ₗ[ℂ]
    constantSections (ζ := ζ) (hζ := hζ) S D ρ V) where
  toFun s := LinearEquiv.smulOfUnit (KPCuspGenuineMonodromy.chi F ζ hζ (ρ s))
  map_one' := by
    ext f z
    change (KPCuspGenuineMonodromy.chi F ζ hζ (ρ 1) : ℂ) * f.val z = f.val z
    simp
  map_mul' s t := by
    ext f z
    change (KPCuspGenuineMonodromy.chi F ζ hζ (ρ (s*t)) : ℂ) * f.val z =
      (KPCuspGenuineMonodromy.chi F ζ hζ (ρ s) : ℂ) *
        ((KPCuspGenuineMonodromy.chi F ζ hζ (ρ t) : ℂ) * f.val z)
    simp [mul_assoc]
private theorem scalar_ker (V : Submodule ℂ ℂ) : D.ratio.ker ≤ (scalarAction (ζ := ζ) (hζ := hζ) S D ρ V).ker := by
  intro s hs
  rw [← D.exact] at hs
  obtain ⟨x, rfl⟩ := hs
  apply LinearEquiv.ext
  intro f
  apply Subtype.ext
  funext z
  have heq := f.property.1.2 x.toAdd (0 : KPCuspCharts.Horizontal F)
  change (KPCuspGenuineMonodromy.chi F ζ hζ (ρ (D.inclusion x)) : ℂ) * f.val z = f.val z
  have hc := f.property.2
  change f.val _ = (KPCuspGenuineMonodromy.chi F ζ hζ (ρ (D.inclusion x)) : ℂ) * f.val _ at heq
  simpa only [hc, zero_add] using heq.symm

structure ConstantLocalSystem (V : Submodule ℂ ℂ)
    (O : KPCuspGenuineMonodromy.CuspOutput (ζ := ζ) (hζ := hζ) S D ρ V) where
  finiteDimensional : FiniteDimensional ℂ (constantSections (ζ := ζ) (hζ := hζ) S D ρ V)
  rank_le_one : Module.finrank ℂ (constantSections (ζ := ζ) (hζ := hζ) S D ρ V) ≤ 1
  transport : D.E →* (constantSections (ζ := ζ) (hζ := hζ) S D ρ V ≃ₗ[ℂ]
    constantSections (ζ := ζ) (hζ := hζ) S D ρ V)
  transition_formula : ∀ (s : S)
    (f : constantSections (ζ := ζ) (hζ := hζ) S D ρ V) z,
    (transport (D.ratio s) f).val z =
      (KPCuspGenuineMonodromy.chi F ζ hζ (ρ s) : ℂ) * f.val (O.monodromy s⁻¹ z)
  unitary : ∀ u (f : constantSections (ζ := ζ) (hζ := hζ) S D ρ V),
    ‖(transport u f).val 0‖ = ‖f.val 0‖
  locally_constant : ∀ u (f : constantSections (ζ := ζ) (hζ := hζ) S D ρ V),
    IsLocallyConstant (fun _ : KPCuspCharts.Shape F => transport u f)
  translation_trivial : ∀ (x : D.L)
    (f : constantSections (ζ := ζ) (hζ := hζ) S D ρ V),
    transport (D.ratio (D.inclusion (Multiplicative.ofAdd x))) f = f

private theorem constantSystem_test (V : Submodule ℂ ℂ)
    (O : KPCuspGenuineMonodromy.CuspOutput (ζ := ζ) (hζ := hζ) S D ρ V) :
    Nonempty (ConstantLocalSystem (ζ := ζ) (hζ := hζ) S D ρ V O) := by
  let ev := evalConstant (ζ := ζ) (hζ := hζ) S D ρ V
  letI := FiniteDimensional.of_injective ev (eval_injective S D ρ V)
  let α := scalarAction (ζ := ζ) (hζ := hζ) S D ρ V
  let τ := MonoidHom.liftOfSurjective D.ratio D.surjective ⟨α, scalar_ker S D ρ V⟩
  have ht : ∀ s, τ (D.ratio s) = α s := by
    intro s
    exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  refine ⟨{ finiteDimensional := inferInstance
            rank_le_one := ?_
            transport := τ
            transition_formula := ?_
            unitary := ?_
            locally_constant := fun u f => IsLocallyConstant.const _
            translation_trivial := ?_ }⟩
  · simpa using (LinearMap.finrank_le_finrank_of_injective (eval_injective (ζ := ζ) (hζ := hζ) S D ρ V))
  · intro s f z
    rw [ht]
    change (KPCuspGenuineMonodromy.chi F ζ hζ (ρ s) : ℂ) * f.val z = _
    rw [f.property.2 z, f.property.2 (O.monodromy s⁻¹ z)]
  · intro u f
    obtain ⟨s, rfl⟩ := D.surjective u
    rw [ht]
    change ‖(KPCuspGenuineMonodromy.chi F ζ hζ (ρ s) : ℂ) * f.val 0‖ = _
    rw [norm_mul]
    have hp : (KPCuspGenuineMonodromy.chi F ζ hζ (ρ s) : ℂ) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← map_pow]
      have hpow : ρ s ^ 3 = 1 := by
        apply Subtype.ext
        exact (ρ s).property
      rw [hpow, map_one, Units.val_one]
    rw [Complex.norm_eq_one_of_pow_eq_one hp (by norm_num), one_mul]
  · intro x f
    have hx : D.ratio (D.inclusion (Multiplicative.ofAdd x)) = 1 := by
      change D.inclusion (Multiplicative.ofAdd x) ∈ D.ratio.ker
      rw [← D.exact]
      exact ⟨_, rfl⟩
    rw [hx, map_one]
    rfl

private theorem triple_kernel (x : D.L) : (3 : ℤ) • (x : F) ∈ KPCuspGenuineMonodromy.kernelLattice S D ρ := by
  refine ⟨D.L.zsmul_mem x.property 3, ?_⟩
  intro hx
  have he : (⟨(3 : ℤ) • (x : F), hx⟩ : D.L) = (3 : ℤ) • x := rfl
  rw [he]
  change ρ (D.inclusion ((Multiplicative.ofAdd x) ^ (3 : ℤ))) = 1
  rw [map_zpow, map_zpow]
  change ρ (D.inclusion (Multiplicative.ofAdd x)) ^ (3 : ℕ) = 1
  apply Subtype.ext
  exact (ρ (D.inclusion (Multiplicative.ofAdd x))).property
private theorem kernel_horiz_full (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (G : KPCuspCharts.ChartOutput F hF S D) :
    ∃ hd : DiscreteTopology (KPCuspCharts.translationLattice F (KPCuspGenuineMonodromy.kernelLattice S D ρ)).toIntSubmodule,
    letI := hd; IsZLattice ℝ (KPCuspCharts.translationLattice F (KPCuspGenuineMonodromy.kernelLattice S D ρ)).toIntSubmodule := by
  obtain ⟨hd, hf⟩ := G.lattice
  letI := hd
  letI := hf
  have hle : KPCuspCharts.translationLattice F (KPCuspGenuineMonodromy.kernelLattice S D ρ) ≤
      KPCuspCharts.translationLattice F D.L := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, hx.1, rfl⟩
  letI : DiscreteTopology (KPCuspCharts.translationLattice F (KPCuspGenuineMonodromy.kernelLattice S D ρ)).toIntSubmodule := DiscreteTopology.of_subset hd hle
  refine ⟨inferInstance, ⟨?_⟩⟩
  apply top_le_iff.mp
  rw [← IsZLattice.span_top (K := ℝ) (L := (KPCuspCharts.translationLattice F D.L).toIntSubmodule)]
  apply Submodule.span_le.mpr
  intro y hy
  obtain ⟨x, hx, rfl⟩ := hy
  have hm : (3 : ℤ) • KPCuspCharts.embedding F x ∈
      KPCuspCharts.translationLattice F (KPCuspGenuineMonodromy.kernelLattice S D ρ) := by
    refine ⟨(3 : ℤ) • x, triple_kernel S D ρ ⟨x,hx⟩, ?_⟩
    exact map_zsmul _ _ _
  have hs := Submodule.subset_span (R := ℝ) hm
  have hh := Submodule.smul_mem (Submodule.span ℝ (KPCuspCharts.translationLattice F (KPCuspGenuineMonodromy.kernelLattice S D ρ) : Set (KPCuspCharts.Horizontal F))) (1/3 : ℝ) hs
  rw [← Int.cast_smul_eq_zsmul ℝ, smul_smul] at hh
  norm_num at hh
  exact hh
private theorem kernel_euclidean_full (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (G : KPCuspCharts.ChartOutput F hF S D) :
    ∃ hd : DiscreteTopology (kernelEuclideanLattice S D ρ), letI := hd; IsZLattice ℝ (kernelEuclideanLattice S D ρ) := by
  obtain ⟨hd, hf⟩ := kernel_horiz_full S D ρ hF G
  letI := hd
  letI := hf
  let e := (coordinates (KPCuspLogShape.dimension F)).toContinuousLinearEquiv
  have he : kernelEuclideanLattice S D ρ =
      ZLattice.comap ℝ (KPCuspCharts.translationLattice F (KPCuspGenuineMonodromy.kernelLattice S D ρ)).toIntSubmodule e.toLinearMap := by
    ext y
    constructor
    · rintro ⟨z, hz, hzy⟩
      change e y ∈ (KPCuspCharts.translationLattice F (KPCuspGenuineMonodromy.kernelLattice S D ρ)).toIntSubmodule
      subst y
      exact hz
    · intro hy
      exact ⟨e y, hy, (coordinates _).symm_apply_apply y⟩
  rw [he]
  exact ⟨inferInstance, inferInstance⟩

 def linearScale (u : Fˣ) : Euclidean (KPCuspLogShape.dimension F) →ₗ[ℝ] Euclidean (KPCuspLogShape.dimension F) where
  toFun x := (coordinates _).symm (fun i => star (KPCuspCharts.embedding F (u : F) i) * coordinates _ x i)
  map_add' x y := by
    ext i
    change star (KPCuspCharts.embedding F (u : F) i) * (coordinates _ (x+y) i) =
      star (KPCuspCharts.embedding F (u : F) i) * coordinates _ x i + star (KPCuspCharts.embedding F (u : F) i) * coordinates _ y i
    simp [mul_add]
  map_smul' a x := by
    ext i
    change star (KPCuspCharts.embedding F (u : F) i) * (coordinates _ (a • x) i) =
      a • (star (KPCuspCharts.embedding F (u : F) i) * coordinates _ x i)
    simp [mul_comm, mul_left_comm]
private theorem scale_pair (u : Fˣ) (ξ : Euclidean (KPCuspLogShape.dimension F)) (y : KPCuspCharts.Horizontal F) :
    inner ℝ (linearScale u ξ) ((coordinates _).symm y) =
      inner ℝ ξ ((coordinates _).symm (fun i => KPCuspCharts.embedding F (u : F) i * y i)) := by
  simp only [PiLp.inner_apply (𝕜 := ℝ)]
  apply Finset.sum_congr rfl
  intro i hi
  change inner ℝ (star (KPCuspCharts.embedding F (u : F) i) * coordinates _ ξ i) (y i) =
    inner ℝ (coordinates _ ξ i) (KPCuspCharts.embedding F (u : F) i * y i)
  simp_rw [real_inner_eq_re_inner ℂ, RCLike.inner_apply]
  change (y i * star (star (KPCuspCharts.embedding F (u : F) i) * coordinates _ ξ i)).re =
    ((KPCuspCharts.embedding F (u : F) i * y i) * star (coordinates _ ξ i)).re
  simp [mul_comm, mul_left_comm, mul_assoc]
 theorem scale_mul (u v : Fˣ) (ξ : Euclidean (KPCuspLogShape.dimension F)) :
    linearScale (u*v) ξ = linearScale u (linearScale v ξ) := by
  ext i
  change star (KPCuspCharts.embedding F ((u*v : Fˣ) : F) i) * coordinates _ ξ i =
    star (KPCuspCharts.embedding F (u : F) i) * (star (KPCuspCharts.embedding F (v : F) i) * coordinates _ ξ i)
  simp [KPCuspCharts.embedding, mul_assoc]
 theorem scale_one (ξ : Euclidean (KPCuspLogShape.dimension F)) : linearScale (1 : Fˣ) ξ = ξ := by
  ext i
  change star (KPCuspCharts.embedding F (1 : F) i) * coordinates _ ξ i = coordinates _ ξ i
  simp [KPCuspCharts.embedding]
 theorem scale_dual (V : Submodule ℂ ℂ)
    (O : KPCuspGenuineMonodromy.CuspOutput (ζ := ζ) (hζ := hζ) S D ρ V)
    (s : S) (ξ : Frequency S D ρ) : linearScale (D.ratio s : Fˣ) ξ ∈ Frequency S D ρ := by
  apply (LinearMap.BilinForm.mem_dualSubmodule _).mpr
  intro y hy
  obtain ⟨z, hz, rfl⟩ := hy
  obtain ⟨x, hx, rfl⟩ := hz
  change inner ℝ (linearScale (D.ratio s : Fˣ) ξ) ((coordinates _).symm (KPCuspCharts.embedding F x)) ∈ (1 : Submodule ℤ ℝ)
  rw [scale_pair]
  apply (LinearMap.BilinForm.mem_dualSubmodule _).mp ξ.property
  apply Submodule.mem_map.mpr
  refine ⟨KPCuspCharts.embedding F (((D.ratio s : Fˣ) : F) * x), ?_, ?_⟩
  · exact ⟨_, O.stable s ⟨x,hx⟩, rfl⟩
  · change (coordinates _).symm (KPCuspCharts.embedding F (((D.ratio s : Fˣ) : F) * x)) =
      (coordinates _).symm (fun i => KPCuspCharts.embedding F ((D.ratio s : Fˣ) : F) i * KPCuspCharts.embedding F x i)
    congr 1
    funext i
    simp [KPCuspCharts.embedding]
 def dualScale (V : Submodule ℂ ℂ)
    (O : KPCuspGenuineMonodromy.CuspOutput (ζ := ζ) (hζ := hζ) S D ρ V) (s : S) :
    AddAut (Frequency S D ρ) where
  toFun ξ := ⟨linearScale (D.ratio s : Fˣ) ξ, scale_dual S D ρ V O s ξ⟩
  invFun ξ := ⟨linearScale (D.ratio s⁻¹ : Fˣ) ξ, scale_dual S D ρ V O s⁻¹ ξ⟩
  left_inv ξ := by
    apply Subtype.ext
    change linearScale (D.ratio s⁻¹ : Fˣ) (linearScale (D.ratio s : Fˣ) ξ) = ξ
    rw [← scale_mul]
    simp only [map_inv, Subgroup.coe_inv, inv_mul_cancel]
    exact scale_one _
  right_inv ξ := by
    apply Subtype.ext
    change linearScale (D.ratio s : Fˣ) (linearScale (D.ratio s⁻¹ : Fˣ) ξ) = ξ
    rw [← scale_mul]
    simp only [map_inv, Subgroup.coe_inv, mul_inv_cancel]
    exact scale_one _
  map_add' ξ η := by apply Subtype.ext; exact (linearScale _).map_add _ _

structure CuspOutput (V : Submodule ℂ ℂ)
    (O : KPCuspGenuineMonodromy.CuspOutput (ζ := ζ) (hζ := hζ) S D ρ V) where
  kernel_discrete : DiscreteTopology (kernelEuclideanLattice S D ρ)

  kernel_full : letI := kernel_discrete; IsZLattice ℝ (kernelEuclideanLattice S D ρ)

  constantSystem : ConstantLocalSystem (ζ := ζ) (hζ := hζ) S D ρ V O

  gap : ∀ (B : Set (KPCuspCharts.Shape F)), IsCompact B →
    ∃ c : ℝ, 0 < c ∧ ∀ b ∈ B, ∀ ξ : Frequency S D ρ,
      (ξ : Euclidean (KPCuspLogShape.dimension F)) ≠ 0 →
      c ≤ shapeEnergy b ξ ∧ ∀ t : ℝ,
        4 * Real.pi ^ 2 * c * Real.exp (2 * t) ≤ horizontalEnergy t b ξ

theorem cusp_frequency_gap
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (G : KPCuspCharts.ChartOutput F hF S D) (V : Submodule ℂ ℂ)
    (O : KPCuspGenuineMonodromy.CuspOutput (ζ := ζ) (hζ := hζ) S D ρ V) :
    Nonempty (CuspOutput (ζ := ζ) (hζ := hζ) S D ρ V O) := by
  obtain ⟨hdisc, hfull⟩ := kernel_euclidean_full S D ρ hF G
  letI := hdisc
  letI := hfull
  obtain ⟨C⟩ := constantSystem_test S D ρ V O
  refine ⟨{ kernel_discrete := hdisc
            kernel_full := hfull
            constantSystem := C
            gap := ?_ }⟩
  intro B hB
  obtain ⟨c, hc, hgap⟩ := uniform_shortest_frequency _ (kernelEuclideanLattice S D ρ) B hB
  refine ⟨c, hc, ?_⟩
  intro b hb ξ hξ
  have hh := hgap b hb ξ hξ
  refine ⟨hh, fun t => ?_⟩
  unfold horizontalEnergy
  calc
    4 * Real.pi ^ 2 * c * Real.exp (2 * t) =
        (4 * Real.pi ^ 2 * Real.exp (2 * t)) * c := by ring
    _ ≤ (4 * Real.pi ^ 2 * Real.exp (2 * t)) * shapeEnergy b ξ :=
      mul_le_mul_of_nonneg_left hh (by positivity)

end Cusp
end KPCuspFrequencyGap

end DedekindZetaZeroFree

end
