import FixedPointTheorems.Sperner
import Mathlib.Analysis.Convex.PartitionOfUnity
import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.SplitIfs
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Nonsingular
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Logic.Equiv.Sum
import Mathlib.Logic.Equiv.Prod
import Mathlib.Order.Antisymmetrization
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Choose
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Int.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.GroupTheory.Perm.DomMulAct
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.Polynomial.Expand
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Positivity
import OAI.LinearAlgebra.MatrixMultiplication.Model

noncomputable section

/-! Fixed points of continuous maps on compact convex sets of real-valued functions. -/

namespace OAI.MatrixMultiplication.AuxiliarySeparation

open Set

/-- Schauder--Tychonoff for an arbitrary product of real lines. Compactness of the
set, rather than finite dimensionality of the ambient space, is the hypothesis. -/
theorem compact_convex_fixedPoint_of_continuous {I : Type*} {K : Set (I → ℝ)}
    (hKcompact : IsCompact K) (hKconvex : Convex ℝ K) (hKne : K.Nonempty)
    (g : (I → ℝ) → I → ℝ) (hg : ContinuousOn g K) (hm : MapsTo g K K) : ∃ x ∈ K, g x = x := by
  classical
  let f := hm.restrict
  have hf := hg.mapsToRestrict hm
  have := isCompact_iff_compactSpace.mp hKcompact
  obtain ⟨x₀, hx₀⟩ := hKne
  have hc (i : I) : Continuous fun x : K => x.1 i := (continuous_apply i).comp continuous_subtype_val
  refine (CompactSpace.iInter_nonempty
    (t := fun p : I × ℕ => {x : K | |(f x).1 p.1 - x.1 p.1| ≤ 1 / (p.2 + 1)})
    (fun p => isClosed_le (((hc _).comp hf).sub (hc _)).abs continuous_const) fun S => ?_).elim
    fun x hx => ⟨x, x.2, funext fun i => sub_eq_zero.1 (abs_nonpos_iff.1
      (ge_of_tendsto' tendsto_one_div_add_atTop_nhds_zero_nat fun n => mem_iInter.1 hx (i, n)))⟩
  let s := S.image Prod.fst
  let ε : ℝ := 1 / (S.sup Prod.snd + 1)
  let U : K → Set K := fun a => {x | ∀ i ∈ s, |a.1 i - x.1 i| < ε}
  have hU a : IsOpen (U a) := by
    simp [U, ofPred_forall]
    exact isOpen_biInter_finset fun i _ => isOpen_lt (continuous_const.sub (hc i)).abs continuous_const
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hU fun x _ =>
    mem_iUnion.2 ⟨x, fun i _ => by simp; positivity⟩
  obtain ⟨w, hw⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ (fun a : t => U a)
    (fun a => hU a) fun x hx => by
      obtain ⟨a, ha, h⟩ := mem_iUnion₂.1 (ht hx); exact mem_iUnion.2 ⟨⟨a, ha⟩, h⟩
  let e := (Fintype.equivFin t).symm
  let M : (Fin (Fintype.card t) → ℝ) → ℝ := fun v => max (∑ j, v j) 1
  have hM v : 0 < M v := lt_max_of_lt_right one_pos
  let c : (Fin (Fintype.card t) → ℝ) → Option (Fin (Fintype.card t)) → ℝ := fun v k =>
    k.elim (1 - (∑ j, v j) / M v) fun j => v j / M v
  let b : Set.Icc (0 : Fin (Fintype.card t) → ℝ) 1 → K := fun v => ⟨∑ k, c v.1 k • k.elim x₀ fun j => (e j).1.1,
    hKconvex.sum_mem (fun k _ => by
      cases k
      · exact sub_nonneg.2 ((div_le_one (hM _)).2 (le_max_left _ _))
      · exact div_nonneg (v.2.1 _) (hM _).le)
      (by simp [c, Fintype.sum_option, ← Finset.sum_div])
      fun k _ => by cases k <;> simp_all⟩
  have hb : Continuous b := by
    refine .subtype_mk ((continuous_finsetSum _ fun k _ =>
      (?_ : Continuous fun v => c v k).smul continuous_const).comp continuous_subtype_val) _
    cases k <;> dsimp [c, M, Option.elim] <;> fun_prop (disch := exact fun _ => (hM _).ne')
  obtain ⟨v, hv⟩ := fixed_point_unit_cube ⟨fun v => ⟨fun j => w (e j) (f (b v)),
    fun j => w.nonneg _ _, fun j => w.le_one _ _⟩,
    .subtype_mk (continuous_pi fun j => (w (e j)).continuous.comp (hf.comp hb)) _⟩
  have hv' j : w (e j) (f (b v)) = v.1 j := congrFun (congrArg Subtype.val hv) j
  have h1 : ∑ j, v.1 j = 1 := by
    simp_rw [← hv', e.sum_comp fun a => w a (f (b v))]
    simpa [finsum_eq_sum_of_fintype] using w.sum_eq_one (mem_univ (f (b v)))
  refine ⟨b v, mem_iInter₂.2 fun p hp => ?_⟩
  have hi : p.1 ∈ s := Finset.mem_image_of_mem _ hp
  have : (b v).1 p.1 - (f (b v)).1 p.1 = ∑ j, v.1 j * ((e j).1.1 p.1 - (f (b v)).1 p.1) := by
    simp [b, c, M, Fintype.sum_option, h1, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [mem_ofPred_eq, abs_sub_comm, this]
  calc _ ≤ ∑ j, v.1 j * ε := (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    _ ≤ _ := by
      rw [← Finset.sum_mul, h1, one_mul]
      unfold ε; gcongr; exact_mod_cast Finset.le_sup hp
  rw [abs_mul, abs_of_nonneg (v.2.1 j)]
  by_cases h : v.1 j = 0
  · simp_all
  exact mul_le_mul_of_nonneg_left (hw (e j) (subset_closure (by simp_all)) p.1 hi).le (v.2.1 j)


/-! Finite obstructions to normalized additive states: conic Carathéodory, rational Farkas,
and a compactness argument; certificates become catalysts in the group completion. -/



open Finset
open Finsupp (single single_apply linearCombination linearCombination_apply)

theorem cara {I E : Type*} [AddCommGroup E] [Module ℝ E] (B : I → E) (s : Finset I) (w : I → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) : ∃ t : Finset I, LinearIndependent ℝ (fun i : t ↦ B i) ∧
      ∃ v : t → ℝ, 0 ≤ v ∧ ∑ i, v i • B i = ∑ i ∈ s, w i • B i := by
  classical
  induction s using Finset.strongInduction generalizing w with | H s ih =>
  by_cases hs : LinearIndependent ℝ (fun i : s ↦ B i)
  · exact ⟨s, hs, fun i ↦ w i, fun i ↦ hw i i.2, sum_coe_sort s fun i ↦ w i • B i⟩
  obtain ⟨g, hg, i, hi, h0⟩ := not_linearIndepOn_finset_iff.1 hs
  wlog hgi : 0 < g i generalizing g
  · exact this (-g) (by simp_all) (by simp_all) (by simp; order)
  obtain ⟨j, hj, hmin⟩ := (s.filter (0 < g ·)).exists_min_image (fun j ↦ w j / g j)
    ⟨i, by grind⟩
  simp only [mem_filter] at hj hmin
  obtain ⟨t, ht, v, hv, he⟩ := ih _ (erase_ssubset hj.1) (fun k ↦ w k - w j / g j * g k)
    fun k hk ↦ sub_nonneg.2 <| by
      have hk := mem_of_mem_erase hk
      by_cases h : 0 < g k
      · exact (le_div_iff₀ h).1 (hmin k ⟨hk, h⟩)
      nlinarith [div_nonneg (hw j hj.1) hj.2.le, hw k hk]
  refine ⟨t, ht, v, hv, he.trans ?_⟩
  rw [sum_erase _ (by simp [hj.2.ne'])]
  simp [sub_smul, mul_smul, sum_sub_distrib, ← smul_sum, hg]

theorem farkas {I J : Type*} [Fintype I] [Fintype J] (A : I → J → ℤ) (u : J → ℤ)
    (hno : ∀ (t : Finset I) (m : ℕ), 0 < m → ∀ n : t → ℕ,
      ¬∀ j, ∑ i, (n i : ℤ) * A i j = -(m : ℤ) * u j) :
    ∃ L : (J → ℝ) →L[ℝ] ℝ, L (fun j ↦ (u j : ℝ)) = 1 ∧ ∀ i, 0 ≤ L fun j ↦ (A i j : ℝ) := by
  classical
  let B i j : ℝ := A i j
  have key : (PointedCone.hull ℝ (Set.range B) : Set (J → ℝ)) =
      ⋃ t : {t : Finset I // LinearIndependent ℝ fun i : t ↦ B i},
        Fintype.linearCombination ℝ (fun i : t.1 ↦ B i) '' Set.Ici 0 := by
    ext x
    constructor
    · intro hx
      obtain ⟨w, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hx
      obtain ⟨t, ht, v, hv, he⟩ := cara B univ (fun i ↦ w i) fun i _ ↦ (w i).2
      exact Set.mem_iUnion.2 ⟨⟨t, ht⟩, v, hv, by simpa [Fintype.linearCombination_apply,
        ← Nonneg.coe_smul] using he⟩
    simp only [Set.mem_iUnion]
    rintro ⟨t, v, hv, rfl⟩
    exact Submodule.sum_mem _ fun i _ ↦ PointedCone.smul_mem _ (hv i)
      (PointedCone.subset_hull ⟨i, rfl⟩)
  have hC : IsClosed (PointedCone.hull ℝ (Set.range B) : Set (J → ℝ)) :=
    key ▸ isClosed_iUnion_of_finite fun t ↦ (LinearMap.isClosedEmbedding_of_injective
      (LinearMap.ker_eq_bot.2 t.2.fintypeLinearCombination_injective)).isClosedMap _ isClosed_Ici
  obtain ⟨f, hf, hfu⟩ := ProperCone.hyperplane_separation_point ⟨_, hC⟩
    (x₀ := -fun j ↦ (u j : ℝ)) fun hx ↦ by
      change _ ∈ (PointedCone.hull ℝ (Set.range B) : Set (J → ℝ)) at hx
      rw [key, Set.mem_iUnion] at hx
      obtain ⟨⟨t, ht⟩, v, hv, he⟩ := hx
      obtain ⟨p, h1⟩ := Module.Projective.exists_dual_eq_one ℚ (one_ne_zero : (1 : ℝ) ≠ 0)
      have hp (z : ℤ) (r : ℝ) : p (r * z) = z * p r := by simpa [mul_comm] using map_zsmul p z r
      have hz (z : ℤ) : p z = z := by simpa [h1] using hp z 1
      have hq : ∀ j, ∑ i, p (v i) * A i j = -u j := fun j ↦ by
        simpa [B, mul_comm, Fintype.linearCombination_apply, hp, hz] using
          congrArg (fun x ↦ p (x j)) he
      have hqv : (fun i ↦ (p (v i) : ℝ)) = v := ht.fintypeLinearCombination_injective <| by
        rw [he]; ext j; simpa [Fintype.linearCombination_apply, B] using (mod_cast hq j :
          ∑ i, (p (v i) : ℝ) * A i j = -u j)
      have h0 i : 0 ≤ p (v i) := by have := hv i; rw [← hqv] at this; simpa using this
      have hc i : ∃ c : ℕ, (∏ i, (p (v i)).den : ℚ) * p (v i) = c := by
        obtain ⟨k, hk⟩ := dvd_prod_of_mem (fun i ↦ (p (v i)).den) (mem_univ i)
        refine ⟨k * (p (v i)).num.natAbs, ?_⟩
        rw [← Nat.cast_prod, hk]
        simp [Nat.cast_natAbs, abs_of_nonneg (Rat.num_nonneg.2 (h0 i)), ← Rat.mul_den_eq_num]
        ring
      choose c hc using hc
      refine hno t (∏ i, (p (v i)).den) (prod_pos fun i _ ↦ (p (v i)).den_pos) c fun j ↦ ?_
      exact_mod_cast (by simp only [← hc, mul_assoc, ← mul_sum, hq]; push_cast; ring :
        ∑ i, (c i : ℚ) * A i j = -(∏ i, (p (v i)).den : ℕ) * u j)
  simp at hfu
  exact ⟨(f fun j ↦ (u j : ℝ))⁻¹ • f, by simp [hfu.ne'], fun i ↦ mul_nonneg (inv_nonneg.2 hfu.le)
    (hf _ (PointedCone.subset_hull ⟨i, rfl⟩))⟩

variable {S : Type*} [CommSemiring S] [Preorder S]

/-- Homogeneous inequalities defining a normalized additive state. -/
inductive StateConstraint (S : Type*) [CommSemiring S] [Preorder S]
  | lower (x : S)
  | upper (x : S)
  | add (b : Bool) (x y : S)
  | order (x y : S) (h : x ≤ y)
  | detector (x : S) (h : 1 ≤ x)

/-- Additive restriction-monotone states with a fixed detector inequality. -/
def normalizedStates (R : S → ℕ) (d : S) (k : ℕ) : Set (S → ℝ) :=
  {f | (∀ x, 0 ≤ f x ∧ f x ≤ R x) ∧ f 1 = 1 ∧ (∀ x y, f (x + y) = f x + f y) ∧
    (∀ x y, x ≤ y → f x ≤ f y) ∧ ∀ x, 1 ≤ x → k * f x ≤ f (d * x)}

/-- Appendix A: without positive scalar-gain catalysts, a monotone character detects `k`.
Finite obstructions give a normalized state; normalized translates have fixed points on
frozen slices, and compactness yields a multiplicative state. -/
theorem exists_monotone_ringHom_of_no_catalyst (R : S → ℕ) (d : S) (k : ℕ)
    (hzero : ∀ x : S, 0 ≤ x) (hbound : ∀ x : S, x ≤ (R x : S))
    (hadd : ∀ a b c e : S, a ≤ b → c ≤ e → a + c ≤ b + e)
    (hno : ∀ (D s : S) (m : ℕ), 0 < m → (s = 0 ∨ 1 ≤ s) → ¬D + (m : S) + d * s ≤ D + (k : S) * s)
    (hmul : ∀ z x y : S, x ≤ y → z * x ≤ z * y) :
    ∃ χ : S →+* ℝ, Monotone χ ∧ k ≤ χ d := by
  classical
  have hne : (normalizedStates R d k).Nonempty := by
    let v : StateConstraint S → S →₀ ℤ := fun
      | .lower x => single x 1
      | .upper x => single 1 (R x : ℤ) - single x 1
      | .add b x y => (if b then 1 else -1 : ℤ) • (single (x + y) 1 - single x 1 - single y 1)
      | .order x y _ => single y 1 - single x 1
      | .detector x _ => single (d * x) 1 - single x (k : ℤ)
    refine (((isCompact_pi_infinite fun x ↦ isCompact_Icc (a := (0 : ℝ))
      (b := R x)).inter_right (isClosed_eq (continuous_apply 1) continuous_const)).inter_iInter_nonempty
      (fun c ↦ {f : S → ℝ | 0 ≤ linearCombination ℤ f (v c)}) (fun c ↦ isClosed_le continuous_const
        (by simp [linearCombination_apply, Finsupp.sum]; fun_prop)) fun F ↦ ?_).elim
      fun f ⟨⟨hB, (h1 : f 1 = 1)⟩, hf⟩ ↦ ?_
    swap
    · simp at hf
      refine ⟨f, hB, h1, fun x y ↦ ?_, fun x y h ↦ ?_, fun x h ↦ ?_⟩
      · have h₁ := hf (.add true x y)
        have h₂ := hf (.add false x y)
        simp [v] at h₁ h₂
        linarith
      · simpa [v] using hf (.order x y h)
      simpa [v, zsmul_eq_mul] using hf (.detector x h)
    let H := insert 1 (F.biUnion fun c ↦ (v c).support)
    let cs : F ⊕ (Bool × H) → StateConstraint S := fun
      | .inl c => c
      | .inr (b, x) => cond b (.upper x) (.lower x)
    have hH i x (hx : x ∉ H) : v (cs i) x = 0 := by
      rcases i with c | ⟨_ | _, y⟩
      · grind
      all_goals simp [cs, v, ne_of_mem_of_not_mem y.2 hx,
        ne_of_mem_of_not_mem (mem_insert_self 1 _) hx]
    obtain ⟨L, hL1, hL⟩ := farkas (fun i (j : H) ↦ v (cs i) j) (fun j ↦ single (1 : S) (1 : ℤ) j)
        fun t m hm n hn ↦ by
      have hsum : ∑ i : t, n i • v (cs i) = single 1 (-m : ℤ) := by
        ext x
        by_cases hx : x ∈ H
        · simpa [single_apply, -Finsupp.single_neg] using hn ⟨x, hx⟩
        simp [hH _ x hx, ne_of_mem_of_not_mem (mem_insert_self 1 _) hx]
      let η := Algebra.GrothendieckAddGroup.of (M := S)
      have hcast (n : ℕ) : η n = n • η 1 := by rw [← nsmul_one, map_nsmul]
      have : ∀ c, ∃ X Y Z : S, X ≤ Y ∧
          linearCombination ℤ η (v c) = η Y - η X + η (d * Z) - k • η Z ∧ (Z = 0 ∨ 1 ≤ Z) := by
        rintro (x | x | ⟨b, x, y⟩ | ⟨x, y, h⟩ | ⟨x, h⟩)
        · exact ⟨0, x, 0, hzero x, by simp [v], .inl rfl⟩
        · exact ⟨x, R x, 0, hbound x, by simp [v, hcast], .inl rfl⟩
        · exact ⟨0, 0, 0, le_rfl, by cases b <;> simp [v], .inl rfl⟩
        · exact ⟨x, y, 0, h, by simp [v], .inl rfl⟩
        exact ⟨0, 0, x, le_rfl, by simp [v], .inr h⟩
      choose X Y Z hXY hΦ hZ using this
      have hp (a b : S) (ha : a = 0 ∨ 1 ≤ a) (hb : b = 0 ∨ 1 ≤ b) : a + b = 0 ∨ 1 ≤ a + b := by
        rcases ha with rfl | ha
        · simpa
        exact .inr (ha.trans (by simpa using hadd _ _ _ _ le_rfl (hzero b)))
      have h2 := congrArg (linearCombination ℤ η) hsum
      simp only [map_sum, map_nsmul, hΦ, Finsupp.linearCombination_single] at h2
      have : AddLeftMono S := ⟨fun c _ _ h ↦ hadd _ _ _ _ le_rfl h⟩
      obtain ⟨C, hC⟩ := (AddLocalization.addMonoidOf ⊤).exists_of_eq (show η (m + ∑ i, n i • Y (cs i) +
          d * ∑ i, n i • Z (cs i)) = η (∑ i, n i • X (cs i) + k * ∑ i, n i • Z (cs i)) by
        rw [← nsmul_eq_mul]
        simp only [map_add, map_sum, map_nsmul, hcast, mul_sum, mul_smul_comm]
        simp only [smul_sub, smul_add, sum_add_distrib, sum_sub_distrib, smul_comm _ k, ← smul_sum, neg_smul, natCast_zsmul] at h2
        linear_combination (norm := abel) h2)
      refine hno ((C : S) + ∑ i, n i • Y (cs i)) (∑ i, n i • Z (cs i)) m hm
        (sum_induction _ _ hp (.inl rfl) fun i _ ↦ ?_) ?_
      · induction n i with
        | zero => simp
        | succ j ih => rw [succ_nsmul]; exact hp _ _ ih (hZ _)
      calc _ = C + ((m : S) + ∑ i, n i • Y (cs i) + d * ∑ i, n i • Z (cs i)) := by ring
        _ = _ := hC
        _ ≤ _ := hadd _ _ _ _ le_rfl (hadd _ _ _ _ (sum_le_sum fun i _ ↦
          nsmul_le_nsmul_right (hXY _) _) le_rfl)
        _ = _ := by ring
    let g (x : S) := L fun j : H ↦ if ↑j = x then (1 : ℝ) else 0
    have key (w : S →₀ ℤ) : linearCombination ℤ g w = L fun j ↦ (w j : ℝ) := by
      simp only [g, linearCombination_apply, Finsupp.sum, ← map_zsmul, ← map_sum]
      congr 1
      ext j
      simp_all
    have hc i := key _ ▸ hL i
    have hg1 : g 1 = 1 := by simpa using (key _).trans hL1
    refine ⟨g, ⟨fun x ↦ ?_, hg1⟩, Set.mem_iInter₂.2 fun c h ↦ hc (.inl ⟨c, h⟩)⟩
    by_cases hx : x ∈ H
    · have h₁ := hc (.inr (false, ⟨x, hx⟩))
      have h₂ := hc (.inr (true, ⟨x, hx⟩))
      simp [cs, v, hg1] at h₁ h₂
      grind
    simp [g, ne_of_mem_of_not_mem _ hx, ← Pi.zero_def]
  set N := normalizedStates R d k
  have h0 f (hf : f ∈ N) : f 0 = 0 := by simpa using hf.2.2.1 0 0
  have hpos f (hf : f ∈ N) w (hw : 1 ≤ w) : 0 < f w := by linarith [hf.2.1, hf.2.2.2.1 _ _ hw]
  have hT w (hw : 1 ≤ w) : Set.MapsTo (fun f x ↦ f (w * x) / f w) N N := fun f hf ↦ by
    have := hpos f hf w hw
    have hn (n : ℕ) x : f (n * x) = n * f x := by
      induction n <;> simp_all [add_mul, hf.2.2.1]
    refine ⟨fun x ↦ ⟨div_nonneg (hf.1 _).1 this.le, (div_le_iff₀ this).2 ?_⟩, by grind,
      fun x y ↦ by simp [mul_add, hf.2.2.1, add_div], fun x y h ↦ div_le_div_of_nonneg_right
        (hf.2.2.2.1 _ _ (hmul w x y h)) this.le, fun x hx ↦ ?_⟩
    · have := hf.2.2.2.1 _ _ (hmul w _ _ (hbound x)); rwa [mul_comm w (R x : S), hn] at this
    dsimp only; rw [mul_left_comm w d, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right (hf.2.2.2.2 _ (hw.trans (by simpa using hmul w _ _ hx)))
      this.le
  have hN : IsCompact N := (isCompact_univ_pi fun x ↦ isCompact_Icc (a := (0 : ℝ))
     ).of_isClosed_subset (by
    simp [N, normalizedStates, Set.ofPred_and, Set.ofPred_forall]
    repeat' first | apply IsClosed.inter | (apply isClosed_iInter; intro) |
      (apply isClosed_le <;> fun_prop) | (apply isClosed_eq <;> fun_prop)) fun f hf x _ ↦ hf.1 x
  have hcv : Convex ℝ N := fun f hf g hg a b ha hb hab ↦ by
    simp [N, normalizedStates, Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at *
    refine ⟨fun x ↦ ⟨by nlinarith [hf.1 x, hg.1 x], by nlinarith [hf.1 x, hg.1 x]⟩,
      by grind, fun x y ↦ by grind,
      fun x y h ↦ by nlinarith [hf.2.2.2.1 x y h, hg.2.2.2.1 x y h],
      fun x hx ↦ by nlinarith [hf.2.2.2.2 x hx, hg.2.2.2.2 x hx]⟩
  have key (t : Finset S) : ∀ K ⊆ N, IsCompact K → Convex ℝ K → K.Nonempty →
      (∀ w, 1 ≤ w → Set.MapsTo (fun f x ↦ f (w * x) / f w) K K) →
        ∃ f ∈ K, ∀ z ∈ t, ∀ x, f (z * x) = f z * f x := by
    induction t using Finset.induction_on with
    | empty => exact fun K _ _ _ ⟨f, hf⟩ _ ↦ ⟨f, hf, by simp⟩
    | insert z t _ ih =>
      intro K hKN hK hc hne hT
      have hz : 1 ≤ z + 1 := by simpa using hadd _ _ _ _ (hzero z) (le_refl (1 : S))
      obtain ⟨g, hg, hgg⟩ := compact_convex_fixedPoint_of_continuous hK hc hne _
        (continuousOn_pi.2 fun x ↦ (continuous_apply _).continuousOn.div
          (continuous_apply _).continuousOn fun f hf ↦ (hpos f (hKN hf) _ hz).ne') (hT _ hz)
      obtain ⟨f, ⟨hf, (hfz : ∀ x, f ((z + 1) * x) = g (z + 1) * f x)⟩, h⟩ :=
        ih (K ∩ {f | ∀ x, f ((z + 1) * x) = g (z + 1) * f x})
        (Set.inter_subset_left.trans hKN) (hK.inter_right (by
          simp [Set.ofPred_forall]
          exact isClosed_iInter fun x ↦ isClosed_eq (by fun_prop) (by fun_prop)))
        (hc.inter fun f hf g hg a b _ _ _ x ↦ by simp_all; ring)
        ⟨g, hg, fun x ↦ ((div_eq_iff (hpos g (hKN hg) _ hz).ne').1 (congrFun hgg x)).trans
          (mul_comm _ _)⟩
        fun w hw f ⟨hf, (hfz : ∀ x, f ((z + 1) * x) = g (z + 1) * f x)⟩ ↦
          ⟨hT w hw hf, fun x ↦ by simp [mul_left_comm w (z + 1), hfz]; ring⟩
      have := (hKN hf).2
      refine ⟨f, hf, (Finset.forall_mem_insert ..).2 ⟨fun x ↦ ?_, h⟩⟩
      have h1 := hfz x
      have h2 := hfz 1
      simp [add_mul, this.1, this.2.1] at h1 h2
      grind
  obtain ⟨f, hf, hm⟩ := hN.inter_iInter_nonempty (fun z ↦ {f : S → ℝ | ∀ x, f (z * x) = f z * f x})
    (fun z ↦ by
      simp [Set.ofPred_forall]
      exact isClosed_iInter fun x ↦ isClosed_eq (by fun_prop) (by fun_prop))
    fun t ↦ (key t N subset_rfl hN hcv hne hT).imp fun f ⟨hf, h⟩ ↦ ⟨hf, by simp_all⟩
  simp at hm
  exact ⟨⟨⟨⟨f, hf.2.1⟩, hm⟩, h0 f hf, hf.2.2.1⟩, fun _ _ ↦ hf.2.2.2.1 _ _,
    by simpa [hf.2.1] using hf.2.2.2.2 1 le_rfl⟩

end AuxiliarySeparation

/-! Finite coefficient tensors and their algebraic transformations. -/


namespace Foundation

abbrev Tensor (K X Y Z : Type*) := X → Y → Z → K

namespace Tensor


variable {K X Y Z X' Y' Z' : Type*} [CommSemiring K]

def rankOne (a : X → K) (b : Y → K) (c : Z → K) : Tensor K X Y Z :=
  fun x y z => a x * b y * c z

def RankAtMost (T : Tensor K X Y Z) (r : ℕ) : Prop :=
  ∃ (a : Fin r → X → K) (b : Fin r → Y → K) (c : Fin r → Z → K),
    T = fun x y z => ∑ i, rankOne (a i) (b i) (c i) x y z

def restrict [Fintype X] [Fintype Y] [Fintype Z]
    (A : X' → X → K) (B : Y' → Y → K) (C : Z' → Z → K)
    (T : Tensor K X Y Z) : Tensor K X' Y' Z' :=
  fun x' y' z' => ∑ x, ∑ y, ∑ z,
    A x' x * B y' y * C z' z * T x y z

def product {U V W : Type*} (T : Tensor K X Y Z) (S : Tensor K U V W) :
    Tensor K (X × U) (Y × V) (Z × W) :=
  fun x y z => T x.1 y.1 z.1 * S x.2 y.2 z.2

def directSum {ι : Type*} [DecidableEq ι] (T : ι → Tensor K X Y Z) :
    Tensor K (ι × X) (ι × Y) (ι × Z) :=
  fun x y z => if x.1 = y.1 ∧ x.1 = z.1 then T x.1 x.2 y.2 z.2 else 0

def power (T : Tensor K X Y Z) (n : ℕ) :
    Tensor K (Fin n → X) (Fin n → Y) (Fin n → Z) :=
  fun x y z => ∏ i, T (x i) (y i) (z i)

theorem RankAtMost.scale {T : Tensor K X Y Z} {r : ℕ}
    (h : RankAtMost T r) (u : K) :
    RankAtMost (fun x y z => u * T x y z) r := by
  rcases h with ⟨a, b, c, rfl⟩
  exact ⟨fun i x => u * a i x, b, c, by funext; simp [rankOne, Finset.mul_sum, mul_assoc]⟩

theorem rankAtMost_sum_rankOne {ι : Type*} [Fintype ι]
    (a : ι → X → K) (b : ι → Y → K) (c : ι → Z → K) :
    RankAtMost (fun x y z => ∑ i, rankOne (a i) (b i) (c i) x y z)
      (Fintype.card ι) := by
  classical
  exact ⟨_, _, _, funext₃ fun x y z =>
    ((Fintype.equivFin ι).symm.sum_comp fun i => rankOne (a i) (b i) (c i) x y z).symm⟩

theorem RankAtMost.product {U V W : Type*}
    {T : Tensor K X Y Z} {S : Tensor K U V W} {r s : ℕ}
    (hT : RankAtMost T r) (hS : RankAtMost S s) :
    RankAtMost (Tensor.product T S) (r * s) := by
  rcases hT with ⟨a, b, c, rfl⟩
  rcases hS with ⟨d, e, f, rfl⟩
  convert rankAtMost_sum_rankOne (fun i : Fin r × Fin s => fun x : X × U => a i.1 x.1 * d i.2 x.2)
    (fun i (y : Y × V) => b i.1 y.1 * e i.2 y.2) (fun i (z : Z × W) => c i.1 z.1 * f i.2 z.2) using 1
  · funext
    simp [Tensor.product, rankOne, Fintype.sum_prod_type, Finset.sum_mul_sum]
    ac_rfl
  simp

theorem RankAtMost.power {T : Tensor K X Y Z} {r : ℕ}
    (h : RankAtMost T r) (n : ℕ) : RankAtMost (Tensor.power T n) (r ^ n) := by
  rcases h with ⟨a, b, c, rfl⟩
  convert rankAtMost_sum_rankOne (fun f : Fin n → Fin r => fun x : Fin n → X => ∏ i, a (f i) (x i))
    (fun f (y : Fin n → Y) => ∏ i, b (f i) (y i)) (fun f (z : Fin n → Z) => ∏ i, c (f i) (z i)) using 1
  · funext
    simp [Tensor.power, rankOne, Fintype.prod_sum, Finset.prod_mul_distrib]
  simp

variable [Fintype X] [Fintype Y] [Fintype Z]

theorem RankAtMost.restrict {T : Tensor K X Y Z} {r : ℕ}
    (h : RankAtMost T r) (A : X' → X → K) (B : Y' → Y → K)
    (C : Z' → Z → K) : RankAtMost (Tensor.restrict A B C T) r := by
  rcases h with ⟨a, b, c, rfl⟩
  refine ⟨fun i x' => ∑ x, A x' x * a i x,
    fun i y' => ∑ y, B y' y * b i y,
    fun i z' => ∑ z, C z' z * c i z, ?_⟩
  funext
  simp [Tensor.restrict, rankOne, Finset.mul_sum,
    Finset.sum_comm (t := (Finset.univ : Finset (Fin r))), mul_comm, mul_left_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans
    ((Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm)

def dotPairing (U : Type*) [DecidableEq U] : Tensor K U U Unit := fun i j _ => if i = j then 1 else 0

def cyclic (T : Tensor K X Y Z) : Tensor K Y Z X := fun y z x => T x y z

theorem cyclic_directSum {ι : Type*} [DecidableEq ι] (T : ι → Tensor K X Y Z) :
    cyclic (directSum T) = directSum (fun i => cyclic (T i)) := by
  funext ⟨i, x⟩ ⟨j, y⟩ ⟨k, z⟩
  by_cases i = j <;> by_cases i = k <;> simp_all [cyclic, directSum, eq_comm]



def pullback (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z)
    (T : Tensor K X Y Z) : Tensor K X' Y' Z' :=
  fun x y z => T (fx x) (fy y) (fz z)

theorem pullback_eq_restrict [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z) (T : Tensor K X Y Z) :
    pullback fx fy fz T = restrict
      (fun x' x => if x = fx x' then 1 else 0)
      (fun y' y => if y = fy y' then 1 else 0)
      (fun z' z => if z = fz z' then 1 else 0) T := by
  funext
  simp [pullback, restrict, ite_mul, mul_ite]

theorem RankAtMost.pullback {T : Tensor K X Y Z} {r : ℕ}
    (h : RankAtMost T r) (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z) :
    RankAtMost (pullback fx fy fz T) r := by
  rcases h with ⟨a, b, c, rfl⟩
  exact ⟨fun i x => a i (fx x), fun i y => b i (fy y),
    fun i z => c i (fz z), rfl⟩



end Tensor

def matrixMultiplicationTensor {K : Type*} [CommSemiring K] (a b c : ℕ) :
    Tensor K (Fin a × Fin b) (Fin b × Fin c) (Fin c × Fin a) :=
  fun x y z => if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then 1 else 0



/-! Finite coefficient tensors and their algebraic transformations. -/



namespace Tensor

variable {K X Y Z : Type*} [CommSemiring K] [Nontrivial K]

theorem RankAtMost.card_le_of_identity {ι : Type*} [Fintype ι] [DecidableEq ι]
    {T : Tensor K X Y Z} {r : ℕ} (hT : RankAtMost T r)
    (x : ι → X) (y : ι → Y) (z : ι → Z)
    (hidentity : ∀ i j, T (x i) (y i) (z j) = if i = j then 1 else 0) :
    Fintype.card ι ≤ r := by
  rcases hT with ⟨a, b, c, heq⟩
  let L : Matrix ι (Fin r) K := fun i q => a q (x i) * b q (y i)
  let R : Matrix (Fin r) ι K := fun q j => c q (z j)
  have hmul : L * R = (1 : Matrix ι ι K) := by
    funext i j
    calc
      (∑ q, (a q (x i) * b q (y i)) * c q (z j)) = T (x i) (y i) (z j) :=
        (congrFun (congrFun (congrFun heq (x i)) (y i)) (z j)).symm
      _ = _ := hidentity i j
  have hinj : Function.Injective R.mulVecLin := by
    intro v w hvw
    have heq := congrArg L.mulVecLin hvw
    simpa only [← LinearMap.comp_apply, ← Matrix.mulVecLin_mul,
      hmul, Matrix.mulVecLin_one, LinearMap.id_apply] using heq
  simpa only [Fintype.card_fin] using card_le_of_injective K R.mulVecLin hinj

end MatrixMultiplication.Foundation.Tensor





/-!
# Exact tensor rank and its matrix multiplication exponent

The rank is the least size of an exact decomposition into simple tensors. The
exponent is the infimum of the finite matrix multiplication rank ratios from
Section 3; no attainment of this real infimum is assumed.
-/


open MatrixMultiplication.Foundation

namespace MatrixMultiplication.AuxiliarySeparation

variable {K : Type*} [CommSemiring K] [Nontrivial K]

/-- Every finite coefficient tensor has a finite exact rank decomposition. -/
theorem exists_rankAtMost {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) : ∃ r : ℕ, Tensor.RankAtMost T r := by
  classical
  let a : X × Y × Z → X → K := fun p x => if x = p.1 then T p.1 p.2.1 p.2.2 else 0
  let b : X × Y × Z → Y → K := fun p y => if y = p.2.1 then 1 else 0
  let c : X × Y × Z → Z → K := fun p z => if z = p.2.2 then 1 else 0
  refine ⟨Fintype.card (X × Y × Z), ?_⟩
  have heq : T = fun x y z => ∑ p, Tensor.rankOne (a p) (b p) (c p) x y z := by
    simp [a, b, c, Tensor.rankOne, Fintype.sum_prod_type, mul_ite]
  rw [heq]
  exact Tensor.rankAtMost_sum_rankOne a b c

/-- Exact rank of a finite tensor over the coefficient semiring. -/
def exactRank {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) : ℕ := by
  classical
  exact Nat.find (exists_rankAtMost T)

/-- The least exact rank comes with an actual rank decomposition. -/
theorem exactRank_spec {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) : Tensor.RankAtMost T (exactRank T) := by
  classical
  exact Nat.find_spec (exists_rankAtMost T)

/-- Every exact decomposition bounds the least rank. -/
theorem exactRank_le {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    {T : Tensor K X Y Z} {r : ℕ} (h : Tensor.RankAtMost T r) : exactRank T ≤ r := by
  classical
  exact Nat.find_min' (exists_rankAtMost T) h

/-- Exact rank cannot increase under a linear restriction. -/
theorem exactRank_restrict_le {X Y Z X' Y' Z' : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z']
    (T : Tensor K X Y Z) (A : X' → X → K) (B : Y' → Y → K)
    (C : Z' → Z → K) : exactRank (Tensor.restrict A B C T) ≤ exactRank T :=
  exactRank_le ((exactRank_spec T).restrict A B C)

/-- Independent bijections of the three coordinate sets preserve exact rank. -/
theorem exactRank_reindex {X Y Z X' Y' Z' : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z']
    (T : Tensor K X Y Z) (ex : X' ≃ X) (ey : Y' ≃ Y) (ez : Z' ≃ Z) :
    exactRank (Tensor.pullback ex ey ez T) = exactRank T := by
  apply le_antisymm (exactRank_le ((exactRank_spec T).pullback ex ey ez))
  have h := exactRank_le
    ((exactRank_spec (Tensor.pullback ex ey ez T)).pullback ex.symm ey.symm ez.symm)
  have heq : Tensor.pullback ex.symm ey.symm ez.symm (Tensor.pullback ex ey ez T) = T := by
    funext x y z
    simp [Tensor.pullback]
  simpa only [heq] using h

/-- Tensor product decompositions give the usual submultiplicative rank bound. -/
theorem exactRank_product_le {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor K X Y Z) (S : Tensor K U V W) :
    exactRank (Tensor.product T S) ≤ exactRank T * exactRank S :=
  exactRank_le ((exactRank_spec T).product (exactRank_spec S))

/-- Exact rank of the square matrix multiplication tensor. -/
def exactMatrixRank (K : Type*) [CommSemiring K] [Nontrivial K] (n : ℕ) : ℕ := exactRank ((matrixMultiplicationTensor (K := K)) n n n)

theorem exactMatrixRank_spec (n : ℕ) :
    Tensor.RankAtMost ((matrixMultiplicationTensor (K := K)) n n n) ((exactMatrixRank K) n) :=
  exactRank_spec _

theorem exactMatrixRank_lower {n : ℕ} (hn : 0 < n) : n ^ 2 ≤ exactMatrixRank K n := by
  simpa [Fintype.card_prod, pow_two] using (exactMatrixRank_spec n).card_le_of_identity
    (fun i : Fin n × Fin n => (i.2, (⟨0, hn⟩ : Fin n))) (fun i => (⟨0, hn⟩, i.1)) id
    fun i k => by simp [matrixMultiplicationTensor, Prod.ext_iff, eq_comm]

theorem le_logb_iff {n : ℕ} (hn : 2 ≤ n) {τ : ℝ} :
    τ ≤ Real.logb n (exactMatrixRank K n) ↔ (n : ℝ) ^ τ ≤ exactMatrixRank K n :=
  Real.le_logb_iff_rpow_le (mod_cast hn)
    (mod_cast (pow_pos (by omega) 2).trans_le (exactMatrixRank_lower (by omega)))

/-- The set of finite exact-rank exponents in the definition of `ν`. -/
def exactRankExponentSet (K : Type*) [CommSemiring K] [Nontrivial K] : Set ℝ :=
  {τ | ∃ n : ℕ, 2 ≤ n ∧ τ = Real.logb n ((exactMatrixRank K) n)}

/-- The exact-rank exponent `ν = inf_{n ≥ 2} log(R(Tₙ))/log(n)`. -/
def exactRankExponent (K : Type*) [CommSemiring K] [Nontrivial K] : ℝ := sInf (exactRankExponentSet K)

theorem two_le_of_mem : ∀ τ ∈ exactRankExponentSet K, 2 ≤ τ := by
  rintro _ ⟨n, hn, rfl⟩
  rw [le_logb_iff hn, Real.rpow_two]
  exact_mod_cast exactMatrixRank_lower (by omega)

theorem exactRankExponent_lower : 2 ≤ exactRankExponent K :=
  le_csInf ⟨_, 2, le_rfl, rfl⟩ two_le_of_mem

/-- The rank lower bound includes the one-dimensional boundary case. -/
theorem exactMatrixRank_rpow_lower_of_pos {n : ℕ} (hn : 0 < n) :
    (n : ℝ) ^ exactRankExponent K ≤ exactMatrixRank K n := by
  by_cases hn2 : 2 ≤ n
  · exact (le_logb_iff hn2).1 (csInf_le ⟨2, two_le_of_mem⟩ ⟨n, hn2, rfl⟩)
  obtain rfl : n = 1 := by omega
  simpa using exactMatrixRank_lower one_pos

/-- A strict upper bound for the infimum is witnessed by an actual finite block. -/
theorem exists_exactMatrixRank_lt_rpow {τ : ℝ} (hτ : exactRankExponent K < τ) :
    ∃ n : ℕ, 2 ≤ n ∧ (exactMatrixRank K n : ℝ) < (n : ℝ) ^ τ :=
  let ⟨_, ⟨n, hn, rfl⟩, hσ⟩ := exists_lt_of_csInf_lt (by exact ⟨_, 2, le_rfl, rfl⟩) hτ
  ⟨n, hn, not_le.1 fun h => hσ.not_ge ((le_logb_iff hn).2 h)⟩


/-!
# Removing polynomial overhead from exponential inequalities

The interpolation argument in Section 4 bounds tensor powers with an extra
linear factor. Such a factor does not change their exponential growth rate.
The statements below include eventual inequalities and constant factors, so
the same argument also removes fixed counting losses in entropy limits.
-/


open Filter

/-- Fixed multiplicative losses disappear on taking exponential growth rates. -/
theorem le_of_eventually_pow_le_const_mul_pow {a b C : ℝ} (ha : 0 ≤ a)
    (h : ∀ᶠ j : ℕ in atTop, b ^ j ≤ C * a ^ j) : b ≤ a := by
  by_contra! hab
  have hb := ha.trans_lt hab
  have := ge_of_tendsto ((tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg ha hb.le)
    ((div_lt_one hb).2 hab)).const_mul C) (h.mono fun j hj => show 1 ≤ C * (a / b) ^ j by
      rwa [div_pow, ← mul_div_assoc, le_div_iff₀ (pow_pos hb j), one_mul])
  norm_num at this

theorem rpow_exponent_le_of_nat_bound {a b C : ℝ}
    (hbound : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ^ a ≤ C * (n : ℝ) ^ b) :
    a ≤ b := by
  by_contra! hab
  obtain ⟨n, hn, h1⟩ := (((tendsto_rpow_atTop (sub_pos.2 hab)).comp
    tendsto_natCast_atTop_atTop).eventually_gt_atTop C |>.and (eventually_ge_atTop 1)).exists
  have : (0 : ℝ) < n := mod_cast h1
  rw [Function.comp, Real.rpow_sub this, lt_div_iff₀ (by positivity)] at hn
  grind


/-!
# Binary sums of finite coefficient tensors

The coordinate types of the summands may differ.  The identities below give
the explicit changes of coordinates needed for the tensor semiring, together
with the block-diagonal restriction maps.
-/



variable {K X Y Z U V W A B C : Type*} [CommSemiring K]

/-- The binary direct sum, with each of its three block labels retained. -/
def sumTensor (T : Tensor K X Y Z) (S : Tensor K U V W) :
    Tensor K (X ⊕ U) (Y ⊕ V) (Z ⊕ W)
  | .inl x, .inl y, .inl z => T x y z
  | .inr u, .inr v, .inr w => S u v w
  | _, _, _ => 0

/-- The block-diagonal sum of two restriction matrices. -/
def sumRestriction {X' U' : Type*} (f : X' → X → K) (g : U' → U → K) :
    (X' ⊕ U') → (X ⊕ U) → K
  | .inl x', .inl x => f x' x
  | .inr u', .inr u => g u' u
  | _, _ => 0

/-- Independent restrictions of both summands give a restriction of the sum. -/
theorem sumTensor_restrict
    {X' Y' Z' U' V' W' : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W]
    (f : X' → X → K) (g : Y' → Y → K) (h : Z' → Z → K)
    (f' : U' → U → K) (g' : V' → V → K) (h' : W' → W → K)
    (T : Tensor K X Y Z) (S : Tensor K U V W) :
    Tensor.restrict (sumRestriction f f') (sumRestriction g g')
      (sumRestriction h h') (sumTensor T S) =
      sumTensor (Tensor.restrict f g h T) (Tensor.restrict f' g' h' S) := by
  funext x y z
  cases x <;> cases y <;> cases z <;>
    simp [Tensor.restrict, sumRestriction, sumTensor, Fintype.sum_sum_type]


/-!
# Finite tensors modulo mutual restriction

Representatives have three natural-number dimensions and coefficients in `K`.
The order is actual linear restriction, and equality in the quotient is mutual
restriction. In particular, changing coordinates does not change the class.
-/



namespace TensorSemiring


variable {K : Type*} [CommSemiring K] [Nontrivial K]

variable {X Y Z U V W P Q R U' V' W' : Type*} [Fintype U'] [Fintype V'] [Fintype W']
variable [Fintype X] [Fintype Y] [Fintype Z]
variable [Fintype U] [Fintype V] [Fintype W]
variable [Fintype P] [Fintype Q] [Fintype R]

/-- `T` is obtained from `S` by three linear maps on its coordinate spaces. -/
def IsRestriction (T : Tensor K X Y Z) (S : Tensor K U V W) : Prop :=
  ∃ (A : X → U → K) (B : Y → V → K) (C : Z → W → K),
    T = Tensor.restrict A B C S

theorem IsRestriction.trans {T : Tensor K X Y Z} {S : Tensor K U V W}
    {L : Tensor K P Q R} (hTS : IsRestriction T S) (hSL : IsRestriction S L) :
    IsRestriction T L := by
  rcases hTS with ⟨A, B, C, rfl⟩
  rcases hSL with ⟨D, E, F, rfl⟩
  refine ⟨fun a x => ∑ u, A a u * D u x, fun b y => ∑ v, B b v * E v y, fun c z => ∑ w, C c w * F w z,
    ?_⟩
  funext
  simp [Tensor.restrict, Finset.sum_mul, Finset.mul_sum, Finset.sum_comm (s := (Finset.univ : Finset U))]
  simp [Finset.sum_comm (s := (Finset.univ : Finset V))]
  simp [Finset.sum_comm (s := (Finset.univ : Finset W)), mul_comm, mul_left_comm]

theorem IsRestriction.pullback (T : Tensor K X Y Z)
    (fx : U → X) (fy : V → Y) (fz : W → Z) :
    IsRestriction (Tensor.pullback fx fy fz T) T := by
  classical
  exact ⟨_, _, _, Tensor.pullback_eq_restrict fx fy fz T⟩

theorem IsRestriction.of_reindex (T : Tensor K X Y Z)
    (ex : U ≃ X) (ey : V ≃ Y) (ez : W ≃ Z) :
    IsRestriction T (Tensor.pullback ex ey ez T) := by
  convert IsRestriction.pullback (Tensor.pullback ex ey ez T) ex.symm ey.symm ez.symm
  funext; simp [Tensor.pullback]

theorem IsRestriction.product {T : Tensor K X Y Z} {S : Tensor K U V W}
    {T' : Tensor K P Q R} {S' : Tensor K U' V' W'}
    (hT : IsRestriction T T') (hS : IsRestriction S S') :
    IsRestriction (Tensor.product T S) (Tensor.product T' S') := by
  rcases hT with ⟨A, B, C, rfl⟩
  rcases hS with ⟨D, E, F, rfl⟩
  refine ⟨fun x u => A x.1 u.1 * D x.2 u.2, fun y v => B y.1 v.1 * E y.2 v.2,
    fun z w => C z.1 w.1 * F z.2 w.2, ?_⟩
  funext
  simp [Tensor.restrict, Tensor.product, Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum,
    Finset.sum_comm (s := (Finset.univ : Finset U'))]
  simp [Finset.sum_comm (s := (Finset.univ : Finset V'))]
  simp [Finset.sum_comm (s := (Finset.univ : Finset W')), mul_comm, mul_left_comm]

theorem IsRestriction.sum {T : Tensor K X Y Z} {S : Tensor K U V W}
    {T' : Tensor K P Q R} {S' : Tensor K U' V' W'}
    (hT : IsRestriction T T') (hS : IsRestriction S S') :
    IsRestriction (sumTensor T S) (sumTensor T' S') := by
  rcases hT with ⟨A, B, C, rfl⟩
  rcases hS with ⟨D, E, F, rfl⟩
  exact ⟨_, _, _, (sumTensor_restrict A B C D E F T' S').symm⟩

theorem IsRestriction.zero (S : Tensor K U V W) :
    IsRestriction (0 : Tensor K X Y Z) S := by
  refine ⟨0, 0, 0, ?_⟩
  funext x y z
  simp [Tensor.restrict]

theorem IsRestriction.rank_le {T : Tensor K X Y Z} {S : Tensor K U V W}
    (h : IsRestriction T S) : exactRank T ≤ exactRank S := by
  rcases h with ⟨A, B, C, rfl⟩
  exact exactRank_restrict_le S A B C

theorem IsRestriction.eq_zero_of_zero {T : Tensor K X Y Z}
    (h : IsRestriction T (0 : Tensor K U V W)) : T = 0 := by
  rcases h with ⟨A, B, C, h⟩
  funext x y z
  rw [h]
  simp [Tensor.restrict]

/-- A set-sized presentation of any finite coefficient tensor over `K`. -/
structure FiniteTensor (K : Type*) [CommSemiring K] [Nontrivial K] where
  nx : ℕ
  ny : ℕ
  nz : ℕ
  coeff : Tensor K (Fin nx) (Fin ny) (Fin nz)

namespace FiniteTensor

/-- Replace arbitrary finite coordinate sets by standard finite sets. -/
def ofTensor (T : Tensor K X Y Z) : (FiniteTensor K) where
  nx := Fintype.card X
  ny := Fintype.card Y
  nz := Fintype.card Z
  coeff := Tensor.pullback (Fintype.equivFin X).symm
    (Fintype.equivFin Y).symm (Fintype.equivFin Z).symm T

instance : LE (FiniteTensor K) := ⟨fun T S => IsRestriction T.coeff S.coeff⟩

instance : Preorder (FiniteTensor K) where
  le_refl T := IsRestriction.pullback T.coeff id id id
  le_trans _ _ _ := IsRestriction.trans

theorem ofTensor_le_iff (T : Tensor K X Y Z) (S : Tensor K U V W) :
    ofTensor T ≤ ofTensor S ↔ IsRestriction T S :=
  ⟨fun h => (IsRestriction.of_reindex T _ _ _).trans (IsRestriction.trans h (.pullback S _ _ _)),
    fun h => (IsRestriction.pullback T _ _ _).trans (h.trans (.of_reindex S _ _ _))⟩

def product (T S : (FiniteTensor K)) : (FiniteTensor K) :=
  ofTensor (Tensor.product T.coeff S.coeff)

def sum (T S : (FiniteTensor K)) : (FiniteTensor K) :=
  ofTensor (sumTensor T.coeff S.coeff)

theorem product_mono {T T' S S' : (FiniteTensor K)} (hT : T ≤ T') (hS : S ≤ S') :
    product T S ≤ product T' S' :=
  (ofTensor_le_iff _ _).mpr (IsRestriction.product hT hS)

theorem sum_mono {T T' S S' : (FiniteTensor K)} (hT : T ≤ T') (hS : S ≤ S') :
    sum T S ≤ sum T' S' :=
  (ofTensor_le_iff _ _).mpr (IsRestriction.sum hT hS)

end FiniteTensor

variable (K) in
/-- Finite tensors over `K`, with two presentations identified exactly when
each is a linear restriction of the other. -/
abbrev TensorClass := Antisymmetrization (FiniteTensor K) (· ≤ ·)

/-- The class of a finite tensor presentation. -/
def tensorClass (T : (FiniteTensor K)) : (TensorClass K) := toAntisymmetrization (· ≤ ·) T

theorem tensorClass_eq_iff (T S : (FiniteTensor K)) :
    tensorClass T = tensorClass S ↔ T ≤ S ∧ S ≤ T :=
  toAntisymmetrization_eq (· ≤ ·) T S

/-- The quotient class of a tensor on any three finite coordinate sets. -/
def classOf (T : Tensor K X Y Z) : (TensorClass K) := tensorClass (FiniteTensor.ofTensor T)

theorem classOf_le_iff (T : Tensor K X Y Z) (S : Tensor K U V W) :
    classOf T ≤ classOf S ↔ IsRestriction T S := FiniteTensor.ofTensor_le_iff T S

theorem classOf_eq_iff (T : Tensor K X Y Z) (S : Tensor K U V W) :
    classOf T = classOf S ↔ IsRestriction T S ∧ IsRestriction S T := by
  rw [le_antisymm_iff, classOf_le_iff, classOf_le_iff]

theorem classOf_reindex (T : Tensor K X Y Z) (ex : U ≃ X) (ey : V ≃ Y) (ez : W ≃ Z) :
    classOf (Tensor.pullback ex ey ez T) = classOf T :=
  (classOf_eq_iff _ _).mpr ⟨IsRestriction.pullback T ex ey ez,
    IsRestriction.of_reindex T ex ey ez⟩

theorem classOf_eq_of_reindex {T : Tensor K X Y Z} {S : Tensor K U V W}
    (ex : X ≃ U) (ey : Y ≃ V) (ez : Z ≃ W)
    (h : Tensor.pullback ex ey ez S = T) : classOf T = classOf S :=
  (congrArg classOf h).symm.trans (classOf_reindex S ex ey ez)

theorem classOf_coeff (T : (FiniteTensor K)) : classOf T.coeff = tensorClass T := by
  apply (tensorClass_eq_iff _ _).mpr
  exact ⟨IsRestriction.pullback T.coeff _ _ _, IsRestriction.of_reindex T.coeff _ _ _⟩

instance : Mul (TensorClass K) where
  mul := Quotient.map₂ FiniteTensor.product (by
    intro T T' hT S S' hS
    exact ⟨FiniteTensor.product_mono hT.1 hS.1,
      FiniteTensor.product_mono hT.2 hS.2⟩)

instance : Add (TensorClass K) where
  add := Quotient.map₂ FiniteTensor.sum (by
    intro T T' hT S S' hS
    exact ⟨FiniteTensor.sum_mono hT.1 hS.1, FiniteTensor.sum_mono hT.2 hS.2⟩)

theorem classOf_product (T : Tensor K X Y Z) (S : Tensor K U V W) :
    classOf (Tensor.product T S) = classOf T * classOf S := by
  symm
  exact classOf_reindex (Tensor.product T S)
    (Equiv.prodCongr (Fintype.equivFin X).symm (Fintype.equivFin U).symm)
    (Equiv.prodCongr (Fintype.equivFin Y).symm (Fintype.equivFin V).symm)
    (Equiv.prodCongr (Fintype.equivFin Z).symm (Fintype.equivFin W).symm)

theorem classOf_sum (T : Tensor K X Y Z) (S : Tensor K U V W) :
    classOf (sumTensor T S) = classOf T + classOf S := by
  symm
  exact classOf_eq_of_reindex (.sumCongr (Fintype.equivFin X).symm (Fintype.equivFin U).symm)
    (.sumCongr (Fintype.equivFin Y).symm (Fintype.equivFin V).symm)
    (.sumCongr (Fintype.equivFin Z).symm (Fintype.equivFin W).symm)
    (by funext x y z; cases x <;> cases y <;> cases z <;> rfl)

instance : Zero (TensorClass K) := ⟨classOf (0 : Tensor K Empty Empty Empty)⟩
instance : One (TensorClass K) := ⟨classOf (fun (_ _ _ : PUnit.{1}) => (1 : K))⟩

theorem classOf_zero :
    classOf (0 : Tensor K X Y Z) = 0 :=
  (classOf_eq_iff _ _).mpr ⟨IsRestriction.zero _, IsRestriction.zero _⟩

theorem mk_eq (T : FiniteTensor K) : (Quot.mk _ T : TensorClass K) = classOf T.coeff :=
  (classOf_coeff T).symm

theorem zero_def : (0 : TensorClass K) = classOf (0 : Tensor K Empty Empty Empty) := rfl

theorem one_def : (1 : TensorClass K) = classOf (fun (_ _ _ : PUnit.{1}) => (1 : K)) := rfl

local macro "cls" : tactic => `(tactic| ((repeat rintro ⟨_⟩); simp only [mk_eq, zero_def, one_def,
  ← classOf_sum, ← classOf_product]))

instance : CommSemiring (TensorClass K) where
  add_assoc := by
    cls; exact classOf_eq_of_reindex (.sumAssoc _ _ _) (.sumAssoc _ _ _) (.sumAssoc _ _ _) (by
      funext x y z; rcases x with (x | x) | x <;> rcases y with (y | y) | y <;> rcases z with (z | z) | z <;> rfl)
  add_comm := by
    cls; exact classOf_eq_of_reindex (.sumComm _ _) (.sumComm _ _) (.sumComm _ _) (by
      funext x y z; cases x <;> cases y <;> cases z <;> rfl)
  zero_add := by
    cls; exact (classOf_eq_of_reindex (Equiv.emptySum _ _).symm (Equiv.emptySum _ _).symm
      (Equiv.emptySum _ _).symm rfl).symm
  add_zero := by
    cls; exact (classOf_eq_of_reindex (Equiv.sumEmpty _ _).symm (Equiv.sumEmpty _ _).symm
      (Equiv.sumEmpty _ _).symm rfl).symm
  nsmul := nsmulRec
  mul_assoc := by
    cls; exact classOf_eq_of_reindex (.prodAssoc _ _ _) (.prodAssoc _ _ _) (.prodAssoc _ _ _) (by
      funext x y z; simp [Tensor.pullback, Tensor.product, mul_assoc])
  mul_comm := by
    cls; exact classOf_eq_of_reindex (.prodComm _ _) (.prodComm _ _) (.prodComm _ _) (by
      funext x y z; simp [Tensor.pullback, Tensor.product, mul_comm])
  one_mul := by
    cls; exact (classOf_eq_of_reindex (Equiv.punitProd _).symm (Equiv.punitProd _).symm
      (Equiv.punitProd _).symm (by funext x y z; simp [Tensor.pullback, Tensor.product])).symm
  mul_one := by
    cls; exact (classOf_eq_of_reindex (Equiv.prodPUnit _).symm (Equiv.prodPUnit _).symm
      (Equiv.prodPUnit _).symm (by funext x y z; simp [Tensor.pullback, Tensor.product])).symm
  zero_mul := by cls; rw [Subsingleton.elim (Tensor.product _ _) 0, classOf_zero, classOf_zero]
  mul_zero := by cls; rw [Subsingleton.elim (Tensor.product _ _) 0, classOf_zero, classOf_zero]
  left_distrib := by
    cls; exact (classOf_eq_of_reindex (Equiv.prodSumDistrib _ _ _).symm (Equiv.prodSumDistrib _ _ _).symm
      (Equiv.prodSumDistrib _ _ _).symm (by
        funext x y z; cases x <;> cases y <;> cases z <;> simp [Tensor.pullback, Tensor.product, sumTensor])).symm
  right_distrib := by
    cls; exact (classOf_eq_of_reindex (Equiv.sumProdDistrib _ _ _).symm (Equiv.sumProdDistrib _ _ _).symm
      (Equiv.sumProdDistrib _ _ _).symm (by
        funext x y z; cases x <;> cases y <;> cases z <;> simp [Tensor.pullback, Tensor.product, sumTensor])).symm

theorem mul_mono : ∀ {T T' S S' : TensorClass K}, T ≤ T' → S ≤ S' → T * S ≤ T' * S' := by
  rintro ⟨⟩ ⟨⟩ ⟨⟩ ⟨⟩; exact FiniteTensor.product_mono

theorem add_mono : ∀ {T T' S S' : TensorClass K}, T ≤ T' → S ≤ S' → T + S ≤ T' + S' := by
  rintro ⟨⟩ ⟨⟩ ⟨⟩ ⟨⟩; exact FiniteTensor.sum_mono

/-- Every tensor class is nonnegative in the restriction order. -/
theorem zero_le : ∀ T : TensorClass K, 0 ≤ T := by
  cls; exact (classOf_le_iff _ _).2 (.zero _)

/-- Exact rank descends to mutual-restriction classes. -/
def rank : TensorClass K → ℕ := Quotient.lift (fun T : FiniteTensor K => exactRank T.coeff)
  fun _ _ h => le_antisymm h.1.rank_le h.2.rank_le

@[simp] theorem rank_classOf (T : Tensor K X Y Z) : rank (classOf T) = exactRank T :=
  exactRank_reindex T _ _ _

theorem rank_mono : ∀ {T S : TensorClass K}, T ≤ S → rank T ≤ rank S := by
  rintro ⟨⟩ ⟨⟩; exact IsRestriction.rank_le

theorem rank_mul_le : ∀ T S : TensorClass K, rank (T * S) ≤ rank T * rank S := by
  cls; simp; exact exactRank_product_le _ _

/-- Square matrix multiplication as an element of the tensor semiring. -/
def matrixClass (n : ℕ) : TensorClass K := classOf (matrixMultiplicationTensor n n n)

theorem rank_matrixClass (n : ℕ) : rank (matrixClass (K := K) n) = exactMatrixRank K n :=
  rank_classOf _

theorem matrixClass_mul (m n : ℕ) : matrixClass (K := K) (m * n) = matrixClass m * matrixClass n := by
  rw [matrixClass, matrixClass, matrixClass, ← classOf_product]
  let e := (Equiv.prodCongr finProdFinEquiv.symm finProdFinEquiv.symm).trans (Equiv.prodProdProdComm (Fin m) (Fin n) (Fin m) (Fin n))
  refine classOf_eq_of_reindex e e e (funext₃ fun x y z => ?_)
  have key (a b : Fin (m * n)) : a = b ↔ a.modNat = b.modNat ∧ a.divNat = b.divNat := by
    rw [← finProdFinEquiv.symm.injective.eq_iff]; simp [Prod.ext_iff, and_comm]
  simp [e, Tensor.pullback, Tensor.product, matrixMultiplicationTensor, key, ← ite_and]
  grind

@[simp] theorem matrixClass_one : matrixClass (K := K) 1 = 1 := by
  refine classOf_eq_of_reindex (Fintype.equivOfCardEq (by simp)) (Fintype.equivOfCardEq (by simp))
    (Fintype.equivOfCardEq (by simp)) (funext₃ fun x y z => ?_)
  simp [Tensor.pullback, matrixMultiplicationTensor, Fin.fin_one_eq_zero]

theorem matrixClass_pow (m j : ℕ) : matrixClass (K := K) (m ^ j) = matrixClass m ^ j := by
  induction j <;> simp_all [pow_succ, matrixClass_mul]

theorem classOf_eq_zero_iff (T : Tensor K X Y Z) : classOf T = 0 ↔ T = 0 :=
  ⟨fun h => ((classOf_eq_iff T (0 : Tensor K Empty Empty Empty)).1 h).1.eq_zero_of_zero,
    by rintro rfl; exact classOf_zero⟩

end TensorSemiring

/-!
# Characters of finite tensors over a commutative coefficient semiring

The tensor operations in this file are the coefficient operations from
`MatrixMultiplication.Foundation.Tensor`. A character is an assumption on those
operations, not an assertion that a character exists. Restriction monotonicity
forces invariance under independent invertible changes of coordinates, so this
interface descends to the mutual-restriction classes of Section 3 of the paper.
-/






/-- The scalar multiplication tensor, the multiplicative unit. -/
def unitTensor : Tensor K PUnit PUnit PUnit := fun _ _ _ => 1

/-- The direct sum of `r` scalar multiplication tensors, in diagonal coordinates. -/
def scalarTensor (r : ℕ) : Tensor K (Fin r) (Fin r) (Fin r) :=
  fun i j k => if i = j ∧ i = k then 1 else 0

/-- A normalized, additive, multiplicative, restriction-monotone tensor valuation.

Index types vary over all finite types in `Type`. No character-existence result is
included among the fields or claimed by this definition.
-/
structure Character (K : Type*) [CommSemiring K] where
  value : {X Y Z : Type} → [Fintype X] → [Fintype Y] → [Fintype Z] →
    Tensor K X Y Z → ℝ
  nonneg : ∀ {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z), 0 ≤ value T
  map_zero : ∀ {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z],
    value (0 : Tensor K X Y Z) = 0
  map_one : value unitTensor = 1
  map_directSum : ∀ {ι X Y Z : Type} [Fintype ι] [DecidableEq ι]
    [Fintype X] [Fintype Y] [Fintype Z] (T : ι → Tensor K X Y Z),
    value (Tensor.directSum T) = ∑ i, value (T i)
  map_product : ∀ {X Y Z U V W : Type} [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor K X Y Z) (S : Tensor K U V W),
    value (Tensor.product T S) = value T * value S
  monotone : ∀ {X Y Z X' Y' Z' : Type}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z']
    (T : Tensor K X Y Z) (A : X' → X → K)
    (B : Y' → Y → K) (C : Z' → Z → K),
    value (Tensor.restrict A B C T) ≤ value T

namespace Character

variable (χ : (Character K))
variable {X Y Z X' Y' Z' : Type}
variable [Fintype X] [Fintype Y] [Fintype Z]
variable [Fintype X'] [Fintype Y'] [Fintype Z']

/-- Coordinate pullbacks are restrictions. -/
theorem value_pullback_le (T : Tensor K X Y Z)
    (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z) :
    χ.value (Tensor.pullback fx fy fz T) ≤ χ.value T := by
  classical
  rw [Tensor.pullback_eq_restrict]
  exact χ.monotone T _ _ _

/-- Independent coordinate bijections preserve a character. -/
theorem value_reindex (T : Tensor K X Y Z)
    (ex : X' ≃ X) (ey : Y' ≃ Y) (ez : Z' ≃ Z) :
    χ.value (Tensor.pullback ex ey ez T) = χ.value T := by
  refine le_antisymm (χ.value_pullback_le T ex ey ez) ?_
  convert χ.value_pullback_le (Tensor.pullback ex ey ez T) ex.symm ey.symm ez.symm
  funext; simp [Tensor.pullback]

/-- An integer scalar tensor has its expected character value. -/
theorem value_scalarTensor (r : ℕ) : χ.value (scalarTensor r) = r := by
  rw [← show Tensor.pullback (Equiv.prodPUnit (Fin r)).symm (Equiv.prodPUnit (Fin r)).symm
    (Equiv.prodPUnit (Fin r)).symm (Tensor.directSum fun _ => unitTensor) = scalarTensor r
    from rfl, χ.value_reindex, χ.map_directSum]
  simp [χ.map_one]

omit [Fintype X] [Fintype Y] [Fintype Z] in
/-- Restricting a diagonal scalar tensor realizes a rank decomposition. -/
theorem restrict_scalarTensor (r : ℕ) (a : Fin r → X → K)
    (b : Fin r → Y → K) (c : Fin r → Z → K) :
    Tensor.restrict (fun x i => a i x) (fun y i => b i y) (fun z i => c i z)
      (scalarTensor r) =
      fun x y z => ∑ i, Tensor.rankOne (a i) (b i) (c i) x y z := by
  classical
  funext x y z
  simp [Tensor.restrict, scalarTensor, Tensor.rankOne, mul_ite, ite_and]

/-- Character values are bounded by every exact rank decomposition size. -/
theorem value_le_rank {T : Tensor K X Y Z} {r : ℕ} (h : Tensor.RankAtMost T r) :
    χ.value T ≤ r := by
  rcases h with ⟨a, b, c, rfl⟩
  rw [← restrict_scalarTensor r a b c]
  exact (χ.monotone (scalarTensor r) _ _ _).trans_eq (χ.value_scalarTensor r)

/-- A unit coefficient gives a scalar restriction over every commutative semiring. -/
theorem one_le_value_of_coefficient_one {T : Tensor K X Y Z}
    (hT : ∃ x y z, T x y z = 1) : 1 ≤ χ.value T := by
  classical
  obtain ⟨x, y, z, hxyz⟩ := hT
  convert χ.monotone T (fun _ x' => if x' = x then 1 else 0)
    (fun _ y' => if y' = y then 1 else 0) (fun _ z' => if z' = z then 1 else 0)
  rw [← χ.map_one]; congr; funext
  simp [Tensor.restrict, unitTensor, ite_mul, mul_ite, hxyz]

end Character


/-!
# Natural numbers and rank in the tensor semiring

The natural number `r` is the class of the diagonal scalar tensor with `r`
terms.  Consequently, comparison with `r` in the restriction order is exactly
the existence of a rank decomposition with `r` terms.
-/





variable {K : Type*} [CommSemiring K] [Nontrivial K]

/-- Splitting the diagonal index set splits its scalar tensor into two blocks. -/
theorem scalarTensor_add_reindex (m n : ℕ) :
    Tensor.pullback (finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n))
      finSumFinEquiv finSumFinEquiv (scalarTensor (m + n)) =
      sumTensor (scalarTensor m) ((scalarTensor (K := K)) n) := by
  funext x y z
  simp [Tensor.pullback, scalarTensor,
    (finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n)).injective.eq_iff]
  cases x <;> cases y <;> cases z <;> simp [sumTensor, scalarTensor]

/-- A diagonal scalar tensor has its evident decomposition into simple terms. -/
theorem scalarTensor_rankAtMost (r : ℕ) : Tensor.RankAtMost ((scalarTensor (K := K)) r) r := by
  classical
  refine ⟨(fun i x => if x = i then 1 else 0),
    (fun i y => if y = i then 1 else 0), (fun i z => if z = i then 1 else 0), ?_⟩
  funext x y z
  simp [scalarTensor, Tensor.rankOne, mul_ite, ite_and]
  grind

/-- The diagonal flattening also gives the matching lower bound. -/
theorem exactRank_scalarTensor (r : ℕ) : exactRank ((scalarTensor (K := K)) r) = r := by
  apply le_antisymm (exactRank_le (scalarTensor_rankAtMost r))
  have h := (exactRank_spec ((scalarTensor (K := K)) r)).card_le_of_identity id id id
    (by intro i j; simp [scalarTensor])
  simpa only [Fintype.card_fin] using h

namespace TensorSemiring

/-- Addition of the diagonal index sets is semiring addition. -/
theorem classOf_scalarTensor_add (m n : ℕ) :
    classOf (scalarTensor (m + n)) =
      classOf (scalarTensor m) + classOf ((scalarTensor (K := K)) n) := by
  have h := classOf_eq_of_reindex _ _ _ (scalarTensor_add_reindex (K := K) m n)
  exact h.symm.trans (classOf_sum _ _)

@[simp] theorem classOf_scalarTensor_zero :
    classOf (scalarTensor 0) = (0 : (TensorClass K)) := by
  have h : (scalarTensor (K := K)) 0 = 0 := by
    funext x
    exact Fin.elim0 x
  rw [h, classOf_zero]

@[simp] theorem classOf_scalarTensor_one :
    classOf (scalarTensor 1) = (1 : (TensorClass K)) := by
  change classOf (scalarTensor 1) = classOf (fun _ _ _ => (1 : K))
  apply classOf_eq_of_reindex (Equiv.equivPUnit (Fin 1))
    (Equiv.equivPUnit (Fin 1)) (Equiv.equivPUnit (Fin 1))
  funext x y z
  simp [Tensor.pullback, scalarTensor, Subsingleton.elim x y, Subsingleton.elim y z]

/-- Natural numbers in the quotient semiring have their intended tensor meaning. -/
theorem classOf_scalarTensor (r : ℕ) :
    classOf (scalarTensor r) = (r : (TensorClass K)) := by
  induction r <;> simp_all [classOf_scalarTensor_add]

/-- Exact rank decompositions are precisely restrictions of diagonal tensors. -/
theorem rankAtMost_iff_isRestriction_scalarTensor
    {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) (r : ℕ) :
    Tensor.RankAtMost T r ↔ IsRestriction T (scalarTensor r) := by
  constructor
  · rintro ⟨a, b, c, h⟩
    refine ⟨(fun x i => a i x), (fun y i => b i y), (fun z i => c i z), ?_⟩
    apply h.trans
    funext x y z
    simp [Tensor.restrict, scalarTensor, Tensor.rankOne, mul_ite, ite_and]
  rintro ⟨A, B, C, rfl⟩
  exact (scalarTensor_rankAtMost r).restrict A B C

/-- The restriction order below a natural number is exactly the usual rank bound. -/
theorem classOf_le_nat_iff_rankAtMost
    {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) (r : ℕ) :
    classOf T ≤ (r : (TensorClass K)) ↔ Tensor.RankAtMost T r := by
  rw [← classOf_scalarTensor r, classOf_le_iff]
  exact (rankAtMost_iff_isRestriction_scalarTensor T r).symm

/-- Rank takes its usual value on natural numbers in the tensor semiring. -/
theorem rank_natCast (r : ℕ) : rank (r : (TensorClass K)) = r := by
  rw [← classOf_scalarTensor r, rank_classOf, exactRank_scalarTensor]

/-- The rank is a natural-number upper bound in the restriction order. -/
theorem le_rank (T : (TensorClass K)) : T ≤ (rank T : (TensorClass K)) := by
  induction T using Quotient.inductionOn with
  | h T =>
    change tensorClass T ≤ (exactRank T.coeff : (TensorClass K))
    rw [← classOf_coeff T]
    exact (classOf_le_nat_iff_rankAtMost T.coeff (exactRank T.coeff)).mpr
      (exactRank_spec T.coeff)

end TensorSemiring


end MatrixMultiplication.AuxiliarySeparation


end OAI


/-! A fixed finite catalyst cannot make `k` copies dominate multiplication by
`T_d` in the tensor semiring unless `k ≥ d^ν`. -/


open OAI.MatrixMultiplication.Foundation Filter Topology

namespace OAI.MatrixMultiplication.AuxiliarySeparation

variable {K : Type*} [CommSemiring K] [Nontrivial K]

theorem exactMatrixRank_pow_le (u j : ℕ) :
    exactMatrixRank K (u ^ j) ≤ exactMatrixRank K u ^ j := by
  classical
  let e : Fin (u ^ j) ≃ (Fin j → Fin u) := Fintype.equivOfCardEq (by simp)
  let f : Fin (u ^ j) × Fin (u ^ j) → Fin j → Fin u × Fin u := fun x i => (e x.1 i, e x.2 i)
  have h := ((exactMatrixRank_spec (K := K) u).power j).pullback f f f
  rw [show Tensor.pullback f f f (Tensor.power (matrixMultiplicationTensor u u u) j) =
    matrixMultiplicationTensor (u ^ j) (u ^ j) (u ^ j) by
      funext x y z
      simp [Tensor.pullback, Tensor.power, matrixMultiplicationTensor, f,
        Fintype.prod_boole, forall_and, ← funext_iff, e.injective.eq_iff]] at h
  exact exactRank_le h

theorem catalytic_rank_bound_at_slack {d n budget R : ℕ} (hd : 0 < d) (hn : 1 ≤ n)
    (hbound : ∀ j, 1 ≤ j → ∀ g, exactMatrixRank K g ≤ n ^ j →
      exactMatrixRank K (d ^ j * g) ≤ R * budget ^ j) {δ : ℝ} (hδ : 0 < δ) :
    (d : ℝ) ^ exactRankExponent K * (n : ℝ) ^ (exactRankExponent K / (exactRankExponent K + δ)) ≤
      budget := by
  set ν := exactRankExponent K
  have hν : 0 ≤ ν := by linarith [exactRankExponent_lower (K := K)]
  obtain ⟨u, hu, huR⟩ := exists_exactMatrixRank_lt_rpow (lt_add_of_pos_right ν hδ)
  have hu1 : (1 : ℝ) < u := mod_cast hu
  have hn0 : (0 : ℝ) < n := mod_cast hn
  refine le_of_eventually_pow_le_const_mul_pow (C := (u : ℝ) ^ ν * R) (Nat.cast_nonneg _)
    ((eventually_ge_atTop 1).mono fun j hj => ?_)
  set x := j * Real.logb u n / (ν + δ)
  have hx : 0 ≤ x := by
    have := Real.logb_nonneg hu1 (mod_cast hn : (1 : ℝ) ≤ n); positivity
  set l := ⌊x⌋₊
  have hlog := Real.rpow_logb (by positivity) hu1.ne' hn0
  have hl : (exactMatrixRank K (u ^ l) : ℝ) ≤ n ^ j := calc
    _ ≤ (exactMatrixRank K u : ℝ) ^ l := mod_cast exactMatrixRank_pow_le u l
    _ ≤ ((u : ℝ) ^ (ν + δ)) ^ l := by gcongr
    _ ≤ (u : ℝ) ^ ((ν + δ) * x) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      exact Real.rpow_le_rpow_of_exponent_le hu1.le (by gcongr; exact Nat.floor_le hx)
    _ = n ^ j := by
      rw [mul_div_cancel₀ _ (by positivity), mul_comm, Real.rpow_mul (by positivity), hlog,
        Real.rpow_natCast]
  have hsize : (n : ℝ) ^ ((j : ℝ) / (ν + δ)) ≤ u * (u ^ l : ℕ) := calc
    _ = (u : ℝ) ^ x := by rw [← hlog, ← Real.rpow_mul (by positivity)]; congr 1; simp_all; ring
    _ ≤ (u : ℝ) ^ ((l : ℝ) + 1) :=
      Real.rpow_le_rpow_of_exponent_le hu1.le (Nat.lt_floor_add_one x).le
    _ = _ := by push_cast; rw [Real.rpow_add (by positivity), Real.rpow_natCast, Real.rpow_one, mul_comm]
  have hlow := exactMatrixRank_rpow_lower_of_pos (K := K)
    (mul_pos (pow_pos hd j) (pow_pos (by omega : 0 < u) l))
  calc ((d : ℝ) ^ ν * (n : ℝ) ^ (ν / (ν + δ))) ^ j
      = ((d ^ j : ℕ) : ℝ) ^ ν * ((n : ℝ) ^ ((j : ℝ) / (ν + δ))) ^ ν := by
        rw [mul_pow, Real.rpow_pow_comm (by positivity), ← Real.rpow_natCast ((n : ℝ) ^ _),
          ← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity)]
        push_cast; ring_nf
    _ ≤ ((d ^ j : ℕ) : ℝ) ^ ν * (u * (u ^ l : ℕ)) ^ ν := by gcongr
    _ = (u : ℝ) ^ ν * ((d ^ j * u ^ l : ℕ) : ℝ) ^ ν := by
      rw [Nat.cast_mul, Real.mul_rpow, Real.mul_rpow] <;> first | positivity | ring
    _ ≤ (u : ℝ) ^ ν * (R * budget ^ j) := by
      gcongr; exact hlow.trans (mod_cast hbound j hj _ (mod_cast hl))
    _ = _ := by ring

/-- Uniform spectral inequalities for all sizes and slacks force `d^ν ≤ k`. -/
theorem spectral_coefficient_le_of_all_nat {ν k D : ℝ} {d : ℕ} (hν : 0 < ν)
    (hbound : ∀ n : ℕ, 1 ≤ n → ∀ δ : ℝ, 0 < δ →
      (d : ℝ) ^ ν * (n : ℝ) ^ (ν / (ν + δ)) ≤ n * k + D) :
    (d : ℝ) ^ ν ≤ k := by
  have h (n : ℕ) (hn : 1 ≤ n) : (d : ℝ) ^ ν * n ≤ n * k + D := by
    have hc : Tendsto (fun δ : ℝ => (d : ℝ) ^ ν * (n : ℝ) ^ (ν / (ν + δ))) (𝓝 0)
        (𝓝 ((d : ℝ) ^ ν * n ^ (ν / (ν + 0)))) :=
      tendsto_const_nhds.mul ((Real.continuousAt_const_rpow (Nat.cast_ne_zero.2 (by omega))).tendsto.comp
        (tendsto_const_nhds.div (tendsto_const_nhds.add tendsto_id) (by grind)))
    simpa [hν.ne'] using le_of_tendsto (hc.mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall (s := Set.Ioi 0) fun δ hδ => hbound n hn δ hδ)
  by_contra! hk
  obtain ⟨n, hn⟩ := exists_nat_gt (D / ((d : ℝ) ^ ν - k))
  have := (div_lt_iff₀ (sub_pos.2 hk)).1 (hn.trans (lt_add_one (n : ℝ)))
  have := h (n + 1) (by omega)
  grind

open TensorSemiring

theorem tensor_catalytic_obstruction_of_scalar_gain_of_one_le {D s : TensorClass K} {d k m : ℕ}
    (hd : 0 < d) (hs : 1 ≤ s) (hcat : D + (m : TensorClass K) + matrixClass d * s ≤ D + (k : TensorClass K) * s) :
    (d : ℝ) ^ exactRankExponent K ≤ k := by
  set M := matrixClass (K := K) d
  have hcat : D + M * s ≤ D + k * s :=
    (add_mono (by simpa using add_mono le_rfl (zero_le (m : TensorClass K))) le_rfl).trans hcat
  have hiter (n : ℕ) : D + n * (M * s) ≤ D + n * (k * s) := by
    induction n with
    | zero => simp
    | succ n ih => calc
        _ = (D + M * s) + n * (M * s) := by grind
        _ ≤ (D + k * s) + n * (M * s) := add_mono hcat le_rfl
        _ = (D + n * (M * s)) + k * s := by ring
        _ ≤ (D + n * (k * s)) + k * s := add_mono ih le_rfl
        _ = _ := by grind
  have hD : D ≤ (rank D : TensorClass K) * s :=
    (le_rank D).trans (by simpa using mul_mono (le_refl (rank D : TensorClass K)) hs)
  refine spectral_coefficient_le_of_all_nat (D := rank D)
    (by linarith [exactRankExponent_lower (K := K)]) fun n hn δ hδ => ?_
  set N : TensorClass K := ((n * k + rank D : ℕ) : TensorClass K)
  have habsorb : n * M * s ≤ N * s := calc
    _ = 0 + n * (M * s) := by ring
    _ ≤ D + n * (k * s) := (add_mono (zero_le D) le_rfl).trans (hiter n)
    _ ≤ (rank D : TensorClass K) * s + n * (k * s) := add_mono hD le_rfl
    _ = _ := by grind
  have hpow (j : ℕ) : (n : TensorClass K) ^ j * M ^ j * s ≤ N ^ j * s := by
    induction j with
    | zero => simp
    | succ j ih => calc
        _ = (n ^ j * M ^ j) * (n * M * s) := by ring
        _ ≤ (n ^ j * M ^ j) * (N * s) := mul_mono le_rfl habsorb
        _ = N * (n ^ j * M ^ j * s) := by ring
        _ ≤ N * (N ^ j * s) := mul_mono le_rfl ih
        _ = _ := by ring
  have := catalytic_rank_bound_at_slack (K := K) (R := rank s) (budget := n * k + rank D) hd hn
    (fun j _ g hg => ?_) hδ
  · grind
  have hg : matrixClass g ≤ (n : TensorClass K) ^ j := by
    refine (le_rank _).trans ?_
    obtain ⟨q, hq⟩ := Nat.exists_eq_add_of_le hg
    rw [rank_matrixClass, ← Nat.cast_pow, hq, Nat.cast_add]
    simpa using add_mono le_rfl (zero_le (q : TensorClass K))
  calc exactMatrixRank K (d ^ j * g) = rank (M ^ j * matrixClass g) := by
        rw [← matrixClass_pow, ← matrixClass_mul, rank_matrixClass]
    _ ≤ rank (N ^ j * s) := rank_mono <| calc
        _ ≤ M ^ j * (n : TensorClass K) ^ j := mul_mono le_rfl hg
        _ ≤ (n ^ j * M ^ j) * s := by simpa [mul_comm] using mul_mono le_rfl hs
        _ ≤ _ := hpow j
    _ ≤ _ := (rank_mul_le _ _).trans (by simp only [N, ← Nat.cast_pow, rank_natCast]; rw [mul_comm])

/-- A finite tensor cannot absorb a positive scalar direct summand. -/
theorem not_tensor_add_positive_nat_le_self (D : TensorClass K) {m : ℕ} (hm : 0 < m) :
    ¬ D + (m : TensorClass K) ≤ D := by
  intro h
  have hi (n : ℕ) : D + ((n * m : ℕ) : TensorClass K) ≤ D := by
    induction n with
    | zero => simp
    | succ n ih => exact (by grind : _ = D + ((n * m : ℕ) : TensorClass K) + m).trans_le ((add_mono ih le_rfl).trans h)
  have := rank_mono ((zero_add _).ge.trans ((add_mono (zero_le D) le_rfl).trans (hi (rank D + 1))))
  rw [rank_natCast] at this
  nlinarith


/-! Character values on powers, supported subtensors and binary sums. -/



namespace Character
open scoped Classical

variable {K : Type*} [CommSemiring K] (χ : Character K)
variable {X Y Z X' Y' Z' : Type} [Fintype X] [Fintype Y] [Fintype Z]
variable [Fintype X'] [Fintype Y'] [Fintype Z']

theorem value_pi {n : ℕ} (B : Fin n → Tensor K X Y Z) :
    χ.value (fun x y z => ∏ i, B i (x i) (y i) (z i) : Tensor K (Fin n → X) (Fin n → Y) (Fin n → Z)) =
      ∏ i, χ.value (B i) := by
  induction n with
  | zero =>
      rw [← show Tensor.pullback (Equiv.equivPUnit (Fin 0 → X)) (Equiv.equivPUnit (Fin 0 → Y))
          (Equiv.equivPUnit (Fin 0 → Z)) unitTensor = fun x y z => ∏ i, B i (x i) (y i) (z i) by
        funext; simp [Tensor.pullback, unitTensor], χ.value_reindex, χ.map_one]
      simp
  | succ n ih =>
      rw [← show Tensor.pullback (Fin.consEquiv fun _ : Fin (n + 1) => X).symm
          (Fin.consEquiv fun _ : Fin (n + 1) => Y).symm (Fin.consEquiv fun _ : Fin (n + 1) => Z).symm
          (Tensor.product (B 0) fun x y z => ∏ i, B i.succ (x i) (y i) (z i)) =
            fun x y z => ∏ i, B i (x i) (y i) (z i) by
        funext; simp [Tensor.pullback, Tensor.product, Fin.consEquiv, Fin.prod_univ_succ, Fin.tail],
        χ.value_reindex, χ.map_product, ih, Fin.prod_univ_succ]

theorem value_power (T : Tensor K X Y Z) (n : ℕ) :
    χ.value (Tensor.power T n) = χ.value T ^ n :=
  (χ.value_pi fun _ => T).trans (by simp)

/-- A character ignores ambient coordinates outside a tensor's support. -/
theorem value_eq_pullback_of_support (T : Tensor K X' Y' Z')
    (fx : X → X') (fy : Y → Y') (fz : Z → Z')
    (hx : Function.Injective fx) (hy : Function.Injective fy)
    (hz : Function.Injective fz)
    (hs : ∀ x' y' z', T x' y' z' ≠ 0 →
      x' ∈ Set.range fx ∧ y' ∈ Set.range fy ∧ z' ∈ Set.range fz) :
    χ.value T = χ.value (Tensor.pullback fx fy fz T) := by
  refine le_antisymm ?_ (χ.value_pullback_le _ _ _ _)
  convert χ.monotone (Tensor.pullback fx fy fz T) (fun x' x => if fx x = x' then 1 else 0)
    (fun y' y => if fy y = y' then 1 else 0) (fun z' z => if fz z = z' then 1 else 0)
  funext x' y' z'
  by_cases h : T x' y' z' = 0
  · rw [h]
    refine (Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ =>
      Finset.sum_eq_zero fun z _ => ?_).symm
    dsimp [Tensor.pullback]
    simp_all
  obtain ⟨⟨x, rfl⟩, ⟨y, rfl⟩, ⟨z, rfl⟩⟩ := hs _ _ _ h
  simp [Tensor.restrict, Tensor.pullback, hx.eq_iff, hy.eq_iff, hz.eq_iff, ite_mul, mul_ite]

/-- A character is additive on binary direct sums with arbitrary finite
coordinate types. -/
theorem value_sumTensor {U V W : Type} [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor K X Y Z) (S : Tensor K U V W) :
    χ.value (sumTensor T S) = χ.value T + χ.value S := by
  let F (b : Bool) : Tensor K (X ⊕ U) (Y ⊕ V) (Z ⊕ W) := fun x y z =>
    if x.isRight = b then sumTensor T S x y z else 0
  rw [show sumTensor T S = Tensor.pullback (fun x => (x.isRight, x)) (fun y => (y.isRight, y))
      (fun z => (z.isRight, z)) (Tensor.directSum F) by
      funext x y z; cases x <;> cases y <;> cases z <;> simp [F, Tensor.pullback, Tensor.directSum, sumTensor],
    ← χ.value_eq_pullback_of_support _ _ _ _ (fun _ _ h => congrArg Prod.snd h)
      (fun _ _ h => congrArg Prod.snd h) (fun _ _ h => congrArg Prod.snd h) ?_, χ.map_directSum,
    Fintype.sum_bool, add_comm, χ.value_eq_pullback_of_support (F false) Sum.inl Sum.inl Sum.inl
      Sum.inl_injective Sum.inl_injective Sum.inl_injective ?_,
    χ.value_eq_pullback_of_support (F true) Sum.inr Sum.inr Sum.inr
      Sum.inr_injective Sum.inr_injective Sum.inr_injective ?_]
  · rfl
  rotate_right
  · rintro ⟨b, x | x⟩ ⟨c, y | y⟩ ⟨d, z | z⟩ h <;> simp_all [F, Tensor.directSum, sumTensor]
  all_goals intro x y z h; cases x <;> cases y <;> cases z <;> simp_all [F, sumTensor]

end Character

/-!
# Concrete tensor characters and the tensor semiring

The coefficient-level character interface and monotone real-valued semiring
homomorphisms on mutual-restriction classes describe the same valuations.
The map `classOf` uses finite natural-number coordinate presentations, so
the construction applies to all finite coordinate types in the character
interface.
-/






theorem classOf_directSum {X Y Z ι : Type*} [Fintype X] [Fintype Y] [Fintype Z] [Fintype ι] [d : DecidableEq ι]
    (T : ι → Tensor K X Y Z) : classOf (Tensor.directSum T) = ∑ i, classOf (T i) := by
  obtain rfl : d = fun _ _ => Classical.propDecidable _ := Subsingleton.elim _ _
  classical
  refine Fintype.induction_empty_option (P := fun ι _ => ∀ T : ι → Tensor K X Y Z,
    classOf (Tensor.directSum T) = ∑ i, classOf (T i)) (fun α β _ e ih S => ?_) (fun S => ?_)
    (fun α _ ih S => ?_) ι T
  · let : Fintype α := .ofEquiv β e.symm
    rw [← e.sum_comp, ← ih]
    exact classOf_eq_of_reindex (e.symm.prodCongr (.refl _)) (e.symm.prodCongr (.refl _))
      (e.symm.prodCongr (.refl _)) (by funext; simp [Tensor.pullback, Tensor.directSum])
  · simpa using (classOf_eq_zero_iff _).2 (funext fun x => x.1.elim)
  rw [Fintype.sum_option, ← ih, ← classOf_sum]
  refine (classOf_eq_of_reindex optionProdEquiv.symm optionProdEquiv.symm optionProdEquiv.symm ?_).symm
  funext x y z
  rcases x with _ | _ <;> rcases y with _ | _ <;> rcases z with _ | _ <;>
    simp [Tensor.pullback, Tensor.directSum, sumTensor]

namespace Character

/-- A monotone semiring homomorphism on tensor classes gives a character on all
finite coefficient tensors. Normalization follows from preservation of `0` and `1`. -/
def ofTensorClassHom (φ : TensorClass K →+* ℝ) (hφ : Monotone φ) : Character K where
  value T := φ (classOf T)
  nonneg T := φ.map_zero ▸ hφ (zero_le _)
  map_zero := by intros; rw [classOf_zero]; exact φ.map_zero
  map_one := φ.map_one
  map_directSum T := by rw [classOf_directSum, map_sum]
  map_product T S := by rw [classOf_product, map_mul]
  monotone T A B C := hφ ((classOf_le_iff _ _).mpr ⟨A, B, C, rfl⟩)

end Character


/-! Positive monotone multiplicative functions on the positive natural numbers are real powers. -/


theorem positiveMultiplicative_eq_rpow {f : ℕ → ℝ} (hpos : ∀ n, 0 < n → 0 < f n)
    (hmul : ∀ m n, f (m * n) = f m * f n) (hmono : Monotone f) {n : ℕ} (hn : 0 < n) :
    f n = (n : ℝ) ^ (Real.log (f 2) / Real.log 2) := by
  set c := Real.log (f 2) / Real.log 2
  have h1 : f 1 = 1 := by
    have := hmul 1 1; rw [one_mul] at this; nlinarith [hpos 1 one_pos]
  have hp m k : f (m ^ k) = f m ^ k := by induction k <;> simp [pow_succ, *]
  have h2 : f 2 = 2 ^ c := by
    rw [Real.rpow_def_of_pos two_pos, mul_div_cancel₀ _ (Real.log_pos one_lt_two).ne',
      Real.exp_log (hpos 2 two_pos)]
  have hc := div_nonneg (Real.log_nonneg (h1 ▸ hmono one_le_two)) (Real.log_nonneg one_le_two)
  have key k : f n ^ k ≤ f 2 * ((n : ℝ) ^ c) ^ k ∧ ((n : ℝ) ^ c) ^ k ≤ f 2 * f n ^ k := by
    have a := Nat.pow_log_le_self 2 (pow_pos hn k).ne'
    have b := (Nat.lt_pow_succ_log_self one_lt_two (n ^ k)).le
    have A := hmono a
    have B := hmono b
    have C := Real.rpow_le_rpow (by positivity) (Nat.cast_le.2 a) hc
    have D := Real.rpow_le_rpow (by positivity) (Nat.cast_le.2 b) hc
    push_cast at C D
    rw [← Real.rpow_pow_comm two_pos.le, ← h2, ← Real.rpow_pow_comm (by positivity)] at C D
    rw [hp, hp] at A B
    rw [pow_succ] at B D
    constructor <;> nlinarith [hpos 2 two_pos, pow_pos (hpos 2 two_pos) (Nat.log 2 (n ^ k))]
  exact le_antisymm (le_of_eventually_pow_le_const_mul_pow (by positivity) (.of_forall fun k => (key k).1))
    (le_of_eventually_pow_le_const_mul_pow (hpos n hn).le (.of_forall fun k => (key k).2))

end MatrixMultiplication.AuxiliarySeparation




/-!
# Dot-product exponents of tensor characters

The power laws here follow from restriction monotonicity and tensor products.
They are not additional assumptions on a character. The three exponents refer
to the leg on which the corresponding dot product has dimension one.
-/



namespace MatrixMultiplication.AuxiliarySeparation.Character

variable {K : Type*} [CommSemiring K]

variable (χ : (Character K))

/-- Precomposing a character with a cyclic permutation gives a character. -/
def cyclicCharacter : (Character K) where
  value T := χ.value (Tensor.cyclic T)
  nonneg T := χ.nonneg (Tensor.cyclic T)
  map_zero := χ.map_zero
  map_one := χ.map_one
  map_directSum T := by
    rw [Tensor.cyclic_directSum, χ.map_directSum]
  map_product T S := χ.map_product (Tensor.cyclic T) (Tensor.cyclic S)
  monotone T A B C := by
    convert χ.monotone (Tensor.cyclic T) B C A using 2
    funext y z x
    simp [Tensor.cyclic, Tensor.restrict]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans
      (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)

/-- The exponent on dot products whose third leg has dimension one. -/
def pZ : ℝ :=
  Real.log (χ.value (Tensor.dotPairing (Fin 2))) / Real.log 2

/-- The exponent on dot products whose second leg has dimension one. -/
def pY : ℝ := χ.cyclicCharacter.pZ

/-- The exponent on dot products whose first leg has dimension one. -/
def pX : ℝ := χ.cyclicCharacter.cyclicCharacter.pZ

theorem value_dotPairing {m : ℕ} (hm : 0 < m) :
    χ.value (Tensor.dotPairing (Fin m)) = (m : ℝ) ^ χ.pZ := by
  refine positiveMultiplicative_eq_rpow (f := fun m => χ.value (Tensor.dotPairing (Fin m)))
    (fun m hm => zero_lt_one.trans_le (χ.one_le_value_of_coefficient_one
      ⟨⟨0, hm⟩, ⟨0, hm⟩, (), by simp [Tensor.dotPairing]⟩)) (fun m n => ?_) (fun m n h => ?_) hm
  · rw [← χ.map_product, ← χ.value_reindex _ finProdFinEquiv.symm finProdFinEquiv.symm
      (Equiv.prodUnique Unit Unit).symm]
    congr; funext x y z
    simp only [Tensor.pullback, Tensor.product, Tensor.dotPairing,
      ite_zero_mul_ite_zero, one_mul, ← Prod.ext_iff, Equiv.apply_eq_iff_eq]
  convert χ.value_pullback_le (Z' := Unit) _ (Fin.castLE h) (Fin.castLE h) id
  funext; simp [Tensor.pullback, Tensor.dotPairing]

theorem value_cyclic_dotPairing {m : ℕ} (hm : 0 < m) :
    χ.value (Tensor.cyclic (Tensor.dotPairing (Fin m))) =
      (m : ℝ) ^ χ.pY :=
  χ.cyclicCharacter.value_dotPairing hm

theorem value_cyclic_cyclic_dotPairing {m : ℕ} (hm : 0 < m) :
    χ.value (Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (Fin m)))) =
      (m : ℝ) ^ χ.pX :=
  χ.cyclicCharacter.cyclicCharacter.value_dotPairing hm

/-- The character of square matrix multiplication has exponent `pX + pY + pZ`. -/
theorem value_matrixMultiplication {m : ℕ} (hm : 0 < m) :
    χ.value (matrixMultiplicationTensor m m m) =
      (m : ℝ) ^ (χ.pX + χ.pY + χ.pZ) := by
  rw [show matrixMultiplicationTensor m m m = Tensor.pullback
    ((Equiv.prodComm _ _).trans (Equiv.prodPUnit _).symm) ((Equiv.prodPUnit _).symm.prodCongr (.refl _))
    ((Equiv.prodComm _ _).trans ((Equiv.punitProd _).symm.prodCongr (.refl _)))
    (Tensor.product (Tensor.product (Tensor.dotPairing (Fin m))
      (Tensor.cyclic (Tensor.dotPairing (Fin m)))) (Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (Fin m)))))
    from ?_, χ.value_reindex]
  · simp [χ.map_product, χ.value_dotPairing hm, χ.value_cyclic_dotPairing hm,
      χ.value_cyclic_cyclic_dotPairing hm, Real.rpow_add (Nat.cast_pos.2 hm)]
    ring
  funext x y z
  simp [Tensor.pullback, Tensor.product, Tensor.dotPairing, Tensor.cyclic, matrixMultiplicationTensor]
  grind

end Character

/-!
# The polynomial multiplication tensor

The coefficient tensor `convolution a b` represents multiplication of binary forms
of degrees `a - 1` and `b - 1`, or equivalently ordinary coefficient convolution.
The output leg has `a + b - 1` coordinates.  The definitions also make sense when
an input dimension is zero, while the nonzero and full-output-support statements
use the positive dimensions assumed in Section 5 of the paper.
-/



variable {K : Type*} [CommSemiring K]


/-- The tensor `C(a,b)` of Section 5, in monomial coefficient coordinates. -/
def convolution (a b : ℕ) : Tensor K (Fin a) (Fin b) (Fin (a + b - 1)) :=
  fun i j k => if i.val + j.val = k.val then 1 else 0

@[simp] theorem convolution_apply (a b : ℕ)
    (i : Fin a) (j : Fin b) (k : Fin (a + b - 1)) :
    convolution (K := K) a b i j k = if i.val + j.val = k.val then 1 else 0 := rfl

/-- Every pair of input monomials has a valid output coordinate. -/
def convolutionOutput {a b : ℕ} (i : Fin a) (j : Fin b) : Fin (a + b - 1) :=
  ⟨i.val + j.val, by grind⟩

theorem convolution_at_output {a b : ℕ} (i : Fin a) (j : Fin b) :
    convolution (K := K) a b i j (convolutionOutput i j) = 1 := by
  simp [convolutionOutput]

/-- Commuting the two inputs only casts the equal output dimensions. -/
theorem convolution_comm (a b : ℕ) (i : Fin a) (j : Fin b)
    (k : Fin (a + b - 1)) :
    convolution a b i j k =
      convolution (K := K) b a j i (Fin.cast (by omega) k) := by
  simp [convolution, Fin.val_cast, Nat.add_comm]

/-- Relabel the output of `C(1,b)` by its actual dimension `b`. -/
def convolutionOneOutputEquiv (b : ℕ) : Fin b ≃ Fin (1 + b - 1) :=
  finCongr (by omega)

/-- Relabel the single input coordinate of `C(1,b)` by `Unit`. -/
def convolutionOneInputEquiv : Unit ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ()
  left_inv _ := rfl
  right_inv _i := Subsingleton.elim _ _

/-- `C(1,b)` is the dot-product tensor with the singleton on the first leg. -/
theorem convolution_one_left_dotPairing (b : ℕ) :
    Tensor.pullback convolutionOneInputEquiv (Equiv.refl (Fin b))
      (convolutionOneOutputEquiv b) (convolution 1 b) =
      Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (K := K) (Fin b))) := by
  funext i j k
  simp [Tensor.pullback, convolutionOneInputEquiv, convolutionOneOutputEquiv,
    Tensor.cyclic, Tensor.dotPairing, convolution, Fin.ext_iff]


/-!
# Division-free assembly of coefficient restrictions

The direct-sum labels are retained on all three source legs.  These identities
are over commutative semirings and do not use spectral characters or fields.
-/

namespace Integral


variable {R X Y Z U V W ι : Type*} [CommSemiring R]

/-- Move one finite summation past the three source coordinates. -/
theorem sum_comm_three [Fintype U] [Fintype V] [Fintype W] [Fintype ι]
    (f : ι → U → V → W → R) :
    (∑ u, ∑ v, ∑ w, ∑ i, f i u v w) = ∑ i, ∑ u, ∑ v, ∑ w, f i u v w := by
  simp [Finset.sum_comm (t := (Finset.univ : Finset ι))]

/-- Concatenating the three local maps adds the restricted tensors. -/
theorem restrict_directSum [Fintype U] [Fintype V] [Fintype W]
    [Fintype ι] [DecidableEq ι]
    (T : ι → Tensor R U V W)
    (A : ι → X → U → R) (B : ι → Y → V → R) (C : ι → Z → W → R) :
    Tensor.restrict (fun x q => A q.1 x q.2)
      (fun y q => B q.1 y q.2) (fun z q => C q.1 z q.2)
      (Tensor.directSum T) = fun x y z => ∑ i, Tensor.restrict (A i) (B i) (C i) (T i) x y z := by
  funext x y z
  simp [Tensor.restrict, Tensor.directSum, Fintype.sum_prod_type, ite_and]

/-- Tensor powers of the local maps restrict tensor powers of the source. -/
theorem restrict_power [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor R U V W) (A : X → U → R) (B : Y → V → R)
    (C : Z → W → R) (k : ℕ) :
    Tensor.restrict (fun x u => ∏ i : Fin k, A (x i) (u i))
      (fun y v => ∏ i : Fin k, B (y i) (v i))
      (fun z w => ∏ i : Fin k, C (z i) (w i)) (Tensor.power T k) =
      Tensor.power (Tensor.restrict A B C T) k := by
  funext x y z
  simp [Tensor.restrict, Tensor.power, Fintype.prod_sum,
    Finset.prod_mul_distrib]


/-!
# Patching scalar multiples before applying a character

Scalar multiples need not be primitive tensors over the integers. These
lemmas combine their actual coefficient maps first; no character is applied
to a nonprimitive scalar multiple.
-/




/-- A finite Bezout combination patches exact rank decompositions. -/
theorem rankAtMost_patch [Fintype ι] (T : Tensor R X Y Z)
    (d u : ι → R) (r : ι → ℕ) (hu : ∑ i, u i * d i = 1)
    (h : ∀ i, Tensor.RankAtMost (fun x y z => d i * T x y z) (r i)) :
    Tensor.RankAtMost T (∑ i, r i) := by
  classical
  choose a b c hc using fun i => (h i).scale (u i)
  simp [funext_iff] at hc
  convert Tensor.rankAtMost_sum_rankOne (fun q : Σ i, Fin (r i) => a q.1 q.2)
    (fun q => b q.1 q.2) (fun q => c q.1 q.2) using 1
  · funext x y z
    rw [← one_mul (T x y z), ← hu, Finset.sum_mul]
    simp [Fintype.sum_sigma, ← hc, mul_assoc]
  simp

/-- No common prime divisor gives one finite family whose powers are all
Bezout families. -/
theorem exists_finite_bezout_of_prime_witness (S : Set ℤ)
    (h : ∀ p : ℕ, p.Prime → ∃ D ∈ S, ¬ (p : ℤ) ∣ D) :
    ∃ t : Finset ℤ, (↑t : Set ℤ) ⊆ S ∧ ∀ k, ∃ u : t → ℤ, ∑ i, u i * (i : ℤ) ^ k = 1 := by
  classical
  have hu : IsUnit (Submodule.IsPrincipal.generator (Ideal.span S)) := by
    rw [Int.isUnit_iff_natAbs_eq]
    by_contra hg
    obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hg
    obtain ⟨D, hDS, hpD⟩ := h p hp
    exact hpD ((Int.natCast_dvd.mpr hpg).trans
      ((Submodule.IsPrincipal.mem_iff_generator_dvd _).mp (Ideal.subset_span hDS)))
  obtain ⟨t, htS, ht⟩ := Submodule.mem_span_finite_of_mem_span ((Ideal.eq_top_iff_one _).mp
    ((Ideal.span_singleton_generator (Ideal.span S)).symm.trans (Ideal.span_singleton_eq_top.mpr hu)))
  refine ⟨t, htS, fun k => ?_⟩
  have := (Ideal.eq_top_iff_one _).mp (Ideal.span_pow_eq_top _ ((Ideal.eq_top_iff_one _).mpr ht) k)
  rw [Set.image_eq_range] at this
  obtain ⟨u, hu⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp this
  exact ⟨u, by simp_all⟩

end AuxiliarySeparation.Integral

/-! Fixed finite free algebra descent. No field hypothesis and no division.
The unit-splitting functional is supplied explicitly: it need not exist for an
arbitrary finite algebra over a ring. -/

namespace Foundation.Tensor


variable {R E X Y Z : Type*} [CommRing R] [CommRing E] [Algebra R E]

/-- Expand only the first two extension coefficients in a fixed basis. -/
theorem project_mul_mul {ι : Type*} [Fintype ι] (basis : Module.Basis ι R E) (π : E →ₗ[R] R)
    (v w t : E) :
    π (v * w * t) = ∑ i, ∑ j, basis.repr v i * basis.repr w j * π (basis i * basis j * t) := by
  conv_lhs => rw [← basis.sum_repr v, ← basis.sum_repr w]
  simp only [Finset.sum_mul, Finset.mul_sum, map_sum, smul_mul_assoc, mul_smul_comm, map_smul,
    smul_eq_mul, mul_assoc]
  rw [Finset.sum_comm]
  ac_rfl

/-- Applying a base-ring linear functional to coefficients increases exact
tensor rank by at most the square of the basis cardinality. -/
theorem RankAtMost.project_finite_basis {ι : Type*} [Fintype ι]
    (basis : Module.Basis ι R E) (π : E →ₗ[R] R)
    {T : Tensor E X Y Z} {r : ℕ} (h : RankAtMost T r) :
    RankAtMost (fun x y z => π (T x y z)) (r * Fintype.card ι * Fintype.card ι) := by
  rcases h with ⟨a, b, c, rfl⟩
  convert rankAtMost_sum_rankOne (fun q : Fin r × ι × ι => fun x => basis.repr (a q.1 x) q.2.1)
      (fun q y => basis.repr (b q.1 y) q.2.2) (fun q z => π (basis q.2.1 * basis q.2.2 * c q.1 z)) using 1
  · funext x y z
    simp [rankOne, Fintype.sum_prod_type, project_mul_mul basis π (a _ x)]
  simp [mul_assoc]

/-- Exact rank descent with a supplied basis and a functional splitting the unit.
The basis is fixed independently of any tensor-power parameter. -/
theorem RankAtMost.descend_finite_basis {ι : Type*} [Fintype ι]
    (basis : Module.Basis ι R E) (π : E →ₗ[R] R) (hπ : π 1 = 1)
    {T : Tensor R X Y Z} {r : ℕ}
    (h : RankAtMost (fun x y z => algebraMap R E (T x y z)) r) :
    RankAtMost T (r * Fintype.card ι * Fintype.card ι) := by
  have ha (v : R) : π (algebraMap R E v) = v := by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, hπ, smul_eq_mul, mul_one]
  simpa only [ha] using h.project_finite_basis basis π

/-- The constant coordinate of a monic quotient's power basis splits the unit. -/
theorem coord_one {f : Polynomial R} (hf : f.Monic) (h : 0 < f.natDegree) :
    (AdjoinRoot.powerBasis' hf).basis.coord ⟨0, h⟩ 1 = 1 := by
  rw [show (1 : AdjoinRoot f) = (AdjoinRoot.powerBasis' hf).basis ⟨0, h⟩ by simp,
    Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same]

end Foundation.Tensor

/-!
# Integral interpolation using adjugates

A Vandermonde adjugate supplies an exact scheme for its determinant times
convolution, even when that determinant is not a unit. A second adjugate,
of multiplication by that determinant in a finite free algebra, replaces the
algebra-valued multiplier with its base-ring norm. No localization is used.
-/

namespace AuxiliarySeparation.Integral

open scoped Matrix

section

variable {R : Type*} [CommRing R]

/-- A length `a+b-1` rank scheme for the Vandermonde determinant times ordinary
polynomial convolution, by adjugate interpolation. Nodes may coincide. -/
theorem rankAtMost_vandermonde_convolution (a b : ℕ) (v : Fin (a + b - 1) → R) :
    Tensor.RankAtMost (fun (i : Fin a) (j : Fin b) (k : Fin (a + b - 1)) =>
        (Matrix.vandermonde v).det * (if i.val + j.val = k.val then 1 else 0)) (a + b - 1) := by
  refine ⟨(fun r i => v r ^ i.val), (fun r j => v r ^ j.val),
    (fun r k => (Matrix.vandermonde v).adjugate k r), funext₃ fun i j k => ?_⟩
  simpa [Matrix.mul_apply, Matrix.vandermonde, Matrix.one_apply, mul_comm, eq_comm, Tensor.rankOne, ← pow_add,
    Fin.ext_iff] using (congrFun (congrFun (Matrix.adjugate_mul (Matrix.vandermonde v)) k)
      ⟨i.val + j.val, by omega⟩).symm

/-- The same interpolation scheme after clearing the algebra-valued determinant
by its integral multiplication-matrix determinant, using the adjugate of
multiplication by that determinant applied to the coordinates of 1. -/
theorem rankAtMost_norm_convolution {E ι : Type*} [CommRing E] [Algebra R E]
    [Fintype ι] [DecidableEq ι] (basis : Module.Basis ι R E)
    (a b : ℕ) (v : Fin (a + b - 1) → E) :
    Tensor.RankAtMost
      (fun (i : Fin a) (j : Fin b) (k : Fin (a + b - 1)) =>
        algebraMap R E (Algebra.leftMulMatrix basis (Matrix.vandermonde v).det).det *
          (if i.val + j.val = k.val then 1 else 0))
      (a + b - 1) := by
  obtain ⟨c, h⟩ : ∃ c, (Matrix.vandermonde v).det * c =
      algebraMap R E (Algebra.leftMulMatrix basis (Matrix.vandermonde v).det).det :=
    ⟨basis.equivFun.symm ((Algebra.leftMulMatrix basis _).adjugate *ᵥ basis.repr 1), basis.equivFun.injective (by
      rw [Module.Basis.equivFun_apply, ← Algebra.leftMulMatrix_mulVec_repr, ← Module.Basis.equivFun_apply,
        LinearEquiv.apply_symm_apply, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec,
        Matrix.one_mulVec, Algebra.algebraMap_eq_smul_one, map_smul]; rfl)⟩
  convert (rankAtMost_vandermonde_convolution a b v).scale c using 1
  grind



/-! Specializing a finite free algebra together with its basis commutes with
multiplication matrices and their determinants. This isolates the exact input
needed to prove that an interpolation-clearing norm is prime to a chosen prime. -/



variable {R S E K ι : Type*} [CommRing R] [Field S] [CommRing E] [Field K]
  [Algebra R E] [Algebra S K] [Fintype ι] [DecidableEq ι]
  (b : Module.Basis ι R E) (c : Module.Basis ι S K) (ψ : R →+* S) (φ : E →+* K)
  (hφ : ∀ r, φ (algebraMap R E r) = algebraMap S K (ψ r)) (hb : ∀ i, φ (b i) = c i)
include hφ hb

/-- Coordinates specialize coefficientwise when the basis vectors specialize. -/
theorem repr_specialize (x : E) (i : ι) : c.repr (φ x) i = ψ (b.repr x i) := by
  conv_lhs => rw [← b.sum_repr x]
  simp_rw [map_sum, Algebra.smul_def, map_mul, hφ, hb, ← Algebra.smul_def]
  simp [Finsupp.single_apply]

/-- Surjectivity of the coefficient map and specialization of a whole basis
imply surjectivity on the finite free algebra. -/
theorem surjective_of_basis_specialize (hψ : Function.Surjective ψ) : Function.Surjective φ := by
  intro y
  choose a ha using fun i => hψ (c.repr y i)
  refine ⟨∑ i, a i • b i, ?_⟩
  simp_rw [map_sum, Algebra.smul_def, map_mul, hφ, hb, ha, ← Algebra.smul_def, c.sum_repr]

/-- A basis-preserving specialization to a field detects a nonzero norm.
For R=Z and S=ZMod p, this says the integer norm is not divisible by p. -/
theorem norm_specialize_ne_zero (x : E) (hx : φ x ≠ 0) :
    ψ (Algebra.leftMulMatrix b x).det ≠ 0 := by
  rw [RingHom.map_det, show ψ.mapMatrix (Algebra.leftMulMatrix b x) = Algebra.leftMulMatrix c (φ x) by
    ext i j
    simp [Algebra.leftMulMatrix_eq_repr_mul, ← repr_specialize b c ψ φ hφ hb, hb]]
  exact ((Matrix.isUnit_iff_isUnit_det _).mp
    ((isUnit_iff_ne_zero.mpr hx).map (Algebra.leftMulMatrix c).toMonoidHom)).ne_zero

end


/-! Monic integral lifts of finite-field power bases. The integral algebra need
not be a domain or a field. Its reduction has a full basis, which is what the
norm-specialization argument requires. -/



/-- For each prime, convolution has a clearing integer not divisible by that
prime. A finite-field power basis is lifted to a monic integer quotient, and
tensor powers are descended through that one fixed finite free algebra. -/
theorem exists_prime_clearing_convolution (p : ℕ) [Fact p.Prime] (a b : ℕ) :
    ∃ D : ℤ, ∃ d : ℕ, (D : ZMod p) ≠ 0 ∧ ∀ k : ℕ,
      Foundation.Tensor.RankAtMost
        (fun x y z => D ^ k * Foundation.Tensor.power
          (fun (i : Fin a) (j : Fin b) (l : Fin (a + b - 1)) =>
            (if i.val + j.val = l.val then 1 else 0 : ℤ)) k x y z)
        ((a + b - 1) ^ k * d) := by
  classical
  let h := a + b - 1
  let K := GaloisField p (h + 1)
  letI : Fintype K := Fintype.ofFinite K
  let pb := Field.powerBasisOfFiniteOfSeparable (ZMod p) K
  obtain ⟨nodes⟩ : Nonempty (Fin h ↪ K) := Function.Embedding.nonempty_of_card_le (by
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, GaloisField.card p (h + 1) (by omega)]
    exact (Nat.le_succ h).trans (Nat.lt_pow_self (Fact.out : Nat.Prime p).one_lt).le)
  obtain ⟨f, hmap, hdeg, hf⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (Polynomial.mem_lifts_of_surjective (f := Int.castRingHom _) ZMod.intCast_surjective (minpoly (ZMod p) pb.gen))
    (minpoly.monic pb.isIntegral_gen)
  have hroot : f.eval₂ (Int.castRingHom K) pb.gen = 0 := by
    rw [← RingHom.ext_int ((algebraMap (ZMod p) K).comp (Int.castRingHom _)) (Int.castRingHom K), ← Polynomial.eval₂_map,
      hmap]
    exact minpoly.aeval _ _
  let basis := (AdjoinRoot.powerBasis' hf).basis.reindex (finCongr (hdeg.trans pb.natDegree_minpoly))
  let φ := AdjoinRoot.lift (Int.castRingHom K) pb.gen hroot
  have hφ (r : ℤ) : φ (algebraMap ℤ _ r) = algebraMap (ZMod p) K (Int.castRingHom _ r) := by simp
  have hb i : φ (basis i) = pb.basis i := by
    simp [basis, φ, pb.basis_eq_pow]
    rfl
  choose v hv using fun i : Fin h => surjective_of_basis_specialize basis pb.basis _ φ hφ hb
    ZMod.intCast_surjective (nodes i)
  let D := (Algebra.leftMulMatrix basis (Matrix.vandermonde v).det).det
  have hD : (D : ZMod p) ≠ 0 := norm_specialize_ne_zero basis pb.basis _ φ hφ hb _ (by
    rw [RingHom.map_det, show φ.mapMatrix (Matrix.vandermonde v) = Matrix.vandermonde (nodes ·) by
      ext i j; simp_all]
    exact Matrix.det_vandermonde_ne_zero_iff.mpr nodes.injective)
  let T : Foundation.Tensor ℤ (Fin a) (Fin b) (Fin h) :=
    fun i j l => if i.val + j.val = l.val then 1 else 0
  refine ⟨D, pb.dim * pb.dim, hD, fun k => ?_⟩
  convert (show Foundation.Tensor.RankAtMost (fun x y z => algebraMap ℤ (AdjoinRoot f)
    (D ^ k * Foundation.Tensor.power T k x y z)) (h ^ k) by
      convert (rankAtMost_norm_convolution basis a b v).power k using 1
      funext; simp only [Foundation.Tensor.power, map_mul, map_pow, map_prod, Finset.prod_mul_distrib,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin, T, D, apply_ite (algebraMap ℤ _), map_one, map_zero]).descend_finite_basis
    basis _ (Foundation.Tensor.coord_one hf (by rw [hdeg, pb.natDegree_minpoly]; exact pb.dim_pos)) using 1
  simp [h, mul_assoc]

end Integral


namespace Character

/-!
# Integral convolution character bounds

A finite family of prime-local clearing schemes is selected once, giving one
constant overhead for all powers of integer convolution; this suffices for the
sharp character bound.
-/

variable (χ : Character ℤ)

theorem value_convolution_le_int (a b : ℕ) :
    χ.value (convolution a b) ≤ ((a + b - 1 : ℕ) : ℝ) := by
  classical
  obtain ⟨t, htS, hu⟩ := Integral.exists_finite_bezout_of_prime_witness {D | ∃ d : ℕ, ∀ k,
    Foundation.Tensor.RankAtMost (fun x y z => D ^ k * Foundation.Tensor.power
      (convolution a b) k x y z) ((a + b - 1) ^ k * d)} fun p hp => by
    letI : Fact p.Prime := ⟨hp⟩
    obtain ⟨D, d, hD, h⟩ := Integral.exists_prime_clearing_convolution p a b
    exact ⟨D, ⟨d, h⟩, fun h => hD ((ZMod.intCast_zmod_eq_zero_iff_dvd D p).mpr h)⟩
  choose d hd using fun i : t => htS i.2
  refine le_of_eventually_pow_le_const_mul_pow (C := ((∑ j, d j : ℕ) : ℝ)) (Nat.cast_nonneg _) (.of_forall fun k => ?_)
  obtain ⟨u, hu⟩ := hu k
  simpa [χ.value_power, Finset.mul_sum, mul_comm] using
    χ.value_le_rank (Integral.rankAtMost_patch _ (fun j : t => (j : ℤ) ^ k) u _ hu (hd · k))

end AuxiliarySeparation.Character

/-! Finite laws, Shannon entropy, exact-type words, and the entropy growth
rate of the number of words of a repeated type. -/


namespace Foundation

open Filter Nat

variable {A : Type*} [Fintype A]

def finiteEntropy (p : A → ℝ) : ℝ := ∑ a, Real.negMulLog (p a)

structure FiniteLaw (A : Type*) [Fintype A] where
  mass : A → ℝ
  nonneg : ∀ a, 0 ≤ mass a
  total : ∑ a, mass a = 1

theorem tendsto_finiteEntropy_of_tendsto {I : Type*} {l : Filter I} {p : I → A → ℝ} {q : A → ℝ}
    (h : ∀ a, Tendsto (fun i => p i a) l (𝓝 (q a))) :
    Tendsto (fun i => finiteEntropy (p i)) l (𝓝 (finiteEntropy q)) :=
  tendsto_finsetSum _ fun a _ => (Real.continuous_negMulLog.tendsto _).comp (h a)

def ExactWords [DecidableEq A] (counts : A → ℕ) :=
  {w : Fin (∑ a, counts a) → A // ∀ a, Fintype.card {i // w i = a} = counts a}

instance [DecidableEq A] (counts : A → ℕ) : Fintype (ExactWords counts) := by
  unfold ExactWords; infer_instance

theorem exactWords_card_mul [DecidableEq A] (counts : A → ℕ) :
    Fintype.card (ExactWords counts) * ∏ a, (counts a)! = (∑ a, counts a)! := by
  classical
  let e : Fin (∑ a, counts a) ≃ Σ a, Fin (counts a) := Fintype.equivOfCardEq (by simp)
  let w := fun i => (e i).1
  have hw a : Fintype.card {i // w i = a} = counts a := (Fintype.card_congr
    ((e.subtypeEquiv fun _ => Iff.rfl).trans (Equiv.sigmaSubtype a))).trans (Fintype.card_fin _)
  let G := DomMulAct (Equiv.Perm (Fin (∑ a, counts a)))
  let : Fintype G := Fintype.ofEquiv _ DomMulAct.mk
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group G w
  rw [Fintype.card_congr (Equiv.subtypeEquiv (q := fun g : Equiv.Perm _ => w ∘ g = w) DomMulAct.mk.symm fun _ =>
      DomMulAct.mem_stabilizer_iff), DomMulAct.stabilizer_card,
    Fintype.card_congr DomMulAct.mk.symm, Fintype.card_perm, Fintype.card_fin] at h
  simp only [hw] at h
  rw [← h]
  congr 1
  refine Fintype.card_congr (Equiv.subtypeEquivRight fun v => ?_)
  refine ⟨fun h => ⟨DomMulAct.mk _, (funext (Equiv.ofFiberEquiv_map fun a =>
    Fintype.equivOfCardEq ((h a).trans (hw a).symm)) :)⟩, fun h a => ?_⟩
  obtain ⟨g, rfl⟩ := h
  exact (Fintype.card_congr ((DomMulAct.mk.symm g).subtypeEquiv fun _ => Iff.rfl)).trans (hw a)

theorem exactWords_card_pos [DecidableEq A] (counts : A → ℕ) :
    0 < Fintype.card (ExactWords counts) :=
  Nat.pos_of_ne_zero fun h => factorial_ne_zero _ (by simpa [h] using (exactWords_card_mul counts).symm)

def factorialLogRemainder (n : ℕ) : ℝ := Real.log (n ! : ℝ) - (n * Real.log n - n)

theorem tendsto_factorialLogRemainder_mul_div (m : ℕ) :
    Tendsto (fun t : ℕ => factorialLogRemainder (t * m) / t) atTop (𝓝 0) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [factorialLogRemainder]
  have h : Tendsto (fun n : ℕ => factorialLogRemainder n / n) atTop (𝓝 0) := by
    have := ((Stirling.tendsto_stirlingSeq_sqrt_pi.log (by positivity)).div_atTop
      tendsto_natCast_atTop_atTop).add ((((tendsto_const_nhds (x := Real.log 2)).div_atTop
        tendsto_natCast_atTop_atTop).add (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
          tendsto_natCast_atTop_atTop)).const_mul (1 / 2))
    simp at this
    refine this.congr' ((eventually_ne_atTop 0).mono fun n hn => ?_)
    have := Stirling.log_stirlingSeq_formula n
    rw [Real.log_div (by positivity) (by positivity), Real.log_exp,
      Real.log_mul two_ne_zero (by positivity)] at this
    simp [factorialLogRemainder, this]
    field_simp
    ring
  have := (h.comp (tendsto_id.atTop_mul_const' hm)).mul_const (m : ℝ)
  rw [zero_mul] at this
  refine this.congr' ((eventually_ne_atTop 0).mono fun t ht => ?_)
  simp
  field_simp

theorem tendsto_log_exactWords_card_mul [DecidableEq A] (c : A → ℕ) (hD : 0 < ∑ a, c a) :
    Tendsto (fun t : ℕ => Real.log (Fintype.card (ExactWords fun a => t * c a)) /
        (t * (∑ a, c a : ℕ))) atTop (𝓝 (finiteEntropy fun a => (c a : ℝ) / (∑ a, c a : ℕ))) := by
  have := (tendsto_const_nhds (x := finiteEntropy fun a => (c a : ℝ) / (∑ a, c a : ℕ))).add
    (((tendsto_factorialLogRemainder_mul_div (∑ a, c a)).sub (tendsto_finsetSum Finset.univ
      fun a _ => tendsto_factorialLogRemainder_mul_div (c a))).div_const ((∑ a, c a : ℕ) : ℝ))
  simp only [Finset.sum_const_zero, sub_zero, zero_div, add_zero] at this
  refine this.congr' ((eventually_ne_atTop 0).mono fun t ht => ?_)
  have h := congrArg (fun n : ℕ => Real.log n) (exactWords_card_mul fun a => t * c a)
  simp at h
  rw [Real.log_mul (mod_cast (exactWords_card_pos _).ne') (by positivity),
    Real.log_prod fun a _ => by positivity] at h
  dsimp only
  rw [eq_sub_of_add_eq h]
  have hN : ((∑ a, c a : ℕ) : ℝ) ≠ 0 := by positivity
  have e a : Real.negMulLog ((c a : ℝ) / (∑ a, c a : ℕ)) = (t * c a * Real.log (t * (∑ a, c a : ℕ)) -
      t * c a * Real.log (t * c a)) / (t * (∑ a, c a : ℕ)) := by
    rcases eq_or_ne (c a) 0 with h | h
    · simp_all
    rw [Real.negMulLog, Real.log_div (by positivity) hN, Real.log_mul (by positivity) hN,
      Real.log_mul (by positivity) (by positivity)]
    field_simp
    ring
  simp only [finiteEntropy, e, factorialLogRemainder, ← Finset.sum_div, Finset.sum_sub_distrib,
    ← Finset.sum_mul, Nat.cast_mul]
  field_simp
  simp [← Finset.mul_sum, Nat.cast_sum]
  ring

end Foundation

/-!
# Probability laws for the polynomial tensor inequalities

The determinant filtration uses an arbitrary binary law, while the three-sector
filtration uses the uniform law on three branches.
-/



namespace AuxiliarySeparation

/-- The common binary probability law used for every permuted character. -/
def binaryLaw (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) : FiniteLaw (Fin 2) where
  mass i := if i = 0 then q else 1 - q
  nonneg i := by grind
  total := by simp

theorem binaryLaw_entropy (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    finiteEntropy (binaryLaw q hq₀ hq₁).mass = Real.binEntropy q := by
  simp [binaryLaw, finiteEntropy, Fin.sum_univ_two, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]

theorem binaryLaw_product (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) (f : Fin 2 → ℝ) :
    (∏ i, f i ^ (binaryLaw q hq₀ hq₁).mass i) = f 0 ^ q * f 1 ^ (1 - q) := by
  simp [binaryLaw, Fin.prod_univ_two]

def uniformThree : FiniteLaw (Fin 3) := ⟨fun _ => 1 / 3, by norm_num, by norm_num⟩

theorem uniformThree_entropy_factor (p : ℝ) :
    Real.exp (p * finiteEntropy uniformThree.mass) = (3 : ℝ) ^ p := by
  simp [finiteEntropy, uniformThree, Real.negMulLog, Real.rpow_def_of_pos, mul_comm]

theorem uniformThree_product (f : Fin 3 → ℝ) :
    (∏ i, f i ^ uniformThree.mass i) =
      f 0 ^ (1 / 3 : ℝ) * f 1 ^ (1 / 3 : ℝ) * f 2 ^ (1 / 3 : ℝ) := by
  simp [Fin.prod_univ_three, uniformThree, mul_assoc]

end AuxiliarySeparation

/-! Polynomial tensor restrictions and exact coefficient extraction. -/



namespace Foundation.Tensor


variable {F X Y Z X' Y' Z' : Type*} [CommRing F]
variable [Fintype X] [Fintype Y] [Fintype Z]

structure PolynomialRestrictionDegeneration
    (T : Tensor F X Y Z) (U : Tensor F X' Y' Z') (k Lx Ly Lz : ℕ) where
  leftMap : X' → X → Polynomial F
  middleMap : Y' → Y → Polynomial F
  rightMap : Z' → Z → Polynomial F
  left_degree : ∀ x' x, (leftMap x' x).degree ≤ Lx
  middle_degree : ∀ y' y, (middleMap y' y).degree ≤ Ly
  right_degree : ∀ z' z, (rightMap z' z).degree ≤ Lz
  vanishes : ∀ x' y' z' j, j < k →
    (restrict leftMap middleMap rightMap
      (fun x y z => Polynomial.C (T x y z)) x' y' z').coeff j = 0
  leading : ∀ x' y' z',
    (restrict leftMap middleMap rightMap
      (fun x y z => Polynomial.C (T x y z)) x' y' z').coeff k = U x' y' z'

end Foundation.Tensor
namespace AuxiliarySeparation.Integral



/-!
# Coefficient extraction without interpolation

Only the first two local-map degrees control the number of copies. The guard
in `shiftedCoeff` is essential: natural subtraction alone would incorrectly
reuse the constant coefficient when the shift exceeds the requested degree.
-/


open scoped Polynomial

variable {R : Type*} [CommSemiring R]

/-- Expanding just the first two factors gives a quadratic-size extraction. -/
theorem coeff_mul_mul_bounded (p q t : R[X]) (a b h : ℕ)
    (hp : p.natDegree ≤ a) (hq : q.natDegree ≤ b) :
    (p * q * t).coeff h =
      ∑ i : Fin (a + 1), ∑ j : Fin (b + 1),
        p.coeff i * q.coeff j * if i.val + j.val ≤ h then t.coeff (h - (i + j)) else 0 := by
  conv_lhs => rw [p.as_sum_range' (a + 1) (by omega), q.as_sum_range' (b + 1) (by omega)]
  simp only [← Fin.sum_univ_eq_sum_range, Finset.sum_mul, Finset.mul_sum, Polynomial.finsetSum_coeff,
    Polynomial.monomial_mul_monomial]
  simp [← Polynomial.C_mul_X_pow_eq_monomial, mul_assoc, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow_mul']
  exact Finset.sum_comm

end AuxiliarySeparation.Integral

namespace Foundation.Tensor.PolynomialRestrictionDegeneration

open scoped Polynomial
open OAI.MatrixMultiplication.AuxiliarySeparation.Integral

variable {R X Y Z X' Y' Z' : Type*} [CommRing R]
variable [Fintype X] [Fintype Y] [Fintype Z]
variable {T : Tensor R X Y Z} {U : Tensor R X' Y' Z'}
variable {k Lx Ly Lz : ℕ}

theorem D {A B : Type*} {F : A → B → R[X]} {L n : ℕ} (hF : ∀ a b, (F a b).degree ≤ L)
    (a : Fin n → A) (b : Fin n → B) : (∏ i, F (a i) (b i)).degree ≤ ↑(L * n) :=
  Polynomial.degree_le_of_natDegree_le ((Polynomial.natDegree_prod_le _ _).trans
    ((Finset.sum_le_card_nsmul _ _ _ fun i _ => Polynomial.natDegree_le_of_degree_le
      (hF _ _)).trans_eq (by simp [mul_comm])))

/-- Powers of a polynomial restriction over a ring retain linear local-degree
bounds. This is the same degeneration structure as the original field proof. -/
def power (L : PolynomialRestrictionDegeneration T U k Lx Ly Lz) (n : ℕ) :
    PolynomialRestrictionDegeneration (Tensor.power T n) (Tensor.power U n)
      (k * n) (Lx * n) (Ly * n) (Lz * n) := by
  obtain ⟨f, g, h, hf, hg, hh, hv, hl⟩ := L
  choose N hN using fun x y z => Polynomial.X_pow_dvd_iff.mpr (hv x y z)
  refine ⟨fun x u => ∏ i, f (x i) (u i), fun y v => ∏ i, g (y i) (v i),
    fun z w => ∏ i, h (z i) (w i), D hf, D hg, D hh, fun x y z j hj => ?_, fun x y z => ?_⟩
  all_goals rw [show (fun u v w => Polynomial.C (Tensor.power T n u v w)) =
    Tensor.power (fun u v w => Polynomial.C (T u v w)) n by funext; simp [Tensor.power],
    restrict_power]
  all_goals simp [Tensor.power, hN, Finset.prod_mul_distrib, ← pow_mul, Polynomial.coeff_X_pow_mul',
    Polynomial.coeff_zero_prod, ← hl]
  omega

/-- An exact restriction from `(Lx+1)(Ly+1)` source copies, obtained by taking
one coefficient rather than evaluating at field points. -/
theorem extract (L : PolynomialRestrictionDegeneration T U k Lx Ly Lz) :
    ∃ A B C, U = Tensor.restrict A B C
      (Tensor.directSum (fun _ : Fin (Lx + 1) × Fin (Ly + 1) => T)) := by
  refine ⟨_, _, _, (restrict_directSum (fun _ : Fin (Lx + 1) × Fin (Ly + 1) => T)
    (fun q x u => (L.leftMap x u).coeff q.1)
    (fun q y v => (L.middleMap y v).coeff q.2)
    (fun q z w => if q.1.val + q.2.val ≤ k then (L.rightMap z w).coeff (k - (q.1 + q.2)) else 0)).trans ?_ |>.symm⟩
  funext x y z
  rw [← L.leading]
  simp only [Tensor.restrict, Polynomial.finsetSum_coeff, Polynomial.coeff_mul_C]
  simp_rw [coeff_mul_mul_bounded _ _ _ Lx Ly k (Polynomial.natDegree_le_of_degree_le (L.left_degree _ _)) (Polynomial.natDegree_le_of_degree_le (L.middle_degree _ _))]
  simp only [Finset.sum_mul]
  rw [← sum_comm_three]
  simp [Fintype.sum_prod_type]

end Foundation.Tensor.PolynomialRestrictionDegeneration


namespace AuxiliarySeparation


/-- A polynomial prefactor does not change an exponential growth rate. -/
theorem le_of_pow_le_const_product_linear_mul_pow {a b A B C : ℝ}
    (ha : 0 ≤ a)
    (h : ∀ n : ℕ, b ^ n ≤ C * ((n : ℝ) * A + 1) * (n * B + 1) * a ^ n) :
    b ≤ a := by
  by_contra! hab
  have hb := ha.trans_lt hab
  have hr₀ := div_nonneg ha hb.le
  have hr₁ := (div_lt_one hb).2 hab
  have hlim : Tendsto (fun n : ℕ => C * ((n : ℝ) * A + 1) * (n * B + 1) * (a / b) ^ n) atTop (𝓝 0) := by
    convert (((tendsto_pow_const_mul_const_pow_of_lt_one 2 hr₀ hr₁).mul_const (C * A * B)).add
      ((tendsto_self_mul_const_pow_of_lt_one hr₀ hr₁).mul_const (C * (A + B)))).add
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hr₀ hr₁).const_mul C) using 1 <;> try simp
    funext n
    ring
  have : (1 : ℝ) ≤ 0 := ge_of_tendsto hlim (Eventually.of_forall fun n => by
    simpa only [div_self (pow_ne_zero n hb.ne'), mul_div_assoc, div_pow] using
      (div_le_div_iff_of_pos_right (pow_pos hb n)).2 (h n))
  linarith

namespace Character


variable {K : Type*} [CommRing K]
variable (χ : Character K)
variable {X Y Z X' Y' Z' : Type}
variable [Fintype X] [Fintype Y] [Fintype Z]
variable [Fintype X'] [Fintype Y'] [Fintype Z']

/-- Division-free polynomial coefficient extraction proves character
monotonicity over every commutative ring. No infinitude or field assumption
and no continuity of the character are needed. -/
theorem value_polynomialRestrictionDegeneration_le_ring
    {T : Tensor K X Y Z} {U : Tensor K X' Y' Z'} {k Lx Ly Lz : ℕ}
    (L : Tensor.PolynomialRestrictionDegeneration T U k Lx Ly Lz) :
    χ.value U ≤ χ.value T := by
  apply le_of_pow_le_const_product_linear_mul_pow
    (A := (Lx : ℝ)) (B := (Ly : ℝ)) (C := 1) (χ.nonneg T)
  intro n
  obtain ⟨A, B, C, h⟩ := (L.power n).extract
  have h := h ▸ χ.monotone _ A B C
  simp [χ.value_power, χ.map_directSum, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at h
  convert h using 1 <;> ring

/-- A fixed constant and two local polynomial degree bounds disappear in a
power comparison. The exponential source-copy factor `L^n` remains as `L`. -/
theorem value_le_mul_of_power_comparisons
    (T : Tensor K X Y Z) (U : Tensor K X' Y' Z') (A B C L : ℝ) (hL : 0 ≤ L)
    (h : ∀ n : ℕ, χ.value (Tensor.power U n) ≤
      C * ((n : ℝ) * A + 1) * (n * B + 1) * L ^ n * χ.value (Tensor.power T n)) :
    χ.value U ≤ L * χ.value T := by
  apply le_of_pow_le_const_product_linear_mul_pow
    (mul_nonneg hL (χ.nonneg T))
  intro n
  simpa only [χ.value_power, mul_pow, mul_assoc] using h n

/-- A pair of coprime scalar powers is cancelled before applying monotonicity.
The two exact restrictions may have unrelated finite coordinate spaces. -/
theorem value_le_add_of_coprime_scaled_restrictions
    {U₁ V₁ W₁ U₂ V₂ W₂ : Type}
    [Fintype U₁] [Fintype V₁] [Fintype W₁]
    [Fintype U₂] [Fintype V₂] [Fintype W₂]
    (T : Tensor K X Y Z) (S₁ : Tensor K U₁ V₁ W₁) (S₂ : Tensor K U₂ V₂ W₂)
    {d e : K} (hde : IsCoprime d e) (n : ℕ)
    (h₁ : ∃ A B C, Tensor.restrict A B C S₁ = fun x y z => d ^ n * T x y z)
    (h₂ : ∃ A B C, Tensor.restrict A B C S₂ = fun x y z => e ^ n * T x y z) :
    χ.value T ≤ χ.value S₁ + χ.value S₂ := by
  obtain ⟨u, v, huv⟩ := hde.pow
  obtain ⟨A, B, C, h₁⟩ := h₁
  obtain ⟨A', B', C', h₂⟩ := h₂
  simp [funext_iff] at h₁ h₂
  convert χ.monotone (sumTensor S₁ S₂)
    (fun x => Sum.elim (A x) (A' x)) (fun y => Sum.elim (B y) (B' y))
    (fun z => Sum.elim (fun w => u * C z w) (fun w => v * C' z w)) using 1
  · congr
    funext x y z
    rw [← one_mul (T x y z), ← huv, add_mul, mul_assoc, mul_assoc, ← h₁, ← h₂]
    simp [Tensor.restrict, Fintype.sum_sum_type, sumTensor, Finset.mul_sum, mul_comm, mul_left_comm]
  exact (χ.value_sumTensor _ _).symm

end Character

/-!
# The tensor map with an arbitrary Fourier period

The branches have a common first coordinate space and common sizes on the other
two legs. Their second and third coordinates carry a matching sector label.
The three maps below are independent linear substitutions on the three legs of
`L` complete copies of the source tensor.
-/




variable {M L : ℕ} {X Y Z : Type*}

/-- Branches sharing X, with matching and disjoint Y and Z sectors. -/
def sharedFirstTensor {K : Type*} [CommSemiring K] (B : Fin M → Tensor K X Y Z) :
    Tensor K X (Fin M × Y) (Fin M × Z) :=
  fun x y z => if y.1 = z.1 then B y.1 x y.2 z.2 else 0

/-- The surviving tensor: sector labels match on all three legs, while the
additional second/third coordinates form a dot product. -/
def separationTarget {K : Type*} [CommSemiring K] (B : Fin M → Tensor K X Y Z) :
    Tensor K (X × Fin M) ((Fin M × Y) × Fin M) ((Fin M × Z) × Fin M) :=
  fun x y z => if x.2 = y.1.1 ∧ y.1.1 = z.1.1 ∧ y.2 = z.2 then
    B y.1.1 x.1 y.1.2 z.1.2 else 0

/-- The first-leg relabeling adds the trivial first coordinate of the dot product. -/
def separationFirstEquiv : (X × Fin M) ≃ (Fin M × (X × Unit)) where
  toFun x := (x.2, (x.1, ()))
  invFun x := (x.2.1, x.1)
  left_inv _ := rfl
  right_inv x := by grind

/-- The other two relabelings merely reassociate their coordinates. -/
def separationSideEquiv (A : Type*) : ((Fin M × A) × Fin M) ≃
    (Fin M × (A × Fin M)) := Equiv.prodAssoc _ _ _

/-- The separated target, expressed as a genuine full direct sum of products. -/
theorem separationTarget_eq_directSum {K : Type*} [CommSemiring K]
    (B : Fin M → Tensor K X Y Z) :
    separationTarget B =
      Tensor.pullback
        separationFirstEquiv (separationSideEquiv Y) (separationSideEquiv Z)
        (Tensor.directSum (fun h => Tensor.product (B h)
          (Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (Fin M)))))) := by
  classical
  funext x y z
  simp [separationTarget, Tensor.pullback, Tensor.directSum, Tensor.product,
    Tensor.cyclic, Tensor.dotPairing, separationFirstEquiv, separationSideEquiv,
    Equiv.coe_fn_mk, Equiv.prodAssoc_apply]
  by_cases hxy : x.2 = y.1.1 <;> grind


/-! An explicit polynomial degeneration to `L` times the separated tensor over a
domain with a primitive `L`-th root of unity. The Fourier phase `u - v + 2 (g - h)`
selects monomials; on the selected ones the degree is `2 M² + (g - h)²`. -/

namespace Integral



variable {E : Type*} [CommRing E] [IsDomain E] {M L : ℕ} {X Y Z : Type*}

theorem fourier_sum {ζ : Eˣ} (hζ : IsPrimitiveRoot ζ L) {e : ℤ} (he : |e| < L) :
    ∑ r : Fin L, (↑(ζ ^ ((r : ℤ) * e)) : E) = if e = 0 then (L : E) else 0 := by
  have h (r : ℕ) : (↑(ζ ^ ((r : ℤ) * e)) : E) = (↑(ζ ^ e) : E) ^ r := by
    rw [mul_comm, zpow_mul, zpow_natCast, Units.val_pow_eq_pow_val]
  rw [Fin.sum_univ_eq_sum_range (fun r : ℕ => (↑(ζ ^ ((r : ℤ) * e)) : E))]
  simp_all
  split_ifs with h0
  · simp_all
  refine (mul_eq_zero.1 (?_ : (1 - (↑(ζ ^ e) : E)) * _ = 0)).resolve_left
    (sub_ne_zero.2 fun h1 => h0 (Int.eq_zero_of_abs_lt_dvd
      ((hζ.zpow_eq_one_iff_dvd e).1 (Units.val_eq_one.1 h1.symm)) he))
  rw [mul_neg_geom_sum, ← Units.val_pow_eq_pow_val, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
    zpow_natCast, hζ.pow_eq_one, one_zpow, Units.val_one, sub_self]

theorem exists_degree_bound {A B : Type*} [Fintype A] [Fintype B] (P : A → B → Polynomial E) :
    ∃ N : ℕ, ∀ a b, (P a b).degree ≤ N :=
  ⟨_, fun a b => Polynomial.degree_le_of_natDegree_le
    (Finset.le_sup (f := fun q : A × B => (P q.1 q.2).natDegree) (Finset.mem_univ (a, b)))⟩

/-- No inverse of L occurs in any local map. -/
theorem integralSeparationDegeneration [Fintype X] [Fintype Y] [Fintype Z]
    {ζ : Eˣ} (hM : 0 < M) (hL : 5 * M ≤ L) (hζ : IsPrimitiveRoot ζ L)
    (B : Fin M → Tensor E X Y Z) : ∃ Lx Ly Lz, Nonempty (Tensor.PolynomialRestrictionDegeneration
      (Tensor.directSum (fun _ : Fin L => sharedFirstTensor B))
      (fun x y z => (L : E) * separationTarget B x y z) (2 * M ^ 2) Lx Ly Lz) := by
  classical
  let m (d : ℕ) (e : ℤ) (r : Fin L) : Polynomial E := Polynomial.monomial d ↑(ζ ^ ((r : ℤ) * e))
  let a := fun (x : X × Fin M) (r : Fin L × X) =>
    if r.2 = x.1 then m (x.2 * x.2) (2 * x.2) r.1 else 0
  let b := fun (y : (Fin M × Y) × Fin M) (r : Fin L × (Fin M × Y)) =>
    if r.2 = y.1 then m (M * M + y.1.1 * y.2 - y.1.1 * y.1.1) (y.2 - y.1.1) r.1 else 0
  let c := fun (z : (Fin M × Z) × Fin M) (r : Fin L × (Fin M × Z)) =>
    if r.2 = z.1 then m (M * M - z.1.1 * z.2) (-z.2 - z.1.1) r.1 else 0
  have key x y z : Tensor.restrict a b c
      (fun x y z => Polynomial.C (Tensor.directSum (fun _ : Fin L => sharedFirstTensor B) x y z)) x y z =
      Polynomial.monomial (x.2 * x.2 + (M * M + y.1.1 * y.2 - y.1.1 * y.1.1) + (M * M - z.1.1 * z.2))
        ((∑ r : Fin L, (↑(ζ ^ ((r : ℤ) * (2 * x.2 + (y.2 - y.1.1) + (-z.2 - z.1.1)))) : E)) *
          sharedFirstTensor B x.1 y.1 z.1) := by
    simp [Tensor.restrict, Tensor.directSum, Fintype.sum_prod_type, a, b, c, m, ite_and, Finset.sum_mul,
      Polynomial.monomial_mul_monomial]
    simp [apply_ite (Polynomial.monomial _), map_zero]
    simp [← Units.val_mul, ← zpow_add, mul_add]
  have hD (g h u v : ℕ) (hh : h < M) (hu : u < M) (hv : v < M) (hp : 2 * g + (u - h) + (-v - h : ℤ) = 0) :
      ((g * g + (M * M + h * u - h * h) + (M * M - h * v) : ℕ) : ℤ) = 2 * M ^ 2 + (g - h : ℤ) ^ 2 := by
    push_cast [Nat.cast_sub (by nlinarith : h * v ≤ M * M), Nat.cast_sub (by nlinarith : h * h ≤ M * M + h * u)]
    nlinarith
  refine ⟨_, _, _, ⟨a, b, c, (exists_degree_bound _).choose_spec, (exists_degree_bound _).choose_spec,
    (exists_degree_bound _).choose_spec, fun ⟨x, g⟩ ⟨⟨h, y⟩, u⟩ ⟨⟨h', z⟩, v⟩ j hj => ?_,
    fun ⟨x, g⟩ ⟨⟨h, y⟩, u⟩ ⟨⟨h', z⟩, v⟩ => ?_⟩⟩ <;>
    rw [key, Polynomial.coeff_monomial, fourier_sum hζ (abs_lt.2 ⟨by omega, by omega⟩)] <;> clear key <;>
    simp only [sharedFirstTensor, separationTarget] <;> simp only [ite_mul, mul_ite, zero_mul, mul_zero, ← ite_and]
  · rw [if_neg]
    rintro ⟨rfl, rfl, hp⟩
    have := Int.ofNat_lt.2 hj
    rw [hD _ _ _ _ h.2 u.2 v.2 hp] at this
    push_cast at this
    nlinarith
  refine if_congr ⟨fun ⟨h1, h2, hp⟩ => ?_, fun ⟨h1, h2, h3⟩ => ?_⟩ rfl rfl
  · subst h2
    have := hD _ _ _ _ h.2 u.2 v.2 hp
    push_cast at this
    have : ((g : ℕ) : ℤ) - h = 0 := pow_eq_zero_iff two_ne_zero |>.1 (by linarith)
    grind
  subst h1 h2 h3
  have hp : 2 * ((g : ℕ) : ℤ) + (u - g) + (-u - g) = 0 := by ring
  refine ⟨?_, rfl, hp⟩
  have := hD _ _ _ _ g.2 u.2 u.2 hp
  simp at this
  exact_mod_cast this



/-! Restriction-level finite-free descent. Kept separate from rank descent so
its larger coefficient-map identities do not delay monic quotient setup. -/



variable {R E ι X Y Z U V W : Type*}
variable [CommRing R] [CommRing E] [Algebra R E] [Fintype ι]

/-- When the functional splits the unit, a restriction defined over the finite
free algebra descends to D² source copies over the base ring. -/
theorem descend_restriction_basis [Fintype U] [Fintype V] [Fintype W]
    [DecidableEq ι] (basis : Module.Basis ι R E) (π : E →ₗ[R] R) (hπ : π 1 = 1)
    (S : Tensor R X Y Z) (T : Tensor R U V W)
    (A : X → U → E) (B : Y → V → E) (C : Z → W → E)
    (h : Tensor.restrict A B C (fun u v w => algebraMap R E (T u v w)) =
      fun x y z => algebraMap R E (S x y z)) :
    ∃ A B C, S = Tensor.restrict A B C (Tensor.directSum (fun _ : ι × ι => T)) := by
  refine ⟨_, _, _, (restrict_directSum (fun _ : ι × ι => T)
    (fun q x u => basis.repr (A x u) q.1) (fun q y v => basis.repr (B y v) q.2)
    (fun q z w => π (basis q.1 * basis q.2 * C z w))).trans ?_ |>.symm⟩
  funext x y z
  have := congr(π ($h x y z))
  simp [Algebra.algebraMap_eq_smul_one, map_smul, hπ, smul_eq_mul, mul_one, Tensor.restrict,
    map_sum, Tensor.project_mul_mul basis π (A _ _)] at this
  rw [← this]
  simp [Tensor.restrict]
  rw [← sum_comm_three]
  simp [Fintype.sum_prod_type, Finset.mul_sum]
  ac_rfl



/-! Integral cyclotomic coefficients: a fixed finite free algebra containing
a primitive root as a unit, without inverting its order. -/



abbrev CyclotomicAlgebra (L : ℕ) := AdjoinRoot (Polynomial.cyclotomic L ℤ)

instance cyclotomicAlgebra_isDomain (L : ℕ) [NeZero L] :
    IsDomain (CyclotomicAlgebra L) :=
  AdjoinRoot.isDomain_of_prime (Polynomial.cyclotomic.irreducible (NeZero.pos L)).prime

theorem cyclotomic_natDegree_pos (L : ℕ) [NeZero L] :
    0 < (Polynomial.cyclotomic L ℤ).natDegree := by
  rw [Polynomial.natDegree_cyclotomic]
  exact Nat.totient_pos.mpr (NeZero.pos L)

instance cyclotomicAlgebra_charZero (L : ℕ) [NeZero L] :
    CharZero (CyclotomicAlgebra L) := by
  apply charZero_of_injective_algebraMap (R := ℤ)
  exact AdjoinRoot.of.injective_of_monic_of_degree_pos
    (Polynomial.cyclotomic.monic L ℤ)
    (Polynomial.natDegree_pos_iff_degree_pos.mp (cyclotomic_natDegree_pos L))

theorem cyclotomic_root_primitive (L : ℕ) [NeZero L] :
    IsPrimitiveRoot (AdjoinRoot.root (Polynomial.cyclotomic L ℤ)) L := by
  apply (Polynomial.isRoot_cyclotomic_iff_charZero (NeZero.pos L)).mp
  rw [← Polynomial.map_cyclotomic_int L (CyclotomicAlgebra L)]
  exact AdjoinRoot.isRoot_root _

def cyclotomicUnit (L : ℕ) [NeZero L] : (CyclotomicAlgebra L)ˣ :=
  ((cyclotomic_root_primitive L).isUnit (NeZero.ne L)).unit

theorem cyclotomicUnit_primitive (L : ℕ) [NeZero L] :
    IsPrimitiveRoot (cyclotomicUnit L) L :=
  (cyclotomic_root_primitive L).isUnit_unit (NeZero.ne L)





variable {M L : ℕ} {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]

abbrev CyclotomicIndex (L : ℕ) := Fin (Polynomial.cyclotomic L ℤ).natDegree

/-- One period supplies all powers of a scalar multiple, in a single fixed
finite free cyclotomic algebra. The degree bounds are chosen before n. -/
theorem separation_scalar_power_restrictions (hM : 0 < M) (hL : 5 * M ≤ L)
    (B : Fin M → Tensor ℤ X Y Z) :
    ∃ Lx Ly : ℕ, ∀ n : ℕ,
      ∃ A C D, Tensor.restrict A C D
          (Tensor.directSum fun _ : CyclotomicIndex L × CyclotomicIndex L =>
            Tensor.directSum fun _ : Fin (Lx * n + 1) × Fin (Ly * n + 1) =>
              Tensor.power (Tensor.directSum fun _ : Fin L => sharedFirstTensor B) n) =
          fun x y z => (L : ℤ) ^ n * Tensor.power (separationTarget B) n x y z := by
  classical
  letI : NeZero L := ⟨by omega⟩
  let BE : Fin M → Tensor (CyclotomicAlgebra L) X Y Z := fun i x y z => algebraMap ℤ _ (B i x y z)
  have hs (x y z) : sharedFirstTensor BE x y z = algebraMap ℤ _ (sharedFirstTensor B x y z) := by
    simp only [sharedFirstTensor, BE]; split_ifs <;> simp
  have ht (x y z) : separationTarget BE x y z = algebraMap ℤ _ (separationTarget B x y z) := by
    simp only [separationTarget, BE]; split_ifs <;> simp
  obtain ⟨Lx, Ly, _, ⟨D⟩⟩ := integralSeparationDegeneration hM hL (cyclotomicUnit_primitive L) BE
  refine ⟨Lx, Ly, fun n => ?_⟩
  obtain ⟨A, B', C, h⟩ := (D.power n).extract
  obtain ⟨A, B', C, h⟩ := descend_restriction_basis (AdjoinRoot.powerBasis' (Polynomial.cyclotomic.monic L ℤ)).basis _
    (Tensor.coord_one (Polynomial.cyclotomic.monic L ℤ) (cyclotomic_natDegree_pos L)) (fun x y z => (L : ℤ) ^ n * Tensor.power (separationTarget B) n x y z)
    (Tensor.directSum fun _ : Fin (_ * n + 1) × Fin (_ * n + 1) =>
      Tensor.power (Tensor.directSum fun _ : Fin L => sharedFirstTensor B) n) A B' C (by
      convert h.symm using 2 <;> simp [funext_iff, Tensor.directSum, Tensor.power, hs, ht,
        Finset.prod_mul_distrib])
  exact ⟨A, B', C, h.symm⟩

/-- Consecutive periods cancel their scalar powers by Bezout before a
character is evaluated. The constant and quadratic costs disappear in n. -/
theorem value_separationTarget_le_int (χ : Character ℤ) (hM : 0 < M)
    (B : Fin M → Tensor ℤ X Y Z) :
    χ.value (separationTarget B) ≤ 6 * (M : ℝ) * χ.value (sharedFirstTensor B) := by
  classical
  obtain ⟨Ax, Ay, hA⟩ := separation_scalar_power_restrictions hM le_rfl B
  obtain ⟨Bx, By, hB⟩ := separation_scalar_power_restrictions hM (L := 5 * M + 1) (by omega) B
  have : (1 : ℝ) ≤ M := mod_cast hM
  refine (χ.value_le_mul_of_power_comparisons _ _ (Ax + Bx) (Ay + By)
    ((Fintype.card (CyclotomicIndex (5 * M)) : ℝ) ^ 2 + Fintype.card (CyclotomicIndex (5 * M + 1)) ^ 2)
    (5 * M + 1) (by positivity) fun n => ((χ.value_le_add_of_coprime_scaled_restrictions _ _ _
      ⟨-1, 1, by grind⟩ n (hA n) (hB n)).trans ?_)).trans
    (mul_le_mul_of_nonneg_right (by linarith) (χ.nonneg _))
  rw [add_mul, add_mul, add_mul, add_mul]
  simp [χ.map_directSum, χ.value_power, Finset.sum_const, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    Nat.cast_ofNat, Nat.cast_pow, ← mul_pow, mul_assoc, ← sq]
  lift χ.value (sharedFirstTensor B) to NNReal using χ.nonneg _ with v
  gcongr _ * (?_ * (?_ * ?_)) + _ * (?_ * (?_ * ?_))
  all_goals first | (norm_cast; nlinarith) | (gcongr ?_ ^ _; nlinarith [v.coe_nonneg])

theorem finiteSeparation_bound_int (χ : Character ℤ) (hM : 0 < M)
    (B : Fin M → Tensor ℤ X Y Z) :
    (∑ i, χ.value (B i)) * (M : ℝ) ^ χ.pX ≤
      6 * (M : ℝ) * χ.value (sharedFirstTensor B) := by
  have h := value_separationTarget_le_int χ hM B
  rw [separationTarget_eq_directSum, χ.value_reindex, χ.map_directSum] at h
  simpa only [χ.map_product, χ.value_cyclic_cyclic_dotPairing hM, Finset.sum_mul] using h

end MatrixMultiplication.AuxiliarySeparation.Integral


/-!
# The entropy limit for matched types

The finite hypothesis in this file is an inequality at every integral type.
The conclusion follows by first repeating a fixed type, and then approximating
an arbitrary probability law by rational laws. No entropy inequality is
included in the finite hypothesis.
-/



namespace MatrixMultiplication.AuxiliarySeparation

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- Integral type bounds imply the tag inequality: first for repetitions of a
fixed type, then for every law via the types `⌈q a * n⌉₊`. -/
theorem tag_of_integral_bounds (q : FiniteLaw A) (values : A → ℝ) (p source C : ℝ)
    (hvalues : ∀ a, 0 < values a) (hsource : 0 < source) (hC : 0 < C)
    (hfinite : ∀ counts : A → ℕ, 0 < ∑ a, counts a →
      (Fintype.card (ExactWords counts) : ℝ) ^ p * ∏ a, values a ^ counts a ≤
        C * source ^ (∑ a, counts a)) :
    Real.exp (p * finiteEntropy q.mass) * ∏ a, values a ^ q.mass a ≤ source := by
  have key (c : A → ℕ) (hD : 0 < ∑ a, c a) : p * finiteEntropy (fun a => (c a : ℝ) / (∑ a, c a : ℕ)) +
      ∑ a, (c a : ℝ) / (∑ a, c a : ℕ) * Real.log (values a) ≤ Real.log source := by
    have h₁ t : (0 : ℝ) < Fintype.card (ExactWords fun a => t * c a) := by
      exact_mod_cast exactWords_card_pos _
    have h₂ t : 0 < ∏ a, values a ^ (t * c a) := Finset.prod_pos fun a _ => pow_pos (hvalues a) _
    have := ((tendsto_const_div_atTop_nhds_zero_nat (Real.log C)).comp
      (tendsto_id.atTop_mul_const' hD)).add_const (Real.log source)
    rw [zero_add] at this
    refine le_of_tendsto_of_tendsto (((tendsto_log_exactWords_card_mul c hD).const_mul p).add_const _) this
      ((eventually_gt_atTop 0).mono fun t ht => ?_)
    have h := Real.log_le_log (mul_pos (Real.rpow_pos_of_pos (h₁ t) p) (h₂ t))
      (hfinite (fun a => t * c a) (by rw [← Finset.mul_sum]; positivity))
    rw [Real.log_mul (Real.rpow_pos_of_pos (h₁ t) p).ne' (h₂ t).ne', Real.log_rpow (h₁ t),
      Real.log_prod fun a _ => (pow_pos (hvalues a) _).ne', Real.log_mul hC.ne' (by positivity)] at h
    simp at h ⊢
    have hN : 0 < ∑ a, (c a : ℝ) := mod_cast hD
    rw [← sub_nonneg] at h ⊢
    convert div_nonneg h (mul_pos (Nat.cast_pos.2 ht) hN).le using 1
    simp [div_mul_eq_mul_div, ← Finset.sum_div, mul_assoc, ← Finset.mul_sum]
    field_simp
  let c (n : ℕ) a := ⌈q.mass a * n⌉₊
  have hc a : Tendsto (fun n : ℕ => (c n a : ℝ) / n) atTop (𝓝 (q.mass a)) :=
    (tendsto_nat_ceil_mul_div_atTop (q.nonneg a)).comp tendsto_natCast_atTop_atTop
  have hr a : Tendsto (fun n => (c n a : ℝ) / (∑ b, c n b : ℕ)) atTop (𝓝 (q.mass a)) := by
    have := (hc a).div (tendsto_finsetSum Finset.univ fun b _ => hc b) (by simp [q.total])
    rw [q.total, div_one] at this
    refine this.congr' ((eventually_gt_atTop 0).mono fun n hn => ?_)
    simp [Pi.div_apply, ← Finset.sum_div, Nat.cast_sum]
    exact div_div_div_cancel_right₀ (by positivity) _ _
  have hD := (eventually_gt_atTop 0).mono fun n hn => by
    have : (n : ℝ) ≤ ∑ a, (c n a : ℝ) := by
      calc (n : ℝ) = ∑ a, q.mass a * n := by rw [← Finset.sum_mul, q.total, one_mul]
        _ ≤ _ := Finset.sum_le_sum fun a _ => Nat.le_ceil _
    exact_mod_cast (show (0 : ℝ) < n by positivity).trans_le this
  have := le_of_tendsto (((tendsto_finiteEntropy_of_tendsto hr).const_mul p).add
    (tendsto_finsetSum _ fun a _ => (hr a).mul_const _)) (hD.mono fun n hn => key _ hn)
  rw [← Real.exp_le_exp, Real.exp_log hsource, Real.exp_add, Real.exp_sum] at this
  convert this using 2
  exact Finset.prod_congr rfl fun a _ => by rw [Real.rpow_def_of_pos (hvalues a), mul_comm]






/-!
# The shared-input tensor tag inequality

Exact type words in a power of a matched-sector tensor are obtained by explicit
coordinate pullbacks. Their character values depend only on the type counts.
The finite auxiliary separation inequality therefore supplies the integral
bounds required by the entropy limit.
-/




variable {s : ℕ} {X Y Z : Type}
  [Fintype X] [Fintype Y] [Fintype Z]

/-- A coefficient one in each branch gives the shared-input tag inequality from a
finite separation bound, via exact-type words in a power. -/
theorem Character.sharedFirst_tag_of_separation_of_coefficient_one (χ : Character ℤ)
    (q : FiniteLaw (Fin s)) (B : Fin s → Tensor ℤ X Y Z)
    (hB : ∀ a, ∃ x y z, B a x y z = 1) (ly : Y → Fin s) (lz : Z → Fin s)
    (hl : ∀ i x y z, B i x y z ≠ 0 → ly y = i ∧ lz z = i) :
    Real.exp (χ.pX * finiteEntropy q.mass) * ∏ a, χ.value (B a) ^ q.mass a ≤ χ.value (∑ i, B i) := by
  rw [← show χ.value (sharedFirstTensor B) = χ.value (∑ i, B i) by
    rw [χ.value_eq_pullback_of_support _ id (fun y => (ly y, y)) (fun z => (lz z, z))
      Function.injective_id (fun _ _ h => congrArg Prod.snd h) (fun _ _ h => congrArg Prod.snd h)]
    · congr 1
      funext x y z
      simp [Finset.sum_apply, Tensor.pullback, sharedFirstTensor, id]
      rw [Finset.sum_eq_single (ly y) (fun i _ hi => not_not.1 fun h => hi (hl i x y z h).1.symm)
        (by simp)]
      split_ifs with h <;> grind
    intro x y z h
    have hyz : y.1 = z.1 := by_contra fun hne => h (by simp [sharedFirstTensor, hne])
    obtain ⟨hy, hz⟩ := hl _ x _ _ (by simpa [sharedFirstTensor, hyz] using h)
    exact ⟨⟨x, rfl⟩, ⟨y.2, Prod.ext (hy.trans hyz.symm) rfl⟩, ⟨z.2, Prod.ext hz rfl⟩⟩]
  obtain ⟨a⟩ : Nonempty (Fin s) := by by_contra h; simpa [not_nonempty_iff.1 h] using q.total
  refine tag_of_integral_bounds q (fun a => χ.value (B a)) χ.pX _ 6
    (fun a => zero_lt_one.trans_le (χ.one_le_value_of_coefficient_one (hB a)))
    (zero_lt_one.trans_le (χ.one_le_value_of_coefficient_one ?_)) (by norm_num) fun counts _ => ?_
  · obtain ⟨x, y, z, h⟩ := hB a
    exact ⟨x, (a, y), (a, z), by simp [sharedFirstTensor, h]⟩
  let M := Fintype.card (ExactWords counts)
  let e : Fin M ≃ ExactWords counts := (Fintype.equivFin _).symm
  let W (h : Fin M) : Tensor ℤ (Fin (∑ a, counts a) → X) (Fin (∑ a, counts a) → Y)
      (Fin (∑ a, counts a) → Z) := fun x y z => ∏ i, B ((e h).1 i) (x i) (y i) (z i)
  have hM := exactWords_card_pos counts
  have h1 := Integral.finiteSeparation_bound_int χ hM W
  have hW h : χ.value (W h) = ∏ a, χ.value (B a) ^ counts a := by
    rw [χ.value_pi, ← Fintype.prod_fiberwise' (e h).1 fun a => χ.value (B a)]
    simp [(e h).2]
  have h2 : χ.value (sharedFirstTensor W) ≤ χ.value (sharedFirstTensor B) ^ (∑ a, counts a) := by
    rw [← χ.value_power]
    convert χ.value_pullback_le (Tensor.power (sharedFirstTensor B) _) id (fun y : _ × (_ → _) => fun i => ((e y.1).1 i, y.2 i))
      fun y : _ × (_ → _) => fun i => ((e y.1).1 i, y.2 i)
    funext x y z
    by_cases h : y.1 = z.1
    · simp [Tensor.pullback, Tensor.power, sharedFirstTensor, W, h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp fun heq => h (e.injective (Subtype.ext heq))
    simp [Tensor.pullback, Tensor.power, sharedFirstTensor, h, ↓reduceIte, id_eq]
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (by grind)).symm
  simp [hW, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
  refine le_of_mul_le_mul_left ?_ (Nat.cast_pos.2 hM : (0 : ℝ) < M)
  nlinarith [mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 6 * M)]


/-!
# The determinant inequality for an actual tensor character

The shared-input tag inequality is applied to the two concrete branches of the
checked determinant degeneration. All basis changes and the output-dual change
are supplied by `DeterminantFiltration`.
-/




namespace DeterminantFiltration


abbrev Index (e : ℕ) := Sum (Fin (e + 2)) (Fin e)

/-- Multiplication coefficients in the adapted quotient/kernel bases. -/
def adaptedTensor (d e : ℕ) : Tensor ℤ (Fin (d + 1)) (Index e) (Index (d + e))
  | i, .inl j, .inl k => if i.val + j.val = k.val then 1 else 0
  | i, .inl j, .inr k =>
      if j.val = e + 1 ∧ i.val < d ∧ e + i.val = k.val then 1 else 0
  | _, .inr _, .inl _ => 0
  | i, .inr j, .inr k => if i.val + j.val = k.val then 1 else 0

/-- The two graded blocks, padded with zeros in common coordinate spaces. -/
def branch (d e : ℕ) (n : Fin 2) :
    Tensor ℤ (Fin (d + 1)) (Index e) (Index (d + e))
  | i, .inl j, .inl k => if n = 0 then if i.val + j.val = k.val then 1 else 0 else 0
  | i, .inr j, .inr k => if n = 1 then if i.val + j.val = k.val then 1 else 0 else 0
  | _, _, _ => 0

def degeneration (d e : ℕ) :
    Tensor.PolynomialRestrictionDegeneration (adaptedTensor d e)
      (∑ n, branch d e n) 1 0 1 1 where
  leftMap i x := if i = x then 1 else 0
  middleMap j y := if j = y then j.elim (fun _ => Polynomial.X) 1 else 0
  rightMap k z := if k = z then k.elim 1 fun _ => Polynomial.X else 0
  left_degree _ _ := by split_ifs <;> simp
  middle_degree := by rintro (_ | _) _ <;> split_ifs <;> simp
  right_degree := by rintro (_ | _) _ <;> split_ifs <;> simp
  vanishes i j k n hn := by
    rcases j with j | j <;> rcases k with k | k
    all_goals simp [Tensor.restrict, adaptedTensor, ite_mul, show n = 0 by omega]
    all_goals split_ifs <;> simp
  leading i j k := by
    rcases j with j | j <;> rcases k with k | k
    all_goals simp [Tensor.restrict, adaptedTensor, branch, ite_mul]
    all_goals split_ifs <;> simp

/-- Adapted input vectors, written in the monomial coordinates of `(s, w)`. -/
def inMap (e : ℕ) : Index e → Fin (e + 1) × Fin 2 → ℤ
  | .inl j, y => if Fin.lastCases (Fin.last e, 1) (·, 0) j = y then 1 else 0
  | .inr j, y => (if (j.castSucc, 1) = y then 1 else 0) - if (j.succ, 0) = y then 1 else 0

/-- The dual output coordinates of the adapted basis. -/
def outMap {m : ℕ} (n : ℕ) : Index n → Fin m × Fin 2 → ℤ
  | .inl k, z => if k.val = z.1.val + z.2.val then 1 else 0
  | .inr k, z => if z.2 = 1 ∧ k.val = z.1.val then 1 else 0

theorem restrict_eq (d e : ℕ) :
    Tensor.restrict (fun i x => if (i, ()) = x then 1 else 0) (inMap e) (outMap (d + e))
      (Tensor.product (convolution (d + 1) (e + 1))
        (Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (Fin 2))))) = adaptedTensor d e := by
  have hP (x : Fin (d + 1) × Unit) y z : Tensor.product (convolution (K := ℤ) (d + 1) (e + 1))
      (Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (Fin 2)))) x y z =
      if z = (⟨x.1 + y.1, by omega⟩, y.2) then 1 else 0 := by
    simp [Tensor.product, Tensor.cyclic, Tensor.dotPairing, Prod.ext_iff, Fin.ext_iff, eq_comm,
      ← ite_and, and_comm]
  funext i j k
  simp [Tensor.restrict, hP, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ]
  rcases j with j | j <;> rcases k with k | k
  all_goals try cases j using Fin.lastCases
  all_goals simp [inMap, Fin.lastCases_last, Fin.lastCases_castSucc, sub_mul,
    Finset.sum_sub_distrib, Finset.mem_univ]
  all_goals simp [outMap, adaptedTensor] <;> grind

end DeterminantFiltration

namespace Character


open DeterminantFiltration

variable (χ : Character ℤ)

/-- The determinant inequality in the paper's positive-dimension notation. -/
theorem convolution_concavity_tag_of_separation
    (a b : ℕ) (ha : 0 < a) (hb : 2 ≤ b)
    (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    Real.exp (χ.pX * Real.binEntropy q) *
        χ.value (convolution a (b + 1)) ^ q *
        χ.value (convolution a (b - 1)) ^ (1 - q) ≤
      (2 : ℝ) ^ χ.pX * χ.value (convolution a b) := by
  rcases a with _ | d
  · omega
  rcases b with _ | e
  · omega
  have ht := χ.sharedFirst_tag_of_separation_of_coefficient_one (binaryLaw q hq₀ hq₁)
    (branch d e) (fun n ↦ by
      fin_cases n
      · exact ⟨0, .inl 0, .inl 0, by simp [branch]⟩
      exact ⟨0, .inr ⟨0, by omega⟩, .inr ⟨0, by omega⟩, by simp [branch]⟩)
    (Sum.elim 0 1) (Sum.elim 0 1) fun n i j k h ↦ by
      fin_cases n <;> rcases j with j | j <;> rcases k with k | k <;> simp_all [branch]
  rw [binaryLaw_entropy, binaryLaw_product,
    χ.value_eq_pullback_of_support _ id Sum.inl
      (Sum.inl ∘ Fin.cast (by omega : d + 1 + (e + 1 + 1) - 1 = d + e + 2))
      Function.injective_id Sum.inl_injective (Sum.inl_injective.comp (Fin.cast_injective _))
      ?_,
    χ.value_eq_pullback_of_support _ id Sum.inr
      (Sum.inr ∘ Fin.cast (by omega : d + 1 + (e + 1 - 1) - 1 = d + e))
      Function.injective_id Sum.inr_injective (Sum.inr_injective.comp (Fin.cast_injective _))
      ?_] at ht
  · refine ((mul_assoc ..).trans_le ht).trans <|
      (χ.value_polynomialRestrictionDegeneration_le_ring (degeneration d e)).trans ?_
    rw [← restrict_eq]
    refine (χ.monotone _ _ _ _).trans_eq ?_
    rw [χ.map_product, χ.value_cyclic_cyclic_dotPairing two_pos]
    grind
  all_goals rintro i (j | j) (k | k) h
  all_goals simp [branch] at h
  all_goals exact ⟨⟨i, rfl⟩, ⟨j, rfl⟩, ⟨Fin.cast (by omega) k, rfl⟩⟩

end Character







namespace Sector


/-- The sector of a second-leg coordinate. -/
def yl (a h j : ℕ) : Fin 3 := if j < h then 0 else if j < 2 * h + a - 1 then 1 else 2

/-- The sector of a third-leg coordinate. -/
def zl (a h k : ℕ) : Fin 3 := if k < h + a - 1 then 0 else if k < 2 * h + a - 1 then 1 else 2

/-- The three retained branches of `C(a, 3h+a-1)`. -/
def branch (a h : ℕ) (b : Fin 3) :
    Tensor ℤ (Fin a) (Fin (3 * h + a - 1)) (Fin (a + (3 * h + a - 1) - 1)) :=
  fun i j k => if i.val + j.val = k.val ∧ yl a h j = b ∧ zl a h k = b then 1 else 0

/-- Weight one on the middle second-leg sector and on the outer third-leg sectors. -/
def restriction (a h : ℕ) : Tensor.PolynomialRestrictionDegeneration
    (convolution a (3 * h + a - 1)) (∑ b, branch a h b) 1 0 1 1 where
  leftMap i x := if i = x then 1 else 0
  middleMap j y := if j = y then if yl a h j = 1 then Polynomial.X else 1 else 0
  rightMap k z := if k = z then if zl a h k = 1 then 1 else Polynomial.X else 0
  left_degree _ _ := by split_ifs <;> simp
  middle_degree _ _ := by split_ifs <;> simp
  right_degree _ _ := by split_ifs <;> simp
  vanishes i j k n hn := by
    have := i.isLt
    simp only [Tensor.restrict, ite_mul, mul_ite, mul_zero, zero_mul, one_mul, Finset.sum_ite_irrel,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    by_cases hc : i.val + j.val = k.val <;> by_cases h1 : j.val < h <;>
      by_cases h2 : j.val < 2 * h + a - 1 <;> by_cases h3 : k.val < h + a - 1 <;>
      by_cases h4 : k.val < 2 * h + a - 1 <;> simp [hc, h1, h2, h3, h4, yl, zl, show n = 0 by omega] <;> omega
  leading i j k := by
    have := i.isLt
    simp only [Finset.sum_apply, Fin.sum_univ_three, Tensor.restrict, ite_mul, mul_ite, mul_zero, zero_mul, one_mul, Finset.sum_ite_irrel,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    by_cases hc : i.val + j.val = k.val <;> by_cases h1 : j.val < h <;>
      by_cases h2 : j.val < 2 * h + a - 1 <;> by_cases h3 : k.val < h + a - 1 <;>
      by_cases h4 : k.val < 2 * h + a - 1 <;> simp [hc, h1, h2, h3, h4, yl, zl, branch] <;> omega

theorem value_branch (χ : Character ℤ) {a h n m : ℕ} (T : Tensor ℤ (Fin a) (Fin n) (Fin m)) (b : Fin 3)
    (fx : Fin a → Fin a) (hx : fx.Bijective) (cy cz : ℕ) (hy : cy + n ≤ 3 * h + a - 1)
    (hz : cz + m ≤ a + (3 * h + a - 1) - 1)
    (hs : ∀ i j k, branch a h b i j k ≠ 0 →
      cy ≤ j.val ∧ j.val < cy + n ∧ cz ≤ k.val ∧ k.val < cz + m)
    (hT : ∀ i (j : Fin n) (k : Fin m), branch a h b (fx i) ⟨cy + j, by omega⟩ ⟨cz + k, by omega⟩ = T i j k) :
    χ.value (branch a h b) = χ.value T := by
  rw [χ.value_eq_pullback_of_support _ fx (fun j : Fin n => (⟨cy + j, by omega⟩ : Fin _))
    (fun k : Fin m => (⟨cz + k, by omega⟩ : Fin _)) hx.1 (fun _ _ h => by grind)
    (fun _ _ h => by grind) fun i j k hn => ?_]
  · exact congrArg _ (funext₃ hT)
  have := hs i j k hn
  exact ⟨hx.2 i, ⟨⟨j - cy, by omega⟩, by grind⟩, ⟨⟨k - cz, by omega⟩, by grind⟩⟩

theorem convolution_tripling_tag_of_separation (χ : Character ℤ)
    (a h : ℕ) (ha : 0 < a) (hh : 0 < h) :
    (3 : ℝ) ^ χ.pX * χ.value (convolution a h) ^ (2 / 3 : ℝ) *
      χ.value (fun i s r => convolution a h i r s) ^ (1 / 3 : ℝ) ≤
        χ.value (convolution a (3 * h + a - 1)) := by
  have ht := χ.sharedFirst_tag_of_separation_of_coefficient_one uniformThree
    (branch a h) (fun b ↦ by
      fin_cases b
      · exact ⟨⟨0, ha⟩, ⟨0, by omega⟩, ⟨0, by omega⟩, by simp [branch, yl, zl]; omega⟩
      · exact ⟨⟨a - 1, by omega⟩, ⟨h, by omega⟩, ⟨h + a - 1, by omega⟩, by simp [branch, yl, zl]; omega⟩
      exact ⟨⟨0, ha⟩, ⟨2 * h + a - 1, by omega⟩, ⟨2 * h + a - 1, by omega⟩, by simp [branch, yl, zl]; omega⟩)
    (yl a h ·) (zl a h ·) fun b i j k hb => by simp [branch] at hb; exact hb.2
  rw [uniformThree_entropy_factor, uniformThree_product,
    value_branch χ (convolution a h) 0 id Function.bijective_id 0 0 (by omega) (by omega) ?_ ?_,
    value_branch χ (fun i s r => convolution a h i r s) 1 Fin.rev Fin.rev_bijective h (h + a - 1)
      (by omega) (by omega) ?_ ?_,
    value_branch χ (convolution a h) 2 id Function.bijective_id (2 * h + a - 1) (2 * h + a - 1)
      (by omega) (by omega) ?_ ?_] at ht
  · refine le_trans (le_of_eq ?_) (ht.trans (χ.value_polynomialRestrictionDegeneration_le_ring (restriction a h)))
    rw [mul_assoc, mul_right_comm (_ ^ _), ← Real.rpow_add' (χ.nonneg _) (by norm_num)]
    norm_num
  all_goals intro i j k
  all_goals simp [branch, yl, zl, convolution_apply, id, Fin.val_rev]; split_ifs <;> simp <;> omega

end Sector





/-!
# Growth of the scalar profile

The scalar implication of Section 6 (Lemma 6.1): a symmetric profile which is
concave in its second index and satisfies shifted tripling grows on the
diagonal at least like `n ^ (4 / 3)`, so the rank bound forces `t ≤ 3 / 4`.
-/


theorem exponent_le_three_quarters {t : ℝ} {v : ℕ → ℕ → ℝ} (ht : 0 < t)
    (hpos : ∀ n, 0 < n → 0 ≤ v n n) (hsymm : ∀ a b, v a b = v b a) (hone : v 1 1 = 1)
    (hconc : ∀ a h, 0 < a → 2 ≤ h → v a (h - 1) + v a (h + 1) ≤ 2 * v a h)
    (htrip : ∀ a h, 0 < a → 0 < h → 3 * v a h ≤ v a (3 * h + a - 1))
    (hrank : ∀ n, 0 < n → v n n ≤ ((n + n - 1 : ℕ) : ℝ) ^ (1 / t)) :
    t ≤ 3 / 4 := by
  have hd a h (ha : 0 < a) (hh : 0 < h) k :
      v a (h + k + 1) - v a (h + k) ≤ v a (h + 1) - v a h := by
    induction k <;> grind
  have hkey a h (ha : 0 < a) (hh : 0 < h) :
      2 * v a h ≤ (2 * h + a - 1 : ℝ) * (v a (h + 1) - v a h) := by
    have haff k : v a (h + k) ≤ v a h + k * (v a (h + 1) - v a h) := by
      induction k <;> grind
    have h1 := haff (2 * h + a - 1)
    rw [show h + (2 * h + a - 1) = 3 * h + a - 1 by omega, Nat.cast_sub (by omega)] at h1
    grind
  have hD (m : ℕ) : ((m : ℝ) + 1) ^ 4 ≤ v (m + 1) (m + 1) ^ 3 := by
    induction m with
    | zero => simp_all
    | succ m ih =>
      have h1 := hkey (m + 1) (m + 1) (by omega) (by omega)
      have h3 := hconc (m + 1 + 1) (m + 1 + 1) (by omega) (by omega)
      have h0 := hpos (m + 1) (by omega)
      push_cast at *
      have h4 : v (m + 1) (m + 1) * ((3 * m + 4) * (3 * m + 5)) ≤
          v (m + 1 + 1) (m + 1 + 1) * ((3 * m + 3) * (3 * m + 2)) := by
        have e1 : v (m + 1) (m + 1) * (3 * m + 4) ≤ (3 * m + 2) * v (m + 1) (m + 1 + 1) := by linarith
        have e2 : v (m + 1) (m + 1 + 1) * (3 * m + 5) ≤ (3 * m + 3) * v (m + 1 + 1) (m + 1 + 1) := by grind
        nlinarith [mul_le_mul_of_nonneg_left e1 (by positivity),
          mul_le_mul_of_nonneg_left e2 (by positivity)]
      refine le_of_mul_le_mul_right ?_ (by positivity : (0 : ℝ) < ((3 * m + 3) * (3 * m + 2)) ^ 3)
      calc ((m + 1 + 1 : ℝ)) ^ 4 * ((3 * m + 3) * (3 * m + 2)) ^ 3
          ≤ (m + 1) ^ 4 * ((3 * m + 4) * (3 * m + 5)) ^ 3 := sub_nonneg.1 (by ring_nf; positivity)
        _ ≤ v (m + 1) (m + 1) ^ 3 * ((3 * m + 4) * (3 * m + 5)) ^ 3 := by gcongr
        _ = (v (m + 1) (m + 1) * ((3 * m + 4) * (3 * m + 5))) ^ 3 := (mul_pow ..).symm
        _ ≤ _ := (pow_le_pow_left₀ (by positivity) h4 3).trans_eq (mul_pow ..)
  have := rpow_exponent_le_of_nat_bound (b := 3 / t) (C := 2 ^ (3 / t)) fun n hn => by
    rcases n with _ | m
    · omega
    calc ((m + 1 : ℕ) : ℝ) ^ (4 : ℝ) ≤ v (m + 1) (m + 1) ^ 3 := by simp_all
      _ ≤ (((2 * (m + 1) : ℕ) : ℝ) ^ (1 / t)) ^ 3 := by
          gcongr
          · grind
          exact (hrank _ (by omega)).trans (by gcongr; omega)
      _ = _ := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), Nat.cast_mul,
            Real.mul_rpow (by positivity) (by positivity)]
          ring_nf
  rw [le_div_iff₀ ht] at this
  linarith





/-!
# Combining the scalar sector bounds

Pointwise character bounds multiply over a finite family of leg orders. After
normalization by the sum of the singleton exponents, the entropy identity gives
the midpoint-concavity bound for the profile.
-/



theorem log_root {ι : Type*} [Fintype ι] {D : ι → ℝ} (s : ℝ) (hD : ∀ i, 0 < D i) :
    0 < (∏ i, D i) ^ (1 / s) ∧ Real.log ((∏ i, D i) ^ (1 / s)) = (∑ i, Real.log (D i)) / s := by
  have := Finset.prod_pos fun i (_ : i ∈ Finset.univ) => hD i
  exact ⟨by positivity, by rw [Real.log_rpow this, Real.log_prod fun i _ => (hD i).ne']; ring⟩

theorem finite_product_concavity {ι : Type*} [Fintype ι]
    (A B C p : ι → ℝ) {s : ℝ} (hs : 0 < s) (hsum : ∑ i, p i = s)
    (hA : ∀ i, 0 < A i) (hB : ∀ i, 0 < B i) (hC : ∀ i, 0 < C i)
    (hbound : ∀ i q, 0 ≤ q → q ≤ 1 →
      Real.exp (p i * Real.binEntropy q) * (B i) ^ q * (C i) ^ (1 - q) ≤
        (2 : ℝ) ^ (p i) * A i) :
    (∏ i, B i) ^ (1 / s) + (∏ i, C i) ^ (1 / s) ≤
      2 * (∏ i, A i) ^ (1 / s) := by
  obtain ⟨ha, la⟩ := log_root s hA
  obtain ⟨hb, lb⟩ := log_root s hB
  obtain ⟨hc, lc⟩ := log_root s hC
  generalize (∏ i, B i) ^ (1 / s) = b at *
  generalize (∏ i, C i) ^ (1 / s) = c at *
  have h := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => by
    have := hA i; have := hB i; have := hC i
    simpa (disch := positivity) only [Real.log_mul, Real.log_exp, Real.log_rpow] using
      Real.log_le_log (by positivity) (hbound i (b / (b + c)) (by positivity)
      (div_le_one_of_le₀ (by linarith) (by positivity)))
  simp [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, Real.negMulLog_def,
    Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hsum] at h
  rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_mul two_ne_zero ha.ne']
  rw [eq_div_iff hs.ne'] at la lb lc
  rw [← la, ← lb, ← lc, one_sub_div (add_pos hb hc).ne', add_sub_cancel_left,
    Real.log_div hc.ne' (add_pos hb hc).ne', Real.log_div hb.ne' (add_pos hb hc).ne'] at h
  refine le_of_mul_le_mul_left ?_ hs
  have : b / (b + c) + c / (b + c) = 1 := by field_simp
  linarith [congrArg (· * (s * Real.log (b + c))) this]

theorem finite_product_tripling {ι : Type*} [Fintype ι]
    (A B C p : ι → ℝ) {s : ℝ} (hs : 0 < s) (hsum : ∑ i, p i = s)
    (hA : ∀ i, 0 < A i) (hB : ∀ i, 0 < B i) (hC : ∀ i, 0 < C i)
    (hbound : ∀ i, (3 : ℝ) ^ p i * B i ^ (2 / 3 : ℝ) * C i ^ (1 / 3 : ℝ) ≤ A i)
    (hprod_eq : ∏ i, C i = ∏ i, B i) :
    3 * (∏ i, B i) ^ (1 / s) ≤ (∏ i, A i) ^ (1 / s) := by
  obtain ⟨ha, la⟩ := log_root s hA
  obtain ⟨hb, lb⟩ := log_root s hB
  have lc := (log_root s hC).2
  rw [hprod_eq, lb, div_left_inj' hs.ne'] at lc
  rw [← Real.log_le_log_iff (by positivity) ha, Real.log_mul three_ne_zero hb.ne', la, lb,
    le_div_iff₀ hs, add_mul, div_mul_cancel₀ _ hs.ne']
  have h := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => by
    have := hA i; have := hB i; have := hC i
    simpa (disch := positivity) only [Real.log_mul, Real.log_rpow] using Real.log_le_log (by positivity) (hbound i)
  simp [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hsum, ← lc] at h
  linarith





/-!
# The inequalities for the polynomial profile

Precomposing a character with a leg permutation gives another character. The
six resulting values multiply to the symmetrized product, and each singleton
leg exponent occurs twice among their first-leg exponents. The six character
values are combined before the common probability law is optimized, so the
total entropy exponent is exactly six times the mean exponent used to
normalize the profile.
-/



namespace Character

variable (χ : Character ℤ) {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]

/-- The reflected character exchanges the second and third tensor legs. -/
def swap23Character : Character ℤ where
  value T := χ.value (fun x z y => T x y z)
  nonneg T := χ.nonneg _
  map_zero := χ.map_zero
  map_one := χ.map_one
  map_directSum T := by
    rw [← χ.map_directSum]
    congr; funext; simp [Tensor.directSum, and_comm]
  map_product T S := χ.map_product (fun x z y => T x y z) (fun x z y => S x y z)
  monotone T A B C := by
    convert χ.monotone (fun x z y => T x y z) A C B using 2
    funext
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans
      (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)

/-- The three cyclic orders followed by their reflected orders. -/
def permutedCharacter (i : Fin 6) : Character ℤ :=
  ![χ, χ.cyclicCharacter, χ.cyclicCharacter.cyclicCharacter,
    χ.swap23Character, χ.swap23Character.cyclicCharacter,
    χ.swap23Character.cyclicCharacter.cyclicCharacter] i

/-- The product of character values in the six orders of the legs. -/
def sixfoldProduct (T : Tensor ℤ X Y Z) : ℝ := ∏ i, (χ.permutedCharacter i).value T

theorem sixfoldProduct_eq (T : Tensor ℤ X Y Z) : χ.sixfoldProduct T = χ.value T *
    (χ.value (fun y z x => T x y z) * (χ.value (fun z x y => T x y z) * (χ.value (fun x z y => T x y z) *
      (χ.value (fun y x z => T x y z) * χ.value (fun z y x => T x y z))))) := by
  simp [sixfoldProduct, Fin.prod_univ_succ]; rfl

/-- The three dot-product exponents of an actual character sum to at most `9/4`. -/
theorem exponent_sum_le_nine_quarters : χ.pX + χ.pY + χ.pZ ≤ 9 / 4 := by
  have hc (ψ : Character ℤ) : ψ.cyclicCharacter.pX = ψ.pZ ∧ ψ.cyclicCharacter.pY = ψ.pX ∧
    ψ.cyclicCharacter.pZ = ψ.pY := ⟨rfl, rfl, rfl⟩
  have hs (ψ : Character ℤ) : ψ.swap23Character.pX = ψ.pX ∧ ψ.swap23Character.pY = ψ.pZ ∧
      ψ.swap23Character.pZ = ψ.pY := by
    refine ⟨?_, ?_, ?_⟩ <;> simp [pX, pY, pZ] <;> congr 2 <;> apply congrArg ψ.value <;>
      funext <;> simp [Tensor.cyclic, Tensor.dotPairing, eq_comm]
  have hs : ∑ i, (χ.permutedCharacter i).pX = 2 * (χ.pX + χ.pY + χ.pZ) := by
    simp [permutedCharacter, Fin.sum_univ_succ, hc, hs]; ring
  have hp a b (ha : 0 < a) (hb : 0 < b) i : 0 < (χ.permutedCharacter i).value (convolution a b) :=
    zero_lt_one.trans_le (one_le_value_of_coefficient_one _ ⟨_, _, _, convolution_at_output ⟨0, ha⟩ ⟨0, hb⟩⟩)
  rcases le_or_gt (χ.pX + χ.pY + χ.pZ) 0 with ht | ht
  · linarith
  have := exponent_le_three_quarters (t := (χ.pX + χ.pY + χ.pZ) / 3)
    (v := fun a b => χ.sixfoldProduct (convolution a b) ^ (1 / ∑ i, (χ.permutedCharacter i).pX)) (by positivity)
    (fun n hn => (Real.rpow_pos_of_pos (Finset.prod_pos fun i _ => hp n n hn hn i) _).le)
    (fun a b => ?_) ?_ (fun a b ha hb => ?_) (fun a h ha hh => ?_) fun n hn => ?_
  · linarith
  · have h : (fun j i k => convolution (K := ℤ) a b i j k) =
        Tensor.pullback (Equiv.refl _) (Equiv.refl _) (finCongr (by omega)) (convolution b a) := by
      funext j i k; exact convolution_comm a b i j k
    rw [← show χ.sixfoldProduct (fun j i k => convolution a b i j k) =
      χ.sixfoldProduct (convolution a b) by simp only [sixfoldProduct_eq]; ring, h]
    simp only [sixfoldProduct, value_reindex]
  · have h (ψ : Character ℤ) : ψ.value (convolution 1 1) = 1 := by
      rw [← ψ.value_reindex _ convolutionOneInputEquiv (Equiv.refl _) (convolutionOneOutputEquiv 1),
        convolution_one_left_dotPairing, value_cyclic_cyclic_dotPairing _ one_pos]
      simp
    simp [sixfoldProduct, h]
  · have h := finite_product_concavity _ _ _ _ (by linarith) rfl
      (hp _ _ ha (by omega))
      (hp _ _ ha (by omega))
      (hp _ _ ha (by omega))
      fun i q => (χ.permutedCharacter i).convolution_concavity_tag_of_separation a b ha hb q
    exact (add_comm _ _).trans_le h
  · have h := finite_product_tripling _ _ _ _ (by linarith) rfl
      (hp _ _ ha (by omega))
      (hp _ _ ha hh)
      (fun i => zero_lt_one.trans_le ((χ.permutedCharacter i).one_le_value_of_coefficient_one
        ⟨⟨0, ha⟩, convolutionOutput ⟨0, ha⟩ ⟨0, hh⟩, ⟨0, hh⟩, convolution_at_output _ _⟩))
      (fun i => Sector.convolution_tripling_tag_of_separation (χ.permutedCharacter i) a h ha hh)
      (by change χ.sixfoldProduct _ = χ.sixfoldProduct _; simp only [sixfoldProduct_eq]; ring)
    exact h
  calc _ ≤ ((((n + n - 1 : ℕ) : ℝ)) ^ 6) ^ (1 / ∑ i, (χ.permutedCharacter i).pX) :=
        Real.rpow_le_rpow (Finset.prod_nonneg fun i _ => (χ.permutedCharacter i).nonneg _)
          ((Finset.prod_le_prod₀ (fun i _ => (χ.permutedCharacter i).nonneg _)
            fun i _ => (χ.permutedCharacter i).value_convolution_le_int n n).trans_eq (by simp))
          (one_div_nonneg.2 (by linarith))
    _ = _ := by rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), hs]; congr 1; field_simp; norm_num

end AuxiliarySeparation.Character

/-! Straight-line programs computing families of ring functions, and the
recursive block algorithms obtained from exact integer rank schemes. -/

namespace Arithmetic

open Finset Fintype Foundation


variable {F I M O T : Type*} [Ring F]

@[simp] theorem Program.eval_step_zero {r} (p : Program F I r) (g x) :
    (p.step g).eval x 0 = g.eval x (p.eval x) := rfl

@[simp] theorem Program.eval_step_succ {r} (p : Program F I r) (g x) (i : Fin r) :
    (p.step g).eval x i.succ = p.eval x i := rfl

@[simp] theorem Program.cost_step {r} (p : Program F I r) g :
    (p.step g).cost = p.cost + g.cost := rfl

/-- `f` is computed by a program with at most `c` counted gates. -/
def Comp (f : (I → F) → O → F) (c : ℕ) : Prop :=
  ∃ r, ∃ p : Program F I r, ∃ o : O → Fin r, (∀ x i, p.eval x (o i) = f x i) ∧ p.cost ≤ c

def Gate.bind {R S : Type*} (f : M → Gate F I S) (e : R → S) : Gate F M R → Gate F I S
  | .constant z => .constant z
  | .input j => f j
  | .add a b => .add (e a) (e b)
  | .sub a b => .sub (e a) (e b)
  | .mul a b => .mul (e a) (e b)

/-- Run `q` after `p`, reading each input of `q` from an input or a register of `p`. -/
theorem subst {s} (q : Program F M s) {r} (p : Program F I r) (w : M → I ⊕ Fin r) :
    ∃ r', ∃ p' : Program F I r', ∃ old : Fin r → Fin r', ∃ new : Fin s → Fin r',
      (∀ x i, p'.eval x (old i) = p.eval x i) ∧
      (∀ x i, p'.eval x (new i) = q.eval (fun j => (w j).elim x (p.eval x)) i) ∧
      p'.cost = p.cost + q.cost := by
  induction q with
  | nil => exact ⟨_, p, id, Fin.elim0, fun _ _ => rfl, fun _ i => i.elim0, rfl⟩
  | step q g ih =>
    obtain ⟨r', p', old, new, h1, h2, h3⟩ := ih
    by_cases hj : ∃ j k, g = .input j ∧ w j = .inr k
    · obtain ⟨j, k, rfl, hw⟩ := hj
      exact ⟨r', p', old, Fin.cases (old k) new, h1,
        fun x i => i.cases (by simp [Gate.eval, hw, h1]) (h2 x), by simp [h3, Gate.cost]⟩
    refine ⟨_, p'.step (g.bind (fun j => (w j).elim .input fun _ => .constant 0) new),
      Fin.succ ∘ old, Fin.cases 0 (Fin.succ ∘ new), h1, fun x i => i.cases ?_ (h2 x), ?_⟩ <;>
    cases g <;> simp_all [Gate.bind, Gate.eval, Gate.cost, add_assoc] <;>
    cases h : w ‹M› <;> simp_all

namespace Comp

variable {f : (I → F) → M → F} {c d : ℕ}

theorem of {g : (I → F) → O → F} (h : Comp f c) (e : O → M) (hg : ∀ x o, g x o = f x (e o))
    (hc : c ≤ d) : Comp g d :=
  let ⟨r, p, o, hp, h'⟩ := h
  ⟨r, p, o ∘ e, fun x i => (hp x _).trans (hg x i).symm, h'.trans hc⟩

theorem comp {g : (M → F) → O → F} (hf : Comp f c) (hg : Comp g d) :
    Comp (fun x => g (f x)) (c + d) := by
  obtain ⟨r, p, o, hp, hc⟩ := hf
  obtain ⟨s, q, o', hq, hd⟩ := hg
  obtain ⟨_, p', -, new, -, h2, h3⟩ := subst q p (.inr ∘ o)
  exact ⟨_, p', new ∘ o', fun x i => by simp_all, by omega⟩

theorem pair {g : (I → F) → O → F} (hf : Comp f c) (hg : Comp g d) :
    Comp (fun x => Sum.elim (f x) (g x)) (c + d) := by
  obtain ⟨r, p, o, hp, hc⟩ := hf
  obtain ⟨s, q, o', hq, hd⟩ := hg
  obtain ⟨_, p', old, new, h1, h2, h3⟩ := subst q p .inl
  exact ⟨_, p', Sum.elim (old ∘ o) (new ∘ o'), fun x i => by cases i <;> simp_all,
    by omega⟩

theorem pre {g : (M → F) → O → F} (hg : Comp g c) (h : M → I) :
    Comp (fun x : I → F => g fun j => x (h j)) c := by
  obtain ⟨s, q, o', hq, hd⟩ := hg
  obtain ⟨_, p', -, new, -, h2, h3⟩ := subst q (.nil : Program F I 0) (.inl ∘ h)
  exact ⟨_, p', new ∘ o', fun x i => by simp_all, by simp [h3, Program.cost, hd]⟩

theorem fam {k} {f : Fin k → (I → F) → O → F} {c : Fin k → ℕ} (h : ∀ i, Comp (f i) (c i)) :
    Comp (fun x (p : Fin k × O) => f p.1 x p.2) (∑ i, c i) := by
  induction k with
  | zero => exact ⟨0, .nil, fun p => p.1.elim0, fun _ p => p.1.elim0, Nat.zero_le _⟩
  | succ k ih =>
    exact ((h 0).pair (ih fun i => h i.succ)).of
      (fun p => p.1.cases (.inl p.2) fun i => .inr (i, p.2))
      (fun x ⟨i, o⟩ => by cases i using Fin.cases <;> rfl) (Fin.sum_univ_succ c).ge

/-- A sum of `n` products of inputs and constants. -/
theorem lin {n} (u w : Fin n → I ⊕ F) :
    Comp (fun x (_ : Unit) => ∑ i, (u i).elim x id * (w i).elim x id) (2 * n) := by
  induction n with
  | zero => exact ⟨1, .step .nil (.constant 0), fun _ => 0, fun _ _ => by simp [Gate.eval], le_rfl⟩
  | succ n ih =>
    obtain ⟨r, p, o, hp, hc⟩ := ih (u ∘ Fin.succ) (w ∘ Fin.succ)
    refine ⟨_, (((p.step ((u 0).elim .input .constant)).step ((w 0).elim .input .constant)).step
      (.mul (Fin.succ 0) 0)).step (.add 0 (o ()).succ.succ.succ), fun _ => 0,
      fun x _ => ?_, ?_⟩ <;> cases h : u 0 <;> cases h' : w 0 <;>
      simp [Gate.eval, Gate.cost, Fin.sum_univ_succ, hp, h, h', -Fin.succ_zero_eq_one',
        -Fin.succ_zero_eq_one] <;> omega

theorem lins [Fintype O] [Fintype T] (u w : O → T → I ⊕ F) :
    Comp (fun x o => ∑ t, (u o t).elim x id * (w o t).elim x id) (card O * (2 * card T)) :=
  (fam fun i => lin (fun j => u ((equivFin O).symm i) ((equivFin T).symm j))
    fun j => w ((equivFin O).symm i) ((equivFin T).symm j)).of (fun o => (equivFin O o, ()))
    (fun x o => by simp [← (equivFin T).symm.sum_comp]) (by simp)

end Comp

/-- Square matrix multiplication as a function of the input entries. -/
def mm (n : ℕ) (x : MatrixInput n n n → F) (o : Fin n × Fin n) : F :=
  ∑ j, x (.inl (o.1, j)) * x (.inr (j, o.2))

theorem Comp.alg {n c} (h : Comp (mm (F := F) n) c) :
    ∃ P : MatrixAlgorithm F n n n, P.Correct ∧ P.cost ≤ c :=
  let ⟨r, p, o, hp, hc⟩ := h
  ⟨⟨r, p, fun i k => o (i, k)⟩, fun A B => by
    ext; simp [MatrixAlgorithm.eval, hp, mm, matrixInputs, Matrix.mul_apply], hc⟩

theorem naive n : Comp (mm (F := F) n) (n * n * (2 * n)) :=
  (Comp.lins (fun o t => .inl (.inl (o.1, t)))
    fun o t => .inl (.inr (t, o.2))).of id (fun _ _ => rfl) (by simp)

theorem Comp.pad {n k c} (h : Comp (mm (F := F) (n + k)) c) : Comp (mm (F := F) n) c := by
  obtain ⟨r, q, o', hq, hc⟩ := h
  let g (a b : Fin (n + k)) (v : Fin n → Fin n → MatrixInput n n n) :
      MatrixInput n n n ⊕ Fin 1 := if h : ↑a < n ∧ ↑b < n then .inl (v ⟨a, h.1⟩ ⟨b, h.2⟩) else .inr 0
  obtain ⟨_, p', -, new, -, h2, h3⟩ := subst q (.step .nil (.constant (0 : F))) fun y =>
    y.elim (fun y => g y.1 y.2 fun a b => .inl (a, b)) fun y => g y.1 y.2 fun a b => .inr (a, b)
  refine ⟨_, p', fun o => new (o' (Fin.castAdd k o.1, Fin.castAdd k o.2)), fun x o => ?_,
    by simp [h3, Gate.cost, Program.cost, hc]⟩
  simp [h2, hq, mm, Fin.sum_univ_add, Gate.eval, g]

/-- Integer coefficients are central, so a bilinear identity preserves the
order of the two inputs even in a noncommutative ring. -/
theorem int_rank_bilinear_identity {n r : ℕ} {a b c : Fin r → Fin n × Fin n → ℤ}
    (h : matrixMultiplicationTensor n n n =
      fun x y z => ∑ q, Tensor.rankOne (a q) (b q) (c q) x y z)
    (L R : Fin n × Fin n → F) (i k : Fin n) :
    ∑ q, (c q (k, i) : F) * (∑ x, (a q x : F) * L x) * ∑ y, (b q y : F) * R y =
      ∑ j, L (i, j) * R (j, k) := by
  have e x y : ∑ q, b q y * (a q x * c q (k, i)) =
      matrixMultiplicationTensor _ _ _ x y (k, i) := by
    rw [h]; exact sum_congr rfl fun _ _ => by simp [Tensor.rankOne]; ring
  simp [← zsmul_eq_mul, mul_sum, sum_mul, smul_smul, smul_sum]
  simp_rw [sum_comm (s := (univ : Finset (Fin r))), ← sum_smul, e]
  simp [matrixMultiplicationTensor, Fintype.sum_prod_type, ite_and]

/-- One recursive step built from an exact integer rank-`r` scheme. -/
theorem Comp.block {n m r c}
    (h : Tensor.RankAtMost (matrixMultiplicationTensor (K := ℤ) n n n) r)
    (hP : Comp (mm (F := F) m) c) : Comp (mm (F := F) (n * m)) (r * c + 6 * r * n ^ 2 * m ^ 2) := by
  obtain ⟨a, b, z, h⟩ := h
  let e := @finProdFinEquiv n m
  refine ((lins
    (fun o t => .inr (o.2.elim (fun _ => (a o.1 t : F)) fun _ => b o.1 t))
    fun o t => .inl (o.2.elim (fun s => .inl (e (t.1, s.1), e (t.2, s.2)))
      fun s => .inr (e (t.1, s.1), e (t.2, s.2)))).comp
    ((fam fun q => hP.pre (q, ·)).comp (lins
      (fun o q => .inr (z q ((e.symm o.2).1, (e.symm o.1).1) : F))
      fun o q => .inl (q, ((e.symm o.1).2, (e.symm o.2).2))))).of id ?_ (by simp; ring_nf; rfl)
  rintro x ⟨I, K⟩
  obtain ⟨⟨i, s⟩, rfl⟩ := e.surjective I
  obtain ⟨⟨k, u⟩, rfl⟩ := e.surjective K
  simp [mm, id, Sum.elim_inl, Sum.elim_inr, Equiv.symm_apply_apply]
  simp_rw [mul_sum (s := (univ : Finset (Fin m))), ← mul_assoc]
  rw [← e.sum_comp, Fintype.sum_prod_type, sum_comm, sum_comm (γ := Fin r)]
  simp_rw [int_rank_bilinear_identity h]

/-- Arbitrarily close integer rank schemes give the arithmetic exponent bound
over every ring, including the zero ring. -/
theorem admissibleExponent_of_int_rank_bounds {τ : ℝ} (hτ : 2 ≤ τ)
    (hR : ∀ ε : ℝ, 0 < ε → ∃ n r : ℕ, 2 ≤ n ∧
      Tensor.RankAtMost (matrixMultiplicationTensor (K := ℤ) n n n) r ∧
      (r : ℝ) ≤ (n : ℝ) ^ (τ + ε)) :
    AdmissibleExponent F τ := by
  intro ε hε
  obtain ⟨n, r, hn, hr, hrn⟩ := hR (ε / 2) (by positivity)
  have n1 : (1 : ℝ) < n := mod_cast hn
  set q := (n : ℝ) ^ (τ + ε)
  have hq : (r : ℝ) < q := hrn.trans_lt (Real.rpow_lt_rpow_of_exponent_lt n1 (by linarith))
  have hq2 : (n : ℝ) ^ 2 ≤ q := by
    rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le n1.le (by grind)
  set C := 2 + 6 * r * n ^ 2 / (q - r)
  have hC : 6 * r * n ^ 2 ≤ C * (q - r) := by
    rw [add_mul, div_mul_cancel₀ _ (sub_pos.2 hq).ne']; nlinarith
  have key k : ∃ c : ℕ, Comp (mm (F := F) (n ^ k)) c ∧ (c : ℝ) ≤ C * q ^ k := by
    induction k with
    | zero => exact ⟨_, naive 1, by simp [C]; positivity⟩
    | succ k ih =>
      obtain ⟨c, hc, hcC⟩ := ih
      refine ⟨_, pow_succ' n k ▸ hc.block hr, ?_⟩
      have : ((n : ℝ) ^ k) ^ 2 ≤ q ^ k := by rw [← pow_mul, mul_comm, pow_mul]; gcongr
      push_cast
      rw [pow_succ q]
      linarith [mul_le_mul_of_nonneg_left hcC r.cast_nonneg,
        mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 6 * r * n ^ 2),
        mul_le_mul_of_nonneg_right hC (pow_pos (show 0 < q by positivity) k).le]
  refine ⟨C * q, by positivity, fun N hN => ?_⟩
  obtain ⟨c, hc, hcC⟩ := key (Nat.log n N + 1)
  have h1 := (Nat.lt_pow_succ_log_self hn N).le
  obtain ⟨P, hP, hPc⟩ := (Nat.add_sub_cancel' h1 ▸ hc).pad.alg
  refine ⟨P, hP, (Nat.cast_le.2 hPc).trans (hcC.trans ?_)⟩
  rw [Real.rpow_pow_comm (by positivity), mul_assoc, ← Real.mul_rpow (by positivity) (by positivity)]
  gcongr
  exact_mod_cast pow_succ' n _ ▸ Nat.mul_le_mul_left n (Nat.pow_log_le_self n (by omega))


/-! Every output of a correct program needs its own arithmetic gate, so the
exponent is at least two over a nontrivial ring; over a trivial ring one zero
constant answers everything and the real infimum is zero by convention. -/




def Program.registerCost : {r : ℕ} → Program F I r → Fin r → ℕ
  | 0, .nil => Fin.elim0
  | _ + 1, .step p g => Fin.cases g.cost p.registerCost

theorem Program.sum_registerCost {r} (p : Program F I r) : ∑ i, p.registerCost i = p.cost := by
  induction p <;> simp [registerCost, Fin.sum_univ_succ, Program.cost, *, add_comm]

theorem Program.eval_of_registerCost [Ring F] {r} (p : Program F I r) i
    (hi : p.registerCost i = 0) : ∃ g : Gate F I (Fin 0), ∀ x, p.eval x i = g.eval x Fin.elim0 := by
  induction p with
  | nil => exact i.elim0
  | step p g ih =>
    cases i using Fin.cases
    · cases g <;> simp_all [registerCost, Gate.cost]
      exacts [⟨.constant _, fun _ => rfl⟩, ⟨.input _, fun _ => rfl⟩]
    exact ih _ hi

theorem MatrixAlgorithm.sq_le_cost [Ring F] [Nontrivial F] {n} (P : MatrixAlgorithm F n n n)
    (hn : 1 ≤ n) (hP : P.Correct) : n * n ≤ P.cost := by
  classical
  have h A B i k : P.program.eval (matrixInputs A B) (P.output i k) = (A * B) i k :=
    congrFun₂ (hP A B) i k
  let E (i k : Fin n) := matrixInputs (Matrix.single i ⟨0, hn⟩ (1 : F)) (Matrix.single ⟨0, hn⟩ k 1)
  have hE i k i' k' : P.program.eval (E i k) (P.output i' k') = if i = i' ∧ k = k' then 1 else 0 := by
    simp [E, h, Matrix.single_apply]
  have inj : Function.Injective fun o : Fin n × Fin n => P.output o.1 o.2 := fun o o' e => by
    simpa [hE, Prod.ext_iff] using congrArg (P.program.eval (E o.1 o.2)) e
  have one i k : 1 ≤ P.program.registerCost (P.output i k) := by
    by_contra! h0
    obtain ⟨g, hg⟩ := P.program.eval_of_registerCost (P.output i k) (by omega)
    rcases g with z | ⟨⟨a, b⟩ | ⟨a, b⟩⟩ | ⟨a⟩ | ⟨a⟩ | ⟨a⟩ <;> simp [Gate.eval] at hg
    · have := (h 0 0 i k).symm.trans ((hg _).trans (hg (E i k)).symm)
      simp [hE] at this
    · have := (hE i k i k).symm.trans ((hg _).trans ((hg (matrixInputs (Matrix.single i ⟨0, hn⟩ 1) 0)).symm.trans (h _ _ i k)))
      simp at this
    · have := (hE i k i k).symm.trans ((hg _).trans ((hg (matrixInputs 0 (Matrix.single ⟨0, hn⟩ k 1))).symm.trans (h _ _ i k)))
      simp at this
    all_goals exact a.elim0
  calc n * n = (univ.image fun o : Fin n × Fin n => P.output o.1 o.2).card := by
        simp [card_image_of_injective _ inj]
    _ ≤ _ := by simpa using card_nsmul_le_sum _ P.program.registerCost 1 (by grind)
    _ ≤ _ := sum_le_sum_of_subset (subset_univ _)
    _ = _ := P.program.sum_registerCost

theorem admissibleExponent_two_le [Ring F] [Nontrivial F] {τ : ℝ}
    (hτ : AdmissibleExponent F τ) : 2 ≤ τ := by
  by_contra! h2
  obtain ⟨C, -, hC⟩ := hτ ((2 - τ) / 2) (by linarith)
  obtain ⟨n, hn, h1⟩ := (((tendsto_rpow_atTop (by linarith : 0 < (2 - τ) / 2)).comp
    tendsto_natCast_atTop_atTop).eventually_gt_atTop C).and (eventually_ge_atTop 1) |>.exists
  obtain ⟨P, hP, hc⟩ := hC n h1
  have n0 : (0 : ℝ) < n := mod_cast h1
  have : (n * n : ℝ) ≤ P.cost := mod_cast P.sq_le_cost h1 hP
  have e : (n : ℝ) * n = n ^ (τ + (2 - τ) / 2) * n ^ ((2 - τ) / 2) := by
    rw [← Real.rpow_add n0]; ring_nf; simp
  simp at hn
  linarith [mul_lt_mul_of_pos_left hn (Real.rpow_pos_of_pos n0 (τ + (2 - τ) / 2))]

end Arithmetic

/-!
# Matrix multiplication over every ring

Exact integer coefficient schemes give the bound `9/4` over every associative
unital ring, including noncommutative rings. The arithmetic exponent uses the
same program semantics, gate costs, positive slack, and infimum as the prior
all-fields theorem. For nontrivial rings its admissible-exponent set is bounded
below. For trivial rings multiplication has zero arithmetic cost, and the
real-valued infimum is zero by Mathlib's convention for an unbounded-below set.

The direct operation-count theorem also includes the zero ring. Its exponent
is `9/4 + ε` for every positive `ε`; it does not assert an exact `O(n^(9/4))`
operation bound or a uniform circuit-generation algorithm.
-/


universe u

namespace AuxiliarySeparation.Integral

open Foundation TensorSemiring

/-- The exact integer coefficient rank exponent is at most `9/4`.
Both finite separation and convolution bounds are supplied by proved integral
constructions, with no field or algebraic-closure hypothesis. -/
theorem exactRankExponent_int_le_nine_quarters :
    exactRankExponent ℤ ≤ (9 : ℝ) / 4 := by
  refine rpow_exponent_le_of_nat_bound (C := 2) fun d hd => ?_
  obtain rfl | hd := hd.eq_or_lt
  · norm_num
  have hx : 0 < (d : ℝ) ^ exactRankExponent ℤ := by positivity
  have hc := Nat.one_le_ceil_iff.2 hx
  obtain ⟨χ, hχ⟩ : ∃ χ : Character ℤ,
      ((⌈(d : ℝ) ^ exactRankExponent ℤ⌉₊ - 1 : ℕ) : ℝ) ≤ χ.value (matrixMultiplicationTensor d d d) := by
    refine (exists_monotone_ringHom_of_no_catalyst rank
      (matrixClass d) _ zero_le le_rank (fun _ _ _ _ ↦ add_mono)
      (fun D s m hm hs h ↦ ?_) fun _ _ _ ↦ mul_mono le_rfl).elim
      fun φ ⟨hφ, h⟩ ↦ ⟨Character.ofTensorClassHom φ hφ, h⟩
    rcases hs with rfl | hs
    · exact not_tensor_add_positive_nat_le_self D hm (by simp_all)
    refine (tensor_catalytic_obstruction_of_scalar_gain_of_one_le (by omega) hs h).not_gt ?_
    rw [Nat.cast_sub hc, Nat.cast_one, sub_lt_iff_lt_add]
    exact Nat.ceil_lt_add_one hx.le
  rw [χ.value_matrixMultiplication (by omega), Nat.cast_sub hc, Nat.cast_one] at hχ
  have := Real.rpow_le_rpow_of_exponent_le (x := d) (mod_cast hd.le)
    χ.exponent_sum_le_nine_quarters
  linarith [Nat.le_ceil ((d : ℝ) ^ exactRankExponent ℤ),
    Real.one_le_rpow (x := d) (z := 9 / 4) (mod_cast hd.le) (by norm_num)]

end AuxiliarySeparation.Integral

theorem int_rank_nine_quarters {ε : ℝ} (hε : 0 < ε) : ∃ n r : ℕ, 2 ≤ n ∧
    Foundation.Tensor.RankAtMost (Foundation.matrixMultiplicationTensor (K := ℤ) n n n) r ∧
      (r : ℝ) ≤ (n : ℝ) ^ ((9 : ℝ) / 4 + ε) :=
  let ⟨n, hn, hr⟩ := AuxiliarySeparation.exists_exactMatrixRank_lt_rpow
    (by linarith [AuxiliarySeparation.Integral.exactRankExponent_int_le_nine_quarters])
  ⟨n, _, hn, AuxiliarySeparation.exactMatrixRank_spec n, hr.le⟩

theorem admissibleExponent_nine_quarters_all_rings (R : Type u) [Ring R] :
    Arithmetic.AdmissibleExponent R ((9 : ℝ) / 4) :=
  Arithmetic.admissibleExponent_of_int_rank_bounds (by norm_num) fun _ => int_rank_nine_quarters
