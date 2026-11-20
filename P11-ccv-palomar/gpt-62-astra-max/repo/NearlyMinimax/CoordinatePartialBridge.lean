module

public import NearlyMinimax.ModelRegularity


@[expose] public section

/-!
The model's ordered coordinate partials are contractions of its genuine
Fréchet derivatives. The finite-order symmetry proof below is adapted from
`RoughRegime/DerivativeSymmetry.lean` in the supplied related formalization.
It uses Schwarz's theorem and adjacent transpositions; no analytic hypothesis
or derivative comparison is assumed.
-/

noncomputable section
open Set Filter
open scoped ContDiff Topology BigOperators
namespace NearlyMinimax
namespace CoordinatePartialBridge

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Finite continuous differentiability suffices for interchange of the
first two true Fréchet derivative directions. -/
lemma iteratedFDeriv_swap_head {n : ℕ} {f : E → F} {x : E}
    (hf : ContDiffAt ℝ (n+2 : ℕ) f x) (a b : E) (w : Fin n → E) :
    iteratedFDeriv ℝ (n+2) f x (Fin.cons a (Fin.cons b w)) =
      iteratedFDeriv ℝ (n+2) f x (Fin.cons b (Fin.cons a w)) := by
  let g  := fun y => iteratedFDeriv ℝ n f y w
  have hg : ContDiffAt ℝ 2 g x :=
    (ContinuousMultilinearMap.apply ℝ (fun _  => E) F w).contDiff.contDiffAt.comp x
      (hf.iteratedFDeriv_right (by simp [add_comm]))
  have hid a b : iteratedFDeriv ℝ (n+2) f x (Fin.cons a (Fin.cons b w)) =
      fderiv ℝ (fderiv ℝ g) x a b := by
    rw [(hf.differentiableAt_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self _)).iteratedFDeriv_succ_apply_left']
    simp only [Fin.tail_cons,Fin.cons_zero]
    have heq : (fun y => iteratedFDeriv ℝ (n+1) f y (Fin.cons b w)) =ᶠ[𝓝 x]
        fun y => fderiv ℝ g y b := by
      filter_upwards [hf.eventually (Ne.symm (ne_of_beq_false rfl))] with y hy
      exact ((hy.differentiableAt_iteratedFDeriv (by exact_mod_cast (show n < n+2 by omega))).iteratedFDeriv_succ_apply_left' (m := Fin.cons b w))
    rw [heq.fderiv_eq, fderiv_clm_apply ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero) (differentiableAt_const b)]
    simp
  rw [hid a b,hid b a]
  exact (hg.isSymmSndFDerivAt (by simp)) a b



lemma iteratedFDeriv_adjacent_swap (n : ℕ) {f : E → F} {x : E}
    (hf : ContDiffAt ℝ (n+1 : ℕ) f x) (i : Fin n) (v : Fin (n+1) → E) :
    iteratedFDeriv ℝ (n+1) f x (v ∘ Equiv.swap i.castSucc i.succ) =
      iteratedFDeriv ℝ (n+1) f x v := by
  induction n generalizing x with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · have heq : v ∘ Equiv.swap 0 1 =
          Fin.cons (v 1) (Fin.cons (v 0) (Fin.tail (Fin.tail v))) := by
        ext j
        refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j
        · simp
        · simp
        · rfl
      have hdecomp : Fin.cons (v 0) (Fin.cons (v 1) (Fin.tail (Fin.tail v))) = v := by
        rw [show v 1 = Fin.tail v 0 from rfl,Fin.cons_self_tail,Fin.cons_self_tail]
      simpa only [Fin.castSucc_zero,Fin.succ_zero_eq_one,heq,hdecomp] using
        iteratedFDeriv_swap_head hf (v 1) (v 0) (Fin.tail (Fin.tail v))
    · have hzero : (v ∘ Equiv.swap i.succ.castSucc i.succ.succ) 0 = v 0 := rfl
      have htail : Fin.tail (v ∘ Equiv.swap i.succ.castSucc i.succ.succ) =
          Fin.tail v ∘ Equiv.swap i.castSucc i.succ := by
        funext j
        simp only [Fin.tail,Function.comp_apply,Fin.castSucc_succ]
        rw [← (Fin.succ_injective _).map_swap]
      have hd  :=
        hf.differentiableAt_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self _)
      rw [hd.iteratedFDeriv_succ_apply_left',hd.iteratedFDeriv_succ_apply_left',hzero,htail]
      have he : (fun y => iteratedFDeriv ℝ (n+1) f y (Fin.tail v ∘ Equiv.swap i.castSucc i.succ)) =ᶠ[𝓝 x]
          fun y => iteratedFDeriv ℝ (n+1) f y (Fin.tail v) := by
        filter_upwards [hf.eventually (by simp)] with y hy
        exact ih (hy.of_le (by bound)) i (Fin.tail v)
      rw [he.fderiv_eq]



/-- The actual q-th Fréchet derivative of a real C^q function is symmetric.
This uses finite differentiability and genuine adjacent transpositions,
rather than analytic regularity. -/
theorem iteratedFDeriv_comp_perm_finite {q : ℕ} {f : E → F} {x : E}
    (hf : ContDiffAt ℝ q f x) (v : Fin q → E) (σ : Equiv.Perm (Fin q)) :
    iteratedFDeriv ℝ q f x (v ∘ σ) = iteratedFDeriv ℝ q f x v := by
  cases q with
  | zero => rfl
  | succ n =>
    let S : Submonoid (Equiv.Perm (Fin (n+1))) := {
      carrier := {p | ∀ v,
        iteratedFDeriv ℝ (n+1) f x (v ∘ p) = iteratedFDeriv ℝ (n+1) f x v}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb v
        exact (hb (v ∘ a)).trans (ha v) }
    have hgen : Set.range (fun i : Fin n => Equiv.swap i.castSucc i.succ) ⊆ S := by
      rintro p ⟨i,rfl⟩
      solve_by_elim [iteratedFDeriv_adjacent_swap]
    exact (Submonoid.closure_le.mpr hgen) (by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]
      trivial) v




end CoordinatePartialBridge

section
variable {q d : ℕ} (γ : Fin d → ℕ) {a b : ℕ} (h : a = b) (F : Covariate d → ℝ) {U : Set (Covariate d)}
    (k : b = a) (hU : IsOpen U) (x : Covariate d) (v : Fin b → Covariate d) (σ : Fin q → Fin d)
    (w : List (Fin d))

/-- The sorted coordinate word used in the paper's mixed partial definition. -/
def coordinateWord : List (Fin d) :=
  (List.finRange d).flatMap (fun i => List.replicate (γ i) i)

/-- Coordinate directions of a finite word, with the word's actual length. -/
def wordBasis : Fin w.length → Covariate d :=
  fun j => Pi.single (w.get j) 1

/-- Successive coordinate differentiation in the supplied order. -/
def partialWord :
    Covariate d → ℝ :=
  w.foldl (fun G i => coordinatePartial i G) F

include hU in
/-- Left folds add their latest differentiation direction at the head of
the true iterated derivative, hence the reversed word on the right. -/
theorem partialWord_eq_iteratedFDeriv {F : Covariate d → ℝ} {ℓ : ℕ}
    (hf : ContDiffOn ℝ ℓ F U) (w : List (Fin d)) (hw : w.length ≤ ℓ)
    {x : Covariate d} (hx : x ∈ U) :
    partialWord F w x =
      iteratedFDeriv ℝ w.reverse.length F x (wordBasis w.reverse) := by
  induction w using List.reverseRecOn generalizing x with
  | nil => rfl
  | append_singleton w i ih =>
    have hw' : w.length < ℓ := by simpa using hw
    have he : partialWord F w =ᶠ[𝓝 x]
        fun y => iteratedFDeriv ℝ w.reverse.length F y (wordBasis w.reverse) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact ih (Nat.le_of_lt hw') hy
    have hd  :=
      (hf.contDiffAt (hU.mem_nhds hx)).differentiableAt_iteratedFDeriv
        (by exact_mod_cast (show w.reverse.length < ℓ by simpa using hw'))
    simp [partialWord, coordinatePartial]
    change fderiv ℝ (partialWord F w) x (Pi.single i 1) = _
    rw [he.fderiv_eq, List.reverse_append, List.reverse_singleton, List.singleton_append]
    exact (hd.iteratedFDeriv_succ_apply_left' (m := Fin.cons (Pi.single i 1) (wordBasis w.reverse))).symm

theorem coordinateWord_length :
    (coordinateWord γ).length = ∑ i, γ i := by
  simp [coordinateWord]
  rfl

theorem coordinateWord_count (i : Fin d) :
    (coordinateWord γ).count i = γ i := by
  simp only [coordinateWord, List.count_flatMap]
  rw [← List.sum_toFinset _ (List.nodup_finRange d)]
  simp [List.count_replicate]

theorem coordinate_counts_sum :
    (∑ i, w.count i) = w.length := by
  simpa using (Multiset.sum_count_eq_card
    (m := (w : Multiset (Fin d))) (by simp))

theorem coordinate_fiber_card (i : Fin d) :
    Fintype.card {j : Fin q // σ j = i} = (List.ofFn σ).count i := by
  rw [Fintype.card_subtype, List.ofFn_eq_map, List.count, List.countP_map, List.countP_eq_length_filter]
  rfl

theorem coordinate_tuple_perm_of_counts {σ τ : Fin q → Fin d}
    (hcount : ∀ i, (List.ofFn σ).count i = (List.ofFn τ).count i) :
    ∃ p : Equiv.Perm (Fin q), τ ∘ p = σ := by
  let e i : {j : Fin q // σ j = i} ≃ {j : Fin q // τ j = i} :=
    Fintype.equivOfCardEq (by rw [coordinate_fiber_card, coordinate_fiber_card, hcount i])
  exact ⟨Equiv.ofFiberEquiv e, funext (Equiv.ofFiberEquiv_map e)⟩

theorem iteratedFDeriv_cast_order :
    iteratedFDeriv ℝ a F x (fun j => v (Fin.cast h j)) =
      iteratedFDeriv ℝ b F x v := by
  cases h
  rfl

/-- Directions corresponding to a mixed partial, in the reverse order
required by its left-fold definition. -/
def multiIndexBasis : Fin (∑ i, γ i) → Covariate d :=
  fun j => wordBasis (coordinateWord γ).reverse
    (Fin.cast (by rw [List.length_reverse, coordinateWord_length]) j)

end

variable {d : ℕ} {U : Set (Covariate d)} (hU : IsOpen U) {F : Covariate d → ℝ} {ℓ : ℕ} {α H : ℝ}
    (hH : 0 ≤ H) (hf : ContDiffOn ℝ ℓ F U) (hNorm : holderNorm U F ℓ α ≤ ENNReal.ofReal H) {q : ℕ}
include hU

include hf in
theorem multiPartial_eq_iteratedFDeriv {γ : Fin d → ℕ} (hγ : (∑ i, γ i) ≤ ℓ)
    {x : Covariate d} (hx : x ∈ U) :
    multiPartial F γ x =
      iteratedFDeriv ℝ (∑ i, γ i) F x (multiIndexBasis γ) := by
  have hpart := partialWord_eq_iteratedFDeriv hU hf (coordinateWord γ)
    (by simpa only [coordinateWord_length] using hγ) hx
  have hlen : (coordinateWord γ).reverse.length = ∑ i, γ i := by
    rw [List.length_reverse, coordinateWord_length]
  exact hpart.trans (iteratedFDeriv_cast_order hlen F x (multiIndexBasis γ))

/-- Every ordering of coordinate directions represents the model's mixed
partial with the same multiplicities. -/
theorem iteratedFDeriv_coordinates_eq_multiPartial
    (hf : ContDiffOn ℝ ℓ F U) (hq : q ≤ ℓ) (σ : Fin q → Fin d)
    {x : Covariate d} (hx : x ∈ U) :
    iteratedFDeriv ℝ q F x (fun j => Pi.single (σ j) 1) =
      multiPartial F (fun i => (List.ofFn σ).count i) x := by
  let γ  := fun i => (List.ofFn σ).count i
  let w := coordinateWord γ
  have hlen : w.reverse.length = q := by
    simp [List.length_reverse, w, coordinateWord_length, γ]
    rw [coordinate_counts_sum, List.length_ofFn]
  let τ  := fun j => w.reverse.get (Fin.cast hlen.symm j)
  have hlist : List.ofFn τ = w.reverse := by
    rw [← List.ofFn_congr hlen w.reverse.get, List.ofFn_get]
  have hcount i : (List.ofFn σ).count i = (List.ofFn τ).count i := by
    rw [hlist, List.count_reverse,  coordinateWord_count]
  obtain ⟨p, hp⟩ := coordinate_tuple_perm_of_counts hcount
  have hsym := CoordinatePartialBridge.iteratedFDeriv_comp_perm_finite
    ((hf.contDiffAt (hU.mem_nhds hx)).of_le (by exact_mod_cast hq))
    (fun j => Pi.single (τ j) 1) p
  have hvec : (fun j => (Pi.single (τ j) 1 : Covariate d)) ∘ p =
      fun j => Pi.single (σ j) 1 := by
    funext j
    exact congrArg (fun i => Pi.single i 1) (congrFun hp j)
  rw [hvec] at hsym
  have hpart := partialWord_eq_iteratedFDeriv hU hf w
    (by simpa only [← hlen, List.length_reverse] using hq) hx
  have hder : iteratedFDeriv ℝ w.reverse.length F x (wordBasis w.reverse) =
      iteratedFDeriv ℝ q F x (fun j => Pi.single (τ j) 1) := iteratedFDeriv_cast_order hlen F x (fun j => Pi.single (τ j) 1)
  rw [hder] at hpart
  exact hsym.trans hpart.symm

include hH hf hNorm in
/-- The paper's Hölder norm bounds each ordered contraction of the actual
Fréchet derivative, in every order through `ℓ`. -/
theorem ordered_coordinate_bound (hq : q ≤ ℓ) (σ : Fin q → Fin d)
    {x : Covariate d} (hx : x ∈ U) :
    |iteratedFDeriv ℝ q F x (fun j => Pi.single (σ j) 1)| ≤ H := by
  let γ : Fin d → Fin (ℓ + 1) := fun i =>
    ⟨(List.ofFn σ).count i,
      lt_of_le_of_lt (by simpa using (List.count_le_length (l := List.ofFn σ)))
        (Nat.lt_succ_of_le hq)⟩
  rw [iteratedFDeriv_coordinates_eq_multiPartial hU hf hq σ hx]
  exact holderNorm_derivative_bound hH hNorm γ
    (by simpa only [γ, coordinate_counts_sum, List.length_ofFn] using hq) hx

include hH hf hNorm in
/-- The top ordered Fréchet contractions inherit the exact Euclidean
Hölder modulus in the model norm. -/
theorem ordered_coordinate_modulus
    (σ : Fin ℓ → Fin d) {x y : Covariate d} (hx : x ∈ U) (hy : y ∈ U) :
    |iteratedFDeriv ℝ ℓ F x (fun j => Pi.single (σ j) 1) -
      iteratedFDeriv ℝ ℓ F y (fun j => Pi.single (σ j) 1)| ≤
      H * euclideanNorm (x - y) ^ α := by
  let γ : Fin d → Fin (ℓ + 1) := fun i =>
    ⟨(List.ofFn σ).count i,
      lt_of_le_of_lt (by simpa using (List.count_le_length (l := List.ofFn σ)))
        (Nat.lt_succ_self ℓ)⟩
  rw [iteratedFDeriv_coordinates_eq_multiPartial hU hf le_rfl σ hx,
    iteratedFDeriv_coordinates_eq_multiPartial hU hf le_rfl σ hy]
  exact holderNorm_top_derivative_modulus hH hNorm γ
    (by simp [γ, coordinate_counts_sum, List.length_ofFn]) hx hy

end NearlyMinimax
