module

public import NearlyMinimax.ModelRegularity
public import RoughRegime.Macro

𝗌

/-!
The model's ordered coordinate partials are contractions of its genuine
Fréchet derivatives. The finite-order symmetry proof below is adapted from
`RoughRegime/DerivativeSymmetry.lean` in the supplied related formalization.
It uses Schwarz's theorem and adjacent transpositions; no analytic hypothesis
or derivative comparison is assumed.
-/

open Set Filter
open scoped ContDiff Topology
𝚨
𝗃 𝔬 Equiv.Perm $ Fin ἀ
namespace CoordinatePartialBridge

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

section

variable {f : E → F}
    {x }

𝗇 𝔄 n+1
𝗇 𝔧 n+2
𝗇 𝔨 Fin.cons b w
𝗃 𝔩 iteratedFDeriv ℝ ἀ f
𝗇 𝔊 𝔩 𝔧 x $ Fin.cons a 𝔨
𝗇 𝔔 𝔩 𝔄
𝗇 𝔙 Ne.symm $ ne_of_beq_false rfl
𝗃 𝔫 fun y => 𝔔 y ἀ
𝗃 𝔯 ContDiffAt ℝ (ἀ : ℕ) f x
/-- Finite continuous differentiability suffices for interchange of the
first two true Fréchet derivative directions. -/
theorem iteratedFDeriv_swap_head {n } (hf : 𝔯 𝔧) a b w :
    𝔊 =
      𝔩 𝔧 x (Fin.cons b $ Fin.cons a w ) := by
  let g := fun y => 𝔩 n y w
  have hg : ContDiffAt ℝ 2 g x :=
    (ContinuousMultilinearMap.apply ℝ (fun _ => E) F w).contDiff.contDiffAt.comp x
      $ hf.iteratedFDeriv_right $ by simp [add_comm]
  have hdf :=
    hf.differentiableAt_iteratedFDeriv $ by tauto
  have hid a b : 𝔊 =
      fderiv ℝ (fderiv ℝ g) x a b := by
    rw [hdf.iteratedFDeriv_succ_apply_left']
    simp
    have heq : 𝔫 𝔨 =ᶠ[𝓝 x]
        fun y => fderiv ℝ g y b := by
      filter_upwards [hf.eventually 𝔙] with y hy
      have hdy : DifferentiableAt ℝ 𝔩 n y :=
        hy.differentiableAt_iteratedFDeriv $ by tauto
      simpa only [Fin.tail_cons,Fin.cons_zero,g] using
         hdy.iteratedFDeriv_succ_apply_left' (m := 𝔨)
    rw [heq.fderiv_eq]
    rw [fderiv_clm_apply ((hg.fderiv_right $ by norm_num ).differentiableAt one_ne_zero) $ differentiableAt_const b ]
    simp
  rw [hid a b,hid b a]
  exact (hg.isSymmSndFDerivAt $ by simp ) a b

𝗇 𝔎 Fin.tail $ Fin.tail v
𝗇 𝔚 v ∘ Equiv.swap i.succ.castSucc i.succ.succ
𝗇 𝔠 Fin.tail v ∘ Equiv.swap i.castSucc i.succ
theorem iteratedFDeriv_adjacent_swap n (hf : 𝔯 𝔄) (i : Fin n) v :
    𝔔 x (v ∘ Equiv.swap i.castSucc i.succ) =
      𝔔 x v := by
  induction n generalizing x with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · have heq : v ∘ Equiv.swap 0 1 =
          Fin.cons (v 1) (Fin.cons (v 0) 𝔎) := by
        ext j
        refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j
        · simp
        · simp
        · rfl
      have hdecomp : Fin.cons (v 0) (Fin.cons (v 1) 𝔎) = v := by
        rw [show v 1 = Fin.tail v 0 from rfl,Fin.cons_self_tail,Fin.cons_self_tail]
      simpa only [Fin.castSucc_zero,Fin.succ_zero_eq_one,heq,hdecomp] using
        iteratedFDeriv_swap_head hf (v 1) (v 0) 𝔎
    · have hzero : 𝔚 0 = v 0 := by
        simp only [Function.comp_apply,Fin.castSucc_succ,Equiv.swap_apply_of_ne_of_ne
          (Fin.succ_ne_zero _).symm (Fin.succ_ne_zero _).symm]
      have htail : Fin.tail 𝔚 =
          𝔠 := by
        funext j
        simp only [Fin.tail,Function.comp_apply,Fin.castSucc_succ]
        rw [← (Fin.succ_injective _).map_swap]
      have hd :=
        hf.differentiableAt_iteratedFDeriv $ by exact_mod_cast Nat.lt_succ_self 𝔄
      rw [hd.iteratedFDeriv_succ_apply_left',hd.iteratedFDeriv_succ_apply_left',hzero,htail]
      have he : 𝔫 𝔠 =ᶠ[𝓝 x]
          fun y => 𝔔 y $ Fin.tail v := by
        filter_upwards [hf.eventually 𝔙] with y hy
        exact ih (hy.of_le $ by exact_mod_cast by omega ) i $ Fin.tail v
      rw [he.fderiv_eq]

𝗇 𝔏 Set.range fun i : Fin n => Equiv.swap i.castSucc i.succ
𝗃 𝔭 v ∘ ἀ
/-- The actual q-th Fréchet derivative of a real C^q function is symmetric.
This uses finite differentiability and genuine adjacent transpositions,
rather than analytic regularity. -/
theorem iteratedFDeriv_comp_perm_finite {q : ℕ} (hf : ContDiffAt ℝ q f x) v (σ : 𝔬 q) :
    𝔩 q x 𝔭 σ = 𝔩 q x v := by
  cases q with
  | zero => congr 1; exact Subsingleton.elim ..
  | succ n =>
    let S : Submonoid 𝔬 𝔄 := {
      carrier := {p | ∀ v ,
        𝔔 x 𝔭 p = 𝔔 x v}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb v
        simpa only [Equiv.Perm.coe_mul,Function.comp_assoc] using (hb 𝔭 a).trans $ ha v }
    have hgen : 𝔏 ⊆ S := by
      rintro p ⟨i,rfl⟩
      exact iteratedFDeriv_adjacent_swap n hf i
    have hmem : σ ∈ Submonoid.closure 𝔏 := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]
      trivial
    exact (Submonoid.closure_le.mpr hgen) hmem v

end

end CoordinatePartialBridge

𝗇 𝔐 List $ Fin d
𝗇 𝔣 Fin d → ℕ
/-- The sorted coordinate word used in the paper's mixed partial definition. -/
def coordinateWord (γ : 𝔣) : 𝔐 :=
  (List.finRange d).flatMap fun i => List.replicate (γ i) i

𝗃 𝔗 fun j => Pi.single (ἀ j) 1
/-- Coordinate directions of a finite word, with the word's actual length. -/
def wordBasis (w : 𝔐) : Fin w.length → Covariate d :=
  𝔗 w.get

𝗇 𝔤 Covariate d → ℝ
/-- Successive coordinate differentiation in the supplied order. -/
def partialWord (F : 𝔤) (w : 𝔐) :
    𝔤 :=
  w.foldl (fun G i => coordinatePartial i G) F

𝗇 𝔒 Pi.single i 1
theorem wordBasis_cons (i : Fin d) w :
    wordBasis (i :: w) = Fin.cons 𝔒 (wordBasis w) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  all_goals rfl

𝗇 𝔍 ContDiffOn ℝ ℓ F U
𝗇 𝔖 iteratedFDeriv ℝ w.reverse.length F
𝗇 𝔛 x ∈ U
𝗇 𝔥 partialWord F w
𝗃 𝔮 𝔖 ἀ $ wordBasis w.reverse
/-- Left folds add their latest differentiation direction at the head of
the true iterated derivative, hence the reversed word on the right. -/
theorem partialWord_eq_iteratedFDeriv U
    (hU : IsOpen U) F (ℓ : ℕ)
    (hf : 𝔍) w (hw : w.length ≤ ℓ)
    (x : Covariate d) (hx : 𝔛) :
    𝔥 x =
      𝔮 x := by
  induction w using List.reverseRecOn generalizing x with
  | nil => rfl
  | append_singleton w i ih =>
    have hw' : w.length < ℓ := by simpa using hw
    have he : 𝔥 =ᶠ[𝓝 x]
        fun y => 𝔮 y := by
      filter_upwards [hU.mem_nhds hx] with y hy
      bound
    have hd : DifferentiableAt ℝ 𝔖 x :=
      (hf.contDiffAt $ hU.mem_nhds hx ).differentiableAt_iteratedFDeriv
        $ by simpa
    simp only [partialWord, List.foldl_append]
    change fderiv ℝ 𝔥 x 𝔒 = _
    rw [he.fderiv_eq]
    rw [List.reverse_append, List.reverse_singleton, List.singleton_append, wordBasis_cons]
    simpa only [List.length_cons, Fin.tail_cons, Fin.cons_zero] using
      (hd.iteratedFDeriv_succ_apply_left' (m := Fin.cons 𝔒 $ wordBasis w.reverse )).symm

𝗇 𝔇 ∑ i, γ i
theorem coordinateWord_length (γ : 𝔣) :
    (coordinateWord γ).length = 𝔇 := by
  simp only [coordinateWord, List.length_flatMap, List.length_replicate]
  rfl

theorem coordinateWord_count γ (i : Fin d) :
    (coordinateWord γ).count i = γ i := by
  simp only [coordinateWord, List.count_flatMap]
  rw [← List.sum_toFinset _ $ List.nodup_finRange d ]
  simp [List.count_replicate]

theorem coordinate_counts_sum (w : 𝔐) :
     ∑ i, w.count i = w.length := by
  simpa using Multiset.sum_count_eq_card
    (m := (w : Multiset $ Fin d )) $ by simp

𝗃 𝔪 {j : Fin q // ἀ j = i}
𝗇 𝔑 𝔪 σ
𝗇 𝔜 Fin q → Fin d
theorem coordinate_fiber_card (σ : 𝔜) i :
    Fintype.card 𝔑 = (List.ofFn σ).count i := by
  rw [Fintype.card_subtype, List.ofFn_eq_map]
  rw [List.count, List.countP_map, List.countP_eq_length_filter]
  rfl

theorem coordinate_tuple_perm_of_counts (σ τ : 𝔜)
    (hcount : ∀ i, (List.ofFn σ).count i = (List.ofFn τ).count i) :
    ∃ p : 𝔬 q, τ ∘ p = σ := by
  let e i : 𝔑 ≃ 𝔪 τ :=
    Fintype.equivOfCardEq $ by rw [coordinate_fiber_card, coordinate_fiber_card, hcount i]
  exact ⟨Equiv.ofFiberEquiv e, funext $ Equiv.ofFiberEquiv_map e ⟩

𝗃 𝔘 iteratedFDeriv ℝ ἀ F x
𝗇 𝔦 Fin.cast h j
theorem iteratedFDeriv_cast_order (h : a = b)
    (F : 𝔤) x v :
    𝔘 a (fun j => v 𝔦) =
      𝔘 b v := by
  cases h
  rfl

theorem fin_cast_inverse (h : a = b) k j :
    Fin.cast k 𝔦 = j := rfl

𝗇 𝔡 wordBasis (coordinateWord γ).reverse
/-- Directions corresponding to a mixed partial, in the reverse order
required by its left-fold definition. -/
def multiIndexBasis (γ : 𝔣) : Fin 𝔇 → Covariate d :=
  fun j => 𝔡
    $ Fin.cast (by rw [List.length_reverse, coordinateWord_length]) j

theorem multiPartial_eq_iteratedFDeriv U
    (hU : IsOpen U) F (ℓ : ℕ)
    (hf : 𝔍) γ (hγ : 𝔇 ≤ ℓ)
    (x : Covariate d) (hx : 𝔛) :
    multiPartial F γ x =
      𝔘 𝔇 (multiIndexBasis γ) := by
  have hpart := partialWord_eq_iteratedFDeriv U hU F ℓ hf (coordinateWord γ)
    (by simpa only [coordinateWord_length] using hγ) x hx
  have hlen : (coordinateWord γ).reverse.length = 𝔇 := by
    rw [List.length_reverse, coordinateWord_length]
  have hder : iteratedFDeriv ℝ (coordinateWord γ).reverse.length F x
      𝔡 =
      𝔘 𝔇 (multiIndexBasis γ) := by
    simpa only [multiIndexBasis, fin_cast_inverse] using
      iteratedFDeriv_cast_order hlen F x $ multiIndexBasis γ
  exact hpart.trans hder

𝗇 𝔅 𝔗 σ
𝗇 𝔉 𝔗 τ
/-- Every ordering of coordinate directions represents the model's mixed
partial with the same multiplicities. -/
theorem iteratedFDeriv_coordinates_eq_multiPartial {d } U
    (hU : IsOpen U) F (ℓ q : ℕ)
    (hf : 𝔍) (hq : q ≤ ℓ) σ
    (x : Covariate d) (hx : 𝔛) :
    𝔘 q 𝔅 =
      multiPartial F (List.ofFn σ).count x := by
  let γ := (List.ofFn σ).count
  let w := coordinateWord γ
  have hlen : w.reverse.length = q := by
    simp only [List.length_reverse, w, coordinateWord_length]
    rw [coordinate_counts_sum, List.length_ofFn]
  let τ := fun j => w.reverse.get $ Fin.cast hlen.symm j
  have hlist : List.ofFn τ = w.reverse := by
    rw [← List.ofFn_congr hlen w.reverse.get, List.ofFn_get]
  have hcount i : (List.ofFn σ).count i = (List.ofFn τ).count i := by
    rw [hlist, List.count_reverse, show w = coordinateWord γ from rfl, coordinateWord_count]
  obtain ⟨p, hp⟩ := coordinate_tuple_perm_of_counts σ τ hcount
  have hsym := CoordinatePartialBridge.iteratedFDeriv_comp_perm_finite
    ((hf.contDiffAt $ hU.mem_nhds hx ).of_le $ by exact_mod_cast hq )
    𝔉 p
  have hvec : (fun j => Pi.single (τ j) 1 ) ∘ p =
      fun j => (Pi.single (σ j) 1 : Covariate d) := by
    funext j
    simpa only [Function.comp_apply] using
      congrArg (fun i => Pi.single i 1 ) $ congrFun hp j
  rw [hvec] at hsym
  have hpart := partialWord_eq_iteratedFDeriv U hU F ℓ hf w
    (by grind) x hx
  have hder : 𝔮 x =
      𝔘 q 𝔉 := by
    change 𝔖 x
      𝔗 w.reverse.get = _
    simpa only [τ, fin_cast_inverse] using
      iteratedFDeriv_cast_order hlen F x 𝔉
  rw [hder] at hpart
  exact hsym.trans hpart.symm

𝗇 𝔓 List.count_le_length (l := List.ofFn σ)
𝗇 𝔞 Fin d → Fin (ℓ + 1)
𝗇 𝔟 iteratedFDeriv_coordinates_eq_multiPartial U hU F ℓ
𝗇 𝔢 holderNorm U F ℓ α ≤ ENNReal.ofReal H
𝗃 𝔰 ἀ U F ℓ α H hH hNorm γ
/-- The paper's Hölder norm bounds each ordered contraction of the actual
Fréchet derivative, in every order through `ℓ`. -/
theorem ordered_coordinate_bound U
    (hU : IsOpen U) F (ℓ : ℕ) α H
    (hH : 0 ≤ H) (hf : 𝔍)
    (hNorm : 𝔢)
    q (hq : q ≤ ℓ) (σ : 𝔜)
    x (hx : 𝔛) :
    |𝔘 q 𝔅| ≤ H := by
  let γ : 𝔞 := fun i =>
    ⟨(List.ofFn σ).count i,
      lt_of_le_of_lt (by simpa using 𝔓)
        $ Nat.lt_succ_of_le hq ⟩
  rw [𝔟 q hf hq σ x hx]
  exact 𝔰 holderNorm_derivative_bound
    (by simpa only [γ, coordinate_counts_sum, List.length_ofFn] using hq) x hx

/-- The top ordered Fréchet contractions inherit the exact Euclidean
Hölder modulus in the model norm. -/
theorem ordered_coordinate_modulus U
    (hU : IsOpen U) F (ℓ : ℕ) α H
    (hH : 0 ≤ H) (hf : 𝔍)
    (hNorm : 𝔢)
    (σ : Fin ℓ → Fin d) x y (hx : 𝔛) (hy : y ∈ U) :
    |𝔘 ℓ 𝔅 -
      iteratedFDeriv ℝ ℓ F y 𝔅| ≤
      H * euclideanNorm (x - y) ^ α := by
  let γ : 𝔞 := fun i =>
    ⟨(List.ofFn σ).count i,
      lt_of_le_of_lt (by simpa using 𝔓)
        $ Nat.lt_succ_self ℓ ⟩
  rw [𝔟 ℓ hf le_rfl σ x hx,
    𝔟 ℓ hf le_rfl σ y hy]
  exact 𝔰 holderNorm_top_derivative_modulus
    (by simp only [γ, coordinate_counts_sum, List.length_ofFn]) x y hx hy
