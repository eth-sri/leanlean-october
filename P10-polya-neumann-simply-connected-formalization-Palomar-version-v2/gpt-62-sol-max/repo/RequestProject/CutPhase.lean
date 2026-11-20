module

public import RequestProject.TraceBound

/-!
# Cut logarithms and arc counts (Lemmas 9.3–9.5, abstract part)

For `0 < ε < 2π`, the branch `log_ε` of the logarithm with cut through `e^{iε}` and
`log_ε 1 = 0` takes the argument `argCut ε z ∈ (ε - 2π, ε)` at a unimodular `z ≠ e^{iε}`.
It differs from the negative branch `Arg₋` exactly on the open upper arc
`{e^{it} : 0 < t < ε}`, where it is larger by `2π`. Hence the cut phase sum
`∑ mult(z) argCut ε z` equals `Φ₋ + 2π n_{(0,ε)}(U)`, where `n_{(0,ε)}(U)` counts the eigenvalues
of `U` on that arc with multiplicity (the identity behind (9.3) in the proof of Lemma 9.5).

We also record the resonance rank bound of Proposition 7.10 on eigenvectors
(`CayleyRankBound`), and its consequences for the arc count.
-/

@[expose] public section

noncomputable section

open scoped Real ComplexConjugate
open MeasureTheory

namespace PolyaNeumann

section General

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The argument of `z` for the branch of the logarithm with cut through `e^{iε}` and value `0`
at `1`: the value in `(ε - 2π, ε)` (for unimodular `z ≠ 1, e^{iε}`). -/
def argCut (ε : ℝ) (z : ℂ) : ℝ := if argNeg z + 2 * π < ε then argNeg z + 2 * π else argNeg z

section

variable (ε : ℝ) (U : H →L[ℂ] H)
include ε U

/-- The term `mult(z) · argCut ε z` of the cut phase sum, indexed by `z ≠ 1`. -/
def cutPhaseTerm  (z : {z : ℂ // z ≠ 1}) : ℝ :=
  (eigenMult U z : ℝ) * argCut ε z

/-- The cut phase sum `∑_{z ∈ σ_p(U) \ {1}} argCut ε z = tr(-i log_ε U)`, eigenvalues counted
with multiplicity. -/
def cutPhaseSum  : ℝ := ∑' z, cutPhaseTerm ε U z

/-- The multiplicity of `z` if `z` lies on the open upper arc `{e^{it} : 0 < t < ε}`, and `0`
otherwise. -/
def arcTerm  (z : {z : ℂ // z ≠ 1}) : ℝ :=
  if argNeg z + 2 * π < ε then (eigenMult U z : ℝ) else 0

/-- The arc count `n_{(0,ε)}(U)`: the number of eigenvalues of `U` on the open arc
`{e^{it} : 0 < t < ε}`, counted with multiplicity. -/
def arcCount  : ℝ := ∑' z, arcTerm ε U z

end

/-- Proposition 7.10 on eigenvectors: every orthonormal family of eigenvectors of `U` whose
eigenvalues `e^{it}` (`0 < t < 2π`) correspond to Cayley eigenvalues `cot(t/2) > A` has at
most `m` members. -/
def CayleyRankBound (U : H →L[ℂ] H) (A : ℝ) (m : ℕ) : Prop :=
  ∀ (n : ℕ) (v : Fin n → H) (t : Fin n → ℝ), Orthonormal ℂ v →
    (∀ k, 0 < t k ∧ t k < 2 * π) → (∀ k, U (v k) = Complex.exp (t k * Complex.I) • v k) →
    (∀ k, A < Real.cot (t k / 2)) → n ≤ m

omit [CompleteSpace H] in
lemma cutPhaseTerm_eq (ε : ℝ) (U : H →L[ℂ] H) (z : {z : ℂ // z ≠ 1}) :
    cutPhaseTerm ε U z = phaseTerm U z + 2 * π * arcTerm ε U z := by
  unfold cutPhaseTerm phaseTerm arcTerm argCut
  grind

/-- `cot(t/2)` is antitone in `t ∈ (0, π)`. -/
lemma cot_half_le_cot_half {t s : ℝ} (ht : 0 < t) (hts : t ≤ s) (hs : s < π) :
    Real.cot (s / 2) ≤ Real.cot (t / 2) := by
  have hs2 : 0 < Real.sin (s / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have ht2 : 0 < Real.sin (t / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hsin : Real.sin (t / 2) ≤ Real.sin (s / 2) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith)
  have hcos : Real.cos (s / 2) ≤ Real.cos (t / 2) :=
    Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith)
  have hc : 0 < Real.cos (s / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin, div_le_div_iff₀ hs2 ht2]
  nlinarith

/-- For every `A` there is `ε ∈ (0, π)` with `cot(ε/2) > A`. -/
lemma exists_cot_half_gt (A : ℝ) : ∃ ε, 0 < ε ∧ ε < π ∧ A < Real.cot (ε / 2) := by
  set y : ℝ := 1 / (|A| + 1) with hy
  have hy0 : 0 < y := by positivity
  refine ⟨2 * Real.arctan y, by positivity, ?_, ?_⟩
  · have := Real.arctan_lt_pi_div_two y; linarith
  · rw [mul_div_cancel_left₀ _ two_ne_zero, Real.cot_eq_cos_div_sin, Real.cos_arctan,
      Real.sin_arctan]
    have hsq : 0 < √(1 + y ^ 2) := by positivity
    rw [div_div_div_cancel_right₀ hsq.ne', one_div_one_div]
    grind

/-- A nonunit spectral value of `U` with `U - I` compact is an eigenvalue. -/
lemma exists_eigen_of_mem_spectrum {U : H →L[ℂ] H} (hC : IsCompactOperator ⇑(U - 1)) {k : ℂ}
    (hk : k ∈ spectrum ℂ U) (hk1 : k ≠ 1) : ∃ v : H, v ≠ 0 ∧ U v = k • v := by
  have hk' : k - 1 ∈ spectrum ℂ (U - 1) := by
    rw [spectrum.mem_iff] at hk ⊢
    convert hk using 2
    rw [map_sub, map_one]; abel
  obtain ⟨v, hv0, hv⟩ := exists_eigenvector_of_mem_spectrum hC hk' (sub_ne_zero.mpr hk1)
  refine ⟨v, hv0, ?_⟩
  rw [sub_smul, one_smul] at hv
  simp_all

omit [CompleteSpace H] in
/-- With rank bound `0`, no eigenvalue `e^{it}` has `cot(t/2) > A`. -/
lemma CayleyRankBound.cot_le {U : H →L[ℂ] H} {A : ℝ} (h : CayleyRankBound U A 0) {t : ℝ}
    (ht0 : 0 < t) (ht : t < 2 * π) {v : H} (hv : v ≠ 0)
    (hUv : U v = Complex.exp (t * Complex.I) • v) : Real.cot (t / 2) ≤ A := by
  by_contra hlt
  push_neg at hlt
  have hn : (‖v‖ : ℂ) ≠ 0 := by simp_all
  have := h 1 (fun _ => ((‖v‖ : ℂ)⁻¹) • v) (fun _ => t) ?_ (fun _ => ⟨ht0, ht⟩) ?_ (fun _ => hlt)
  trivial
  · rw [orthonormal_iff_ite]
    intro i j
    rw [Subsingleton.elim i j, if_pos rfl, inner_smul_left, inner_smul_right,
      inner_self_eq_norm_sq_to_K]
    field_simp
    simp
    grind
  · intro k
    rw [map_smul, hUv, smul_comm]

omit [CompleteSpace H] in
/-- From the rank bound `0` with `cot(ε/2) > A` and `ε < π`: `U` has no eigenvalue `e^{it}` with
`0 < t ≤ ε`. -/
lemma CayleyRankBound.no_arc_eigen {U : H →L[ℂ] H} {A ε : ℝ} (h : CayleyRankBound U A 0)
    (hε : ε < π) (hA : A < Real.cot (ε / 2)) :
    ∀ t, 0 < t → t ≤ ε → ∀ v : H, v ≠ 0 → U v ≠ Complex.exp (t * Complex.I) • v := by
  intro t ht0 htε v hv hUv
  have h1 := h.cot_le ht0 (by linarith) hv hUv
  have h2 := cot_half_le_cot_half ht0 htε hε
  linarith

/-- `e^{it} ≠ 1` for `0 < t < 2π`. -/
lemma exp_mul_I_ne_one {t : ℝ} (h0 : 0 < t) (h1 : t < 2 * π) :
    Complex.exp (t * Complex.I) ≠ 1 := by
  intro h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  have htn : t = n * (2 * π) := by
    have := congrArg Complex.im hn
    simpa [Complex.mul_im] using this
  have hp := Real.pi_pos
  have hn1 : (0 : ℝ) < n := by
    simp_all
  have hn2 : (n : ℝ) < 1 := by
    simp_all
  have h1' : (0 : ℤ) < n := by exact_mod_cast hn1
  have h2' : n < (1 : ℤ) := by exact_mod_cast hn2
  omega

/-- A nonzero phase with no eigenvector is outside the spectrum. -/
lemma exp_mul_I_notMem_spectrum {U : H →L[ℂ] H} (hC : IsCompactOperator ⇑(U - 1)) {ε : ℝ}
    (hε0 : 0 < ε) (hε : ε < π)
    (hno : ∀ v : H, v ≠ 0 → U v ≠ Complex.exp (ε * Complex.I) • v) :
    Complex.exp (ε * Complex.I) ∉ spectrum ℂ U := by
  intro hmem
  have hne := exp_mul_I_ne_one hε0 (by linarith [Real.pi_pos])
  obtain ⟨v, hv0, hv⟩ := exists_eigen_of_mem_spectrum hC hmem hne
  tauto

section

variable {U : H →L[ℂ] H} (hU : U ∈ unitary (H →L[ℂ] H)) (hC : IsCompactOperator ⇑(U - 1)) {ε : ℝ} (hno : ∀ t, 0 < t → t < ε → ∀ v : H, v ≠ 0 → U v ≠ Complex.exp (t * Complex.I) • v)
include U hU hC ε hno

/-- If no eigenvalue lies on the arc `{e^{it} : 0 < t < ε}`, the arc terms vanish. -/
lemma arcTerm_eq_zero 
    (z : {z : ℂ // z ≠ 1}) : arcTerm ε U z = 0 := by
  unfold arcTerm
  split_ifs with h
  · by_contra hm
    have hm' : 0 < eigenMult U z := Nat.pos_of_ne_zero (by exact_mod_cast hm)
    haveI := finiteDimensional_eigenspace hC z.2
    obtain ⟨⟨v, hv⟩, hv0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hm'
    have hv0' : v ≠ 0 := fun h => hv0 (by simp [h])
    have hveig : U v = (z : ℂ) • v := Module.End.mem_eigenspace_iff.mp hv
    have hz1 : ‖(z : ℂ)‖ = 1 := norm_eq_one_of_eigen hU hv0' hveig
    have hI := argNeg_mem_Ioo hz1 z.2
    refine hno (argNeg z + 2 * π) (by linarith [hI.1]) h v hv0' ?_
    rw [hveig]
    congr 1
    push_cast
    rw [add_mul, Complex.exp_add, exp_argNeg hz1, Complex.exp_two_pi_mul_I, mul_one]
  rfl

/-- If no eigenvalue lies on the arc `{e^{it} : 0 < t < ε}`, the cut and negative phase sums
agree. -/
lemma cutPhaseSum_eq_phaseSum  :
    cutPhaseSum ε U = phaseSum U := by
  unfold cutPhaseSum phaseSum
  congr 1
  ext z
  rw [cutPhaseTerm_eq, arcTerm_eq_zero hU hC hno, mul_zero, add_zero]

end

/-- Under the rank bound `m`, if `cot(t/2) > A` for `0 < t < ε ≤ 2π`, then finitely many
eigenvalues lie on the arc `{e^{it} : 0 < t < ε}` and their number, with multiplicity, is at
most `m`. -/
lemma arcCount_le {U : H →L[ℂ] H} (hU : U ∈ unitary (H →L[ℂ] H))
    (hC : IsCompactOperator ⇑(U - 1)) {ε A : ℝ} {m : ℕ} (hε : ε ≤ 2 * π)
    (hA : ∀ t, 0 < t → t < ε → A < Real.cot (t / 2)) (h : CayleyRankBound U A m) :
    Summable (arcTerm ε U) ∧ arcCount ε U ≤ m := by
  classical
  have hnn : ∀ z, 0 ≤ arcTerm ε U z := fun z => by unfold arcTerm; positivity
  have hfin : ∀ s : Finset {z : ℂ // z ≠ 1}, ∑ z ∈ s, arcTerm ε U z ≤ m := by
    intro s
    set s' := s.filter (fun z : {z : ℂ // z ≠ 1} => argNeg (z : ℂ) + 2 * π < ε) with hs'
    have hsum : ∑ z ∈ s, arcTerm ε U z = ∑ z ∈ s', (eigenMult U z : ℝ) := by
      rw [Finset.sum_filter]
      rfl
    obtain ⟨e, he, heig⟩ := exists_orthonormal_eigen_family hU s'
    have hne := fun p => he.ne_zero p
    have hz1 :=
      fun p => norm_eq_one_of_eigen hU (hne p) (heig p)
    have hP : ∀ p : (Σ z : s', Fin (eigenMult U z)),
        argNeg ((p.1 : {z : ℂ // z ≠ 1}) : ℂ) + 2 * π < ε := fun p =>
      (Finset.mem_filter.mp p.1.2).2
    set t : (Σ z : s', Fin (eigenMult U z)) → ℝ := fun p => argNeg p.1.1 + 2 * π with ht
    have ht0 : ∀ p, 0 < t p := fun p => by
      have := argNeg_mem_Ioo (hz1 p) p.1.1.2
      simp  ; linarith [this.1]
    have htε := hP
    have hexp : ∀ p, Complex.exp (t p * Complex.I) = ((p.1 : {z : ℂ // z ≠ 1}) : ℂ) := by
      intro p
      simp only [ht]
      push_cast
      rw [add_mul, Complex.exp_add, exp_argNeg (hz1 p), Complex.exp_two_pi_mul_I, mul_one]
    set f := Fintype.equivFin (Σ z : s', Fin (eigenMult U z)) with hf
    have hcard := h _ (e ∘ f.symm) (t ∘ f.symm) (he.comp _ f.symm.injective)
      (fun k => ⟨ht0 _, show t (f.symm k) < 2 * π by linarith [htε (f.symm k)]⟩)
      (fun k => by simp  ; rw [hexp, heig])
      (fun k => hA _ (ht0 _) (htε _))
    rw [hsum]
    have : (Fintype.card (Σ z : s', Fin (eigenMult U z)) : ℝ) = ∑ z ∈ s', (eigenMult U z : ℝ) := by
      rw [Fintype.card_sigma]
      simp only [Fintype.card_fin]
      push_cast
      rw [← Finset.sum_coe_sort s']
    rw [← this]
    exact_mod_cast hcard
  exact ⟨summable_of_sum_le hnn hfin, Real.tsum_le_of_sum_le hnn hfin⟩

omit [CompleteSpace H] in
lemma arcTerm_nonneg (ε : ℝ) (U : H →L[ℂ] H) (z : {z : ℂ // z ≠ 1}) : 0 ≤ arcTerm ε U z := by grind [arcTerm]

omit [CompleteSpace H] in
lemma arcCount_nonneg (ε : ℝ) (U : H →L[ℂ] H) : 0 ≤ arcCount ε U :=
  tsum_nonneg fun z => arcTerm_nonneg ε U z

omit [CompleteSpace H] in
/-- The identity (9.3): `∑ argCut ε = Φ₋ + 2π n_{(0,ε)}(U)`. -/
lemma cutPhaseSum_eq_add {U : H →L[ℂ] H} {ε : ℝ} (hs : Summable (phaseTerm U))
    (ha : Summable (arcTerm ε U)) :
    cutPhaseSum ε U = phaseSum U + 2 * π * arcCount ε U := by
  unfold cutPhaseSum phaseSum arcCount
  simp  [cutPhaseTerm_eq]
  rw [hs.tsum_add (ha.mul_left _), tsum_mul_left]

end General

section

variable {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
include γ K hK

/-- The monodromy `U_E` of a Lipschitz curve is unitary. -/
lemma monodromyAt_mem_unitary  (E : ℝ) :
    monodromyAt γ E ∈ unitary (Ell2 →L[ℂ] Ell2) := by
  obtain ⟨W, hW⟩ := transport_exists_of_lipschitz γ hK E
  rw [monodromyAt_eq hK hW, monodromy]
  exact Unitary.star_mem (transport_mem_unitary hK hW ⟨by positivity, le_rfl⟩)

/-- For a closed Lipschitz curve and `E ≥ 0`, `U_E - I` is compact (Lemma 4.7). -/
lemma isCompactOperator_monodromyAt_sub_one 
    (hclosed : γ (2 * π) = γ 0) {E : ℝ} (hE : 0 ≤ E) :
    IsCompactOperator ⇑(monodromyAt γ E - 1) := by
  obtain ⟨W, hW⟩ := transport_exists_of_lipschitz γ hK E
  rw [monodromyAt_eq hK hW]
  exact isCompactOperator_monodromy_sub_one hK hclosed hE hW

/-- For a closed Lipschitz curve, `E ↦ U_E` is norm-continuous on `(0, ∞)` (Lemma 4.7). -/
lemma continuousAt_monodromyAt 
    (hclosed : γ (2 * π) = γ 0) {E : ℝ} (hE : 0 < E) : ContinuousAt (monodromyAt γ) E := by
  choose Ws hWs using fun E' : ℝ => transport_exists_of_lipschitz γ hK E'
  have h : monodromyAt γ = fun E' => monodromy (Ws E') :=
    funext fun E' => monodromyAt_eq hK (hWs E')
  rw [h]
  exact (hasDerivAt_monodromy_energy hK hclosed hWs hE).continuousAt

end

/-- The cut phase count `J_ε(E) = (E|Ω|/2 - tr(-i log_ε U_E)) / (2π)` of Lemma 9.3, with the
trace written as the multiplicity-weighted sum of `argCut ε` over the eigenvalues `z ≠ 1` of
`U_E`. -/
def cutPhaseCount (Ω : Set ℂ) (γ : ℝ → ℂ) (ε E : ℝ) : ℝ :=
  ((volume Ω).toReal * E / 2 - cutPhaseSum ε (monodromyAt γ E)) / (2 * π)

/-- Removing the eigenvalues on the open arc converts the cut count to the negative-branch count. -/
lemma phaseCount_eq_cutPhaseCount_add_arcCount {Ω : Set ℂ} {γ : ℝ → ℂ} {ε E : ℝ}
    (hs : Summable (cutPhaseTerm ε (monodromyAt γ E)))
    (ha : Summable (arcTerm ε (monodromyAt γ E))) :
    phaseCount Ω γ E = cutPhaseCount Ω γ ε E + arcCount ε (monodromyAt γ E) := by
  have hp : Summable (phaseTerm (monodromyAt γ E)) :=
    (hs.sub (ha.mul_left (2 * π))).congr fun z => by rw [cutPhaseTerm_eq]; ring
  rw [phaseCount, cutPhaseCount, cutPhaseSum_eq_add hp ha]
  field_simp [Real.pi_ne_zero]
  ring

end PolyaNeumann
