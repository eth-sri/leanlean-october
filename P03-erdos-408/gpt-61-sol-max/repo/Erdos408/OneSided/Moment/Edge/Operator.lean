module
public import Mathlib.Tactic

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Real.Sqrt

/-!
# Kernel bounds on finite sets

The clean edge bound (M6, `Moment/Edge/Clean.lean`) moves between many concrete index sets:
chain states, label tuples, positions of the root box, and boxes of lattice coordinates.
Its operators are recorded as kernels `k : α → β → ℂ` acting from functions on a finite set
`S' ⊆ β` to functions on a finite set `S ⊆ α`, by `(k f)(x) = ∑_{y ∈ S'} k(x, y) f(y)`.

* `KerLe S S' k c` says `‖k f‖ ≤ c ‖f‖` in `ℓ²`; `WKerLe` is the weighted version.
* `KerLe.bilinear` and `kerLe_of_bilinear`: the bound is equivalent to the bilinear bound
  `|⟨g, k f⟩| ≤ c ‖g‖ ‖f‖`. Hence bounds add (`KerLe.add`, `KerLe.sum`).
* `KerLe.mul_diag`: multipliers of modulus at most one at both ends cost nothing.
* `KerLe.comp_embed`: a kernel pulled back along maps injective on the index sets has no
  larger norm (PD: "extending the product variable means composing with extension by zero and
  restriction").
* `KerLe.block`: a kernel that is block diagonal for labelings of both index sets has the norm
  of its worst block.
* `kerLe_of_schur`, `wkerLe_of_schur`: the Schur test with weight one.
* `wkerLe_of_kerLe`: conjugation from weighted to counting measure.
-/

@[expose] public section

namespace Erdos408.OneSided

open Finset

variable {α β γ δ ι : Type*}

/-- `‖k f‖ ≤ c ‖f‖` for the kernel `k` from `ℓ²(S')` to `ℓ²(S)`. -/
def KerLe (S : Finset α) (S' : Finset β) (k : α → β → ℂ) (c : ℝ)  :=
  ∀ f : β → ℂ, ∑ x ∈ S, ‖∑ y ∈ S', k x y * f y‖ ^ 2 ≤ c ^ 2 * ∑ y ∈ S', ‖f y‖ ^ 2

/-- `‖k f‖_μ ≤ c ‖f‖_ν` for the kernel `k` from `ℓ²(S', ν)` to `ℓ²(S, μ)`. -/
def WKerLe (S : Finset α) (S' : Finset β) (μ : α → ℝ) (ν : β → ℝ) (k : α → β → ℂ)
    (c : ℝ)  :=
  ∀ f : β → ℂ, ∑ x ∈ S, μ x * ‖∑ y ∈ S', k x y * f y‖ ^ 2 ≤ c ^ 2 * ∑ y ∈ S', ν y * ‖f y‖ ^ 2

/-! ### Cauchy–Schwarz -/

/-- Cauchy–Schwarz for complex finite sums: `|∑ ā b| ≤ ‖a‖ ‖b‖`. -/
theorem norm_sum_star_mul_le (S : Finset α) (a b : α → ℂ) :
    ‖∑ x ∈ S, star (a x) * b x‖ ≤
      Real.sqrt (∑ x ∈ S, ‖a x‖ ^ 2) * Real.sqrt (∑ x ∈ S, ‖b x‖ ^ 2) := by
  refine (norm_sum_le _ _).trans ?_
  calc ∑ x ∈ S, ‖star (a x) * b x‖ = ∑ x ∈ S, ‖a x‖ * ‖b x‖ := by
        simp_all
    _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt _ _ _

section
variable {A F : ℝ} {S : Finset α} {S' : Finset β} {k k' : α → β → ℂ} {c c' : ℝ} (hk : KerLe S S' k c) (hc : 0 ≤ c)


include hc in
/-- A square bound gives a bound of the square roots. -/
private theorem sqrt_le_of_sq_le     (h : A ≤ c ^ 2 * F) :
    Real.sqrt A ≤ c * Real.sqrt F := by
  calc Real.sqrt A ≤ Real.sqrt (c ^ 2 * F) := Real.sqrt_le_sqrt h
    _ = c * Real.sqrt F := by rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

/-! ### Bilinear form -/

include hk hc in
/-- A kernel bound gives the bilinear bound `|⟨g, k f⟩| ≤ c ‖g‖ ‖f‖`. -/
theorem KerLe.bilinear          
      (f : β → ℂ) (g : α → ℂ) :
    ‖∑ x ∈ S, star (g x) * ∑ y ∈ S', k x y * f y‖ ≤
      c * Real.sqrt (∑ x ∈ S, ‖g x‖ ^ 2) * Real.sqrt (∑ y ∈ S', ‖f y‖ ^ 2) := by
  have h := norm_sum_star_mul_le S g fun x => ∑ y ∈ S', k x y * f y
  have h' := sqrt_le_of_sq_le hc (hk f)
  calc _ ≤ _ := h
    _ ≤ Real.sqrt (∑ x ∈ S, ‖g x‖ ^ 2) * (c * Real.sqrt (∑ y ∈ S', ‖f y‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left h' (Real.sqrt_nonneg _)
    _ = _ := by ring

include hc in
/-- The bilinear bound `|⟨g, k f⟩| ≤ c ‖g‖ ‖f‖` gives the kernel bound. -/
theorem kerLe_of_bilinear          
    (h : ∀ (f : β → ℂ) (g : α → ℂ), ‖∑ x ∈ S, star (g x) * ∑ y ∈ S', k x y * f y‖ ≤
      c * Real.sqrt (∑ x ∈ S, ‖g x‖ ^ 2) * Real.sqrt (∑ y ∈ S', ‖f y‖ ^ 2)) :
    KerLe S S' k c := by
  intro f
  set g : α → ℂ := fun x => ∑ y ∈ S', k x y * f y with hg
  set A := ∑ x ∈ S, ‖g x‖ ^ 2 with hA
  set F := ∑ y ∈ S', ‖f y‖ ^ 2
  have hA0 : 0 ≤ A := sum_nonneg fun x _ => sq_nonneg _
  have hF0 : 0 ≤ F := sum_nonneg fun y _ => sq_nonneg _
  -- `⟨g, k f⟩ = ‖g‖²`
  have hgg : ‖∑ x ∈ S, star (g x) * g x‖ = A := by
    have : ∑ x ∈ S, star (g x) * g x = ((A : ℝ) : ℂ) := by
      rw [hA, Complex.ofReal_sum]
      refine sum_congr rfl fun x _ => ?_
      rw [Complex.ofReal_pow]
      exact Complex.conj_mul' _
    rw [this, Complex.norm_real, Real.norm_of_nonneg hA0]
  have h1 := h f g
  rw [hgg] at h1
  -- `A ≤ c √A √F` gives `√A ≤ c √F`
  have hsA : Real.sqrt A * Real.sqrt A = A := Real.mul_self_sqrt hA0
  have h2 : Real.sqrt A ≤ c * Real.sqrt F := by
    rcases (Real.sqrt_nonneg A).eq_or_lt with h0 | hpos
    · rw [← h0]
      exact mul_nonneg hc (Real.sqrt_nonneg _)
    nlinarith
  calc A = Real.sqrt A ^ 2 := (Real.sq_sqrt hA0).symm
    _ ≤ (c * Real.sqrt F) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h2 2
    _ = c ^ 2 * F := by rw [mul_pow, Real.sq_sqrt hF0]

/-! ### Basic operations -/

include hk hc in
/-- A kernel bound may be enlarged. -/
theorem KerLe.mono          
      (hcc : c ≤ c') : KerLe S S' k c' := fun f =>
  (hk f).trans ((by gcongr <;> first | assumption | positivity | linarith))

/-- The zero kernel has norm zero. -/
theorem kerLe_zero (S : Finset α) (S' : Finset β) : KerLe S S' (fun _ _ => 0) 0 := fun f => by
  simp

/-- Kernel bounds add. -/
theorem KerLe.add     {k₁ k₂ : α → β → ℂ}  {c₁ c₂} 
    (h₁ : KerLe S S' k₁ c₁) (h₂ : KerLe S S' k₂ c₂) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) :
    KerLe S S' (fun x y => k₁ x y + k₂ x y) (c₁ + c₂) := by
  refine kerLe_of_bilinear (add_nonneg hc₁ hc₂) fun f g => ?_
  have e : ∑ x ∈ S, star (g x) * ∑ y ∈ S', (k₁ x y + k₂ x y) * f y =
      ∑ x ∈ S, star (g x) * ∑ y ∈ S', k₁ x y * f y +
        ∑ x ∈ S, star (g x) * ∑ y ∈ S', k₂ x y * f y := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun x _ => ?_
    rw [← mul_add, ← sum_add_distrib]
    simp only [add_mul]
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have := add_le_add (h₁.bilinear hc₁ f g) (h₂.bilinear hc₂ f g)
  linarith

/-- Kernel bounds add over a finite family (Minkowski). -/
theorem KerLe.sum     (s : Finset ι) {k : ι → α → β → ℂ}
    {c : ι → ℝ} (hk : ∀ i ∈ s, KerLe S S' (k i) (c i)) (hc : ∀ i ∈ s, 0 ≤ c i) :
    KerLe S S' (fun x y => ∑ i ∈ s, k i x y) (∑ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using kerLe_zero S S'
  | insert i s hi ih =>
    simp only [sum_insert hi]
    exact (hk i (mem_insert_self i s)).add (ih (fun j hj => hk j (mem_insert_of_mem hj))
      fun j hj => hc j (mem_insert_of_mem hj)) (hc i (mem_insert_self i s))
      (sum_nonneg fun j hj => hc j (mem_insert_of_mem hj))

include hk in
/-- A scalar multiple of a kernel. -/
theorem KerLe.const_mul        
       a  : KerLe S S' (fun x y => a * k x y) (‖a‖ * c) := fun f => by
  calc ∑ x ∈ S, ‖∑ y ∈ S', a * k x y * f y‖ ^ 2
      = ‖a‖ ^ 2 * ∑ x ∈ S, ‖∑ y ∈ S', k x y * f y‖ ^ 2 := by
        rw [mul_sum]
        refine sum_congr rfl fun x _ => ?_
        have e : ∑ y ∈ S', a * k x y * f y = a * ∑ y ∈ S', k x y * f y := by
          rw [mul_sum]
          exact sum_congr rfl fun y _ => by ring
        rw [e, norm_mul, mul_pow]
    _ ≤ ‖a‖ ^ 2 * (c ^ 2 * ∑ y ∈ S', ‖f y‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (hk f) (sq_nonneg _)
    _ = (‖a‖ * c) ^ 2 * ∑ y ∈ S', ‖f y‖ ^ 2 := by ring

include hk in
/-- Multipliers of modulus at most one at both ends do not increase the norm. -/
theorem KerLe.mul_diag        
      {φ : α → ℂ} {φ' : β → ℂ} (hφ : ∀ x ∈ S, ‖φ x‖ ≤ 1)
    (hφ' : ∀ y ∈ S', ‖φ' y‖ ≤ 1) : KerLe S S' (fun x y => φ x * k x y * φ' y) c := fun f => by
  calc ∑ x ∈ S, ‖∑ y ∈ S', φ x * k x y * φ' y * f y‖ ^ 2
      ≤ ∑ x ∈ S, ‖∑ y ∈ S', k x y * (φ' y * f y)‖ ^ 2 := by
        refine sum_le_sum fun x hx => ?_
        have e : ∑ y ∈ S', φ x * k x y * φ' y * f y = φ x * ∑ y ∈ S', k x y * (φ' y * f y) := by
          rw [mul_sum]
          exact sum_congr rfl fun y _ => by ring
        rw [e, norm_mul, mul_pow]
        exact mul_le_of_le_one_left (sq_nonneg _)
          (pow_le_one₀ (norm_nonneg _) (hφ x hx))
    _ ≤ c ^ 2 * ∑ y ∈ S', ‖φ' y * f y‖ ^ 2 := hk _
    _ ≤ c ^ 2 * ∑ y ∈ S', ‖f y‖ ^ 2 := by
        refine mul_le_mul_of_nonneg_left (sum_le_sum fun y hy => ?_) (sq_nonneg c)
        rw [norm_mul, mul_pow]
        exact mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ (norm_nonneg _) (hφ' y hy))

include hk in
/-- A kernel agreeing with a bounded one on the index sets is bounded. -/
theorem KerLe.congr        
      (h : ∀ x ∈ S, ∀ y ∈ S', k x y = k' x y) : KerLe S S' k' c := fun f => by
  calc ∑ x ∈ S, ‖∑ y ∈ S', k' x y * f y‖ ^ 2 = ∑ x ∈ S, ‖∑ y ∈ S', k x y * f y‖ ^ 2 :=
        sum_congr rfl fun x hx => by rw [sum_congr rfl fun y hy => by rw [← h x hx y hy]]
    _ ≤ _ := hk f

end

/-! ### Embeddings and blocks -/

section
variable {S : Finset α} {S' : Finset β} {T : Finset γ} {T' : Finset δ} {G : γ → δ → ℂ} {μ : α → ℝ} {ν : β → ℝ} {k : α → β → ℂ} {c R C : ℝ} (hR : 0 ≤ R) (hC : 0 ≤ C) (hμ : ∀ x ∈ S, 0 ≤ μ x) (hrow : ∀ x ∈ S, ∑ y ∈ S', ‖k x y‖ ≤ R) (hν : ∀ y ∈ S', 0 < ν y)


/-- **Pulling back along embeddings**: if `e` and `e'` are injective on `S` and `S'` and map
them into `T` and `T'`, the pulled-back kernel `G(e x, e' y)` has the norm bound of `G`. -/
theorem KerLe.comp_embed        
        (hG : KerLe T T' G c) {e : α → γ} {e' : β → δ}
    (he : Set.InjOn e S) (he' : Set.InjOn e' S') (hmap : ∀ x ∈ S, e x ∈ T)
    (hmap' : ∀ y ∈ S', e' y ∈ T') : KerLe S S' (fun x y => G (e x) (e' y)) c := by
  classical
  intro f
  -- push `f` forward along `e'`
  set F : δ → ℂ := fun w => ∑ y ∈ S' with e' y = w, f y with hF
  have hFe : ∀ y ∈ S', F (e' y) = f y := by
    intro y hy
    have hfib : S'.filter (fun y' => e' y' = e' y) = {y} := by
      ext y'
      simp only [mem_filter, mem_singleton]
      constructor
      · rintro ⟨hy', h⟩
        exact he' hy' hy h
      · rintro rfl
        exact ⟨hy, rfl⟩
    simp_all
  have hF0 : ∀ w, w ∉ S'.image e' → F w = 0 := by
    aesop
  have himg : S'.image e' ⊆ T' := fun w hw => by
    grind
  have hsum : ∀ v, ∑ y ∈ S', G v (e' y) * f y = ∑ w ∈ T', G v w * F w := by
    intro v
    rw [← sum_subset himg fun w _ hw => by rw [hF0 w hw, mul_zero], sum_image he']
    exact sum_congr rfl fun y hy => by rw [hFe y hy]
  have hnorm : ∑ w ∈ T', ‖F w‖ ^ 2 = ∑ y ∈ S', ‖f y‖ ^ 2 := by
    rw [← sum_subset himg fun w _ hw => by rw [hF0 w hw, norm_zero, sq, mul_zero], sum_image he']
    exact sum_congr rfl fun y hy => by rw [hFe y hy]
  have himgS : S.image e ⊆ T := fun v hv => by
    grind
  calc ∑ x ∈ S, ‖∑ y ∈ S', G (e x) (e' y) * f y‖ ^ 2
      = ∑ v ∈ S.image e, ‖∑ w ∈ T', G v w * F w‖ ^ 2 := by
        rw [sum_image he]
        exact sum_congr rfl fun x _ => by rw [hsum]
    _ ≤ ∑ v ∈ T, ‖∑ w ∈ T', G v w * F w‖ ^ 2 :=
        sum_le_sum_of_subset_of_nonneg himgS fun v _ _ => sq_nonneg _
    _ ≤ c ^ 2 * ∑ w ∈ T', ‖F w‖ ^ 2 := hG F
    _ = c ^ 2 * ∑ y ∈ S', ‖f y‖ ^ 2 := by rw [hnorm]

/-- **Block decomposition**: if `k(x, y) ≠ 0` only when the labels `κ x` and `κ' y` agree, and
every block has norm at most `c`, then `k` has norm at most `c`. -/
theorem KerLe.block [DecidableEq ι] {S : Finset α} {S' : Finset β} {k : α → β → ℂ}  {c} 
    (κ : α → ι) (κ' : β → ι) (hk : ∀ x ∈ S, ∀ y ∈ S', k x y ≠ 0 → κ x = κ' y)
    (hblock : ∀ i, KerLe (S.filter (κ · = i)) (S'.filter (κ' · = i)) k c) : KerLe S S' k c := by
  intro f
  set I := S.image κ ∪ S'.image κ' with hI
  -- at an input `x`, only the inputs `y` of its block contribute
  have hrow : ∀ x ∈ S, ∑ y ∈ S', k x y * f y = ∑ y ∈ S'.filter (κ' · = κ x), k x y * f y := by
    intro x hx
    rw [sum_filter]
    refine sum_congr rfl fun y hy => ?_
    grind
  calc ∑ x ∈ S, ‖∑ y ∈ S', k x y * f y‖ ^ 2
      = ∑ i ∈ I, ∑ x ∈ S.filter (κ · = i), ‖∑ y ∈ S'.filter (κ' · = i), k x y * f y‖ ^ 2 := by
        rw [← sum_fiberwise_of_maps_to (g := κ) (t := I) fun x hx =>
          mem_union_left _ (mem_image_of_mem κ hx)]
        refine sum_congr rfl fun i _ => sum_congr rfl fun x hx => ?_
        rw [hrow x (mem_filter.1 hx).1, (mem_filter.1 hx).2]
    _ ≤ ∑ i ∈ I, c ^ 2 * ∑ y ∈ S'.filter (κ' · = i), ‖f y‖ ^ 2 :=
        sum_le_sum fun i _ => hblock i f
    _ = c ^ 2 * ∑ y ∈ S', ‖f y‖ ^ 2 := by
        rw [← mul_sum]
        congr 1
        exact sum_fiberwise_of_maps_to (g := κ') (t := I) (fun y hy =>
          mem_union_right _ (mem_image_of_mem κ' hy)) fun y => ‖f y‖ ^ 2

/-! ### The Schur test -/

include hR hC hμ hrow in
/-- **The weighted Schur test** with weight one: if the absolute row sums of `k` are at most
`R` and the absolute column sums against `μ` are at most `C ν`, then `k` has norm at most
`√(R C)` from `ℓ²(ν)` to `ℓ²(μ)`. -/
theorem wkerLe_of_schur          
           
     
    (hcol : ∀ y ∈ S', ∑ x ∈ S, μ x * ‖k x y‖ ≤ C * ν y) :
    WKerLe S S' μ ν k (Real.sqrt (R * C)) := by
  intro f
  rw [Real.sq_sqrt (mul_nonneg hR hC)]
  -- Cauchy–Schwarz in each row
  have hpt : ∀ x ∈ S, ‖∑ y ∈ S', k x y * f y‖ ^ 2 ≤ R * ∑ y ∈ S', ‖k x y‖ * ‖f y‖ ^ 2 := by
    intro x hx
    have h1 : ‖∑ y ∈ S', k x y * f y‖ ≤ ∑ y ∈ S', ‖k x y‖ * ‖f y‖ :=
      (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun y _ => norm_mul _ _))
    have h2 : (∑ y ∈ S', ‖k x y‖ * ‖f y‖) ^ 2 ≤
        (∑ y ∈ S', ‖k x y‖) * ∑ y ∈ S', ‖k x y‖ * ‖f y‖ ^ 2 :=
      sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun y _ => norm_nonneg _)
        (fun y _ => mul_nonneg (norm_nonneg _) (sq_nonneg _)) fun y _ => le_of_eq (by ring)
    calc ‖∑ y ∈ S', k x y * f y‖ ^ 2 ≤ (∑ y ∈ S', ‖k x y‖ * ‖f y‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ _ := h2
      _ ≤ R * ∑ y ∈ S', ‖k x y‖ * ‖f y‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (hrow x hx)
            (sum_nonneg fun y _ => mul_nonneg (norm_nonneg _) (sq_nonneg _))
  calc ∑ x ∈ S, μ x * ‖∑ y ∈ S', k x y * f y‖ ^ 2
      ≤ ∑ x ∈ S, μ x * (R * ∑ y ∈ S', ‖k x y‖ * ‖f y‖ ^ 2) :=
        sum_le_sum fun x hx => mul_le_mul_of_nonneg_left (hpt x hx) (hμ x hx)
    _ = R * ∑ y ∈ S', ‖f y‖ ^ 2 * ∑ x ∈ S, μ x * ‖k x y‖ := by
        rw [mul_sum]
        simp_rw [mul_sum]
        rw [sum_comm]
        grind
    _ ≤ R * ∑ y ∈ S', ‖f y‖ ^ 2 * (C * ν y) :=
        (by bound)
    _ = R * C * ∑ y ∈ S', ν y * ‖f y‖ ^ 2 := by
        rw [mul_assoc, mul_sum, mul_sum, mul_sum]
        exact sum_congr rfl fun y _ => by ring

include hR hC hrow in
/-- **The Schur test**: absolute row sums at most `R` and column sums at most `C` give norm at
most `√(R C)`. -/
theorem kerLe_of_schur          
       
    (hcol : ∀ y ∈ S', ∑ x ∈ S, ‖k x y‖ ≤ C) : KerLe S S' k (Real.sqrt (R * C)) := by
  intro f
  have h := wkerLe_of_schur (μ := fun _ : α => (1 : ℝ)) (ν := fun _ : β => (1 : ℝ)) hR hC
    (fun _ _ => zero_le_one)
    hrow (fun y hy => by simpa using hcol y hy) f
  simpa using h

/-- The trivial bound: entries of modulus at most `M` give norm at most `M √(|S| |S'|)`. -/
theorem kerLe_of_norm_le        {M}  (hM : 0 ≤ M)
    (h : ∀ x ∈ S, ∀ y ∈ S', ‖k x y‖ ≤ M) :
    KerLe S S' k (M * Real.sqrt (S.card * S'.card)) := by
  have hk := kerLe_of_schur (k := k) (R := S'.card * M) (C := S.card * M) (by positivity)
    (by positivity) (fun x hx => (sum_le_sum fun y hy => h x hx y hy).trans (by simp))
    (fun y hy => (sum_le_sum fun x hx => h x hx y hy).trans (by simp))
  refine hk.mono (Real.sqrt_nonneg _) (le_of_eq ?_)
  rw [show (S'.card : ℝ) * M * (S.card * M) = M ^ 2 * (S.card * S'.card) by ring,
    Real.sqrt_mul (sq_nonneg M), Real.sqrt_sq hM]

/-! ### Weights -/

include hμ hν in
/-- **Conjugation to counting measure**: with `μ ≥ 0` and `ν > 0`, a bound for the kernel
`√μ(x) k(x, y) / √ν(y)` in `ℓ²` gives the weighted bound for `k`. -/
theorem wkerLe_of_kerLe          
         
    (hk : KerLe S S' (fun x y => (Real.sqrt (μ x) : ℂ) * k x y / (Real.sqrt (ν y) : ℂ)) c) :
    WKerLe S S' μ ν k c := by
  intro f
  set g : β → ℂ := fun y => (Real.sqrt (ν y) : ℂ) * f y with hg
  have h := hk g
  have e1 : ∀ x ∈ S, μ x * ‖∑ y ∈ S', k x y * f y‖ ^ 2 =
      ‖∑ y ∈ S', (Real.sqrt (μ x) : ℂ) * k x y / (Real.sqrt (ν y) : ℂ) * g y‖ ^ 2 := by
    intro x hx
    have e : ∑ y ∈ S', (Real.sqrt (μ x) : ℂ) * k x y / (Real.sqrt (ν y) : ℂ) * g y =
        (Real.sqrt (μ x) : ℂ) * ∑ y ∈ S', k x y * f y := by
      rw [mul_sum]
      refine sum_congr rfl fun y hy => ?_
      have : (Real.sqrt (ν y) : ℂ) ≠ 0 := by
        exact_mod_cast (Real.sqrt_pos.2 (hν y hy)).ne'
      rw [hg]
      field_simp
    rw [e, norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (hμ x hx)]
  have e2 : ∀ y ∈ S', ‖g y‖ ^ 2 = ν y * ‖f y‖ ^ 2 := by
    intro y hy
    rw [hg]
    dsimp only
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (hν y hy).le]
  rw [sum_congr rfl e1, ← sum_congr rfl e2]
  exact h

include hμ hν in
/-- **Conjugation from counting measure**: with `μ, ν > 0`, a weighted bound for `k` gives the
bound for the kernel `√μ(x) k(x, y) / √ν(y)` in `ℓ²`. -/
theorem kerLe_of_wkerLe          
          (hk : WKerLe S S' μ ν k c) :
    KerLe S S' (fun x y => (Real.sqrt (μ x) : ℂ) * k x y / (Real.sqrt (ν y) : ℂ)) c := by
  intro g
  set f : β → ℂ := fun y => g y / (Real.sqrt (ν y) : ℂ) with hf
  have h := hk f
  have e1 : ∀ x ∈ S, ‖∑ y ∈ S', (Real.sqrt (μ x) : ℂ) * k x y / (Real.sqrt (ν y) : ℂ) * g y‖ ^ 2 =
      μ x * ‖∑ y ∈ S', k x y * f y‖ ^ 2 := by
    intro x hx
    have e : ∑ y ∈ S', (Real.sqrt (μ x) : ℂ) * k x y / (Real.sqrt (ν y) : ℂ) * g y =
        (Real.sqrt (μ x) : ℂ) * ∑ y ∈ S', k x y * f y := by
      rw [mul_sum]
      grind
    rw [e, norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (hμ x hx)]
  have e2 : ∀ y ∈ S', ν y * ‖f y‖ ^ 2 = ‖g y‖ ^ 2 := by
    intro y hy
    have hs : (0 : ℝ) < Real.sqrt (ν y) := Real.sqrt_pos.2 (hν y hy)
    rw [hf]
    dsimp only
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hs.le, div_pow,
      Real.sq_sqrt (hν y hy).le, mul_div_assoc', mul_div_cancel_left₀ _ (hν y hy).ne']
  rw [sum_congr rfl e1, ← sum_congr rfl e2]
  exact h

/-- A kernel vanishing on the index sets has weighted norm at most any `c ≥ 0`. -/
theorem wkerLe_of_eq_zero        
        (hν : ∀ y ∈ S', 0 ≤ ν y) (hk : ∀ x ∈ S, ∀ y ∈ S', k x y = 0) :
    WKerLe S S' μ ν k c := by
  intro f
  calc ∑ x ∈ S, μ x * ‖∑ y ∈ S', k x y * f y‖ ^ 2 = 0 := by
        simp_all
    _ ≤ c ^ 2 * ∑ y ∈ S', ν y * ‖f y‖ ^ 2 :=
        mul_nonneg (sq_nonneg c) (sum_nonneg fun y hy => mul_nonneg (hν y hy) (sq_nonneg _))

end

end Erdos408.OneSided
