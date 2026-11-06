module

public import AnalyticESC.Conjugation.Koenigs
public import AnalyticESC.Conjugation.Basic
public import AnalyticESC.Generic.Class

@[expose] public section

/-!
# Compositions and periodic words

Compositions `f_w` along nonempty words lie in the class for a smaller `ε`; their functions
`Ĥ_{f_w}` of (5.1) are dual natural projections of periodic words.
-/

namespace AnalyticESC

open Set Metric Filter Topology

namespace Word

variable {N : ℕ}

/-- A periodic word is its period followed by itself. -/
private theorem composite_inf_periodic_eq_prepend {m : ℕ} (hm : 0 < m) (v : Fin m → Fin N) :
    inf (periodic hm v) = (inf (periodic hm v)).prepend (List.ofFn v) :=
  (inf_eq_prepend (periodic hm v) m).trans (congrArg₂ prepend
    (congrArg List.ofFn (funext fun k => congrArg v (Fin.ext (Nat.mod_eq_of_lt k.2))))
    (congrArg inf (funext fun k => congrArg v (Fin.ext (Nat.add_mod_left m k)))))

end Word

/-- `List.ofFn (w ∘ Fin.rev) = (List.ofFn w)^←`. -/
private theorem composite_ofFn_comp_rev {α : Type*} {m : ℕ} (w : Fin m → α) :
    List.ofFn (w ∘ Fin.rev) = (List.ofFn w).reverse := by
  refine List.ext_getElem (by simp) fun n h1 h2 => ?_
  simp only [List.getElem_ofFn, Function.comp_apply, List.getElem_reverse, List.length_ofFn]
  exact congrArg w (Fin.ext (by simp only [Fin.val_rev]; omega))

/-- A bounded solution of `h(z) = R(z) + g'(z) h(g(z))` is unique when `g` maps `S` into itself
with `|g'| ≤ c < 1` on `S`. -/
private theorem composite_eqOn_of_functional_eq {S : Set ℂ} {g R A B : ℂ → ℂ} {c K : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c < 1) (hg : MapsTo g S S) (hgd : ∀ z ∈ S, ‖deriv g z‖ ≤ c)
    (hA : ∀ z ∈ S, A z = R z + deriv g z * A (g z))
    (hB : ∀ z ∈ S, B z = R z + deriv g z * B (g z)) (hK : ∀ z ∈ S, ‖A z - B z‖ ≤ K) :
    ∀ z ∈ S, A z = B z := by
  have key (n : ℕ) : ∀ z ∈ S, ‖A z - B z‖ ≤ c ^ n * K := by
    induction n with
    | zero => simpa using hK
    | succ n ih =>
      intro z hz
      rw [hA z hz, hB z hz, add_sub_add_left_eq_sub, ← mul_sub, norm_mul, pow_succ', mul_assoc]
      exact mul_le_mul (hgd z hz) (ih _ (hg hz)) (norm_nonneg _) hc0
  exact fun z hz => sub_eq_zero.1 (norm_le_zero_iff.1 (ge_of_tendsto'
    (by simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).mul_const K)
    fun n => key n z hz))

namespace IFS

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

/-- Compositions along nonempty words lie in the class for `ε / 4`. -/
theorem inClass_comp {w : List (Fin N)} (hw : w ≠ []) :
    InClass (ε / 4) (Φ.comp w) := by
  have hε := Φ.ε_pos
  have hsub : nbhd (2 * (ε / 4)) ⊆ nbhd ε := nbhd_mono (by linarith)
  have hcl : closure (nbhd (ε / 4)) ⊆ closure (nbhd ε) := closure_mono (nbhd_mono (by linarith))
  exact InClass.of_deriv (by positivity) ((Φ.differentiableOn_comp w).mono hsub)
    (fun _ hx => Φ.im_comp_ofReal w (hsub hx)) (fun _ hx => Φ.re_comp_mem_I w hx)
    (fun _ hz => Φ.deriv_comp_ne_zero w (hcl hz))
    (fun _ hz => (Φ.norm_deriv_comp_le w (hcl hz)).trans_lt
      (pow_lt_one₀ Φ.cmax_nonneg Φ.cmax_lt_one (List.length_pos_iff.2 hw).ne'))

/-- `Ĥ_{f_w} = H_{(w^←)^∞}` on `[0,1]`, where `w^←` is the reversed word. -/
theorem hatH_comp_eq_dualProj {m : ℕ} (hm : 0 < m) (w : Fin m → Fin N) :
    ∀ x ∈ I, hatH (Φ.comp (List.ofFn w)) x = Φ.dualProj (.inf (periodic hm (w ∘ Fin.rev))) x := by
  intro x hx
  have hε4 : 0 < ε / 4 := by linarith [Φ.ε_pos]
  have hf : InClass (ε / 4) (Φ.comp (List.ofFn w)) :=
    Φ.inClass_comp fun h => hm.ne' (List.ofFn_eq_nil_iff.1 h)
  have hsub : nbhd (ε / 4) ⊆ nbhd ε := nbhd_mono (by linarith [Φ.ε_pos])
  obtain ⟨M₁, -, hM₁⟩ := (koenigsIFS hε4 hf).exists_norm_dualProj_le
  obtain ⟨M₂, -, hM₂⟩ := Φ.exists_norm_dualProj_le
  refine composite_eqOn_of_functional_eq (pow_nonneg Φ.cmax_nonneg m)
    (pow_lt_one₀ Φ.cmax_nonneg Φ.cmax_lt_one hm.ne')
    (fun _ hz => hf.mapsTo (subset_closure hz))
    (fun _ hz => by simpa using Φ.norm_deriv_comp_le (List.ofFn w) (subset_closure (hsub hz)))
    (fun _ hz => hatH_eq_add hε4 hf hz) (fun z hz => ?_)
    (fun z hz => by
      rw [hatH_eq_dualProj hε4 hf]
      exact (norm_sub_le _ _).trans
        (add_le_add (hM₁ _ z (subset_closure hz)) (hM₂ _ z (subset_closure (hsub hz)))))
    _ (ofReal_mem_nbhd hε4 hx)
  have h1 := Φ.dualProj_prepend (List.ofFn (w ∘ Fin.rev))
    (.inf (periodic hm (w ∘ Fin.rev))) (subset_closure (hsub hz))
  rwa [← Word.composite_inf_periodic_eq_prepend hm (w ∘ Fin.rev), composite_ofFn_comp_rev,
    List.reverse_reverse, Φ.dualProj_fin_reverse _ (hsub hz)] at h1

end IFS

end AnalyticESC
