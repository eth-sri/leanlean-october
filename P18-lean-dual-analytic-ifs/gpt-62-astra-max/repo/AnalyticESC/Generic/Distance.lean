module
public import AnalyticESC.Basic

@[expose] public section
namespace AnalyticESC.IFS
open Set Metric Topology
variable {N : ℕ} (Φ : IFS N) (Ψ : IFS N)

/-- On the unit interval the jets live in the same sup-norm space, even for
systems with different holomorphic domains. -/
noncomputable abbrev jetOf {f : ℂ → ℂ} (h : AnalyticOnNhd ℂ f Φ.tube) (k : ℕ) : C(I,ℂ) :=
  ⟨_,(h.iterated_deriv k).continuousOn.comp_continuous (f := fun x : I => (x:ℂ)) (by fun_prop) fun x => Φ.real_mem x.2⟩

noncomputable abbrev jet (i : Fin N) := Φ.jetOf ((Φ.analytic_f i).mono subset_closure)

/-- The `C²` distance is precisely the sup over letters of the `ℓ¹` distance
of their three jets. Different holomorphic extensions may have distance zero. -/
noncomputable def code (Φ : IFS N) (i : Fin N) : PiLp 1 (fun _ : Fin 3 => C(I,ℂ)) := WithLp.toLp 1 fun k => Φ.jet i k

noncomputable instance : PseudoMetricSpace (IFS N) := PseudoMetricSpace.induced code inferInstance

lemma dist_eq_d2 : dist Φ Ψ = d2 Φ.f Ψ.f := by
  change dist (code Φ) (code Ψ) = _
  rw [dist_pi_def]; simp only [Finset.sup_univ_eq_ciSup,NNReal.coe_iSup,coe_nndist]; simp only [PiLp.dist_eq_of_L1,
    Fin.sum_univ_three]; simp only [dist_eq_norm,ContinuousMap.norm_eq_iSup_norm]; rfl

lemma d2_upper {u : ℝ} (hu : 0 ≤ u) (h : ∀ i (k : Fin 3) (x : I), ‖deriv^[k.val] (Φ.f i) x - deriv^[k.val] (Ψ.f i) x‖ ≤ u) : dist Φ Ψ ≤ u+u+u := by
  rw [Φ.dist_eq_d2]; apply Real.iSup_le _ (by positivity); intro i
  exact add_le_add (add_le_add (ciSup_le (h i 0)) (ciSup_le (h i 1))) (ciSup_le (h i 2))

end AnalyticESC.IFS
