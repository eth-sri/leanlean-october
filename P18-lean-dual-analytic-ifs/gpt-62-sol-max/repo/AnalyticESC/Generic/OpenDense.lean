module

public import AnalyticESC.Generic.Density
public import AnalyticESC.Generic.Inward
public import AnalyticESC.Generic.Continuity
public import AnalyticESC.Main.Dichotomy

@[expose] public section

/-! Dual separation is open by common series bounds, and dense by localized perturbation. -/

namespace AnalyticESC

open Set Metric Filter Topology
open scoped ENNReal

namespace System

variable {N : ℕ}

open IFS.Continuity

def separated (N : ℕ) : Set (System N) := {F | F.ifs.DualSSC}

theorem isOpen_separated (N : ℕ) : IsOpen (separated N) := by
  let X := System N × ((ℕ → Fin N) × (ℕ → Fin N))
  have hA : IsOpen {p : X | p.2.1 0 = p.2.2 0} :=
    (isOpen_discrete {a : Fin N × Fin N | a.1 = a.2}).preimage (f := fun p : X => (p.2.1 0, p.2.2 0)) (by fun_prop)
  have hB (x : I) : IsOpen {p : X | p.1.ifs.dualProj (.inf p.2.1) x ≠ p.1.ifs.dualProj (.inf p.2.2) x} :=
    (isClosed_eq ((continuous_dualProj x).comp (continuous_fst.prodMk continuous_snd.fst))
      ((continuous_dualProj x).comp (continuous_fst.prodMk continuous_snd.snd))).isOpen_compl
  convert isOpen_forall_compact (hA.union (isOpen_iUnion hB)) using 1
  ext F
  simp [separated, IFS.DualSSC, Prod.forall, Classical.or_iff_not_imp_left]
  rfl

theorem dense_separated (N : ℕ) : Dense (separated N) := Metric.dense_iff.2 fun F r hr => by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact ⟨F, mem_ball_self hr, fun i => (i 0).elim0⟩
  let Φ := F.ifs
  let _ : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  obtain ⟨t, ht, hd⟩ := Φ.exists_small_inward (1/2) (half_pos hr)
  let Φ₁ : IFS N F.property.choose := ⟨fun i => inward (Φ.f i) (1/2) t, Φ.ε_pos,
    fun i => (Φ.inClass i).inward Φ.ε_pos (by norm_num) ht⟩
  have hΦ₁ : d2 Φ Φ₁ < r / 2 := by simpa [d2, d2Sys_eq, Finite.ciSup_lt_iff, Φ₁] using hd
  obtain ⟨ε', Ψ, hΨ, hssc⟩ := Φ₁.exists_dualSSC_near hN (half_pos ht.1)
    (fun i x hx => by simpa only [Φ₁, show (1 : ℝ) - 1/2 = 1/2 by norm_num, mul_one_div] using
      (re_inward_mem (p := 1/2) ht.2.le ((Φ.inClass i).re_mem_I x hx))) (half_pos hr)
  refine ⟨⟨Ψ.f, ε', Ψ.ε_pos, Ψ.inClass⟩, ?_, hssc⟩
  rw [mem_ball, dist_eq_d2]
  have h := dist_triangle (jets Φ) (jets Φ₁) (jets Ψ)
  simp only [← d2_eq_dist] at h
  change d2 Φ Ψ < r
  linarith

end System

/- A property holds on an open dense subset of the union of analytic classes. -/
set_option quotPrecheck false in
scoped notation "Generic[" N ", " P "]" =>
  ∃ U : Set (Fin N → ℂ → ℂ), (∀ f ∈ U, Challenge.InUnionClass f ∧ P f) ∧
    (∀ f ∈ U, ∃ r > 0, ∀ g, Challenge.InUnionClass g → Challenge.d2 f g < r → g ∈ U) ∧
    (∀ f, Challenge.InUnionClass f → ∀ r > 0, ∃ g ∈ U, Challenge.d2 f g < r)

theorem generic_of_open_dense {N : ℕ} {P : (Fin N → ℂ → ℂ) → Prop} {U : Set (System N)}
    (ho : IsOpen U) (hd : Dense U) (hP : ∀ F ∈ U, P F.val) : Generic[N, P] := by
  refine ⟨System.val '' U, ?_, ?_, ?_⟩
  · rintro _ ⟨F, hF, rfl⟩
    exact ⟨F.property, hP _ hF⟩
  · rintro _ ⟨F, hF, rfl⟩
    obtain ⟨r, hr, h⟩ := Metric.isOpen_iff.1 ho F hF
    refine ⟨r, hr, fun g hg hfg => ⟨⟨g, hg⟩, h ?_, rfl⟩⟩
    rwa [mem_ball, System.dist_eq_d2]
  · intro f hf r hr
    obtain ⟨G, hG, h⟩ := Metric.dense_iff.1 hd ⟨f, hf⟩ r hr
    exact ⟨G.val, ⟨G, h, rfl⟩, by grind [mem_ball, System.dist_eq_d2]⟩

/-- Theorem 1.4: strong exponential separation is generic in the `C²` metric. -/
theorem _root_.Challenge.audit_sesc_open_dense (N : ℕ) : Generic[N, Challenge.SESC] :=
  generic_of_open_dense (System.isOpen_separated N) (System.dense_separated N)
    fun F hF => F.ifs.theorem_2_2 hF

end AnalyticESC
