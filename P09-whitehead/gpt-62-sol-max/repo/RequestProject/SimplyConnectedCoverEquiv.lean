module

public import RequestProject.UniversalToCover
public import RequestProject.ZeroPi2Descent

@[expose] public section

/-! A connected simply connected cellular covering is the actual path-class universal cover. -/

namespace FiniteChains.Comb
universe u
variable {D K : Complex2.{u}} {p : Hom D K} {d₀ : D.V}

theorem coverV_surjective (hcov : IsCovering p) (hconn : IsConnected D) :
    Function.Surjective (coverV hcov (d₀ := d₀) rfl) := by
  intro v
  obtain ⟨m, hm⟩ := hconn d₀ v
  refine ⟨UV.mk (pathFromMap p d₀ hm), ?_⟩
  exact coverV_eq hcov rfl ⟨m, hm, rfl⟩

/-- Simple connectivity removes precisely the ambiguity between lifts of path classes. -/
theorem coverV_injective (hcov : IsCovering p) (hsc : SimplyConnected D) :
    Function.Injective (coverV hcov (d₀ := d₀) rfl) := by
  intro c d
  induction c using UV.ind with
  | h q =>
    induction d using UV.ind with
    | h r =>
      intro he
      obtain ⟨m, hm, hmq⟩ := coverV_spec hcov rfl q
      obtain ⟨n, hn, hnr⟩ := coverV_spec hcov rfl r
      rw [← he] at hn
      have htriv : Pi1Trivial p := fun a l hl => mapPath_htpy p (hsc a l hl)
      have hh := htpy_mapPath_of_pi1Trivial htriv hm hn
      rw [hmq, hnr] at hh
      apply UV.sound
      have hend := onV_coverV hcov rfl (UV.mk q)
      rw [hend] at hh
      exact hh

theorem coverF_injective (hcov : IsCovering p) (hsc : SimplyConnected D) :
    Function.Injective (coverF hcov (d₀ := d₀) rfl) := by
  intro c d he
  apply Subtype.ext
  apply Prod.ext
  · apply coverV_injective hcov hsc
    rw [← base_coverF, ← base_coverF, he]
  · rw [← onF_coverF hcov rfl c, ← onF_coverF hcov rfl d, he]

/-- Identify a lifted face by its projected cell and its lifted base vertex. -/
theorem coverF_eq_of_base_and_image (hcov : IsCovering p) (c : UF K (p.onV d₀))
    (g : D.F) (himage : p.onF g = c.1.2)
    (hbase : D.base g = coverV hcov (d₀ := d₀) rfl c.1.1) :
    coverF hcov (d₀ := d₀) rfl c = g := by
  obtain ⟨w, -, hw⟩ := exists_unique_liftCell hcov c.1.2
    (v := coverV hcov (d₀ := d₀) rfl c.1.1) (coverF_cond hcov rfl c)
  exact (hw _ ⟨onF_coverF hcov rfl c, base_coverF hcov rfl c⟩).trans
    (hw g ⟨himage, hbase⟩).symm

end FiniteChains.Comb
