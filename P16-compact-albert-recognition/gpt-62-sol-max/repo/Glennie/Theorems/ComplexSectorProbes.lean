module

public import Glennie.Theorems.ComplexSectorSpan
public import Glennie.Compact.NativeNormKernelR01
@[expose] public section

namespace Glennie.PeirceSlots
noncomputable section
open scoped BigOperators

abbrev diag (d : Fin 3 → ℝ) := diagonalAlbert (d 0) (d 1) (d 2)
def e (i : Fin 3) := diag (Pi.single i 1)
def diagonals (x : Albert) : Fin 3 → ℝ := ![x.d0,x.d1,x.d2]
def entries (x : Albert) : Fin 3 → Octonion := ![x.o01,x.o02,x.o12]
def slot (i : Fin 3) : Octonion →ₗ[ℝ] Albert where
  toFun u := ⟨0,0,0,if i = 0 then u else 0,if i = 1 then u else 0,if i = 2 then u else 0⟩
  map_add' u v := by fin_cases i <;> apply Albert.ext <;> norm_num
  map_smul' t u := by fin_cases i <;> apply Albert.ext <;> norm_num

theorem assemble_mem {K : Submodule ℝ Albert} (he : ∀ i, e i ∈ K) (x : Albert)
    (hs : ∀ i, slot i (entries x i) ∈ K) : x ∈ K := by
  suffices x = (∑ i, diagonals x i • e i) + ∑ i, slot i (entries x i) by
    rw [this]
    exact K.add_mem (K.sum_mem fun i _ => K.smul_mem _ (he i)) (K.sum_mem fun i _ => hs i)
  apply Albert.ext <;>
    norm_num [Fin.sum_univ_three, e, diagonals, diagonalAlbert, Pi.single_apply, slot, entries]

/-- The pair of incident rows minus the opposite row isolates the slot
once the diagonal is subtracted. -/
private theorem isolate (x : Albert) (i : Fin 3) :
    slot i (entries x i) = (∑ j, jordan (e j) x) - (∑ j, diagonals x j • e j) -
      (2 : ℝ) • jordan (e (2-i)) x + (2 * diagonals x (2-i)) • e (2-i) := by
  simp only [e, diag, diagonal_jordan, Fin.sum_univ_three]
  fin_cases i <;> apply Albert.ext <;>
    norm_num [diagonals, diagonalAlbert, Pi.single_apply, slot, entries, smul_smul] <;> module

theorem slot_mem_of_probes {K : Submodule ℝ Albert} (he : ∀ i, e i ∈ K)
    {x : Albert} (hx : ∀ i, jordan (e i) x ∈ K) (i : Fin 3) : slot i (entries x i) ∈ K := by
  rw [isolate]
  exact K.add_mem (K.sub_mem (K.sub_mem (K.sum_mem fun j _ => hx j)
    (K.sum_mem fun j _ => K.smul_mem _ (he j))) (K.smul_mem _ (hx _))) (K.smul_mem _ (he _))

def triangle (x : Albert) := (complexPart x.o01 * complexPart x.o12 * star (complexPart x.o02)).im

private theorem square_slot_det (x : Albert) (hx : InComplexSector x) (i : Fin 3) :
    (star (complexPart (entries x i)) * complexPart (entries (jordan x x) i)).im =
      (![(-1 : ℝ), 1, -1] i) * triangle x := by
  rw [← complexAlbert_eq x hx]
  fin_cases i <;> simp [entries, triangle, jordan_o01, jordan_o02, jordan_o12, complexAlbert,
    complexOct, complexPart, octMul, octConj, Complex.mul_re, Complex.mul_im, smul_eq_mul] <;> ring

private theorem complexOct_part (x : Albert) (hx : InComplexSector x) (i : Fin 3) :
    complexOct (complexPart (entries x i)) = entries x i := by
  rw [← complexAlbert_eq x hx]
  fin_cases i <;> rfl

private def complexOctLinear : ℂ →ₗ[ℝ] Octonion where
  toFun := complexOct
  map_add' a b := by ext <;> simp [complexOct]
  map_smul' _ _ := by ext <;> simp [complexOct]

private theorem complex_line {K : Submodule ℝ Albert} (L : ℂ →ₗ[ℝ] Albert) (u v : ℂ)
    (hu : L u ∈ K) (hv : L v ∈ K) (hd : (star u * v).im ≠ 0) (z : ℂ) : L z ∈ K := by
  have hh : (star u * v).im • z = (star z * v).im • u + (star u * z).im • v := by
    apply Complex.ext <;> simp [Complex.mul_im, Complex.mul_re] <;> ring
  have h := congrArg L hh
  simp only [map_add, map_smul] at h
  exact (K.smul_mem_iff hd).1 (h ▸ K.add_mem (K.smul_mem _ hu) (K.smul_mem _ hv))

/-- The diagonal probes and the probes from the first two powers of a complex
sector element span that entire sector when its triangle is nonreal. -/
theorem sector_le_of_probes (K : Submodule ℝ Albert) (y : Albert)
    (hc : InComplexSector y) (ht : triangle y ≠ 0) (he : ∀ i, e i ∈ K)
    (hy : ∀ i, jordan (e i) y ∈ K) (hs : ∀ i, jordan (e i) (jordan y y) ∈ K) :
    complexSector ≤ K := by
  intro x hx
  apply assemble_mem he x
  intro i
  let L := (slot i).comp complexOctLinear
  have h (z : Albert) (hz : InComplexSector z) (hp : ∀ j, jordan (e j) z ∈ K) :
      L (complexPart (entries z i)) ∈ K := by
    change slot i (complexOct (complexPart (entries z i))) ∈ K
    rw [complexOct_part z hz]
    exact slot_mem_of_probes he hp i
  rw [← complexOct_part x ((complexSector_mem_iff x).mp hx) i]
  exact complex_line L _ _ (h y hc hy) (h _ (complexSector_jordan _ _ hc hc) hs)
    (by rw [square_slot_det y hc]; fin_cases i <;> simpa using ht) _

end
end Glennie.PeirceSlots
