/- Actual native images of the explicit finite reference transporter family.
no orbit/transitivity premise. -/
module

public import AlbertRecognition.ReferenceTransport.FamilyDefinitions

@[expose] public section
namespace AlbertRecognition.ReferenceTransport
section
open Glennie AlbertRecognition.FixedFrame

theorem transport12_image (a : Octonion) (ha : octNormSq a = 1) :
    (transport12 a ha).equiv (e 0) = Transporter.p12Plus a := by
  simp only [transport12, CompactAutomorphism.comp_apply]
  rw [Transporter.swap_image, Transporter.rotation_image, Transporter.middle_image]

theorem slotTransporter_image (slot : Fin 3) (a : Octonion)
    (ha : octNormSq a = 1) :
    (slotTransporter slot a ha).equiv (e 0) = slotIdempotent slot a := by
  fin_cases slot
  · change realSwap01Automorphism.equiv
      (realSwap02Automorphism.equiv ((transport12 a ha).equiv (e 0))) = _
    rw [transport12_image, Transporter.p12Plus_coordinates]
    change realConjugateAlbert realSwap01
      (realConjugateAlbert realSwap02 _) = _
    rw [realSwap02_coordinates, realSwap01_coordinates]
    apply Albert.ext <;> simp [slotIdempotent, octConj]
    all_goals apply Prod.ext <;> rfl
  · change realSwap01Automorphism.equiv ((transport12 a ha).equiv (e 0)) = _
    rw [transport12_image, Transporter.p12Plus_coordinates]
    change realConjugateAlbert realSwap01 _ = _
    rw [realSwap01_coordinates]
    apply Albert.ext <;> simp [slotIdempotent, octConj]
  · change (transport12 a ha).equiv (e 0) =
      ⟨0,1/2,1/2,0,0,(1/2 : ℝ) • a⟩
    exact (transport12_image a ha).trans (Transporter.p12Plus_coordinates a)

theorem transporter_image (i : FamilyIndex) :
    (transporter i).equiv (e 0) = familyIdempotent i := by
  cases i with
  | inl i =>
    fin_cases i
    · rfl
    · exact Transporter.swap_image
    · change realConjugateAlbert realSwap02 (e 0) = e 2
      rw [realSwap02_coordinates]
      apply Albert.ext <;> simp [e, octConj]
  | inr i =>
    rcases i with ⟨slot,t,plus⟩
    exact slotTransporter_image slot (signedBasis t plus) (signedBasis_norm t plus)

theorem direction_coe (i : FamilyIndex) :
    (direction i : Albert) = (1 : Albert) - (3 : ℝ) • familyIdempotent i := by
  change (transporter i).equiv (h 0 : Albert) = _
  rw [h_coe, map_sub, map_smul, (transporter i).map_unit, transporter_image]

theorem direction_diagonal (i : Fin 3) : direction (Sum.inl i) = h i := by
  apply Subtype.ext
  rw [direction_coe, h_coe]
  rfl

theorem direction_difference (slot : Fin 3) (t : Fin 8) :
    direction (Sum.inr (slot,t,true)) - direction (Sum.inr (slot,t,false)) =
      (-3 : ℝ) • slotVector slot (octBasis t) := by
  apply Subtype.ext
  change (direction (Sum.inr (slot,t,true)) : Albert) -
      (direction (Sum.inr (slot,t,false)) : Albert) = _
  rw [direction_coe, direction_coe]
  fin_cases slot <;> apply Albert.ext <;>
    norm_num [familyIdempotent, signedBasis, slotIdempotent, slotVector, X01, X02, X12] <;>
    module


end
end AlbertRecognition.ReferenceTransport
