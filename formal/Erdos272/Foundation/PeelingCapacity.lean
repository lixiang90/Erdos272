import Erdos272.Foundation.StarCompletion

/-! Finite counting from hereditary private points. The geometric existence
of those points is proved separately in `ChainGeometry`, not assumed by the
final chain or prime-power theorem. -/

namespace JSP233.PeelingCapacity

open StarCompletion

/-- Every subfamily with at least two members has a point private to one
of its actual members. This is a geometric interface, not a cardinal bound. -/
def HereditaryPrivate (D : Finset (Finset Int)) : Prop :=
  ∀ E ⊆ D, 2 ≤ E.card →
    ∃ S ∈ E, ∃ x ∈ S, ∀ T ∈ E, T ≠ S → x ∉ T

theorem hereditaryPrivate_mono {D E : Finset (Finset Int)}
    (hD : HereditaryPrivate D) (hED : E ⊆ D) : HereditaryPrivate E := by
  intro H hHE htwo
  exact hD H (hHE.trans hED) htwo

/-- Actual finite deletion: a removed member and its private point cost
exactly one family slot and one ground slot. The fixed AP anchor survives. -/
theorem hereditary_private_card_bound
    (Ω A : Finset Int) (D : Finset (Finset Int))
    (hA : IsAP A) (hAΩ : A ⊆ Ω)
    (hground : ∀ S ∈ D, S ⊆ Ω)
    (hcore : ∀ S ∈ D, A ⊆ S)
    (hcrooked : ∀ S ∈ D, ¬ IsAP S)
    (hprivate : HereditaryPrivate D) :
    D.card + A.card ≤ Ω.card := by
  classical
  induction D using Finset.strongInductionOn generalizing Ω with
  | _ D ih =>
    by_cases htwo : 2 ≤ D.card
    · obtain ⟨S,hSD,x,hxS,hxpriv⟩ := hprivate D (by intro T hT; exact hT) htwo
      obtain ⟨T,hTD,hTS⟩ := Finset.exists_mem_ne (by omega : 1 < D.card) S
      have hxA : x ∉ A := by
        intro hx
        exact hxpriv T hTD hTS (hcore T hTD hx)
      have hxΩ : x ∈ Ω := hground S hSD hxS
      have hAΩ' : A ⊆ Ω.erase x := by
        intro y hy
        exact Finset.mem_erase.mpr ⟨by intro he; exact hxA (he ▸ hy),hAΩ hy⟩
      have hground' : ∀ U ∈ D.erase S, U ⊆ Ω.erase x := by
        intro U hU y hy
        have hUD := (Finset.mem_erase.mp hU).2
        have hUS := (Finset.mem_erase.mp hU).1
        exact Finset.mem_erase.mpr
          ⟨by intro he; exact hxpriv U hUD hUS (he ▸ hy),hground U hUD hy⟩
      have hcore' : ∀ U ∈ D.erase S, A ⊆ U := by
        intro U hU; exact hcore U (Finset.mem_erase.mp hU).2
      have hcrooked' : ∀ U ∈ D.erase S, ¬ IsAP U := by
        intro U hU; exact hcrooked U (Finset.mem_erase.mp hU).2
      have hsmaller : D.erase S ⊂ D := Finset.erase_ssubset hSD
      have hbound := ih (D.erase S) hsmaller (Ω.erase x) hAΩ'
        hground' hcore' hcrooked' (hereditaryPrivate_mono hprivate (Finset.erase_subset _ _))
      rw [Finset.card_erase_of_mem hSD, Finset.card_erase_of_mem hxΩ] at hbound
      have hDpos : 0 < D.card := Finset.card_pos.mpr ⟨S,hSD⟩
      have hΩpos : 0 < Ω.card := Finset.card_pos.mpr ⟨x,hxΩ⟩
      omega
    · by_cases hD : D.Nonempty
      · obtain ⟨S,hSD⟩ := hD
        have hne : A ≠ S := by
          intro he; exact hcrooked S hSD (he ▸ hA)
        have hstrict : A ⊂ S := ⟨hcore S hSD,fun hs => hne (Finset.Subset.antisymm (hcore S hSD) hs)⟩
        have hlt := Finset.card_lt_card hstrict
        have hle := Finset.card_le_card (hground S hSD)
        have hDpos : 0 < D.card := Finset.card_pos.mpr ⟨S,hSD⟩
        omega
      · have hzero : D.card = 0 := by
          apply Finset.card_eq_zero.mpr
          exact Finset.not_nonempty_iff_eq_empty.mp hD
        have hle := Finset.card_le_card hAΩ
        omega

#print axioms hereditaryPrivate_mono
#print axioms hereditary_private_card_bound

end JSP233.PeelingCapacity
