module

public import Erdos272.Core.UnitPrivate32

@[expose] public section

/-! Actual singleton private pools have only three signed affine shapes.
Their finite physical keys are one nonroot ground point and one of three tags. -/
namespace JSP233.SingletonCapacity32
open StarCompletion PrivatePairExistence JointResources31 AffineLine30 SinglePrivate32
open scoped Classical
noncomputable section

def Pattern (tag : Fin 3) : Finset ℤ :=
  if tag=0 then {0,1,2,4} else if tag=1 then {0,1,2,3,4,6} else {-2,0,1,2}

def PatternCandidates (c : ℤ) (Ω : Finset ℤ) : Finset (Finset ℤ) :=
  ((Ω.erase c).product (Finset.univ : Finset (Fin 3))).image
    (fun key => mapSet c (key.1-c) (Pattern key.2))

theorem pattern_one (tag : Fin 3) : (1:ℤ)∈Pattern tag := by
  unfold Pattern
  split_ifs <;> simp

theorem unit_shape_pattern {U : Finset ℤ}
    (hshape : U={0,1,2,4} ∨ U={0,1,2,3,4,6} ∨ U={-2,0,1,2}) :
    ∃ tag : Fin 3, U=Pattern tag := by
  rcases hshape with h | h | h
  · exact ⟨0,by simpa [Pattern] using h⟩
  · exact ⟨1,by simpa [Pattern] using h⟩
  · exact ⟨2,by simpa [Pattern] using h⟩

theorem actual_singleton_three_patterns {c : ℤ} {Ω : Finset ℤ}
    {G : Finset (Finset ℤ)} (hlegal : Legal Ω G) (hroot : Rooted G c)
    {S : Finset ℤ} (hS : S∈SingletonPrivateLarge c Ω G) :
    ∃ m : ℤ, ∃ tag : Fin 3, m≠0 ∧ S=mapSet c m (Pattern tag) := by
  obtain ⟨m,U,v,hm,hSmap,h0,h1,hcard,hbad,hv,hv0,h1v,hu⟩ :=
    actual_singleton_unit_normalization hlegal hroot hS
  have hshape := UnitPrivate32.unit_singleton_classification h0 h1 hbad hcard hu
  obtain ⟨tag,htag⟩ := unit_shape_pattern hshape
  exact ⟨m,tag,hm,by rw [←htag]; exact hSmap⟩

theorem pattern_actual_key {c m : ℤ} {Ω S : Finset ℤ} {tag : Fin 3}
    (hm : m≠0) (hS : S=mapSet c m (Pattern tag)) (hground : S⊆Ω) :
    c+m∈Ω.erase c ∧ S=mapSet c ((c+m)-c) (Pattern tag) := by
  have hp : c+m∈S := by
    rw [hS]
    exact Finset.mem_image.mpr ⟨1,pattern_one tag,by dsimp [affine]; ring⟩
  exact ⟨Finset.mem_erase.mpr ⟨by omega,hground hp⟩,by simpa using hS⟩

theorem represented_family_subset_candidates {c : ℤ} {Ω : Finset ℤ}
    {H : Finset (Finset ℤ)} (hground : ∀ S∈H, S⊆Ω)
    (hshape : ∀ S∈H, ∃ m : ℤ, ∃ tag : Fin 3, m≠0 ∧ S=mapSet c m (Pattern tag)) :
    H⊆PatternCandidates c Ω := by
  intro S hS
  obtain ⟨m,tag,hm,hmap⟩ := hshape S hS
  obtain ⟨hkey,hkeymap⟩ := pattern_actual_key hm hmap (hground S hS)
  exact Finset.mem_image.mpr ⟨(c+m,tag),Finset.mem_product.mpr ⟨hkey,Finset.mem_univ _⟩,
    hkeymap.symm⟩

theorem pattern_candidates_card_le (c : ℤ) (Ω : Finset ℤ) :
    (PatternCandidates c Ω).card≤3*(Ω.erase c).card := by
  unfold PatternCandidates
  have hh := Finset.card_image_le (s:=(Ω.erase c).product (Finset.univ : Finset (Fin 3)))
    (f:=fun key => mapSet c (key.1-c) (Pattern key.2))
  rw [Finset.product_eq_sprod,Finset.card_product,Finset.card_univ,Fintype.card_fin] at hh
  simpa only [Finset.product_eq_sprod,Nat.mul_comm] using hh

theorem represented_family_card_le {c : ℤ} {Ω : Finset ℤ}
    {H : Finset (Finset ℤ)} (hground : ∀ S∈H, S⊆Ω)
    (hshape : ∀ S∈H, ∃ m : ℤ, ∃ tag : Fin 3, m≠0 ∧ S=mapSet c m (Pattern tag)) :
    H.card≤3*(Ω.erase c).card :=
  (Finset.card_le_card (represented_family_subset_candidates hground hshape)).trans
    (pattern_candidates_card_le c Ω)

theorem actual_singleton_card_le_erase {c : ℤ} {Ω : Finset ℤ}
    {G : Finset (Finset ℤ)} (hlegal : Legal Ω G) (hroot : Rooted G c) :
    (SingletonPrivateLarge c Ω G).card≤3*(Ω.erase c).card := by
  apply represented_family_card_le
  · intro S hS
    exact hlegal.1 S (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).1
  · intro S hS
    exact actual_singleton_three_patterns hlegal hroot hS

theorem actual_singleton_card_le {c : ℤ} {Ω : Finset ℤ}
    {G : Finset (Finset ℤ)} (hc : c∈Ω) (hlegal : Legal Ω G) (hroot : Rooted G c) :
    (SingletonPrivateLarge c Ω G).card≤3*(Ω.card-1) := by
  simpa only [Finset.card_erase_of_mem hc] using actual_singleton_card_le_erase hlegal hroot

theorem actual_ground_singleton_card_le {N : ℕ} {c : ℤ}
    {F : Finset (Finset ℤ)} (hc : c∈Ground N) (hlegal : Legal (Ground N) F) :
    (SingletonPrivateLarge c (Ground N) (RootPart F c)).card≤3*(N-1) := by
  simpa only [ground_card] using actual_singleton_card_le hc
    (rootPart_legal c (Ground N) F hlegal) (rootPart_rooted c F)

#print axioms pattern_one
#print axioms unit_shape_pattern
#print axioms actual_singleton_three_patterns
#print axioms pattern_actual_key
#print axioms represented_family_subset_candidates
#print axioms pattern_candidates_card_le
#print axioms represented_family_card_le
#print axioms actual_singleton_card_le_erase
#print axioms actual_singleton_card_le
#print axioms actual_ground_singleton_card_le
end
end JSP233.SingletonCapacity32
