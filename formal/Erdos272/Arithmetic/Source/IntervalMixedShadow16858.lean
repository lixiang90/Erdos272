module

public import Erdos272.Arithmetic.Source.APShadowCapacity16858
public import Mathlib.Data.Int.Interval
public import Erdos272.Foundation.ProofTactics
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

/-! Cross-root triples have unique extreme endpoints. Their middle-point
fibres give the exact mixed contribution to an interval family's shadow. -/
namespace JSP233.IntervalMixedShadow16858
open APShadowCapacity16858
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

def Left (c : ℤ) (p : ℕ × ℕ) : ℤ := c - (p.1 + 1)
def Right (c : ℤ) (p : ℕ × ℕ) : ℤ := c + (p.2 + 1)
def CodeSet (c : ℤ) (D : Finset (ℕ × ℕ)) : Finset (Σ _ : ℕ × ℕ, ℤ) :=
  D.sigma (fun p => Finset.Ioo (Left c p) (Right c p))
def Triple (c : ℤ) (z : Σ _ : ℕ × ℕ, ℤ) : Finset ℤ := {Left c z.1, z.2, Right c z.1}
def Mixed (c : ℤ) (D : Finset (ℕ × ℕ)) : Finset (Finset ℤ) := (CodeSet c D).image (Triple c)

theorem sorted_triple_injective {a b c x y z : ℤ}
    (hab : a < b) (hbc : b < c) (hxy : x < y) (hyz : y < z)
    (he : ({a, b, c} : Finset ℤ) = {x, y, z}) : a = x ∧ b = y ∧ c = z := by
  have ha : a = x ∨ a = y ∨ a = z := by
    have hh : a ∈ ({x, y, z} : Finset ℤ) := he ▸ (by simp)
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hh
  have hx : x = a ∨ x = b ∨ x = c := by
    have hh : x ∈ ({a, b, c} : Finset ℤ) := he.symm ▸ (by simp)
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hh
  have hc : c = x ∨ c = y ∨ c = z := by
    have hh : c ∈ ({x, y, z} : Finset ℤ) := he ▸ (by simp)
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hh
  have hz : z = a ∨ z = b ∨ z = c := by
    have hh : z ∈ ({a, b, c} : Finset ℤ) := he.symm ▸ (by simp)
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hh
  have hb : b = x ∨ b = y ∨ b = z := by
    have hh : b ∈ ({x, y, z} : Finset ℤ) := he ▸ (by simp)
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hh
  omega

theorem triple_card {c : ℤ} {p : ℕ × ℕ} {m : ℤ}
    (hm : m ∈ Finset.Ioo (Left c p) (Right c p)) :
    (Triple c ⟨p, m⟩).card = 3 := by
  obtain ⟨hl, hr⟩ := Finset.mem_Ioo.mp hm
  exact Finset.card_eq_three.mpr ⟨Left c p, m, Right c p,
    ne_of_lt hl, ne_of_lt (hl.trans hr), ne_of_lt hr, rfl⟩

theorem code_injective {c : ℤ} {D : Finset (ℕ × ℕ)} :
    Set.InjOn (Triple c) (CodeSet c D) := by
  rintro ⟨p, m⟩ hz ⟨q, n⟩ hw he
  have hm := Finset.mem_Ioo.mp (Finset.mem_sigma.mp hz).2
  have hn := Finset.mem_Ioo.mp (Finset.mem_sigma.mp hw).2
  obtain ⟨hl, hmid, hr⟩ := sorted_triple_injective hm.1 hm.2 hn.1 hn.2 he
  have hp : p = q := by
    apply Prod.ext
    · dsimp only [Left] at hl
      omega
    · dsimp only [Right] at hr
      omega
  subst q
  change m = n at hmid
  subst n
  rfl

theorem mixed_card (c : ℤ) (D : Finset (ℕ × ℕ)) :
    (Mixed c D).card = ∑ p ∈ D, (p.1 + p.2 + 1) := by
  rw [Mixed, Finset.card_image_of_injOn code_injective, CodeSet, Finset.card_sigma]
  apply Finset.sum_congr rfl
  intro p _hp
  rw [Int.card_Ioo]
  dsimp only [Left, Right]
  omega

theorem mixed_subset_shadow {c : ℤ} {D : Finset (ℕ × ℕ)} {U : Finset (Finset ℤ)}
    (hcover : ∀ p ∈ D, ∃ S ∈ U, Finset.Icc (Left c p) (Right c p) ⊆ S) :
    Mixed c D ⊆ APShadow U := by
  intro Q hQ
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hQ
  obtain ⟨hp, hm⟩ := Finset.mem_sigma.mp hz
  obtain ⟨S, hSU, hS⟩ := hcover z.1 hp
  obtain ⟨hl, hr⟩ := Finset.mem_Ioo.mp hm
  apply Finset.mem_biUnion.mpr
  refine ⟨S, hSU, Finset.mem_powersetCard.mpr ⟨?_, triple_card hm⟩⟩
  intro x hx
  simp only [Triple, Finset.mem_insert, Finset.mem_singleton] at hx
  apply hS
  rcases hx with rfl | rfl | rfl
  · exact Finset.mem_Icc.mpr ⟨le_rfl, (hl.trans hr).le⟩
  · exact Finset.mem_Icc.mpr ⟨hl.le, hr.le⟩
  · exact Finset.mem_Icc.mpr ⟨(hl.trans hr).le, le_rfl⟩

theorem side_disjoint (c : ℤ) (A B : ℕ) :
    Disjoint ((Finset.Icc (c - A) c).powersetCard 3)
      ((Finset.Icc c (c + B)).powersetCard 3) := by
  apply Finset.disjoint_left.mpr
  intro Q hQ hR
  obtain ⟨hL, hcard⟩ := Finset.mem_powersetCard.mp hQ
  have hR := (Finset.mem_powersetCard.mp hR).1
  have hs : Q ⊆ {c} := by
    intro x hx
    have hl := (Finset.mem_Icc.mp (hL hx)).2
    have hr := (Finset.mem_Icc.mp (hR hx)).1
    exact Finset.mem_singleton.mpr (by omega)
  have hh := Finset.card_le_card hs
  simp only [Finset.card_singleton, hcard] at hh
  omega

theorem left_mixed_disjoint (c : ℤ) (A : ℕ) (D : Finset (ℕ × ℕ)) :
    Disjoint ((Finset.Icc (c - A) c).powersetCard 3) (Mixed c D) := by
  apply Finset.disjoint_left.mpr
  intro Q hQ hM
  obtain ⟨z, _hz, rfl⟩ := Finset.mem_image.mp hM
  have hh := (Finset.mem_Icc.mp ((Finset.mem_powersetCard.mp hQ).1
    (by simp [Triple] : Right c z.1 ∈ Triple c z))).2
  dsimp only [Right] at hh
  omega

theorem right_mixed_disjoint (c : ℤ) (B : ℕ) (D : Finset (ℕ × ℕ)) :
    Disjoint ((Finset.Icc c (c + B)).powersetCard 3) (Mixed c D) := by
  apply Finset.disjoint_left.mpr
  intro Q hQ hM
  obtain ⟨z, _hz, rfl⟩ := Finset.mem_image.mp hM
  have hh := (Finset.mem_Icc.mp ((Finset.mem_powersetCard.mp hQ).1
    (by simp [Triple] : Left c z.1 ∈ Triple c z))).1
  dsimp only [Left] at hh
  omega

theorem actual_shadow_lower {c : ℤ} {A B : ℕ} {D : Finset (ℕ × ℕ)} {U : Finset (Finset ℤ)}
    (hleft : (Finset.Icc (c - A) c).powersetCard 3 ⊆ APShadow U)
    (hright : (Finset.Icc c (c + B)).powersetCard 3 ⊆ APShadow U)
    (hcover : ∀ p ∈ D, ∃ S ∈ U, Finset.Icc (Left c p) (Right c p) ⊆ S) :
    (A + 1).choose 3 + (B + 1).choose 3 + (∑ p ∈ D, (p.1 + p.2 + 1)) ≤ (APShadow U).card := by
  have hsub := Finset.union_subset (Finset.union_subset hleft hright) (mixed_subset_shadow hcover)
  have hh := Finset.card_le_card hsub
  have hL : (Finset.Icc (c - A) c).card = A + 1 := by rw [Int.card_Icc]; omega
  have hR : (Finset.Icc c (c + B)).card = B + 1 := by rw [Int.card_Icc]; omega
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr
      ⟨left_mixed_disjoint c A D, right_mixed_disjoint c B D⟩),
    Finset.card_union_of_disjoint (side_disjoint c A B),
    Finset.card_powersetCard, Finset.card_powersetCard, hL, hR, mixed_card] at hh
  exact hh

#print axioms sorted_triple_injective
#print axioms triple_card
#print axioms code_injective
#print axioms mixed_card
#print axioms mixed_subset_shadow
#print axioms side_disjoint
#print axioms left_mixed_disjoint
#print axioms right_mixed_disjoint
#print axioms actual_shadow_lower
end
end JSP233.IntervalMixedShadow16858
