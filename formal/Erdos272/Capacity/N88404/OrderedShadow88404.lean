module

public import Erdos272.Counting.TripleCodes208
public import Erdos272.Arithmetic.Source.IntervalMixedShadow16858
public import Erdos272.Counting.APCount41
public import Erdos272.Arithmetic.Source.APShadowCapacity16858

@[expose] public section

namespace JSP233.OrderedShadow88404
open StarCompletion APGeometry APShadowCapacity16858
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

abbrev PointTriple := ℤ × ℤ × ℤ

def Triple (p : PointTriple) : Finset ℤ := {p.1, p.2.1, p.2.2}

def Sorted (p : PointTriple) : Prop := p.1 < p.2.1 ∧ p.2.1 < p.2.2

def Codes (M : ℕ) (T : Finset (Finset ℤ)) : Finset PointTriple :=
  (Ground M ×ˢ (Ground M ×ˢ Ground M)).filter
    (fun p => Sorted p ∧ Triple p ∈ T)

def Closed (T : Finset (Finset ℤ)) : Prop :=
  ∀ a b c x y z : ℤ, a < b → b < c → ({a,b,c} : Finset ℤ) ∈ T →
    a ≤ x → x < y → y < z → z ≤ c → ({x,y,z} : Finset ℤ) ∈ T

theorem triple_card {p : PointTriple} (hp : Sorted p) : (Triple p).card = 3 := by
  exact Finset.card_eq_three.mpr ⟨p.1, p.2.1, p.2.2,
    ne_of_lt hp.1, ne_of_lt (hp.1.trans hp.2), ne_of_lt hp.2, rfl⟩

theorem triple_injective {p q : PointTriple} (hp : Sorted p) (hq : Sorted q)
    (he : Triple p = Triple q) : p = q := by
  have hh := IntervalMixedShadow16858.sorted_triple_injective hp.1 hp.2 hq.1 hq.2 he
  exact Prod.ext hh.1 (Prod.ext hh.2.1 hh.2.2)

theorem mem_codes {M : ℕ} {T : Finset (Finset ℤ)} {p : PointTriple} :
    p ∈ Codes M T ↔ p.1 ∈ Ground M ∧ p.2.1 ∈ Ground M ∧ p.2.2 ∈ Ground M ∧
      Sorted p ∧ Triple p ∈ T := by
  simp only [Codes, Finset.mem_filter, Finset.mem_product, and_assoc]

theorem codes_image {M : ℕ} {T : Finset (Finset ℤ)} (hT : T ⊆ (Ground M).powersetCard 3) :
    (Codes M T).image Triple = T := by
  ext Q
  constructor
  · intro hQ
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hQ
    exact (mem_codes.mp hp).2.2.2.2
  · intro hQ
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp (hT hQ)
    obtain ⟨a, b, c, hab, hbc, he⟩ := TripleCodes208.sorted_three hcard
    refine Finset.mem_image.mpr ⟨(a,b,c), ?_, he.symm⟩
    apply mem_codes.mpr
    refine ⟨hsub (by rw [he]; simp), hsub (by rw [he]; simp),
      hsub (by rw [he]; simp), ⟨hab, hbc⟩, ?_⟩
    simpa only [Triple, he] using hQ

theorem codes_card {M : ℕ} {T : Finset (Finset ℤ)} (hT : T ⊆ (Ground M).powersetCard 3) :
    (Codes M T).card = T.card := by
  have hinj : Set.InjOn Triple (Codes M T) := by
    intro p hp q hq he
    exact triple_injective (mem_codes.mp hp).2.2.2.1 (mem_codes.mp hq).2.2.2.1 he
  have hh := Finset.card_image_of_injOn hinj
  rw [codes_image hT] at hh
  exact hh.symm

theorem sorted_pair_injective {a b c d : ℤ} (hab : a < b) (hcd : c < d)
    (he : ({a,b} : Finset ℤ) = {c,d}) : a = c ∧ b = d := by
  have ha : a = c ∨ a = d := by
    have hh : a ∈ ({c,d} : Finset ℤ) := by rw [← he]; simp
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hh
  have hb : b = c ∨ b = d := by
    have hh : b ∈ ({c,d} : Finset ℤ) := by rw [← he]; simp
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hh
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> omega

theorem mem_codes_of_inner {M : ℕ} {T : Finset (Finset ℤ)}
    (hclosed : Closed T) {p q : PointTriple} (hp : p ∈ Codes M T)
    (hleft : p.1 ≤ q.1) (hq : Sorted q) (hright : q.2.2 ≤ p.2.2) :
    q ∈ Codes M T := by
  obtain ⟨hpa, hpb, hpc, hps, hpT⟩ := mem_codes.mp hp
  have ha := (mem_ground M p.1).mp hpa
  have hc := (mem_ground M p.2.2).mp hpc
  apply mem_codes.mpr
  refine ⟨(mem_ground M q.1).mpr ⟨by omega, by have := hq.1; have := hq.2; omega⟩,
    (mem_ground M q.2.1).mpr ⟨by have := hq.1; omega, by have := hq.2; omega⟩,
    (mem_ground M q.2.2).mpr ⟨by have := hq.1; have := hq.2; omega, by omega⟩,
    hq, ?_⟩
  exact hclosed _ _ _ _ _ _ hps.1 hps.2 hpT hleft hq.1 hq.2 hright

theorem shadow_carrier {M : ℕ} {U : Finset (Finset ℤ)}
    (hground : ∀ S ∈ U, S ⊆ Ground M) : APShadow U ⊆ (Ground M).powersetCard 3 := by
  intro Q hQ
  obtain ⟨S, hS, hQS⟩ := Finset.mem_biUnion.mp hQ
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hQS
  exact Finset.mem_powersetCard.mpr ⟨hsub.trans (hground S hS), hcard⟩

theorem shadow_closed {U : Finset (Finset ℤ)}
    (hi : ∀ S ∈ U, ∃ a b : ℤ, S = Finset.Icc a b) : Closed (APShadow U) := by
  intro a b c x y z hab hbc hQ hax hxy hyz hzc
  obtain ⟨S, hS, hQS⟩ := Finset.mem_biUnion.mp hQ
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hQS
  obtain ⟨l, r, he⟩ := hi S hS
  have ha := hsub (show a ∈ ({a,b,c} : Finset ℤ) by simp)
  have hc := hsub (show c ∈ ({a,b,c} : Finset ℤ) by simp)
  rw [he] at ha hc
  have hla := Finset.mem_Icc.mp ha
  have hcr := Finset.mem_Icc.mp hc
  apply Finset.mem_biUnion.mpr
  refine ⟨S, hS, Finset.mem_powersetCard.mpr ⟨?_, triple_card (p := (x,y,z)) ⟨hxy,hyz⟩⟩⟩
  rw [he]
  intro t ht
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl <;> exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩

#print axioms triple_card
#print axioms triple_injective
#print axioms mem_codes
#print axioms codes_image
#print axioms codes_card
#print axioms sorted_pair_injective
#print axioms mem_codes_of_inner
#print axioms shadow_carrier
#print axioms shadow_closed
end
end JSP233.OrderedShadow88404
