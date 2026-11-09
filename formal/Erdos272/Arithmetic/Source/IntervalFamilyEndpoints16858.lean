module

public import Erdos272.Arithmetic.Source.IntervalMixedShadow16858
public import Erdos272.Counting.APCount41
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

/-! Actual interval members are encoded by their two endpoints. The axis
members cost only A+B, while the remaining members enter the mixed downset. -/
namespace JSP233.IntervalFamilyEndpoints16858
open APCount41 IntervalMixedShadow16858
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

def Pairs (c : ℤ) (A B : ℕ) (U : Finset (Finset ℤ)) : Finset (ℕ × ℕ) :=
  ((Finset.range A).product (Finset.range B)).filter
    (fun p => ∃ S ∈ U, Left c p ∈ S ∧ Right c p ∈ S)

def Code (c : ℤ) (S : Finset ℤ) : ℕ × ℕ :=
  ((c - Low S).toNat - 1, (High S - c).toNat - 1)

def AxisPool (c : ℤ) (A B : ℕ) : Finset (Finset ℤ) :=
  ((Finset.range A).image (fun i : ℕ => Finset.Icc (c - ((i : ℤ) + 1)) c)) ∪
    ((Finset.range B).image (fun j : ℕ => Finset.Icc c (c + ((j : ℤ) + 1))))

theorem interval_rep {c : ℤ} {S : Finset ℤ} (hc : c ∈ S)
    (hi : ∃ a b : ℤ, S = Finset.Icc a b) : S = Finset.Icc (Low S) (High S) := by
  obtain ⟨a, b, rfl⟩ := hi
  have hne : (Finset.Icc a b).Nonempty := ⟨c, hc⟩
  have hab : a ≤ b := by have hh := Finset.mem_Icc.mp hc; omega
  have hl := low_spec hne
  have hh := high_spec hne
  have hlow : Low (Finset.Icc a b) = a := by
    have hm := (Finset.mem_Icc.mp hl.1).1
    have hb := hl.2 a (Finset.mem_Icc.mpr ⟨le_rfl, hab⟩)
    omega
  have hhigh : High (Finset.Icc a b) = b := by
    have hm := (Finset.mem_Icc.mp hh.1).2
    have hb := hh.2 b (Finset.mem_Icc.mpr ⟨hab, le_rfl⟩)
    omega
  rw [hlow, hhigh]

theorem code_endpoints {c : ℤ} {S : Finset ℤ} (hl : Low S < c) (hr : c < High S) :
    Left c (Code c S) = Low S ∧ Right c (Code c S) = High S := by
  dsimp only [Left, Right, Code]
  constructor <;> omega

theorem axis_card (c : ℤ) (A B : ℕ) : (AxisPool c A B).card ≤ A + B := by
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add
    (Finset.card_image_le.trans_eq (Finset.card_range A))
    (Finset.card_image_le.trans_eq (Finset.card_range B)))

theorem pairs_cover {c : ℤ} {A B : ℕ} {U : Finset (Finset ℤ)}
    (hi : ∀ S ∈ U, ∃ a b : ℤ, S = Finset.Icc a b) :
    ∀ p ∈ Pairs c A B U, ∃ S ∈ U, Finset.Icc (Left c p) (Right c p) ⊆ S := by
  intro p hp
  obtain ⟨_hp, S, hSU, hl, hr⟩ := Finset.mem_filter.mp hp
  obtain ⟨a, b, he⟩ := hi S hSU
  refine ⟨S, hSU, ?_⟩
  rw [he] at hl hr ⊢
  intro x hx
  have hlb := Finset.mem_Icc.mp hl
  have hrb := Finset.mem_Icc.mp hr
  have hxb := Finset.mem_Icc.mp hx
  exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩

theorem actual_count_bound {c : ℤ} {A B : ℕ} {U : Finset (Finset ℤ)}
    (hground : ∀ S ∈ U, S ⊆ Finset.Icc (c - A) (c + B))
    (hroot : ∀ S ∈ U, c ∈ S) (hi : ∀ S ∈ U, ∃ a b : ℤ, S = Finset.Icc a b)
    (htwo : ∀ S ∈ U, 2 ≤ S.card) : U.card ≤ A + B + (Pairs c A B U).card := by
  let E := U.filter (fun S => Low S < c ∧ c < High S)
  let Ax := U.filter (fun S => ¬(Low S < c ∧ c < High S))
  have hmap : Set.MapsTo (Code c) E (Pairs c A B U) := by
    intro S hS
    obtain ⟨hSU, hl, hr⟩ := Finset.mem_filter.mp hS
    have he := code_endpoints hl hr
    have hne : S.Nonempty := ⟨c, hroot S hSU⟩
    have hbL := (Finset.mem_Icc.mp (hground S hSU (low_spec hne).1)).1
    have hbR := (Finset.mem_Icc.mp (hground S hSU (high_spec hne).1)).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr ?_, Finset.mem_range.mpr ?_⟩,
      S, hSU, ?_, ?_⟩
    · dsimp only [Code]; omega
    · dsimp only [Code]; omega
    · rw [he.1]; exact (low_spec hne).1
    · rw [he.2]; exact (high_spec hne).1
  have hinj : Set.InjOn (Code c) E := by
    intro S hS T hT he
    obtain ⟨hSU, hSl, hSr⟩ := Finset.mem_filter.mp hS
    obtain ⟨hTU, hTl, hTr⟩ := Finset.mem_filter.mp hT
    have hSends := code_endpoints hSl hSr
    have hTends := code_endpoints hTl hTr
    have hl : Low S = Low T := by rw [← hSends.1, ← hTends.1, he]
    have hr : High S = High T := by rw [← hSends.2, ← hTends.2, he]
    rw [interval_rep (hroot S hSU) (hi S hSU), interval_rep (hroot T hTU) (hi T hTU), hl, hr]
  have hE := Finset.card_le_card_of_injOn (Code c) hmap hinj
  have hAxsub : Ax ⊆ AxisPool c A B := by
    intro S hS
    obtain ⟨hSU, hnot⟩ := Finset.mem_filter.mp hS
    have hc := hroot S hSU
    have hne : S.Nonempty := ⟨c, hc⟩
    have hlow := low_spec hne
    have hhigh := high_spec hne
    have hlc := hlow.2 c hc
    have hcr := hhigh.2 c hc
    have hre := interval_rep hc (hi S hSU)
    have hstrict : Low S < High S := by
      by_contra hn
      have hsame : Low S = High S := by omega
      have ht := htwo S hSU
      rw [hre, hsame, Finset.Icc_self, Finset.card_singleton] at ht
      omega
    by_cases hl : Low S < c
    · have hr : High S = c := by omega
      have hb := (Finset.mem_Icc.mp (hground S hSU hlow.1)).1
      let i := (c - Low S).toNat - 1
      have hiA : i < A := by dsimp only [i]; omega
      have heL : c - ((i : ℤ) + 1) = Low S := by dsimp only [i]; omega
      apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      refine ⟨i, Finset.mem_range.mpr hiA, ?_⟩
      rw [heL, ← hr, ← hre]
    · have hL : Low S = c := by omega
      have hb := (Finset.mem_Icc.mp (hground S hSU hhigh.1)).2
      let j := (High S - c).toNat - 1
      have hjB : j < B := by dsimp only [j]; omega
      have heR : c + ((j : ℤ) + 1) = High S := by dsimp only [j]; omega
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨j, Finset.mem_range.mpr hjB, ?_⟩
      rw [heR, ← hL, ← hre]
  have hAx := (Finset.card_le_card hAxsub).trans (axis_card c A B)
  have hsplit : E.card + Ax.card = U.card :=
    Finset.card_filter_add_card_filter_not (s := U) (fun S => Low S < c ∧ c < High S)
  omega

#print axioms interval_rep
#print axioms code_endpoints
#print axioms axis_card
#print axioms pairs_cover
#print axioms actual_count_bound
end
end JSP233.IntervalFamilyEndpoints16858
