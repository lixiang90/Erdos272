module

public import Erdos272.Core.N200000.ResidueClass200000

@[expose] public section

/-! Pair events are counted on the complement of one shared interval.
Each event retains the exact subtraction of its inside-interval pairs. -/
namespace JSP233.PairEventCount200000
open StarCompletion APGeometry SourceBridge208 ResidueClass200000
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

def Space (A J : Finset ℕ) : Finset (Finset ℕ) := A.powersetCard 2 \ J.powersetCard 2

def Event (A J : Finset ℕ) (q : ℕ) (u : ℤ) : Finset (Finset ℕ) :=
  (Space A J).filter (fun Q => ∀ i ∈ Q, (q : ℤ) ∣ (i : ℤ) - u)

theorem space_card {A J : Finset ℕ} (hJ : J ⊆ A) :
    (Space A J).card = A.card.choose 2 - J.card.choose 2 := by
  have hsub : J.powersetCard 2 ⊆ A.powersetCard 2 := by
    intro Q hQ
    obtain ⟨hQJ, hcard⟩ := Finset.mem_powersetCard.mp hQ
    exact Finset.mem_powersetCard.mpr ⟨hQJ.trans hJ, hcard⟩
  rw [Space, Finset.card_sdiff_of_subset hsub, Finset.card_powersetCard, Finset.card_powersetCard]

theorem event_eq (A J : Finset ℕ) (q : ℕ) (u : ℤ) :
    Event A J q u = (A.filter (fun i : ℕ => (q : ℤ) ∣ (i : ℤ) - u)).powersetCard 2 \
      (J.filter (fun i : ℕ => (q : ℤ) ∣ (i : ℤ) - u)).powersetCard 2 := by
  ext Q
  constructor
  · intro hQ
    obtain ⟨hspace, hall⟩ := Finset.mem_filter.mp hQ
    obtain ⟨hQA, hnotJ⟩ := Finset.mem_sdiff.mp hspace
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hQA
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_powersetCard.mpr ⟨?_, hcard⟩, ?_⟩
    · exact fun i hi => Finset.mem_filter.mpr ⟨hsub hi, hall i hi⟩
    · intro hQJ
      have hsubJ := (Finset.mem_powersetCard.mp hQJ).1
      exact hnotJ (Finset.mem_powersetCard.mpr ⟨fun i hi => (Finset.mem_filter.mp (hsubJ hi)).1, hcard⟩)
  · intro hQ
    obtain ⟨hQA, hnotJ⟩ := Finset.mem_sdiff.mp hQ
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hQA
    have hall : ∀ i ∈ Q, (q : ℤ) ∣ (i : ℤ) - u := fun i hi => (Finset.mem_filter.mp (hsub hi)).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_powersetCard.mpr ⟨?_, hcard⟩, ?_⟩, hall⟩
    · exact fun i hi => (Finset.mem_filter.mp (hsub hi)).1
    · intro hQJ
      have hsubJ := (Finset.mem_powersetCard.mp hQJ).1
      exact hnotJ (Finset.mem_powersetCard.mpr ⟨fun i hi => Finset.mem_filter.mpr ⟨hsubJ hi, hall i hi⟩, hcard⟩)

theorem event_card {A J : Finset ℕ} (hJ : J ⊆ A) (q : ℕ) (u : ℤ) :
    (Event A J q u).card = (A.filter (fun i : ℕ => (q : ℤ) ∣ (i : ℤ) - u)).card.choose 2 -
      (J.filter (fun i : ℕ => (q : ℤ) ∣ (i : ℤ) - u)).card.choose 2 := by
  rw [event_eq]
  exact space_card (Finset.filter_subset_filter _ hJ)

theorem interval_event_bounds {a b l q : ℕ} (hlen : l + b ≤ a) (hq : 0 < q) (u : ℤ) :
    (a / q).choose 2 - ((b + q - 1) / q).choose 2 ≤
        (Event (Finset.range a) (Finset.Ico l (l + b)) q u).card ∧
      (Event (Finset.range a) (Finset.Ico l (l + b)) q u).card ≤
        ((a + q - 1) / q).choose 2 - (b / q).choose 2 := by
  have hJ : Finset.Ico l (l + b) ⊆ Finset.range a := by
    intro i hi
    have hiu := (Finset.mem_Ico.mp hi).2
    exact Finset.mem_range.mpr (by omega)
  have hRange : (Finset.range a).filter (fun i : ℕ => (q : ℤ) ∣ (i : ℤ) - u) = Class 0 a q u := by
    ext i
    simp only [Class, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, Nat.zero_add, Nat.zero_le, true_and]
  have he := event_card hJ q u
  rw [hRange] at he
  change _ = (Class 0 a q u).card.choose 2 - (Class l b q u).card.choose 2 at he
  have hAL := Nat.choose_le_choose 2 (class_card_lower 0 a hq u)
  have hAU := Nat.choose_le_choose 2 (class_card_upper 0 a hq u)
  have hBL := Nat.choose_le_choose 2 (class_card_lower l b hq u)
  have hBU := Nat.choose_le_choose 2 (class_card_upper l b hq u)
  constructor <;> omega

#print axioms space_card
#print axioms event_eq
#print axioms event_card
#print axioms interval_event_bounds
end
end JSP233.PairEventCount200000
