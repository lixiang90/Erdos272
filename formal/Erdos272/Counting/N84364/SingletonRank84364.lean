module

public import Erdos272.Resources.N84364.CrossRankBudget84364
public import Erdos272.Resources.N84364.SmallCreditScalars84364
public import Erdos272.Counting.SparseCross41

@[expose] public section

namespace JSP233.SingletonRank84364
open StarCompletion SparseSmall39 SparseCross41 CrossRankBudget84364 SmallCreditScalars84364
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem actual_singleton_rank_budget {N : ℕ} {F : Finset (Finset ℤ)}
    {A B : Finset ℤ} {c : ℤ} (hlegal : Legal (Ground N) F)
    (hbad : ∀ S ∈ F, ¬IsAP S) (hA : A∈F) (hB : B∈F) (hAB : A∩B={c}) :
    (Avoiders F c).card+3*(A.erase c).card*(B.erase c).card+
      (B.erase c).card*(A.erase c).card.choose 2+
      (A.erase c).card*(B.erase c).card.choose 2≤(A.erase c).card*(B.erase c).card*N := by
  have hc : c∈A∩B := by rw [hAB]; simp
  have hcN : c∈Ground N := hlegal.1 A hA (Finset.mem_inter.mp hc).1
  have hlegalH : Legal (Ground N) (Avoiders F c) :=
    ⟨fun S hS => hlegal.1 S (Finset.mem_filter.mp hS).1,
      fun S hS T hT hne => hlegal.2 S (Finset.mem_filter.mp hS).1
        T (Finset.mem_filter.mp hT).1 hne⟩
  have hD : ({c} : Finset ℤ)⊆Ground N := Finset.singleton_subset_iff.mpr hcN
  have hAe : A.erase c⊆Ground N := (Finset.erase_subset _ _).trans (hlegal.1 A hA)
  have hBe : B.erase c⊆Ground N := (Finset.erase_subset _ _).trans (hlegal.1 B hB)
  have hDA : Disjoint ({c} : Finset ℤ) (A.erase c) := by
    apply Finset.disjoint_left.mpr
    intro y hyD hyA
    exact (Finset.mem_erase.mp hyA).1 (Finset.mem_singleton.mp hyD)
  have hDB : Disjoint ({c} : Finset ℤ) (B.erase c) := by
    apply Finset.disjoint_left.mpr
    intro y hyD hyB
    exact (Finset.mem_erase.mp hyB).1 (Finset.mem_singleton.mp hyD)
  have hav : ∀ S ∈ Avoiders F c, Disjoint S ({c} : Finset ℤ) := by
    intro S hS
    apply Finset.disjoint_left.mpr
    intro y hyS hyD
    exact (Finset.mem_filter.mp hS).2 ((Finset.mem_singleton.mp hyD) ▸ hyS)
  have hhits := actual_singleton_cross_hits hlegal hA hB hAB
  have hhitA : ∀ S ∈ Avoiders F c, (S∩A.erase c).Nonempty := by
    intro S hS
    obtain ⟨a, ha, b, hb, haS, hbS⟩ := hhits S hS
    exact ⟨a, Finset.mem_inter.mpr ⟨haS, ha⟩⟩
  have hhitB : ∀ S ∈ Avoiders F c, (S∩B.erase c).Nonempty := by
    intro S hS
    obtain ⟨a, ha, b, hb, haS, hbS⟩ := hhits S hS
    exact ⟨b, Finset.mem_inter.mpr ⟨hbS, hb⟩⟩
  have hh := actual_cross_hit_budget hlegalH
    (fun S hS => hbad S (Finset.mem_filter.mp hS).1) hD hAe hBe
    (singleton_erases_disjoint hAB) hDA hDB hav hhitA hhitB
  simp only [Finset.card_singleton, ground_card] at hh
  nlinarith only [hh]

theorem actual_singleton_avoider_price {N L : ℕ} {F : Finset (Finset ℤ)}
    {A B : Finset ℤ} {c : ℤ} (hL : 2≤L) (hN : 2*L+1≤N)
    (hlegal : Legal (Ground N) F) (hbad : ∀ S ∈ F, ¬IsAP S)
    (hA : A∈F) (hB : B∈F) (hAL : A.card≤L) (hBL : B.card≤L) (hAB : A∩B={c}) :
    let m : ℝ := ((L-1 : ℕ) : ℝ)
    ((Avoiders F c).card : ℝ)+m^2*(m+2)≤m^2*N := by
  have hb := actual_singleton_rank_budget hlegal hbad hA hB hAB
  have hc : c∈A∩B := by rw [hAB]; simp
  have ha : (A.erase c).card≤L-1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_inter.mp hc).1]
    exact Nat.sub_le_sub_right hAL 1
  have hbsize : (B.erase c).card≤L-1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_inter.mp hc).2]
    exact Nat.sub_le_sub_right hBL 1
  have hbR : ((Avoiders F c).card : ℝ)+3*((A.erase c).card : ℝ)*(B.erase c).card+
      ((B.erase c).card : ℝ)*((A.erase c).card.choose 2 : ℝ)+
      ((A.erase c).card : ℝ)*((B.erase c).card.choose 2 : ℝ)
      ≤((A.erase c).card : ℝ)*(B.erase c).card*N := by exact_mod_cast hb
  rw [Nat.cast_choose_two, Nat.cast_choose_two] at hbR
  have hN' : 2*(L-1)+3≤N := by omega
  have hmax := cross_mono hN' ha hbsize
  dsimp only
  nlinarith only [hbR, hmax]

#print axioms actual_singleton_rank_budget
#print axioms actual_singleton_avoider_price
end
end JSP233.SingletonRank84364
