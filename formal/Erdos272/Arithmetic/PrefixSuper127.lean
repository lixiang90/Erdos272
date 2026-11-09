module

public import Erdos272.Arithmetic.WitnessMoment122
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace JSP233.PrefixSuper127
open scoped Classical BigOperators
open TwoSidedMoment62 StarCompletion RestrictedWitness44
noncomputable section
set_option maxHeartbeats 0

theorem multiples_card (X d : ℕ) :
    ((Finset.Icc 1 X).filter (fun n=>d∣n)).card=X/d := by
  have he : Finset.Icc 1 X=Finset.Ioc 0 X := by ext n;simp only [Finset.mem_Icc,Finset.mem_Ioc];omega
  rw [he]
  exact Nat.Ioc_filter_dvd_card_eq_div X d

theorem divisor_pairs_common (B n : ℕ) (hn : n∈Finset.Icc 1 B) :
    n.divisors.product n.divisors=
      ((Finset.Icc 1 B).product (Finset.Icc 1 B)).filter
        (fun p=>Nat.lcm p.1 p.2∣n) := by
  obtain ⟨hn0,hnB⟩ := Finset.mem_Icc.mp hn
  ext p
  simp only [Finset.product_eq_sprod,Finset.mem_product,Finset.mem_filter,Nat.mem_divisors,Nat.lcm_dvd_iff]
  constructor
  · rintro ⟨⟨hd,hnz⟩,⟨he,_⟩⟩
    exact ⟨⟨Finset.mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos hd hn0,(Nat.le_of_dvd hn0 hd).trans hnB⟩,
      Finset.mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos he hn0,(Nat.le_of_dvd hn0 he).trans hnB⟩⟩,hd,he⟩
  · rintro ⟨_h,hd,he⟩
    exact ⟨⟨hd,by omega⟩,⟨he,by omega⟩⟩

theorem actual_second_moment_common (X B : ℕ) (hXB : X≤B) :
    (∑n∈Finset.Icc 1 X,n.divisors.card^2)=
      ∑p∈(Finset.Icc 1 B).product (Finset.Icc 1 B),X/(Nat.lcm p.1 p.2) := by
  calc
    _=∑n∈Finset.Icc 1 X,
        (((Finset.Icc 1 B).product (Finset.Icc 1 B)).filter
          (fun p=>Nat.lcm p.1 p.2∣n)).card := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [←divisor_pairs_common B n (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1,(Finset.mem_Icc.mp hn).2.trans hXB⟩),Finset.product_eq_sprod,Finset.card_product]
      ring
    _=∑p∈(Finset.Icc 1 B).product (Finset.Icc 1 B),
        ((Finset.Icc 1 X).filter (fun n=>Nat.lcm p.1 p.2∣n)).card := by
      simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
      rw [Finset.sum_comm]
    _=_ := by simp only [multiples_card]

theorem actual_second_moment_superadditive (a b : ℕ) :
    (∑n∈Finset.Icc 1 a,n.divisors.card^2)+
      (∑n∈Finset.Icc 1 b,n.divisors.card^2)≤
        ∑n∈Finset.Icc 1 (a+b),n.divisors.card^2 := by
  rw [actual_second_moment_common a (a+b) (by omega),
    actual_second_moment_common b (a+b) (by omega),
    actual_second_moment_common (a+b) (a+b) le_rfl,←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro p _hp
  exact Nat.add_div_le_add_div a b (Nat.lcm p.1 p.2)

theorem divisors_common (B n : ℕ) (hn : n∈Finset.Icc 1 B) :
    n.divisors=(Finset.Icc 1 B).filter (fun d=>d∣n) := by
  obtain ⟨hn0,hnB⟩ := Finset.mem_Icc.mp hn
  ext d
  simp only [Finset.mem_filter,Nat.mem_divisors]
  constructor
  · rintro ⟨hd,_⟩
    exact ⟨Finset.mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos hd hn0,(Nat.le_of_dvd hn0 hd).trans hnB⟩,hd⟩
  · rintro ⟨_h,hd⟩
    exact ⟨hd,by omega⟩

theorem actual_first_moment_common (X B : ℕ) (hXB : X≤B) :
    (∑n∈Finset.Icc 1 X,n.divisors.card)=∑d∈Finset.Icc 1 B,X/d := by
  calc
    _=∑n∈Finset.Icc 1 X,((Finset.Icc 1 B).filter (fun d=>d∣n)).card := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [←divisors_common B n (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1,(Finset.mem_Icc.mp hn).2.trans hXB⟩)]
    _=∑d∈Finset.Icc 1 B,((Finset.Icc 1 X).filter (fun n=>d∣n)).card := by
      simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
      rw [Finset.sum_comm]
    _=_ := by simp only [multiples_card]

theorem actual_first_moment_superadditive (a b : ℕ) :
    (∑n∈Finset.Icc 1 a,n.divisors.card)+
      (∑n∈Finset.Icc 1 b,n.divisors.card)≤
        ∑n∈Finset.Icc 1 (a+b),n.divisors.card := by
  rw [actual_first_moment_common a (a+b) (by omega),
    actual_first_moment_common b (a+b) (by omega),
    actual_first_moment_common (a+b) (a+b) le_rfl,←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro d _hd
  exact Nat.add_div_le_add_div a b d

theorem actual_prefix_exception_superadditive (a b : ℕ) :
    PrefixException a+PrefixException b≤PrefixException (a+b) := by
  have h2 : (∑n∈Finset.Icc 1 a,(n.divisors.card:ℝ)^2)+
      (∑n∈Finset.Icc 1 b,(n.divisors.card:ℝ)^2)≤
        ∑n∈Finset.Icc 1 (a+b),(n.divisors.card:ℝ)^2 := by
    exact_mod_cast actual_second_moment_superadditive a b
  have h1 : (∑n∈Finset.Icc 1 a,(n.divisors.card:ℝ))+
      (∑n∈Finset.Icc 1 b,(n.divisors.card:ℝ))≤
        ∑n∈Finset.Icc 1 (a+b),(n.divisors.card:ℝ) := by
    exact_mod_cast actual_first_moment_superadditive a b
  dsimp only [PrefixException]
  linarith only [h2,h1]

theorem actual_exception_single_prefix {N : ℕ} {c : ℤ} (hc : c∈Ground N) :
    (WitnessException (Ground N) c:ℝ)≤PrefixException (N-1) := by
  have hcG := (mem_ground N c).mp hc
  have hlen : c.toNat-1+(N-c.toNat)=N-1 := by omega
  rw [actual_exception_split hc]
  convert actual_prefix_exception_superadditive (c.toNat-1) (N-c.toNat) using 1
  rw [hlen]

theorem prefix_exception_nonnegative (X : ℕ) : 0≤PrefixException X := by
  dsimp only [PrefixException]
  positivity

theorem prefix_exception_monotone {X Y : ℕ} (hXY : X≤Y) :
    PrefixException X≤PrefixException Y := by
  have hs := actual_prefix_exception_superadditive X (Y-X)
  rw [Nat.add_sub_of_le hXY] at hs
  linarith only [hs,prefix_exception_nonnegative (Y-X)]

theorem actual_exception_whole_prefix {N : ℕ} {c : ℤ} (hc : c∈Ground N) :
    (WitnessException (Ground N) c:ℝ)≤PrefixException N := by
  exact (actual_exception_single_prefix hc).trans (prefix_exception_monotone (Nat.sub_le N 1))

#print axioms multiples_card
#print axioms divisor_pairs_common
#print axioms actual_second_moment_common
#print axioms actual_second_moment_superadditive
#print axioms divisors_common
#print axioms actual_first_moment_common
#print axioms actual_first_moment_superadditive
#print axioms actual_prefix_exception_superadditive
#print axioms actual_exception_single_prefix
#print axioms prefix_exception_nonnegative
#print axioms prefix_exception_monotone
#print axioms actual_exception_whole_prefix
end
end JSP233.PrefixSuper127
