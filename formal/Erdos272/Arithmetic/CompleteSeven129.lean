module

public import Erdos272.Arithmetic.CompleteFive128
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

namespace JSP233.CompleteSeven129
open CompleteFive128 ParityPool123 DivisorMoment45 SimplexMoment57
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem card_four_union (A B C D : Finset Quad) :
    (A∪B∪C∪D).card+(A∩B).card+(A∩C).card+(A∩D).card+
      (B∩C).card+(B∩D).card+(C∩D).card+(A∩B∩C∩D).card=
        A.card+B.card+C.card+D.card+(A∩B∩C).card+(A∩B∩D).card+
          (A∩C∩D).card+(B∩C∩D).card := by
  have h1 := card_three_union A B C
  have h2 := Finset.card_union_add_card_inter (A∪B∪C) D
  have h3 := card_three_union (A∩D) (B∩D) (C∩D)
  have hu : (A∪B∪C)∩D=(A∩D)∪(B∩D)∪(C∩D) := by
    ext z
    simp only [Finset.mem_inter,Finset.mem_union]
    tauto
  have hAB : (A∩D)∩(B∩D)=A∩B∩D := by
    ext z
    simp only [Finset.mem_inter]
    tauto
  have hAC : (A∩D)∩(C∩D)=A∩C∩D := by
    ext z
    simp only [Finset.mem_inter]
    tauto
  have hBC : (B∩D)∩(C∩D)=B∩C∩D := by
    ext z
    simp only [Finset.mem_inter]
    tauto
  have hABC : (A∩D)∩(B∩D)∩(C∩D)=A∩B∩C∩D := by
    ext z
    simp only [Finset.mem_inter]
    tauto
  rw [hu] at h2
  rw [hABC,hAB,hAC,hBC] at h3
  omega

theorem actual_four_pool_count (N : ℕ) :
    (BothPool 2 N∪BothPool 3 N∪BothPool 5 N∪BothPool 7 N).card+
      DivCount 3 (N/36)+DivCount 3 (N/100)+DivCount 3 (N/196)+
        DivCount 3 (N/225)+DivCount 3 (N/441)+DivCount 3 (N/1225)+DivCount 3 (N/44100)=
          DivCount 3 (N/4)+DivCount 3 (N/9)+DivCount 3 (N/25)+DivCount 3 (N/49)+
            DivCount 3 (N/900)+DivCount 3 (N/1764)+DivCount 3 (N/4900)+DivCount 3 (N/11025) := by
  have h23 : BothPool 2 N∩BothPool 3 N=BothPool 6 N := both_pool_inter N 2 3 (by decide)
  have h25 : BothPool 2 N∩BothPool 5 N=BothPool 10 N := both_pool_inter N 2 5 (by decide)
  have h27 : BothPool 2 N∩BothPool 7 N=BothPool 14 N := both_pool_inter N 2 7 (by decide)
  have h35 : BothPool 3 N∩BothPool 5 N=BothPool 15 N := both_pool_inter N 3 5 (by decide)
  have h37 : BothPool 3 N∩BothPool 7 N=BothPool 21 N := both_pool_inter N 3 7 (by decide)
  have h57 : BothPool 5 N∩BothPool 7 N=BothPool 35 N := both_pool_inter N 5 7 (by decide)
  have h235 : BothPool 2 N∩BothPool 3 N∩BothPool 5 N=BothPool 30 N := by
    rw [h23]
    exact both_pool_inter N 6 5 (by decide)
  have h237 : BothPool 2 N∩BothPool 3 N∩BothPool 7 N=BothPool 42 N := by
    rw [h23]
    exact both_pool_inter N 6 7 (by decide)
  have h257 : BothPool 2 N∩BothPool 5 N∩BothPool 7 N=BothPool 70 N := by
    rw [h25]
    exact both_pool_inter N 10 7 (by decide)
  have h357 : BothPool 3 N∩BothPool 5 N∩BothPool 7 N=BothPool 105 N := by
    rw [h35]
    exact both_pool_inter N 15 7 (by decide)
  have h2357 : BothPool 2 N∩BothPool 3 N∩BothPool 5 N∩BothPool 7 N=BothPool 210 N := by
    rw [h235]
    exact both_pool_inter N 30 7 (by decide)
  have he := card_four_union (BothPool 2 N) (BothPool 3 N) (BothPool 5 N) (BothPool 7 N)
  rw [h2357,h235,h237,h257,h357,h23,h25,h27,h35,h37,h57] at he
  rw [both_pool_div_count 2 N (by decide),both_pool_div_count 3 N (by decide),
    both_pool_div_count 5 N (by decide),both_pool_div_count 7 N (by decide),
    both_pool_div_count 6 N (by decide),both_pool_div_count 10 N (by decide),
    both_pool_div_count 14 N (by decide),both_pool_div_count 15 N (by decide),
    both_pool_div_count 21 N (by decide),both_pool_div_count 35 N (by decide),
    both_pool_div_count 30 N (by decide),both_pool_div_count 42 N (by decide),
    both_pool_div_count 70 N (by decide),both_pool_div_count 105 N (by decide),
    both_pool_div_count 210 N (by decide)] at he
  norm_num only at he
  exact he

theorem actual_divisor_second_moment_seven_nat (N : ℕ) :
    (∑n∈Finset.Icc 1 N,n.divisors.card^2)+DivCount 3 (N/4)+DivCount 3 (N/9)+
      DivCount 3 (N/25)+DivCount 3 (N/49)+DivCount 3 (N/900)+DivCount 3 (N/1764)+
        DivCount 3 (N/4900)+DivCount 3 (N/11025)≤
          DivCount 3 N+DivCount 3 (N/36)+DivCount 3 (N/100)+DivCount 3 (N/196)+
            DivCount 3 (N/225)+DivCount 3 (N/441)+DivCount 3 (N/1225)+DivCount 3 (N/44100) := by
  let U := BothPool 2 N∪BothPool 3 N∪BothPool 5 N∪BothPool 7 N
  have hd2 := coprime_both_disjoint N 2 (by decide)
  have hd3 := coprime_both_disjoint N 3 (by decide)
  have hd5 := coprime_both_disjoint N 5 (by decide)
  have hd7 := coprime_both_disjoint N 7 (by decide)
  have hdis : Disjoint (CoprimePool N) U :=
    Finset.disjoint_union_right.mpr ⟨Finset.disjoint_union_right.mpr
      ⟨Finset.disjoint_union_right.mpr ⟨hd2,hd3⟩,hd5⟩,hd7⟩
  have hsub : CoprimePool N∪U⊆QuadPool N := by
    intro z hz
    rcases Finset.mem_union.mp hz with hC | hU
    · exact (Finset.mem_filter.mp hC).1
    · rcases Finset.mem_union.mp hU with h235 | h7
      · rcases Finset.mem_union.mp h235 with h23 | h5
        · rcases Finset.mem_union.mp h23 with h2 | h3
          · exact (Finset.mem_filter.mp h2).1
          · exact (Finset.mem_filter.mp h3).1
        · exact (Finset.mem_filter.mp h5).1
      · exact (Finset.mem_filter.mp h7).1
  have hc : (∑n∈Finset.Icc 1 N,n.divisors.card^2)+U.card≤(QuadPool N).card := by
    calc
      _≤(CoprimePool N).card+U.card := Nat.add_le_add_right (actual_coprime_second_moment_encoding N) _
      _=(CoprimePool N∪U).card := (Finset.card_union_of_disjoint hdis).symm
      _≤_ := Finset.card_le_card hsub
  have he := actual_four_pool_count N
  dsimp only [U] at hc
  rw [quad_pool_eq_div_count] at hc
  omega

theorem actual_divisor_second_moment_seven (N : ℕ) :
    (∑n∈Finset.Icc 1 N,(n.divisors.card:ℝ)^2)+(DivCount 3 (N/4):ℝ)+(DivCount 3 (N/9):ℝ)+
      (DivCount 3 (N/25):ℝ)+(DivCount 3 (N/49):ℝ)+(DivCount 3 (N/900):ℝ)+(DivCount 3 (N/1764):ℝ)+
        (DivCount 3 (N/4900):ℝ)+(DivCount 3 (N/11025):ℝ)≤
          (DivCount 3 N:ℝ)+(DivCount 3 (N/36):ℝ)+(DivCount 3 (N/100):ℝ)+(DivCount 3 (N/196):ℝ)+
            (DivCount 3 (N/225):ℝ)+(DivCount 3 (N/441):ℝ)+(DivCount 3 (N/1225):ℝ)+(DivCount 3 (N/44100):ℝ) := by
  exact_mod_cast actual_divisor_second_moment_seven_nat N

#print axioms card_four_union
#print axioms actual_four_pool_count
#print axioms actual_divisor_second_moment_seven_nat
#print axioms actual_divisor_second_moment_seven
end
end JSP233.CompleteSeven129
