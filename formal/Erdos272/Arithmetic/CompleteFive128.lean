module

public import Erdos272.Arithmetic.CompletePool126
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

namespace JSP233.CompleteFive128
open ParityPool123 DivisorMoment45 SimplexMoment57
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

def BothPool (d N : ℕ) : Finset Quad :=
  (QuadPool N).filter (fun z=>d∣z.2.1 ∧ d∣z.2.2.1)

def scaleMiddle (d : ℕ) (z : Quad) : Quad := ⟨z.1,d*z.2.1,d*z.2.2.1,z.2.2.2⟩

theorem scale_middle_mem {d N : ℕ} (hd : 0<d) {z : Quad}
    (hz : z∈QuadPool (N/(d*d))) : scaleMiddle d z∈BothPool d N := by
  rcases z with ⟨g,a,b,t⟩
  obtain ⟨hg,ha,hb,ht,hprod⟩ := mem_quad_pool.mp hz
  have hp := (Nat.le_div_iff_mul_le (Nat.mul_pos hd hd)).mp hprod
  apply Finset.mem_filter.mpr
  change (⟨g,d*a,d*b,t⟩:Quad)∈QuadPool N ∧ d∣d*a ∧ d∣d*b
  refine ⟨mem_quad_pool.mpr ⟨hg,Nat.mul_pos hd ha,Nat.mul_pos hd hb,ht,?_⟩,⟨a,rfl⟩,⟨b,rfl⟩⟩
  convert hp using 1
  ring

theorem scale_middle_injective {d : ℕ} (hd : 0<d) : Function.Injective (scaleMiddle d) := by
  intro z w heq
  have hg := congrArg (fun u:Quad=>u.1) heq
  have ha := congrArg (fun u:Quad=>u.2.1) heq
  have hb := congrArg (fun u:Quad=>u.2.2.1) heq
  have ht := congrArg (fun u:Quad=>u.2.2.2) heq
  rcases z with ⟨g,a,b,t⟩
  rcases w with ⟨g',a',b',t'⟩
  change g=g' at hg
  change d*a=d*a' at ha
  change d*b=d*b' at hb
  change t=t' at ht
  have ha' : a=a' := mul_left_cancel₀ hd.ne' ha
  have hb' : b=b' := mul_left_cancel₀ hd.ne' hb
  subst g'
  subst a'
  subst b'
  subst t'
  rfl

theorem both_pool_card (d N : ℕ) (hd : 0<d) :
    (BothPool d N).card=(QuadPool (N/(d*d))).card := by
  symm
  apply Finset.card_bij (fun z _hz=>scaleMiddle d z)
  · intro z hz
    exact scale_middle_mem hd hz
  · intro z _hz w _hw heq
    exact scale_middle_injective hd heq
  · intro z hz
    obtain ⟨hz,hda,hdb⟩ := Finset.mem_filter.mp hz
    rcases z with ⟨g,a,b,t⟩
    obtain ⟨a',ha'⟩ := hda
    obtain ⟨b',hb'⟩ := hdb
    change a=d*a' at ha'
    change b=d*b' at hb'
    obtain ⟨hg,ha,hb,ht,hprod⟩ := mem_quad_pool.mp hz
    have ha0 : 0<a' := Nat.pos_of_mul_pos_left (ha' ▸ ha)
    have hb0 : 0<b' := Nat.pos_of_mul_pos_left (hb' ▸ hb)
    refine ⟨(⟨g,a',b',t⟩:Quad),mem_quad_pool.mpr ⟨hg,ha0,hb0,ht,?_⟩,?_⟩
    · apply (Nat.le_div_iff_mul_le (Nat.mul_pos hd hd)).mpr
      rw [ha',hb'] at hprod
      convert hprod using 1
      ring
    · dsimp only [scaleMiddle]
      rw [←ha',←hb']

theorem both_pool_div_count (d N : ℕ) (hd : 0<d) :
    (BothPool d N).card=DivCount 3 (N/(d*d)) := by
  rw [both_pool_card d N hd,quad_pool_eq_div_count]

theorem both_pool_inter (N d e : ℕ) (hde : Nat.Coprime d e) :
    BothPool d N∩BothPool e N=BothPool (d*e) N := by
  ext z
  simp only [BothPool,Finset.mem_filter,Finset.mem_inter]
  constructor
  · rintro ⟨⟨hz,hda,hdb⟩,⟨_hz,hea,heb⟩⟩
    exact ⟨hz,hde.mul_dvd_of_dvd_of_dvd hda hea,hde.mul_dvd_of_dvd_of_dvd hdb heb⟩
  · rintro ⟨hz,ha,hb⟩
    have hd : d∣d*e := ⟨e,rfl⟩
    have he : e∣d*e := ⟨d,Nat.mul_comm d e⟩
    exact ⟨⟨hz,hd.trans ha,hd.trans hb⟩,hz,he.trans ha,he.trans hb⟩

theorem coprime_both_disjoint (N d : ℕ) (hd : 2≤d) :
    Disjoint (CoprimePool N) (BothPool d N) := by
  apply Finset.disjoint_left.mpr
  intro z hzC hzB
  have hco := (Finset.mem_filter.mp hzC).2
  obtain ⟨_hz,hda,hdb⟩ := Finset.mem_filter.mp hzB
  have hh := Nat.dvd_gcd hda hdb
  change Nat.gcd z.2.1 z.2.2.1=1 at hco
  rw [hco] at hh
  have he := Nat.dvd_one.mp hh
  omega

theorem card_three_union (A B C : Finset Quad) :
    (A∪B∪C).card+(A∩B).card+(A∩C).card+(B∩C).card=
      A.card+B.card+C.card+(A∩B∩C).card := by
  have h1 := Finset.card_union_add_card_inter A B
  have h2 := Finset.card_union_add_card_inter (A∪B) C
  have h3 := Finset.card_union_add_card_inter (A∩C) (B∩C)
  have he : (A∪B)∩C=(A∩C)∪(B∩C) := by
    ext z
    simp only [Finset.mem_inter,Finset.mem_union]
    tauto
  have ht : (A∩C)∩(B∩C)=A∩B∩C := by
    ext z
    simp only [Finset.mem_inter]
    tauto
  rw [he] at h2
  rw [ht] at h3
  omega

theorem actual_divisor_second_moment_five_nat (N : ℕ) :
    (∑n∈Finset.Icc 1 N,n.divisors.card^2)+DivCount 3 (N/4)+DivCount 3 (N/9)+
      DivCount 3 (N/25)+DivCount 3 (N/900)≤
        DivCount 3 N+DivCount 3 (N/36)+DivCount 3 (N/100)+DivCount 3 (N/225) := by
  let U := BothPool 2 N∪BothPool 3 N∪BothPool 5 N
  have hd2 := coprime_both_disjoint N 2 (by decide)
  have hd3 := coprime_both_disjoint N 3 (by decide)
  have hd5 := coprime_both_disjoint N 5 (by decide)
  have hdis : Disjoint (CoprimePool N) U := by
    apply Finset.disjoint_left.mpr
    intro z hzC hzU
    rcases Finset.mem_union.mp hzU with hz23 | hz5
    · rcases Finset.mem_union.mp hz23 with hz2 | hz3
      · exact Finset.disjoint_left.mp hd2 hzC hz2
      · exact Finset.disjoint_left.mp hd3 hzC hz3
    · exact Finset.disjoint_left.mp hd5 hzC hz5
  have hsub : CoprimePool N∪U⊆QuadPool N := by
    intro z hz
    rcases Finset.mem_union.mp hz with hzC | hzU
    · exact (Finset.mem_filter.mp hzC).1
    · rcases Finset.mem_union.mp hzU with hz23 | hz5
      · rcases Finset.mem_union.mp hz23 with hz2 | hz3
        · exact (Finset.mem_filter.mp hz2).1
        · exact (Finset.mem_filter.mp hz3).1
      · exact (Finset.mem_filter.mp hz5).1
  have hc : (∑n∈Finset.Icc 1 N,n.divisors.card^2)+U.card≤(QuadPool N).card := by
    calc
      _≤(CoprimePool N).card+U.card := Nat.add_le_add_right (actual_coprime_second_moment_encoding N) _
      _=(CoprimePool N∪U).card := (Finset.card_union_of_disjoint hdis).symm
      _≤_ := Finset.card_le_card hsub
  have h23 : BothPool 2 N∩BothPool 3 N=BothPool 6 N := both_pool_inter N 2 3 (by decide)
  have h25 : BothPool 2 N∩BothPool 5 N=BothPool 10 N := both_pool_inter N 2 5 (by decide)
  have h35 : BothPool 3 N∩BothPool 5 N=BothPool 15 N := both_pool_inter N 3 5 (by decide)
  have h235 : BothPool 2 N∩BothPool 3 N∩BothPool 5 N=BothPool 30 N := by
    rw [h23]
    exact both_pool_inter N 6 5 (by decide)
  have he := card_three_union (BothPool 2 N) (BothPool 3 N) (BothPool 5 N)
  rw [h235,h23,h25,h35] at he
  change U.card+(BothPool 6 N).card+(BothPool 10 N).card+(BothPool 15 N).card=
    (BothPool 2 N).card+(BothPool 3 N).card+(BothPool 5 N).card+(BothPool 30 N).card at he
  rw [both_pool_div_count 2 N (by decide),both_pool_div_count 3 N (by decide),
    both_pool_div_count 5 N (by decide),both_pool_div_count 6 N (by decide),
    both_pool_div_count 10 N (by decide),both_pool_div_count 15 N (by decide),
    both_pool_div_count 30 N (by decide)] at he
  rw [quad_pool_eq_div_count] at hc
  norm_num only at he
  omega

theorem actual_divisor_second_moment_five (N : ℕ) :
    (∑n∈Finset.Icc 1 N,(n.divisors.card:ℝ)^2)+(DivCount 3 (N/4):ℝ)+
      (DivCount 3 (N/9):ℝ)+(DivCount 3 (N/25):ℝ)+(DivCount 3 (N/900):ℝ)≤
        (DivCount 3 N:ℝ)+(DivCount 3 (N/36):ℝ)+(DivCount 3 (N/100):ℝ)+(DivCount 3 (N/225):ℝ) := by
  exact_mod_cast actual_divisor_second_moment_five_nat N

#print axioms scale_middle_mem
#print axioms scale_middle_injective
#print axioms both_pool_card
#print axioms both_pool_div_count
#print axioms both_pool_inter
#print axioms coprime_both_disjoint
#print axioms card_three_union
#print axioms actual_divisor_second_moment_five_nat
#print axioms actual_divisor_second_moment_five
end
end JSP233.CompleteFive128
