module

public import Erdos272.Arithmetic.ParityPool123
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-! A finite div3 cube of actual quadruples. Its two middle coordinates are
three times a pair not both even, so the image is disjoint from both the
actual coprime encoding and the complete both-even pool. Every natural
cutoff and finite cube side is retained, including zero and T above N/9. -/

namespace JSP233.ThreePool124
open ParityPool123 DivisorMoment45 SimplexMoment57
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

def OddPairCube (q T : ℕ) : ℕ :=
  ∑g∈Finset.Icc 1 T,∑r∈Finset.Icc 1 T,∑s∈Finset.Icc 1 T,
    if ¬(2∣r ∧ 2∣s) then q/(g*r*s) else 0

def SmallOddPool (q T : ℕ) : Finset Quad :=
  (Finset.Icc 1 T).sigma (fun g=>(Finset.Icc 1 T).sigma
    (fun r=>((Finset.Icc 1 T).filter (fun s=>¬(2∣r ∧ 2∣s))).sigma
      (fun s=>Finset.Icc 1 (q/(g*r*s)))))

def tripleMiddle (z : Quad) : Quad := ⟨z.1,3*z.2.1,3*z.2.2.1,z.2.2.2⟩

def ThreePool (N T : ℕ) : Finset Quad :=
  (SmallOddPool (N/9) T).image tripleMiddle

theorem small_odd_pool_card (q T : ℕ) : (SmallOddPool q T).card=OddPairCube q T := by
  simp only [SmallOddPool,Finset.card_sigma,Nat.card_Icc,Nat.add_sub_cancel,
    Finset.sum_filter,OddPairCube]

theorem mem_small_odd_pool {q T g r s t : ℕ} :
    (⟨g,r,s,t⟩:Quad)∈SmallOddPool q T ↔
      0<g ∧ g≤T ∧ 0<r ∧ r≤T ∧ 0<s ∧ s≤T ∧
      ¬(2∣r ∧ 2∣s) ∧ 0<t ∧ g*r*s*t≤q := by
  simp only [SmallOddPool,Finset.mem_sigma,Finset.mem_filter,Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hg,hgT⟩,⟨⟨hr,hrT⟩,⟨⟨⟨hs,hsT⟩,hp⟩,⟨ht,hb⟩⟩⟩⟩
    have hh := (Nat.le_div_iff_mul_le (Nat.mul_pos (Nat.mul_pos hg hr) hs)).mp hb
    exact ⟨hg,hgT,hr,hrT,hs,hsT,hp,ht,by simpa only [Nat.mul_comm t] using hh⟩
  · rintro ⟨hg,hgT,hr,hrT,hs,hsT,hp,ht,hprod⟩
    refine ⟨⟨hg,hgT⟩,⟨⟨hr,hrT⟩,⟨⟨⟨hs,hsT⟩,hp⟩,⟨ht,?_⟩⟩⟩⟩
    exact (Nat.le_div_iff_mul_le (Nat.mul_pos (Nat.mul_pos hg hr) hs)).mpr
      (by simpa only [Nat.mul_comm t] using hprod)

theorem triple_middle_mem_quad_pool {N T : ℕ} {z : Quad}
    (hz : z∈SmallOddPool (N/9) T) : tripleMiddle z∈QuadPool N := by
  rcases z with ⟨g,r,s,t⟩
  obtain ⟨hg,_hgT,hr,_hrT,hs,_hsT,_hp,ht,hprod⟩ := mem_small_odd_pool.mp hz
  have hprod9 := (Nat.le_div_iff_mul_le (by decide : 0<9)).mp hprod
  apply mem_quad_pool.mpr
  refine ⟨hg,by dsimp only [tripleMiddle];omega,by dsimp only [tripleMiddle];omega,ht,?_⟩
  change g*(3*r)*(3*s)*t≤N
  convert hprod9 using 1;ring

theorem triple_middle_injective : Function.Injective tripleMiddle := by
  intro z w heq
  have hg := congrArg (fun u:Quad=>u.1) heq
  have hr := congrArg (fun u:Quad=>u.2.1) heq
  have hs := congrArg (fun u:Quad=>u.2.2.1) heq
  have ht := congrArg (fun u:Quad=>u.2.2.2) heq
  rcases z with ⟨g,r,s,t⟩
  rcases w with ⟨g',r',s',t'⟩
  change g=g' at hg
  change 3*r=3*r' at hr
  change 3*s=3*s' at hs
  change t=t' at ht
  have hr' : r=r' := by omega
  have hs' : s=s' := by omega
  subst g'
  subst r'
  subst s'
  subst t'
  rfl

theorem three_pool_card (N T : ℕ) : (ThreePool N T).card=OddPairCube (N/9) T := by
  rw [ThreePool,Finset.card_image_of_injective _ triple_middle_injective,small_odd_pool_card]

theorem three_pool_subset (N T : ℕ) : ThreePool N T⊆QuadPool N := by
  intro z hz
  obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
  exact triple_middle_mem_quad_pool hw

theorem coprime_three_disjoint (N T : ℕ) : Disjoint (CoprimePool N) (ThreePool N T) := by
  apply Finset.disjoint_left.mpr
  intro z hzC hz3
  obtain ⟨w,_hw,rfl⟩ := Finset.mem_image.mp hz3
  have hco := (Finset.mem_filter.mp hzC).2
  have hd : 3∣Nat.gcd (3*w.2.1) (3*w.2.2.1) := Nat.dvd_gcd ⟨_,rfl⟩ ⟨_,rfl⟩
  change Nat.gcd (3*w.2.1) (3*w.2.2.1)=1 at hco
  rw [hco] at hd
  norm_num at hd

theorem even_three_disjoint (N T : ℕ) : Disjoint (EvenPool N) (ThreePool N T) := by
  apply Finset.disjoint_left.mpr
  intro z hzE hz3
  obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz3
  rcases w with ⟨g,r,s,t⟩
  have hp := (mem_small_odd_pool.mp hw).2.2.2.2.2.2.1
  obtain ⟨_hz,hdr,hds⟩ := Finset.mem_filter.mp hzE
  change 2∣3*r at hdr
  change 2∣3*s at hds
  exact hp ⟨(Nat.Coprime.dvd_mul_left (by decide : Nat.Coprime 2 3)).mp hdr,
    (Nat.Coprime.dvd_mul_left (by decide : Nat.Coprime 2 3)).mp hds⟩

theorem actual_divisor_second_moment_three_nat (N T : ℕ) :
    (∑n∈Finset.Icc 1 N,n.divisors.card^2)+DivCount 3 (N/4)+OddPairCube (N/9) T≤DivCount 3 N := by
  have hd : Disjoint (CoprimePool N∪EvenPool N) (ThreePool N T) :=
    Finset.disjoint_union_left.mpr ⟨coprime_three_disjoint N T,even_three_disjoint N T⟩
  have hs : (CoprimePool N∪EvenPool N)∪ThreePool N T⊆QuadPool N := by
    intro z hz
    rcases Finset.mem_union.mp hz with hCE | h3
    · rcases Finset.mem_union.mp hCE with hC | hE
      · exact (Finset.mem_filter.mp hC).1
      · exact (Finset.mem_filter.mp hE).1
    · exact three_pool_subset N T h3
  have hc : (∑n∈Finset.Icc 1 N,n.divisors.card^2)+(EvenPool N).card+(ThreePool N T).card≤(QuadPool N).card := by
    calc
      _≤(CoprimePool N).card+(EvenPool N).card+(ThreePool N T).card :=
        Nat.add_le_add_right (Nat.add_le_add_right (actual_coprime_second_moment_encoding N) _) _
      _=((CoprimePool N∪EvenPool N)∪ThreePool N T).card := by
        rw [Finset.card_union_of_disjoint hd,Finset.card_union_of_disjoint (coprime_even_disjoint N)]
      _≤_ := Finset.card_le_card hs
  rwa [even_pool_card,three_pool_card,quad_pool_eq_div_count,quad_pool_eq_div_count] at hc

theorem actual_divisor_second_moment_three (N T : ℕ) :
    (∑n∈Finset.Icc 1 N,(n.divisors.card:ℝ)^2)+(DivCount 3 (N/4):ℝ)+
      (OddPairCube (N/9) T:ℝ)≤(DivCount 3 N:ℝ) := by
  exact_mod_cast actual_divisor_second_moment_three_nat N T

#print axioms small_odd_pool_card
#print axioms mem_small_odd_pool
#print axioms triple_middle_mem_quad_pool
#print axioms triple_middle_injective
#print axioms three_pool_card
#print axioms three_pool_subset
#print axioms coprime_three_disjoint
#print axioms even_three_disjoint
#print axioms actual_divisor_second_moment_three_nat
#print axioms actual_divisor_second_moment_three
end
end JSP233.ThreePool124
