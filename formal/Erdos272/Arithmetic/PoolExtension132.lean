import Erdos272.Arithmetic.Bonferroni132
namespace JSP233.PoolExtension132
open CompleteSeven129 CompleteFive128 ParityPool123 SimplexMoment57 DivisorMoment45
open Bonferroni132
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

def OldPool (N:ℕ) : Finset Quad := BothPool 2 N∪BothPool 3 N∪BothPool 5 N∪BothPool 7 N

def OldLower (N:ℕ) : ℕ :=
  DivCount 3 (N/4)+DivCount 3 (N/9)+DivCount 3 (N/25)+DivCount 3 (N/49)+
    DivCount 3 (N/900)+DivCount 3 (N/1764)+DivCount 3 (N/4900)+DivCount 3 (N/11025)

def OldPenalty (N:ℕ) : ℕ :=
  DivCount 3 (N/36)+DivCount 3 (N/100)+DivCount 3 (N/196)+DivCount 3 (N/225)+
    DivCount 3 (N/441)+DivCount 3 (N/1225)+DivCount 3 (N/44100)

def OldUpper (N:ℕ) : ℕ := DivCount 3 N+OldPenalty N

def ExtraTerms (N:ℕ) (P:List ℕ) : ℕ :=
  (P.map (fun p=>DivCount 3 (N/(p*p)))).sum

def CrossTerm (N p:ℕ) : ℕ :=
  DivCount 3 (N/((p*2)*(p*2)))+DivCount 3 (N/((p*3)*(p*3)))+
    DivCount 3 (N/((p*5)*(p*5)))+DivCount 3 (N/((p*7)*(p*7)))

def CrossTerms (N:ℕ) (P:List ℕ) : ℕ := (P.map (CrossTerm N)).sum

def PairTerms (N:ℕ) : List ℕ→ℕ
  | []=>0
  | p::P=>(P.map (fun q=>DivCount 3 (N/((p*q)*(p*q))))).sum+PairTerms N P

theorem old_pool_subset (N:ℕ) : OldPool N⊆QuadPool N := by
  intro z hz
  simp only [OldPool,BothPool,Finset.mem_union,Finset.mem_filter] at hz
  tauto

theorem extra_pools_subset (N:ℕ) (P:List ℕ) :
    poolUnion (fun p=>BothPool p N) P⊆QuadPool N := by
  intro z hz
  obtain ⟨p,_hp,hz⟩ := (mem_pool_union _ _ _).mp hz
  exact (Finset.mem_filter.mp hz).1

theorem coprime_old_disjoint (N:ℕ) : Disjoint (CoprimePool N) (OldPool N) := by
  exact Finset.disjoint_union_right.mpr ⟨Finset.disjoint_union_right.mpr
    ⟨Finset.disjoint_union_right.mpr ⟨coprime_both_disjoint N 2 (by decide),
      coprime_both_disjoint N 3 (by decide)⟩,coprime_both_disjoint N 5 (by decide)⟩,
        coprime_both_disjoint N 7 (by decide)⟩

theorem coprime_extras_disjoint (N:ℕ) (P:List ℕ) (hP:∀p∈P,2≤p) :
    Disjoint (CoprimePool N) (poolUnion (fun p=>BothPool p N) P) := by
  apply Finset.disjoint_left.mpr
  intro z hzC hzP
  obtain ⟨p,hp,hz⟩ := (mem_pool_union _ _ _).mp hzP
  exact Finset.disjoint_left.mp (coprime_both_disjoint N p (hP p hp)) hzC hz

theorem actual_coprime_extended_budget (N:ℕ) (P:List ℕ) (hP:∀p∈P,2≤p) :
    (∑n∈Finset.Icc 1 N,n.divisors.card^2)+
      (OldPool N∪poolUnion (fun p=>BothPool p N) P).card≤DivCount 3 N := by
  have hd := Finset.disjoint_union_right.mpr
    ⟨coprime_old_disjoint N,coprime_extras_disjoint N P hP⟩
  have hsub : CoprimePool N∪(OldPool N∪poolUnion (fun p=>BothPool p N) P)⊆QuadPool N := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · exact (Finset.mem_filter.mp hz).1
    · rcases Finset.mem_union.mp hz with hz | hz
      · exact old_pool_subset N hz
      · exact extra_pools_subset N P hz
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hd,quad_pool_eq_div_count] at hc
  have he := actual_coprime_second_moment_encoding N
  omega

theorem actual_extra_pool_budget (N:ℕ) (P:List ℕ) (hP:∀p∈P,2≤p) :
    (∑n∈Finset.Icc 1 N,n.divisors.card^2)+(OldPool N).card+
      cardSum (fun p=>BothPool p N) P≤
        DivCount 3 N+baseCost (fun p=>BothPool p N) (OldPool N) P+
          pairCost (fun p=>BothPool p N) P := by
  have hb := card_union_bonferroni (fun p=>BothPool p N) (OldPool N) P
  have hc := actual_coprime_extended_budget N P hP
  omega

theorem card_four_union_le (A B C D:Finset Quad) :
    (A∪B∪C∪D).card≤A.card+B.card+C.card+D.card := by
  have h1 := Finset.card_union_le A B
  have h2 := Finset.card_union_le (A∪B) C
  have h3 := Finset.card_union_le (A∪B∪C) D
  omega

theorem cross_card_bound (N p:ℕ) (hp:2≤p)
    (hbase:Nat.Coprime p 2 ∧ Nat.Coprime p 3 ∧ Nat.Coprime p 5 ∧ Nat.Coprime p 7) :
    (BothPool p N∩OldPool N).card≤CrossTerm N p := by
  have hp0 : 0<p := by omega
  have he : BothPool p N∩OldPool N=
      (BothPool p N∩BothPool 2 N)∪(BothPool p N∩BothPool 3 N)∪
        (BothPool p N∩BothPool 5 N)∪(BothPool p N∩BothPool 7 N) := by
    ext z
    simp only [OldPool,Finset.mem_inter,Finset.mem_union]
    tauto
  rw [he]
  have hc := card_four_union_le (BothPool p N∩BothPool 2 N) (BothPool p N∩BothPool 3 N)
    (BothPool p N∩BothPool 5 N) (BothPool p N∩BothPool 7 N)
  rw [both_pool_inter N p 2 hbase.1,both_pool_inter N p 3 hbase.2.1,
    both_pool_inter N p 5 hbase.2.2.1,both_pool_inter N p 7 hbase.2.2.2] at hc
  rw [both_pool_div_count (p*2) N (by positivity),both_pool_div_count (p*3) N (by positivity),
    both_pool_div_count (p*5) N (by positivity),both_pool_div_count (p*7) N (by positivity)] at hc
  simpa only [CrossTerm,both_pool_inter N p 2 hbase.1,both_pool_inter N p 3 hbase.2.1,
    both_pool_inter N p 5 hbase.2.2.1,both_pool_inter N p 7 hbase.2.2.2] using hc

theorem base_cost_bound (N:ℕ) (P:List ℕ) (hP:∀p∈P,2≤p)
    (hbase:∀p∈P,Nat.Coprime p 2 ∧ Nat.Coprime p 3 ∧ Nat.Coprime p 5 ∧ Nat.Coprime p 7) :
    baseCost (fun p=>BothPool p N) (OldPool N) P≤CrossTerms N P := by
  revert hP hbase
  induction P with
  | nil=>intro _ _;simp [baseCost,CrossTerms]
  | cons p P ih=>
    intro hP hbase
    have ht := ih (fun q hq=>hP q (List.mem_cons_of_mem p hq))
      (fun q hq=>hbase q (List.mem_cons_of_mem p hq))
    have hp := cross_card_bound N p (hP p List.mem_cons_self) (hbase p List.mem_cons_self)
    simp only [baseCost,CrossTerms,List.map_cons,List.sum_cons] at ht ⊢
    omega

theorem card_sum_div_count (N:ℕ) (P:List ℕ) (hP:∀p∈P,2≤p) :
    cardSum (fun p=>BothPool p N) P=ExtraTerms N P := by
  revert hP
  induction P with
  | nil=>intro _;rfl
  | cons p P ih=>
    intro hP
    have hp0 : 0<p := by have := hP p List.mem_cons_self;omega
    have ht := ih (fun q hq=>hP q (List.mem_cons_of_mem p hq))
    simp only [cardSum,ExtraTerms,List.map_cons,List.sum_cons] at ht ⊢
    rw [both_pool_div_count p N hp0,ht]

theorem pair_head_cost (N p:ℕ) (hp:0<p) (P:List ℕ)
    (hP:∀q∈P,2≤q) (hpair:∀q∈P,Nat.Coprime p q) :
    baseCost (fun q=>BothPool q N) (BothPool p N) P=
      (P.map (fun q=>DivCount 3 (N/((p*q)*(p*q))))).sum := by
  revert hP hpair
  induction P with
  | nil=>intro _ _;rfl
  | cons q P ih=>
    intro hP hpair
    have hq0 : 0<q := by have := hP q List.mem_cons_self;omega
    have hqp := (hpair q List.mem_cons_self).symm
    have ht := ih (fun r hr=>hP r (List.mem_cons_of_mem q hr))
      (fun r hr=>hpair r (List.mem_cons_of_mem q hr))
    simp only [baseCost,List.map_cons,List.sum_cons] at ht ⊢
    rw [both_pool_inter N q p hqp,both_pool_div_count (q*p) N (Nat.mul_pos hq0 hp),ht]
    rw [Nat.mul_comm q p]

theorem pair_cost_eq (N:ℕ) (P:List ℕ) (hP:∀p∈P,2≤p) (hpair:P.Pairwise Nat.Coprime) :
    pairCost (fun p=>BothPool p N) P=PairTerms N P := by
  revert hP hpair
  induction P with
  | nil=>intro _ _;rfl
  | cons p P ih=>
    intro hP hpair
    obtain ⟨hhead,htail⟩ := List.pairwise_cons.mp hpair
    have hPt : ∀q∈P,2≤q := fun q hq=>hP q (List.mem_cons_of_mem p hq)
    have hp0 : 0<p := by have := hP p List.mem_cons_self;omega
    have hc := pair_head_cost N p hp0 P hPt hhead
    have ht := ih hPt htail
    simp only [pairCost,PairTerms]
    rw [hc,ht]

theorem old_pool_identity (N:ℕ) : (OldPool N).card+OldPenalty N=OldLower N := by
  have h := actual_four_pool_count N
  dsimp only [OldPool,OldPenalty,OldLower]
  omega

theorem actual_second_moment_extras_nat (N:ℕ) (P:List ℕ) (hP:∀p∈P,2≤p)
    (hbase:∀p∈P,Nat.Coprime p 2 ∧ Nat.Coprime p 3 ∧ Nat.Coprime p 5 ∧ Nat.Coprime p 7)
    (hpair:P.Pairwise Nat.Coprime) :
    (∑n∈Finset.Icc 1 N,n.divisors.card^2)+OldLower N+ExtraTerms N P≤
      OldUpper N+CrossTerms N P+PairTerms N P := by
  have hb := actual_extra_pool_budget N P hP
  rw [card_sum_div_count N P hP,pair_cost_eq N P hP hpair] at hb
  have hc := base_cost_bound N P hP hbase
  have ho := old_pool_identity N
  dsimp only [OldUpper]
  omega

theorem actual_second_moment_extras (N:ℕ) (P:List ℕ) (hP:∀p∈P,2≤p)
    (hbase:∀p∈P,Nat.Coprime p 2 ∧ Nat.Coprime p 3 ∧ Nat.Coprime p 5 ∧ Nat.Coprime p 7)
    (hpair:P.Pairwise Nat.Coprime) :
    (∑n∈Finset.Icc 1 N,(n.divisors.card:ℝ)^2)+(OldLower N:ℝ)+(ExtraTerms N P:ℝ)≤
      (OldUpper N:ℝ)+(CrossTerms N P:ℝ)+(PairTerms N P:ℝ) := by
  exact_mod_cast actual_second_moment_extras_nat N P hP hbase hpair

#print axioms old_pool_subset
#print axioms extra_pools_subset
#print axioms coprime_old_disjoint
#print axioms coprime_extras_disjoint
#print axioms actual_coprime_extended_budget
#print axioms actual_extra_pool_budget
#print axioms card_four_union_le
#print axioms cross_card_bound
#print axioms base_cost_bound
#print axioms card_sum_div_count
#print axioms pair_head_cost
#print axioms pair_cost_eq
#print axioms old_pool_identity
#print axioms actual_second_moment_extras_nat
#print axioms actual_second_moment_extras
end
end JSP233.PoolExtension132
