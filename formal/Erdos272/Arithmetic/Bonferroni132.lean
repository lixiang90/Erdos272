module

public import Erdos272.Arithmetic.CompleteSeven129

@[expose] public section
namespace JSP233.Bonferroni132
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

variable {ι α:Type*} [DecidableEq α]

def poolUnion (A:ι→Finset α) : List ι→Finset α
  | []=>∅
  | a::l=>A a∪poolUnion A l

def cardSum (A:ι→Finset α) (l:List ι) : ℕ := (l.map (fun a=>(A a).card)).sum

def baseCost (A:ι→Finset α) (U:Finset α) (l:List ι) : ℕ :=
  (l.map (fun a=>(A a∩U).card)).sum

def pairCost (A:ι→Finset α) : List ι→ℕ
  | []=>0
  | a::l=>baseCost A (A a) l+pairCost A l

theorem base_cost_union_le (A:ι→Finset α) (U V:Finset α) (l:List ι) :
    baseCost A (U∪V) l≤baseCost A U l+baseCost A V l := by
  induction l with
  | nil=>simp only [baseCost,List.map_nil,List.sum_nil,Nat.zero_add,le_refl]
  | cons a l ih=>
    have he : A a∩(U∪V)=(A a∩U)∪(A a∩V) := by
      ext x
      simp only [Finset.mem_inter,Finset.mem_union]
      tauto
    have hc := Finset.card_union_le (A a∩U) (A a∩V)
    simp only [baseCost,List.map_cons,List.sum_cons] at ih ⊢
    rw [he]
    omega

theorem card_union_bonferroni (A:ι→Finset α) (U:Finset α) (l:List ι) :
    U.card+cardSum A l≤(U∪poolUnion A l).card+baseCost A U l+pairCost A l := by
  induction l generalizing U with
  | nil=>simp only [poolUnion,cardSum,baseCost,pairCost,List.map_nil,List.sum_nil,
      Nat.add_zero,Finset.union_empty,le_refl]
  | cons a l ih=>
    have hi := ih (U∪A a)
    have hb := base_cost_union_le A U (A a) l
    have hc := Finset.card_union_add_card_inter U (A a)
    have he : (U∩A a).card=(A a∩U).card := by rw [Finset.inter_comm]
    rw [Finset.union_assoc] at hi
    simp only [poolUnion,cardSum,baseCost,pairCost,List.map_cons,List.sum_cons] at hi hb ⊢
    omega

theorem mem_pool_union (A:ι→Finset α) (l:List ι) (x:α) :
    x∈poolUnion A l↔∃a∈l,x∈A a := by
  induction l with
  | nil=>simp [poolUnion]
  | cons a l ih=>
    rw [poolUnion,Finset.mem_union,ih]
    constructor
    · rintro (hx | ⟨b,hb,hx⟩)
      · exact ⟨a,List.mem_cons_self,hx⟩
      · exact ⟨b,List.mem_cons_of_mem a hb,hx⟩
    · rintro ⟨b,hb,hx⟩
      rcases List.mem_cons.mp hb with hb | hb
      · subst b
        exact Or.inl hx
      · exact Or.inr ⟨b,hb,hx⟩

#print axioms base_cost_union_le
#print axioms card_union_bonferroni
#print axioms mem_pool_union
end
end JSP233.Bonferroni132
