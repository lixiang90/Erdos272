import Erdos272.Retention.ThinFringe42

/-! Actual indexed traces with pairwise intersection at most one cannot all
be long. No injectivity of the trace map or abstract pool capacity is assumed. -/
namespace JSP233.TracePacking43
open scoped Classical BigOperators
noncomputable section
variable {ι α : Type*} [DecidableEq ι] [DecidableEq α]

theorem trace_sum_bound (F : Finset ι) (T : ι→Finset α)
    (hpair : ∀ i∈F,∀ j∈F,i≠j → ((T i)∩(T j)).card≤1) :
    (∑ i∈F,(T i).card)≤(F.biUnion T).card+F.card.choose 2 := by
  have hall : ∀ G : Finset ι,
      (∀ i∈G,∀ j∈G,i≠j → ((T i)∩(T j)).card≤1) →
      (∑ i∈G,(T i).card)≤(G.biUnion T).card+G.card.choose 2 := by
    intro G
    induction G using Finset.induction_on with
    | empty => simp
    | @insert i G hi ih =>
      intro hp
      have hG : ∀ j∈G,∀ k∈G,j≠k → ((T j)∩(T k)).card≤1 := by
        intro j hj k hk hjk
        exact hp j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hjk
      have hind := ih hG
      have hcross : ((T i)∩G.biUnion T).card≤G.card := by
        have he : (T i)∩G.biUnion T=G.biUnion (fun j=>(T i)∩(T j)) := by
          ext x
          simp only [Finset.mem_inter,Finset.mem_biUnion]
          aesop
        rw [he]
        calc
          _≤∑ j∈G,((T i)∩(T j)).card := Finset.card_biUnion_le
          _≤∑ j∈G,1 := Finset.sum_le_sum (by
            intro j hj
            apply hp i (Finset.mem_insert_self i G) j (Finset.mem_insert_of_mem hj)
            intro heq
            exact hi (heq.symm ▸ hj))
          _=G.card := by simp
      have hU := Finset.card_union_add_card_inter (T i) (G.biUnion T)
      have hchoose : (G.card+1).choose 2=G.card.choose 2+G.card := by
        rw [Nat.choose_succ_succ]
        simp [Nat.add_comm]
      rw [Finset.sum_insert hi,Finset.biUnion_insert,Finset.card_insert_of_notMem hi,hchoose]
      omega
  exact hall F hpair

theorem actual_long_trace_capacity (Ω : Finset α) (F : Finset ι) (T : ι→Finset α)
    (p : ℕ) (hp : 0<p) (hN : p^2*(p+1)≤2*Ω.card)
    (hground : ∀ i∈F,T i⊆Ω)
    (hlong : ∀ i∈F,Ω.card<p*(T i).card)
    (hpair : ∀ i∈F,∀ j∈F,i≠j → ((T i)∩(T j)).card≤1) : F.card≤p := by
  by_contra hn
  obtain ⟨G,hGF,hGc⟩ := Finset.exists_subset_card_eq (show p+1≤F.card by omega)
  have hsum := trace_sum_bound G T (by
    intro i hi j hj hij
    exact hpair i (hGF hi) j (hGF hj) hij)
  have hsub : G.biUnion T⊆Ω := by
    intro x hx
    obtain ⟨i,hi,hx⟩ := Finset.mem_biUnion.mp hx
    exact hground i (hGF hi) hx
  have hupper : (∑ i∈G,(T i).card)≤Ω.card+(p+1).choose 2 := by
    have hu := Finset.card_le_card hsub
    rw [hGc] at hsum
    omega
  have hpoint : ∑ i∈G,(Ω.card+1)≤∑ i∈G,p*(T i).card :=
    Finset.sum_le_sum (by intro i hi;exact hlong i (hGF hi))
  simp only [Finset.sum_const,nsmul_eq_mul,←Finset.mul_sum,hGc] at hpoint
  have hmul := Nat.mul_le_mul_left p hupper
  have hpointR : ((p:ℝ)+1)*((Ω.card:ℝ)+1)≤(p:ℝ)*(∑ i∈G,((T i).card:ℝ)) := by
    exact_mod_cast hpoint
  have hmulR : (p:ℝ)*(∑ i∈G,((T i).card:ℝ))≤
      (p:ℝ)*((Ω.card:ℝ)+((p+1).choose 2:ℕ)) := by exact_mod_cast hmul
  rw [Nat.cast_choose_two] at hmulR
  push_cast at hmulR
  have hNR : (p:ℝ)^2*((p:ℝ)+1)≤2*(Ω.card:ℝ) := by exact_mod_cast hN
  have hpR : (0:ℝ)<p := by exact_mod_cast hp
  nlinarith only [hpointR,hmulR,hNR,hpR]

theorem actual_long_trace_capacity_cubic (Ω : Finset α) (F : Finset ι) (T : ι→Finset α)
    (p : ℕ) (hp : 0<p) (hN : p^3≤Ω.card)
    (hground : ∀ i∈F,T i⊆Ω)
    (hlong : ∀ i∈F,Ω.card<p*(T i).card)
    (hpair : ∀ i∈F,∀ j∈F,i≠j → ((T i)∩(T j)).card≤1) : F.card≤p := by
  apply actual_long_trace_capacity Ω F T p hp ?_ hground hlong hpair
  have hh := Nat.mul_le_mul_left (p^2) (show p+1≤2*p by omega)
  nlinarith only [hh,hN]

#print axioms trace_sum_bound
#print axioms actual_long_trace_capacity
#print axioms actual_long_trace_capacity_cubic
end
end JSP233.TracePacking43
