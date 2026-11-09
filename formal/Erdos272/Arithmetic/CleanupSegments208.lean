module

public import Erdos272.Arithmetic.CleanupEval208

@[expose] public section

namespace JSP233.CleanupSegments208
open CleanupEval208
open scoped BigOperators
set_option maxHeartbeats 0

theorem range_append {f : ℕ → ℕ} {start n m a b : ℕ}
    (ha : a=∑ k∈Finset.range n,f (start+k))
    (hb : b=∑ k∈Finset.range m,f (start+n+k)) :
    a+b=∑ k∈Finset.range (n+m),f (start+k) := by
  rw [Finset.sum_range_add,ha,hb]
  simp only [Nat.add_assoc]

theorem append {r : Row} {start n m : ℕ} {a b : Totals}
    (ha : ChunkFacts r start n a) (hb : ChunkFacts r (start+n) m b) :
    ChunkFacts r start (n+m) (add a b) := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro k hk
    by_cases hl : k<n
    · exact ha.good k hl
    · have hr : k-n<m := by omega
      have hh := hb.good (k-n) hr
      have he : start+n+(k-n)=start+k := by omega
      simpa only [he] using hh
  · exact range_append (f:=fun d=>(step r d).totals.first) ha.first_eq hb.first_eq
  · exact range_append (f:=fun d=>(step r d).totals.second) ha.second_eq hb.second_eq
  · exact range_append (f:=fun d=>(step r d).totals.credit) ha.credit_eq hb.credit_eq
  · exact range_append (f:=fun d=>(step r d).totals.net) ha.net_eq hb.net_eq
  · exact range_append (f:=fun d=>(step r d).totals.light) ha.light_eq hb.light_eq

theorem append_exact {r : Row} {start middle n m total : ℕ} {a b expected : Totals}
    (ha : ChunkFacts r start n a) (hb : ChunkFacts r middle m b)
    (hs : start+n=middle) (hn : n+m=total) (he : add a b=expected) :
    ChunkFacts r start total expected := by
  subst middle total expected
  exact append ha hb

#print axioms append
#print axioms append_exact
end JSP233.CleanupSegments208
