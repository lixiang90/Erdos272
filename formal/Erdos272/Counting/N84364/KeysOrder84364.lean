module

public import Erdos272.Resources.SharpSmall212

@[expose] public section

namespace JSP233.KeysOrder84364
open StarCompletion SparseSmall39 SharpSmall212
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Before (A : Finset ℤ) (x : ℤ) (upper : Bool) : Finset ℤ :=
  A.filter (fun y => ¬Order upper x y)

theorem before_false (A : Finset ℤ) (x : ℤ) : Before A x false=Earlier A x := by
  ext y
  simp [Before, Order, Earlier]

theorem before_true (A : Finset ℤ) (x : ℤ) :
    Before A x true=A.filter (fun y => x<y) := by
  ext y
  simp [Before, Order]

theorem before_card_pair {A : Finset ℤ} {x : ℤ} (hx : x∈A) :
    (Before A x false).card+(Before A x true).card+1=A.card := by
  have hxB : x∉Before A x true := by simp [Before, Order]
  have hdis : Disjoint (Before A x false) (insert x (Before A x true)) := by
    apply Finset.disjoint_left.mpr
    intro y hyL hyR
    have hyx : y<x := by simpa only [Before, Order, Bool.false_eq_true, ↓reduceIte,
      Finset.mem_filter, not_le] using (Finset.mem_filter.mp hyL).2
    rcases Finset.mem_insert.mp hyR with he | hyR
    · omega
    · have hxy : x<y := by
        simpa only [Order, ↓reduceIte, not_le] using (Finset.mem_filter.mp hyR).2
      omega
  have hu : Before A x false∪insert x (Before A x true)=A := by
    ext y
    constructor
    · intro hy
      rcases Finset.mem_union.mp hy with hy | hy
      · exact (Finset.mem_filter.mp hy).1
      · rcases Finset.mem_insert.mp hy with he | hy
        · rwa [he]
        · exact (Finset.mem_filter.mp hy).1
    · intro hy
      by_cases he : y=x
      · exact Finset.mem_union_right _ (Finset.mem_insert.mpr (Or.inl he))
      by_cases hlt : y<x
      · apply Finset.mem_union_left
        exact Finset.mem_filter.mpr ⟨hy, by simpa [Order] using (not_le.mpr hlt)⟩
      · apply Finset.mem_union_right
        apply Finset.mem_insert_of_mem
        exact Finset.mem_filter.mpr ⟨hy, by simp only [Order, ↓reduceIte]; omega⟩
  have hh := Finset.card_union_of_disjoint hdis
  rw [hu, Finset.card_insert_of_notMem hxB] at hh
  omega

#print axioms before_false
#print axioms before_true
#print axioms before_card_pair
end
end JSP233.KeysOrder84364
