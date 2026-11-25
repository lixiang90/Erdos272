module

public import Erdos272.Counting.N20258.IntervalGap20258
public import Erdos272.Counting.N20258.ProgressionPartition20258
public import Erdos272.Arithmetic.N20258.StrideQuotients20258

@[expose] public section
namespace JSP233.IntervalGapTails20258
open StarCompletion PrivatePairExistence APClasses88404 ProgressionLengths20258
open ProgressionTail20258 ProgressionPartition20258
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false

/-- The length and missing-interval bounds apply to the same progression class. -/
def cost (q m L k : ℕ) : ℕ :=
  min (tail q k) ((IntervalGapBounds20258.limit (q+1) m L)/4).toNat

def grouped (n split m L k : ℕ) (kept : Finset ℕ) : ℕ :=
  StrideQuotients20258.grouped n split (fun q => cost q m L k) -
    ∑ d ∈ kept, cost (n/d) m L k

theorem grouped_eq {n split m L k : ℕ} {kept : Finset ℕ}
    (small : split ≤ n) (inside : kept ⊆ Finset.Icc 1 n) :
    grouped n split m L k kept = ∑ d ∈ Finset.Icc 1 n \ kept, cost (n/d) m L k := by
  unfold grouped
  rw [StrideQuotients20258.grouped_eq n split small]
  have h := Finset.sum_sdiff (f := fun d => cost (n/d) m L k) inside
  omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
/-- The high-count tail in the central size-46 case at the target ground. -/
theorem central46_at_target : grouped 20257 142 46 2054 45 {1} = 65378492 := by decide +kernel

theorem partition {N m L k : ℕ} {F G : Finset (Finset ℤ)}
    (hN : 3 ≤ N) (hm : 0 < m) (room : m+1 ≤ N) (level : m ≤ L)
    (cut : (m-1)*k+1 ≤ L) (kept : Finset ℕ) (keptIn : kept ⊆ Finset.Icc 1 (N-1))
    (legal : Legal (Ground N) F) (sub : G ⊆ CrookedMembers F) (many : L*(N-2) < G.card)
    (omits : ∀ x ∈ Ground N, ∃ T ∈ CrookedMembers F, x ∉ T ∧ T.card ≤ m) :
    (F.filter IsAP).card ≤ 1 + (∑ d ∈ kept, (StepAP F d).card) +
      ∑ d ∈ Finset.Icc 1 (N-1) \ kept, cost ((N-1)/d) m L k := by
  let A := Finset.Icc 1 (N-1)
  have all := actual_AP_partition (k := k) (by omega : 1 ≤ N) legal A (by rfl)
    (by intro d h; simp [A] at h)
  simp only [offTail,A,Finset.sdiff_self,Finset.sum_empty,Nat.add_zero] at all
  have member (x : ℤ) (hx : x ∈ Ground N) : ∃ T ∈ F, x ∉ T ∧ T.card ≤ m := by
    obtain ⟨T,hT,miss,small⟩ := omits x hx
    exact ⟨T,(Finset.mem_filter.mp hT).1,miss,small⟩
  have sum : (∑ d ∈ A \ kept, (StepAP F d).card) ≤ ∑ d ∈ A \ kept, cost ((N-1)/d) m L k := by
    apply Finset.sum_le_sum
    intro d hd
    have dpos := (Finset.mem_Icc.mp (Finset.mem_sdiff.mp hd).1).1
    apply le_min
    · apply actual_step_tail (by omega) dpos legal
      intro P hp
      by_contra! small
      have bound := TwoTransversals20258.actual_short_member (by omega : 2 ≤ N) room
        legal (subset F d hp) (is_ap hp) omits
      have price : (m-1)*P.card+1 ≤ L := (Nat.add_le_add_right (Nat.mul_le_mul_left _ small) 1).trans cut
      exact (Nat.not_le_of_lt many)
        (((Finset.card_le_card sub).trans bound).trans (Nat.mul_le_mul_right _ price))
    · have limit := IntervalGap20258.actual_limit hN hm room dpos level legal sub many member
      omega
  have split := Finset.sum_sdiff (f := fun d => (StepAP F d).card) keptIn
  change (∑ d ∈ A \ kept, (StepAP F d).card) + _ = ∑ d ∈ A, (StepAP F d).card at split
  change (F.filter IsAP).card ≤ 1 + ∑ d ∈ A, (StepAP F d).card at all
  change (F.filter IsAP).card ≤ 1 + _ + ∑ d ∈ A \ kept, cost ((N-1)/d) m L k
  omega

#print axioms partition
#print axioms central46_at_target
end
end JSP233.IntervalGapTails20258
