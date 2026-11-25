module

public import Erdos272.Counting.N20258.MatchedStarts20258
public import Erdos272.Counting.N20258.ProgressionPartition20258

@[expose] public section
namespace JSP233.MatchedTails20258
open StarCompletion PrivatePairExistence APCount41 APClasses88404
open ProgressionLengths20258 ProgressionTail20258 ProgressionPartition20258
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false

/-- Sum the disjoint missing starts on the actual lengths k+1 through K. -/
theorem step {N m d k K j L : ℕ} {F G : Finset (Finset ℤ)}
    (hN : 2 ≤ N) (hm : m+1 ≤ N) (hd : 0 < d) (hj : 0 < j)
    (hk : k ≤ K) (short : 2*j ≤ k+1) (wide : K+2*j ≤ (N-1)/d+2)
    (fits : (K-j)*m+j*j ≤ L)
    (legal : Legal (Ground N) F) (sub : G ⊆ CrookedMembers F) (many : L*(N-2) < G.card)
    (omits : ∀ x ∈ Ground N, ∃ Q ∈ CrookedMembers F, x ∉ Q ∧ Q.card ≤ m)
    (hmin : ∀ S ∈ StepAP F d, k < S.card) :
    (StepAP F d).card + (K-k)*j ≤ tail ((N-1)/d) k := by
  let M := max N K
  let I := Finset.Ioc k M
  let B := Finset.Ioc k K
  let c (t : ℕ) := ((StepAP F d).filter (fun S => S.card=t)).card
  have incl : B ⊆ I := fun t ht => Finset.mem_Ioc.mpr
    ⟨(Finset.mem_Ioc.mp ht).1,(Finset.mem_Ioc.mp ht).2.trans (le_max_right _ _)⟩
  have posN : 1 ≤ N := by omega
  have lengths : ∀ S ∈ StepAP F d, S.card ∈ I := by
    intro S hS
    have le := Finset.card_le_card (legal.1 S (APClasses88404.subset F d hS))
    rw [ground_card] at le
    exact Finset.mem_Ioc.mpr ⟨hmin S hS,le.trans (le_max_left _ _)⟩
  have count : (StepAP F d).card = ∑ t ∈ I, c t := Finset.card_eq_sum_card_fiberwise lengths
  have bound : (∑ t ∈ I, (c t + if t ∈ B then j else 0)) ≤
      ∑ t ∈ I, starts ((N-1)/d) t := by
    apply Finset.sum_le_sum
    intro t _
    by_cases hit : t ∈ B
    · rw [ite_eq_left hit]
      obtain ⟨low,high⟩ := Finset.mem_Ioc.mp hit
      exact MatchedStarts20258.actual_layer hN hm hd hj (by omega) (by omega)
        ((Nat.add_le_add_right (Nat.mul_le_mul_right m (Nat.sub_le_sub_right high j)) _).trans fits)
        legal sub many omits
    · rw [ite_eq_right hit,Nat.add_zero]
      exact actual_length posN hd legal
  have paid : (∑ t ∈ I, if t ∈ B then j else 0) = (K-k)*j := by
    rw [←Finset.sum_filter]
    have eqn : I.filter (fun t => t ∈ B) = B := by
      ext t
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2,fun h => ⟨incl h,h⟩⟩
    rw [eqn]
    simp [B]
  have rest := sum_lengths (q := (N-1)/d) (k := k) (n := M) (hk.trans (le_max_right _ _))
  rw [Finset.sum_add_distrib,paid,←count] at bound
  change (∑ t ∈ I, starts ((N-1)/d) t) + _ = _ at rest
  omega

/-- The whole AP count with a credit on an arbitrary set of unpriced real strides. -/
theorem partition {N m k K j L : ℕ} {F G : Finset (Finset ℤ)}
    (hN : 2 ≤ N) (hm : m+1 ≤ N) (hj : 0 < j) (hk : k ≤ K) (short : 2*j ≤ k+1)
    (fits : (K-j)*m+j*j ≤ L) (kept paid : Finset ℕ)
    (keptIn : kept ⊆ Finset.Icc 1 (N-1)) (paidIn : paid ⊆ Finset.Icc 1 (N-1) \ kept)
    (wide : ∀ d ∈ paid, K+2*j ≤ (N-1)/d+2)
    (legal : Legal (Ground N) F) (sub : G ⊆ CrookedMembers F) (many : L*(N-2) < G.card)
    (omits : ∀ x ∈ Ground N, ∃ Q ∈ CrookedMembers F, x ∉ Q ∧ Q.card ≤ m)
    (hmin : ∀ d ∈ Finset.Icc 1 (N-1) \ kept, ∀ S ∈ StepAP F d, k < S.card) :
    (F.filter IsAP).card + paid.card*((K-k)*j) ≤
      1 + (∑ d ∈ kept, (StepAP F d).card) + offTail (N-1) k kept := by
  let A := Finset.Icc 1 (N-1)
  let off := A \ kept
  have posN : 1 ≤ N := by omega
  have bound := actual_AP_partition (k := k) posN legal (Finset.Icc 1 (N-1)) (by rfl)
    (by intro d h; simp at h)
  simp only [offTail,Finset.sdiff_self,Finset.sum_empty,Nat.add_zero] at bound
  have sum := Finset.sum_sdiff (f := fun d => (StepAP F d).card) keptIn
  have limit : (∑ d ∈ off, ((StepAP F d).card + if d ∈ paid then (K-k)*j else 0))
      ≤ offTail (N-1) k kept := by
    apply Finset.sum_le_sum
    intro d hd
    have hdpos := (Finset.mem_Icc.mp (Finset.mem_sdiff.mp hd).1).1
    by_cases hit : d ∈ paid
    · rw [ite_eq_left hit]
      exact step hN hm hdpos hj hk short (wide d hit) fits legal sub many omits (hmin d hd)
    · rw [ite_eq_right hit,Nat.add_zero]
      exact actual_step_tail posN hdpos legal (hmin d hd)
  have credit : (∑ d ∈ off, if d ∈ paid then (K-k)*j else 0) = paid.card*((K-k)*j) := by
    rw [←Finset.sum_filter]
    have eqn : off.filter (fun d => d ∈ paid) = paid := by
      ext d
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2,fun h => ⟨paidIn h,h⟩⟩
    simp [eqn]
  change (∑ d ∈ off, (StepAP F d).card) + _ = ∑ d ∈ A, (StepAP F d).card at sum
  change (F.filter IsAP).card ≤ 1 + ∑ d ∈ A, (StepAP F d).card at bound
  rw [Finset.sum_add_distrib] at limit
  rw [credit] at limit
  omega

#print axioms partition
end
end JSP233.MatchedTails20258
