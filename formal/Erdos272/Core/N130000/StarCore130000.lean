module

public import Erdos272.Counting.N130000.StarEvents130000
public import Erdos272.Counting.N158375.StarActual158375

@[expose] public section

namespace JSP233.StarCore130000
open StarCompletion APGeometry SourceBridge208 IntrinsicTriples208
open IndexedCorePairs200000 ActualCorePairs200000 PrimePairEvents200000 PrimePairResidue200000
open PairEventCount200000 PairUnionSieve200000 CoreUnionSource200000
open StarArithmetic158375 StarCore158375 StarArithmetic130000
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem divided_ceil_lower (a p q : ℕ) (hp : 0 < p) :
    a/(p*q) ≤ ((a+p-1)/p)/q := by
  have hh : a/p ≤ (a+p-1)/p := Nat.div_le_div_right (by omega)
  simpa only [Nat.div_div_eq_div_mul] using (Nat.div_le_div_right hh :
    (a/p)/q ≤ ((a+p-1)/p)/q)

theorem bonus_le_weight (a q : ℕ) (hq : 0 < q) :
    (a/(2*q)).choose 2 ≤ Weight a q := by
  have hdiv : a/(2*q) ≤ a/q := Nat.div_le_div_left (by omega) hq
  have hc : a/q ≤ (a+q-1)/q := Nat.div_le_div_right (by omega)
  exact Nat.choose_le_choose 2 (hdiv.trans hc)

theorem exception_choose_le_extra {a h : ℕ} (ha : 0 < a) (hh : 0 < h) :
    (ExceptionLength a h).choose 2 ≤ Extra a h := by
  by_cases hone : h = 1
  · simp [ExceptionLength, hone]
  · let p := h.minFac
    have hp : p.Prime := Nat.minFac_prime hone
    have hpd : p ∣ h := Nat.minFac_dvd h
    by_cases hpa : p < a
    · have hb := exception_le_ceiling ha hh hp hpd
      exact (Nat.choose_le_choose 2 hb).trans (extra_single (inactive_mem hp hpa hpd))
    · have hb := exception_le_ceiling ha hh hp hpd
      have hbc : ExceptionLength a h ≤ 1 := hb.trans (ceil_le_one hp.pos (by omega))
      have hz : (ExceptionLength a h).choose 2 = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp only [hz, Nat.zero_le]

theorem enhanced_bill {Q : Finset ℕ} {a b l h : ℕ} {ell : ℤ}
    (hlen : l+b ≤ a) (hc : Int.gcd (h : ℤ) ell = 1)
    (hu : (∑ q ∈ AllPrimes a, Weight a q) ≤ a.choose 2)
    (h₂ : 2 ∈ Primes a h) (hQ : Q ⊆ (Primes a h).erase 2) :
    UnitBound a+Extra a h+Refund a h b+
      (∑ q ∈ Q,
        ((BadEvent (Finset.range a) (Finset.Ico l (l+b)) h ell 2) ∩
          (BadEvent (Finset.range a) (Finset.Ico l (l+b)) h ell q)).card) ≤
      (GoodIndex a h ell (Finset.Ico l (l+b))).card+b.choose 2 := by
  have hf := StarEvents130000.primitive_star_bill hlen hc h₂ hQ
  have ha := Nat.sub_add_cancel hu
  have hsum := Finset.sum_sdiff (active_primes_subset a h) (f := Weight a)
  change Extra a h+(∑ q ∈ Primes a h, Weight a q) = _ at hsum
  unfold UnitBound Refund
  omega

theorem inactive_bonus_payment {I : Finset ℕ} {a h p : ℕ}
    (ha : 0 < a) (hh : 0 < h) (hI : I ⊆ Inactive a h) (hpI : p ∈ I) :
    (ExceptionLength a h).choose 2+(∑ q ∈ I, (a/(2*q)).choose 2) ≤
      Extra a h+((ExceptionLength a h)/2).choose 2 := by
  have hpInactive := Finset.mem_sdiff.mp (hI hpI)
  have hpPrime := (Finset.mem_filter.mp hpInactive.1).2
  have hpDiv : p ∣ h := by
    by_contra hn
    exact hpInactive.2 (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hpInactive.1).1, hpPrime, hn⟩)
  have hbc := exception_le_ceiling ha hh hpPrime hpDiv
  have hcontract := divided_choose_contract (k := 2) (by decide) hbc
  have hbonus := Nat.choose_le_choose 2 (divided_ceil_lower a p 2 hpPrime.pos)
  have hbonus' : (a/(2*p)).choose 2 ≤ (((a+p-1)/p)/2).choose 2 := by
    simpa only [Nat.mul_comm] using hbonus
  have hselected : (ExceptionLength a h).choose 2+(a/(2*p)).choose 2 ≤
      Weight a p+((ExceptionLength a h)/2).choose 2 := by
    unfold Weight
    omega
  have hrest : (∑ q ∈ I.erase p, (a/(2*q)).choose 2) ≤
      ∑ q ∈ I.erase p, Weight a q := by
    apply Finset.sum_le_sum
    intro q hq
    have hmem := Finset.mem_sdiff.mp (hI (Finset.mem_erase.mp hq).2)
    exact bonus_le_weight a q (Finset.mem_filter.mp hmem.1).2.pos
  have hex : (∑ q ∈ I, Weight a q) ≤ Extra a h := Finset.sum_le_sum_of_subset hI
  have hsumB := Finset.sum_erase_add I (fun q => (a/(2*q)).choose 2) hpI
  have hsumW := Finset.sum_erase_add I (Weight a) hpI
  omega

theorem star_index_bound {Q : Finset ℕ} {a h l : ℕ} {ell : ℤ}
    (ha : 12 ≤ a) (hh : 0 < h) (hc : Int.gcd (h : ℤ) ell = 1)
    (hu : (∑ q ∈ AllPrimes a, Weight a q) ≤ a.choose 2)
    (hQa : Q ⊆ AllPrimes a) (hodd : ∀ q ∈ Q, q ≠ 2)
    (hrec : (∑ q ∈ Q, (1 : ℝ)/(q : ℝ)) ≤ 1)
    (hlen : l+ExceptionLength a h ≤ a) :
    UnitBound a+Bonus Q a ≤
      (GoodIndex a h ell (Finset.Ico l (l+ExceptionLength a h))).card := by
  let b := ExceptionLength a h
  let A := Q ∩ Primes a h
  let I := Q \ A
  have hAQ : A ⊆ Q := Finset.inter_subset_left
  have hAP : A ⊆ Primes a h := Finset.inter_subset_right
  have hIQ : I ⊆ Q := Finset.sdiff_subset
  have hIE : I ⊆ Inactive a h := by
    intro q hq
    obtain ⟨hqQ, hqA⟩ := Finset.mem_sdiff.mp hq
    refine Finset.mem_sdiff.mpr ⟨hQa hqQ, ?_⟩
    intro hqP
    exact hqA (Finset.mem_inter.mpr ⟨hqQ, hqP⟩)
  have hpos : ∀ q ∈ Q, 0 < q := fun q hq => (Finset.mem_filter.mp (hQa hq)).2.pos
  have hpart := Finset.sum_sdiff hAQ (f := fun q => (a/(2*q)).choose 2)
  change (∑ q ∈ I, (a/(2*q)).choose 2)+(∑ q ∈ A, (a/(2*q)).choose 2) = Bonus Q a at hpart
  have hRI : (∑ q ∈ A, (b/q).choose 2) ≤ Refund a h b := Finset.sum_le_sum_of_subset hAP
  have hWI : (∑ q ∈ I, (a/(2*q)).choose 2) ≤ ∑ q ∈ I, Weight a q := by
    exact Finset.sum_le_sum (fun q hq => bonus_le_weight a q (hpos q (hIQ hq)))
  by_cases h₂ : 2 ∣ h
  · have hi₂ := inactive_mem Nat.prime_two (by omega : 2 < a) h₂
    have hnotI : 2 ∉ I := fun hn => hodd 2 (hIQ hn) rfl
    have hsub : insert 2 I ⊆ Inactive a h := Finset.insert_subset_iff.mpr ⟨hi₂, hIE⟩
    have hExtra := Finset.sum_le_sum_of_subset hsub (f := Weight a)
    rw [Finset.sum_insert hnotI] at hExtra
    change Weight a 2+(∑ q ∈ I, Weight a q) ≤ Extra a h at hExtra
    have hbc : b ≤ (a+1)/2 := by
      simpa [b] using exception_le_ceiling (by omega : 0 < a) hh Nat.prime_two h₂
    have hcontract := divided_choose_sum_contract
      (fun q hq => hpos q (hAQ hq)) (reciprocal_subset hAQ hrec) hbc
    have hbon : (∑ q ∈ A, (a/(2*q)).choose 2) ≤
        ∑ q ∈ A, (((a+1)/2)/q).choose 2 := by
      apply Finset.sum_le_sum
      intro q _
      simpa using Nat.choose_le_choose 2 (divided_ceil_lower a 2 q (by decide))
    have hbase := basic_bill hlen hc hu
    change UnitBound a+Extra a h+Refund a h b ≤
      (GoodIndex a h ell (Finset.Ico l (l+b))).card+b.choose 2 at hbase
    change b.choose 2+_ ≤ Weight a 2+_ at hcontract
    change UnitBound a+Bonus Q a ≤ (GoodIndex a h ell (Finset.Ico l (l+b))).card
    omega
  · have ha₂ := active_mem Nat.prime_two (by omega : 2 < a) h₂
    have hAe : A ⊆ (Primes a h).erase 2 := by
      intro q hq
      exact Finset.mem_erase.mpr ⟨hodd q (hAQ hq), hAP hq⟩
    let J := ∑ q ∈ A,
      ((BadEvent (Finset.range a) (Finset.Ico l (l+b)) h ell 2) ∩
        (BadEvent (Finset.range a) (Finset.Ico l (l+b)) h ell q)).card
    have hactive : (∑ q ∈ A, (a/(2*q)).choose 2) ≤ J+(∑ q ∈ A, (b/q).choose 2) := by
      have ht : ∀ q ∈ A, (a/(2*q)).choose 2 ≤
          ((BadEvent (Finset.range a) (Finset.Ico l (l+b)) h ell 2) ∩
            (BadEvent (Finset.range a) (Finset.Ico l (l+b)) h ell q)).card+(b/q).choose 2 := by
        intro q hq
        have hp := (Finset.mem_filter.mp (hAP hq)).2
        have hstar := StarEvents130000.star_intersection_lower (ell := ell) hlen hp.1
          (hodd q (hAQ hq)) h₂ hp.2
        have hhalf := half_loss b q hp.1.pos
        exact hstar.trans (Nat.add_le_add_left hhalf _)
      have hs := Finset.sum_le_sum ht
      simpa only [Finset.sum_add_distrib, J] using hs
    have hpaid : ∃ r : ℕ,
        b.choose 2+(∑ q ∈ I, (a/(2*q)).choose 2) ≤ Extra a h+r ∧
        r+(∑ q ∈ A, (b/q).choose 2) ≤ Refund a h b := by
      by_cases hI : I.Nonempty
      · obtain ⟨p, hp⟩ := hI
        refine ⟨(b/2).choose 2, inactive_bonus_payment (by omega) hh hIE hp, ?_⟩
        have hnotA : 2 ∉ A := fun hn => hodd 2 (hAQ hn) rfl
        have hsub : insert 2 A ⊆ Primes a h := Finset.insert_subset_iff.mpr ⟨ha₂, hAP⟩
        have hs := Finset.sum_le_sum_of_subset hsub (f := fun q => (b/q).choose 2)
        simpa only [Finset.sum_insert hnotA, Refund] using hs
      · have hzero : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hI
        refine ⟨0, ?_, ?_⟩
        · simpa only [hzero, Finset.sum_empty, add_zero, b] using
            exception_choose_le_extra (by omega : 0 < a) hh
        · simpa only [zero_add] using hRI
    obtain ⟨r, hpay, hrefund⟩ := hpaid
    have hbill := enhanced_bill hlen hc hu ha₂ hAe
    change UnitBound a+Extra a h+Refund a h b+J ≤
      (GoodIndex a h ell (Finset.Ico l (l+b))).card+b.choose 2 at hbill
    change UnitBound a+Bonus Q a ≤ (GoodIndex a h ell (Finset.Ico l (l+b))).card
    omega

theorem actual_finite_star_source {N : ℕ} {S : Finset ℤ} (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, q.Prime ∧ q ≠ 2)
    (hrec : (∑ q ∈ Q, (1 : ℝ)/(q : ℝ)) ≤ 1)
    (hN : N ≤ 2^18) (hground : S ⊆ Ground N) (hS : 2 ≤ S.card)
    (ha : 12 ≤ MaxAPSize S) :
    Defect S*(UnitBound (MaxAPSize S)+Bonus Q (MaxAPSize S)) ≤ (Pool S).card := by
  have hcard : S.card ≤ N := by simpa only [ground_card] using Finset.card_le_card hground
  have hmax : MaxAPSize S ≤ 2^18 := (maxAPSize_le_card S).trans (hcard.trans hN)
  let Qa := Q.filter (fun q => q < MaxAPSize S)
  have hsub : Qa ⊆ Q := Finset.filter_subset _ _
  have hQa : Qa ⊆ AllPrimes (MaxAPSize S) := by
    intro q hq
    obtain ⟨hqQ, hqa⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hqa, (hQ q hqQ).1⟩
  have hbonus : Bonus Qa (MaxAPSize S) = Bonus Q (MaxAPSize S) :=
    bonus_filter (fun q hq => (hQ q hq).1.pos)
  rw [← hbonus]
  apply actual_defect_source_of_index_bound hS
  intro h hh ell hc l hlen
  exact star_index_bound ha hh hc (StarActual158375.weights_le_choose ha hmax) hQa
    (fun q hq => (hQ q (hsub hq)).2) (reciprocal_subset hsub hrec) hlen

theorem actual_two_star_source {N : ℕ} {S : Finset ℤ}
    (hN : N ≤ 2^18) (hground : S ⊆ Ground N) (hS : 2 ≤ S.card)
    (ha : 12 ≤ MaxAPSize S) :
    Defect S*(UnitBound (MaxAPSize S)+(MaxAPSize S/6).choose 2+
      (MaxAPSize S/10).choose 2) ≤ (Pool S).card := by
  have hQ : ∀ q ∈ ({3, 5} : Finset ℕ), q.Prime ∧ q ≠ 2 := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl <;> decide
  have hrec : (∑ q ∈ ({3, 5} : Finset ℕ), (1 : ℝ)/(q : ℝ)) ≤ 1 := by norm_num
  have hs := actual_finite_star_source {3, 5} hQ hrec hN hground hS ha
  simpa [Bonus, add_assoc] using hs

#print axioms divided_ceil_lower
#print axioms bonus_le_weight
#print axioms exception_choose_le_extra
#print axioms enhanced_bill
#print axioms inactive_bonus_payment
#print axioms star_index_bound
#print axioms actual_finite_star_source
#print axioms actual_two_star_source
end
end JSP233.StarCore130000
