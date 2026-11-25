module

public import Erdos272.Counting.N82427.ThreeFiveEvents82427
public import Erdos272.Counting.N82427.ThreeFiveArithmetic82427
public import Erdos272.Resources.N118533.CorrelatedSource118533

@[expose] public section

namespace JSP233.ThreeFiveIndex82427
open StarCompletion APGeometry SourceBridge208 IntrinsicTriples208
open IndexedCorePairs200000 ActualCorePairs200000 PrimePairEvents200000 PrimePairResidue200000
open PairEventCount200000 PairUnionSieve200000 CoreUnionSource200000
open StarArithmetic158375 StarCore158375 StarArithmetic130000
open ThreeFiveEvents82427 ThreeFiveArithmetic82427
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

abbrev Q8 := CorrelatedSource118533.Primes

theorem selected_primes {a : ℕ} (ha : 45≤a) : Q8⊆AllPrimes a := by
  intro q hq
  have hp := (CorrelatedSource118533.primes_odd q hq).1
  have hlt : q<a := by
    simp only [Q8, CorrelatedSource118533.Primes, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, hp⟩

theorem half_weight_bound (a q : ℕ) (hq : 0<q) :
    (((a+1)/2)/q).choose 2≤Weight a q := by
  have h₁ : (a+1)/2≤a := by omega
  have h₂ : a≤a+q-1 := by omega
  exact Nat.choose_le_choose 2
    ((Nat.div_le_div_right h₁).trans (Nat.div_le_div_right h₂))

theorem even_payment {a h g : ℕ} {A I : Finset ℕ}
    (ha : 3≤a) (hh : 0<h) (h₂ : 2∣h)
    (hAP : A⊆Primes a h) (hIE : I⊆Inactive a h) (hnotI : 2∉I)
    (hpos : ∀ q∈A, 0<q) (hrec : (∑ q∈A, (1 : ℝ)/(q : ℝ))≤1)
    (hpart : (∑ q∈I, (a/(2*q)).choose 2)+(∑ q∈A, (a/(2*q)).choose 2)=Bonus Q8 a)
    (hreserve : (∑ q∈I, (((a+1)/2)/q).choose 2)+g≤∑ q∈I, Weight a q) :
    (ExceptionLength a h).choose 2+Bonus Q8 a+g≤
      Extra a h+Refund a h (ExceptionLength a h) := by
  let b := ExceptionLength a h
  have hi₂ := inactive_mem Nat.prime_two (by omega : 2<a) h₂
  have hsub : insert 2 I⊆Inactive a h := Finset.insert_subset_iff.mpr ⟨hi₂, hIE⟩
  have hExtra := Finset.sum_le_sum_of_subset hsub (f := Weight a)
  rw [Finset.sum_insert hnotI] at hExtra
  change Weight a 2+(∑ q∈I, Weight a q)≤Extra a h at hExtra
  have hbc : b≤(a+1)/2 := exception_le_ceiling (by omega : 0<a) hh Nat.prime_two h₂
  have hcontract := divided_choose_sum_contract hpos hrec hbc
  have hbonI : (∑ q∈I, (a/(2*q)).choose 2)≤∑ q∈I, (((a+1)/2)/q).choose 2 := by
    apply Finset.sum_le_sum
    intro q _
    simpa using Nat.choose_le_choose 2 (StarCore130000.divided_ceil_lower a 2 q (by decide))
  have hbonA : (∑ q∈A, (a/(2*q)).choose 2)≤∑ q∈A, (((a+1)/2)/q).choose 2 := by
    apply Finset.sum_le_sum
    intro q _
    simpa using Nat.choose_le_choose 2 (StarCore130000.divided_ceil_lower a 2 q (by decide))
  have hRI : (∑ q∈A, (b/q).choose 2)≤Refund a h b :=
    Finset.sum_le_sum_of_subset hAP
  change b.choose 2+(∑ q∈A, (((a+1)/2)/q).choose 2)≤
    Weight a 2+(∑ q∈A, (b/q).choose 2) at hcontract
  change b.choose 2+Bonus Q8 a+g≤Extra a h+Refund a h b
  omega

theorem chord_index_bound {a h l : ℕ} {ell : ℤ}
    (ha : 45≤a) (hh : 0<h) (hc : Int.gcd (h : ℤ) ell=1)
    (hu : (∑ q∈AllPrimes a, Weight a q)≤a.choose 2)
    (hlen : l+ExceptionLength a h≤a) :
    UnitBound a+Bonus Q8 a+ChordBonus a≤
      (GoodIndex a h ell (Finset.Ico l (l+ExceptionLength a h))).card := by
  let b := ExceptionLength a h
  let A := Q8∩Primes a h
  let I := Q8\A
  let E := BadEvent (Finset.range a) (Finset.Ico l (l+b)) h ell
  let J := ∑ q∈A, (E 2∩E q).card
  change UnitBound a+Bonus Q8 a+ChordBonus a≤
    (GoodIndex a h ell (Finset.Ico l (l+b))).card
  have hQa := selected_primes ha
  have hAQ : A⊆Q8 := Finset.inter_subset_left
  have hAP : A⊆Primes a h := Finset.inter_subset_right
  have hIQ : I⊆Q8 := Finset.sdiff_subset
  have hIE : I⊆Inactive a h := by
    intro q hq
    obtain ⟨hqQ, hqA⟩ := Finset.mem_sdiff.mp hq
    refine Finset.mem_sdiff.mpr ⟨hQa hqQ, ?_⟩
    intro hqP
    exact hqA (Finset.mem_inter.mpr ⟨hqQ, hqP⟩)
  have hposQ : ∀ q∈Q8, 0<q := fun q hq => (CorrelatedSource118533.primes_odd q hq).1.pos
  have hposA : ∀ q∈A, 0<q := fun q hq => hposQ q (hAQ hq)
  have hposI : ∀ q∈I, 0<q := fun q hq => hposQ q (hIQ hq)
  have hbaseI : ∀ q∈I, (a/(2*q)).choose 2≤Weight a q :=
    fun q hq => StarCore130000.bonus_le_weight a q (hposI q hq)
  have hnotI : 2∉I := fun hq => (CorrelatedSource118533.primes_odd 2 (hIQ hq)).2 rfl
  have hnotA : 2∉A := fun hq => (CorrelatedSource118533.primes_odd 2 (hAQ hq)).2 rfl
  have h₃Q : 3∈Q8 := by simp [Q8, CorrelatedSource118533.Primes]
  have h₅Q : 5∈Q8 := by simp [Q8, CorrelatedSource118533.Primes]
  have hpart := Finset.sum_sdiff hAQ (f := fun q => (a/(2*q)).choose 2)
  change (∑ q∈I, (a/(2*q)).choose 2)+(∑ q∈A, (a/(2*q)).choose 2)=Bonus Q8 a at hpart
  have hExtraI : (∑ q∈I, Weight a q)≤Extra a h := Finset.sum_le_sum_of_subset hIE
  have hbase := basic_bill hlen hc hu
  change UnitBound a+Extra a h+Refund a h b≤
    (GoodIndex a h ell (Finset.Ico l (l+b))).card+b.choose 2 at hbase
  by_cases h₂ : 2∣h
  · have hrecA := reciprocal_subset hAQ CorrelatedSource118533.reciprocal_cap
    have hweightI : ∀ q∈I, (((a+1)/2)/q).choose 2≤Weight a q :=
      fun q hq => half_weight_bound a q (hposI q hq)
    have hreserve₀ : (∑ q∈I, (((a+1)/2)/q).choose 2)+0≤∑ q∈I, Weight a q := by
      simpa only [add_zero] using Finset.sum_le_sum hweightI
    have hpay₀ := even_payment (g := 0) (by omega : 3≤a) hh h₂ hAP hIE hnotI
      hposA hrecA hpart hreserve₀
    change b.choose 2+Bonus Q8 a+0≤Extra a h+Refund a h b at hpay₀
    by_cases h₃ : 3∣h
    · have h₃I : 3∈I := by
        apply Finset.mem_sdiff.mpr
        refine ⟨h₃Q, ?_⟩
        intro hmem
        exact (Finset.mem_filter.mp (hAP hmem)).2.2 h₃
      have hr := sum_reserve (fun q => (((a+1)/2)/q).choose 2) (Weight a)
        (debt := ChordBonus a) (refund := 0) hweightI h₃I
        (by simpa only [add_zero] using even_inactive_extra a 3 (Or.inl rfl))
      have hp := even_payment (g := ChordBonus a) (by omega : 3≤a) hh h₂
        hAP hIE hnotI hposA hrecA hpart (by simpa only [add_zero] using hr)
      change b.choose 2+Bonus Q8 a+ChordBonus a≤Extra a h+Refund a h b at hp
      change UnitBound a+Bonus Q8 a+ChordBonus a≤_
      omega
    · by_cases h₅ : 5∣h
      · have h₅I : 5∈I := by
          apply Finset.mem_sdiff.mpr
          refine ⟨h₅Q, ?_⟩
          intro hmem
          exact (Finset.mem_filter.mp (hAP hmem)).2.2 h₅
        have hr := sum_reserve (fun q => (((a+1)/2)/q).choose 2) (Weight a)
          (debt := ChordBonus a) (refund := 0) hweightI h₅I
          (by simpa only [add_zero] using even_inactive_extra a 5 (Or.inr rfl))
        have hp := even_payment (g := ChordBonus a) (by omega : 3≤a) hh h₂
          hAP hIE hnotI hposA hrecA hpart (by simpa only [add_zero] using hr)
        change b.choose 2+Bonus Q8 a+ChordBonus a≤Extra a h+Refund a h b at hp
        change UnitBound a+Bonus Q8 a+ChordBonus a≤_
        omega
      · have ha₃ := active_mem (by decide : Nat.Prime 3) (by omega : 3<a) h₃
        have ha₅ := active_mem (by decide : Nat.Prime 5) (by omega : 5<a) h₅
        have hbill := enhanced_pair_bill hlen hc hu ha₃ ha₅ (by decide : (3 : ℕ)≠5)
        change UnitBound a+Extra a h+Refund a h b+(E 3∩E 5).card≤
          (GoodIndex a h ell (Finset.Ico l (l+b))).card+b.choose 2 at hbill
        have hint := three_five_lower (ell := ell) hlen h₃ h₅
        change (a/15).choose 2≤(E 3∩E 5).card+((b+14)/15).choose 2 at hint
        have hbc : b≤(a+1)/2 := exception_le_ceiling (by omega) hh Nat.prime_two h₂
        have hl : ((b+14)/15).choose 2≤(a/30+1).choose 2 :=
          Nat.choose_le_choose 2 (by omega)
        have hg := chord_bonus_add_den a
        change UnitBound a+Bonus Q8 a+ChordBonus a≤_
        omega
  · have ha₂ := active_mem Nat.prime_two (by omega : 2<a) h₂
    have hAe : A⊆(Primes a h).erase 2 := by
      intro q hq
      exact Finset.mem_erase.mpr
        ⟨(CorrelatedSource118533.primes_odd q (hAQ hq)).2, hAP hq⟩
    have hactive : (∑ q∈A, (a/(2*q)).choose 2)≤J+(∑ q∈A, PairLoss b q) := by
      have ht : ∀ q∈A, (a/(2*q)).choose 2≤(E 2∩E q).card+PairLoss b q := by
        intro q hq
        have hp := (Finset.mem_filter.mp (hAP hq)).2
        exact StarEvents130000.star_intersection_lower (ell := ell) hlen hp.1
          (CorrelatedSource118533.primes_odd q (hAQ hq)).2 h₂ hp.2
      have hs := Finset.sum_le_sum ht
      simpa only [Finset.sum_add_distrib, J] using hs
    have hrefund : (b/2).choose 2+(∑ q∈A, (b/q).choose 2)≤Refund a h b := by
      have hs := Finset.sum_le_sum_of_subset
        (Finset.insert_subset_iff.mpr ⟨ha₂, hAP⟩) (f := fun q => (b/q).choose 2)
      simpa only [Finset.sum_insert hnotA, Refund] using hs
    have hbill := StarCore130000.enhanced_bill hlen hc hu ha₂ hAe
    change UnitBound a+Extra a h+Refund a h b+J≤
      (GoodIndex a h ell (Finset.Ico l (l+b))).card+b.choose 2 at hbill
    by_cases h₃ : 3∣h
    · have h₃I : 3∈I := by
        apply Finset.mem_sdiff.mpr
        refine ⟨h₃Q, ?_⟩
        intro hmem
        exact (Finset.mem_filter.mp (hAP hmem)).2.2 h₃
      have hbc₃ : b≤(a+2)/3 :=
        exception_le_ceiling (by omega) hh (by decide : Nat.Prime 3) h₃
      by_cases h₅ : 5∣h
      · have h₅I : 5∈I := by
          apply Finset.mem_sdiff.mpr
          refine ⟨h₅Q, ?_⟩
          intro hmem
          exact (Finset.mem_filter.mp (hAP hmem)).2.2 h₅
        have h₃I' : 3∈I.erase 5 := Finset.mem_erase.mpr ⟨by decide, h₃I⟩
        have hplain := inactive_plain_payment (by decide : 0<(3 : ℕ)) hbc₃
        have hr := sum_reserve (fun q => (a/(2*q)).choose 2) (Weight a)
          (I := I.erase 5) (debt := b.choose 2) (refund := (b/2).choose 2)
          (fun q hq => hbaseI q (Finset.mem_erase.mp hq).2) h₃I'
          (by simpa [add_comm] using hplain)
        have hs₁ := Finset.sum_erase_add I (fun q => (a/(2*q)).choose 2) h₅I
        have hs₂ := Finset.sum_erase_add I (Weight a) h₅I
        have hfive := inactive_five_extra a
        have hLoss := sum_losses (b := b) hposA
        norm_num only [Nat.reduceMul] at hs₁
        change UnitBound a+Bonus Q8 a+ChordBonus a≤_
        omega
      · have ha₅ := active_mem (by decide : Nat.Prime 5) (by omega : 5<a) h₅
        have h₅A : 5∈A := Finset.mem_inter.mpr ⟨h₅Q, ha₅⟩
        have hpay := three_inactive_payment hbc₃
        have hr := sum_reserve (fun q => (a/(2*q)).choose 2) (Weight a)
          (I := I) (debt := b.choose 2+ChordBonus a+PairLoss b 5)
          (refund := (b/2).choose 2+(b/5).choose 2) hbaseI h₃I
          (by simpa only [pair_loss_five, Nat.reduceMul, add_assoc, add_left_comm, add_comm] using hpay)
        have hLoss := sum_losses_except (b := b) hposA h₅A
        have hs := Finset.sum_erase_add A (fun q => (b/q).choose 2) h₅A
        rw [pair_loss_five] at hr hLoss
        change UnitBound a+Bonus Q8 a+ChordBonus a≤_
        omega
    · have ha₃ := active_mem (by decide : Nat.Prime 3) (by omega : 3<a) h₃
      have h₃A : 3∈A := Finset.mem_inter.mpr ⟨h₃Q, ha₃⟩
      by_cases h₅ : 5∣h
      · have h₅I : 5∈I := by
          apply Finset.mem_sdiff.mpr
          refine ⟨h₅Q, ?_⟩
          intro hmem
          exact (Finset.mem_filter.mp (hAP hmem)).2.2 h₅
        have hbc₅ : b≤(a+4)/5 :=
          exception_le_ceiling (by omega) hh (by decide : Nat.Prime 5) h₅
        have hpay := five_inactive_payment hbc₅
        have hr := sum_reserve (fun q => (a/(2*q)).choose 2) (Weight a)
          (I := I) (debt := b.choose 2+ChordBonus a+PairLoss b 3)
          (refund := (b/2).choose 2+(b/3).choose 2) hbaseI h₅I
          (by simpa only [pair_loss_three, Nat.reduceMul, add_assoc, add_left_comm, add_comm] using hpay)
        have hLoss := sum_losses_except (b := b) hposA h₃A
        have hs := Finset.sum_erase_add A (fun q => (b/q).choose 2) h₃A
        rw [pair_loss_three] at hr hLoss
        change UnitBound a+Bonus Q8 a+ChordBonus a≤_
        omega
      · have ha₅ := active_mem (by decide : Nat.Prime 5) (by omega : 5<a) h₅
        have h₅A : 5∈A := Finset.mem_inter.mpr ⟨h₅Q, ha₅⟩
        have hpaid : ∃ r : ℕ,
            b.choose 2+(∑ q∈I, (a/(2*q)).choose 2)≤Extra a h+r ∧
            r+(∑ q∈A, (b/q).choose 2)≤Refund a h b := by
          by_cases hI : I.Nonempty
          · obtain ⟨p, hp⟩ := hI
            refine ⟨(b/2).choose 2,
              StarCore130000.inactive_bonus_payment (by omega) hh hIE hp, hrefund⟩
          · have hz : I=∅ := Finset.not_nonempty_iff_eq_empty.mp hI
            refine ⟨0, ?_, ?_⟩
            · simpa only [hz, Finset.sum_empty, add_zero, b] using
                StarCore130000.exception_choose_le_extra (by omega : 0<a) hh
            · simpa only [zero_add, Refund] using
                Finset.sum_le_sum_of_subset hAP (f := fun q => (b/q).choose 2)
        obtain ⟨r, hpay, href⟩ := hpaid
        have hdouble := sum_double_losses (b := b) hposA h₃A
        have hcBill := enhanced_chord_bill hlen hc hu ha₂ hAe h₃A h₅A
        change UnitBound a+Extra a h+Refund a h b+J+(E 3∩E 5).card≤
          (GoodIndex a h ell (Finset.Ico l (l+b))).card+b.choose 2+
            (E 2∩(E 3∩E 5)).card at hcBill
        have h35 := three_five_lower (ell := ell) hlen h₃ h₅
        change (a/15).choose 2≤(E 3∩E 5).card+((b+14)/15).choose 2 at h35
        have h235 := two_three_five_upper (ell := ell) hlen h₂ h₃ h₅
        change (E 2∩(E 3∩E 5)).card≤(a/30+1).choose 2 at h235
        have hg := chord_bonus_add_den a
        change UnitBound a+Bonus Q8 a+ChordBonus a≤_
        omega

#print axioms selected_primes
#print axioms half_weight_bound
#print axioms even_payment
#print axioms chord_index_bound
end
end JSP233.ThreeFiveIndex82427
