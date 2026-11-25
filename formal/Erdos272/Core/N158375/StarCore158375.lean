module

public import Erdos272.Counting.N158375.StarEvents158375

@[expose] public section

namespace JSP233.StarCore158375
open StarCompletion APGeometry SourceBridge208 IntrinsicTriples208
open IndexedCorePairs200000 PrimePairEvents200000 PrimePairResidue200000
open PairEventCount200000 PairUnionSieve200000 CoreUnionSource200000
open StarArithmetic158375 StarEvents158375
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Inactive (a h : ℕ) := AllPrimes a \ Primes a h
def Extra (a h : ℕ) := ∑ q ∈ Inactive a h, Weight a q
def Refund (a h b : ℕ) := ∑ q ∈ Primes a h, (b/q).choose 2

theorem inactive_mem {a h p : ℕ} (hp : p.Prime) (hpa : p < a) (hph : p ∣ h) :
    p ∈ Inactive a h := by
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hpa, hp⟩, ?_⟩
  intro hn
  exact (Finset.mem_filter.mp hn).2.2 hph

theorem active_mem {a h p : ℕ} (hp : p.Prime) (hpa : p < a) (hph : ¬p ∣ h) :
    p ∈ Primes a h := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hpa, hp, hph⟩

theorem extra_single {a h p : ℕ} (hp : p ∈ Inactive a h) : Weight a p ≤ Extra a h := by
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hp

theorem extra_pair {a h p q : ℕ} (hp : p ∈ Inactive a h) (hq : q ∈ Inactive a h)
    (hne : p ≠ q) : Weight a p+Weight a q ≤ Extra a h := by
  have hs : ({p,q} : Finset ℕ) ⊆ Inactive a h := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hb := Finset.sum_le_sum_of_subset hs (f := Weight a)
  simpa [hne, Extra] using hb

theorem refund_single {a h b p : ℕ} (hp : p ∈ Primes a h) : (b/p).choose 2 ≤ Refund a h b := by
  unfold Refund
  exact Finset.single_le_sum (f := fun q => (b/q).choose 2) (fun _ _ => Nat.zero_le _) hp

theorem basic_bill {a b l h : ℕ} {ell : ℤ}
    (hlen : l+b ≤ a) (hc : Int.gcd (h:ℤ) ell = 1)
    (hu : (∑ q ∈ AllPrimes a, Weight a q) ≤ a.choose 2) :
    UnitBound a+Extra a h+Refund a h b ≤
      (GoodIndex a h ell (Finset.Ico l (l+b))).card+b.choose 2 := by
  have hf := first_order_sieve hlen hc
  have hs : (∑ q ∈ Primes a h, (Weight a q-(b/q).choose 2))+
      Refund a h b = ∑ q ∈ Primes a h, Weight a q := by
    unfold Refund
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q hq
    have hpos := (Finset.mem_filter.mp hq).2.1.two_le
    have hb : (b/q).choose 2 ≤ Weight a q :=
      Nat.choose_le_choose 2 (Nat.div_le_div_right (by omega))
    exact Nat.sub_add_cancel hb
  have ha := Nat.sub_add_cancel hu
  have hsum := Finset.sum_sdiff (active_primes_subset a h) (f := Weight a)
  have hbc := Nat.choose_le_choose 2 (show b ≤ a by omega)
  unfold FirstBound at hf
  change a.choose 2-b.choose 2-
    (∑ q ∈ Primes a h, (Weight a q-(b/q).choose 2)) ≤
      (GoodIndex a h ell (Finset.Ico l (l+b))).card at hf
  change a.choose 2-(∑ q ∈ AllPrimes a, Weight a q)+_ = _ at ha
  change Extra a h+(∑ q ∈ Primes a h, Weight a q) = _ at hsum
  unfold UnitBound
  omega

theorem enhanced_bill {a b l h : ℕ} {ell : ℤ}
    (hlen : l+b ≤ a) (hc : Int.gcd (h:ℤ) ell = 1)
    (hu : (∑ q ∈ AllPrimes a, Weight a q) ≤ a.choose 2)
    (h₂ : 2 ∈ Primes a h) (h₃ : 3 ∈ Primes a h) :
    UnitBound a+Extra a h+Refund a h b+
      ((BadEvent (Finset.range a) (Finset.Ico l (l+b)) h ell 2) ∩
        (BadEvent (Finset.range a) (Finset.Ico l (l+b)) h ell 3)).card ≤
      (GoodIndex a h ell (Finset.Ico l (l+b))).card+b.choose 2 := by
  have hf := primitive_star_bill hlen hc h₂ h₃
  have ha := Nat.sub_add_cancel hu
  have hsum := Finset.sum_sdiff (active_primes_subset a h) (f := Weight a)
  change Extra a h+(∑ q ∈ Primes a h, Weight a q) = _ at hsum
  unfold UnitBound Refund
  omega

theorem exception_le_ceiling {a h p : ℕ} (ha : 0 < a) (hh : 0 < h)
    (hp : p.Prime) (hph : p ∣ h) : ExceptionLength a h ≤ (a+p-1)/p := by
  by_cases hone : h = 1
  · simp [ExceptionLength, hone]
  · have hb : ExceptionLength a h ≤ (a+h-1)/h := by
      simp only [ExceptionLength, if_neg hone]
      exact min_le_right _ _
    exact hb.trans (ceil_mono_denominator ha hp.pos hh (Nat.le_of_dvd hh hph))

theorem star_index_bound {a h l : ℕ} {ell : ℤ}
    (ha : 12 ≤ a) (hh : 0 < h) (hc : Int.gcd (h:ℤ) ell = 1)
    (hu : (∑ q ∈ AllPrimes a, Weight a q) ≤ a.choose 2)
    (hlen : l+ExceptionLength a h ≤ a) :
    UnitBound a+(a/6).choose 2 ≤
      (GoodIndex a h ell (Finset.Ico l (l+ExceptionLength a h))).card := by
  let b := ExceptionLength a h
  change UnitBound a+(a/6).choose 2 ≤
    (GoodIndex a h ell (Finset.Ico l (l+b))).card
  have hb : l+b ≤ a := hlen
  have hbase := basic_bill hb hc hu
  by_cases h₂ : 2 ∣ h
  · have hi₂ := inactive_mem Nat.prime_two (by omega : 2 < a) h₂
    have hc₂ : b ≤ (a+1)/2 := by
      simpa [b] using exception_le_ceiling (by omega : 0 < a) hh Nat.prime_two h₂
    by_cases h₃ : 3 ∣ h
    · have hi₃ := inactive_mem (by decide : Nat.Prime 3) (by omega : 3 < a) h₃
      have hex := extra_pair hi₂ hi₃ (by decide : (2:ℕ) ≠ 3)
      have hcchoose := Nat.choose_le_choose 2 hc₂
      have hbchoose := Nat.choose_le_choose 2 (show a/6 ≤ (a+2)/3 by omega)
      change b.choose 2 ≤ Weight a 2 at hcchoose
      change (a/6).choose 2 ≤ Weight a 3 at hbchoose
      omega
    · have hr₃ := refund_single (b := b)
        (active_mem (by decide : Nat.Prime 3) (by omega : 3 < a) h₃)
      have hex := extra_single hi₂
      have hcontract := divided_choose_contract (by decide : 0 < (3:ℕ)) hc₂
      have hdiv : a/6 ≤ ((a+1)/2)/3 := by omega
      have hchoose := Nat.choose_le_choose 2 hdiv
      change ((a+1)/2).choose 2 ≤ Extra a h at hex
      omega
  · have ha₂ := active_mem Nat.prime_two (by omega : 2 < a) h₂
    by_cases h₃ : 3 ∣ h
    · have hi₃ := inactive_mem (by decide : Nat.Prime 3) (by omega : 3 < a) h₃
      have hc₃ : b ≤ (a+2)/3 := by
        simpa [b] using exception_le_ceiling (by omega : 0 < a) hh (by decide : Nat.Prime 3) h₃
      have hex := extra_single hi₃
      have hr₂ := refund_single (b := b) ha₂
      have hcontract := divided_choose_contract (by decide : 0 < (2:ℕ)) hc₃
      have hchoose := Nat.choose_le_choose 2 (show a/6 ≤ ((a+2)/3)/2 by omega)
      change ((a+2)/3).choose 2 ≤ Extra a h at hex
      omega
    · have ha₃ := active_mem (by decide : Nat.Prime 3) (by omega : 3 < a) h₃
      have henhanced := enhanced_bill hb hc hu ha₂ ha₃
      have hint := star_intersection_lower (ell := ell) hb h₂ h₃
      have hhalf := half_loss b 3 (by decide)
      have href := refund_single (b := b) ha₃
      have hpay : b.choose 2 ≤ Extra a h := by
        by_cases hone : h = 1
        · have hbzero : b = 0 := by simp [b, ExceptionLength, hone]
          simp [hbzero]
        · let p := h.minFac
          have hp : p.Prime := Nat.minFac_prime hone
          have hpd : p ∣ h := Nat.minFac_dvd h
          by_cases hpa : p < a
          · have hbceil := exception_le_ceiling (by omega : 0 < a) hh hp hpd
            exact (Nat.choose_le_choose 2 hbceil).trans (extra_single (inactive_mem hp hpa hpd))
          · have hph := Nat.le_of_dvd hh hpd
            have hbah : a ≤ h := by omega
            have hbc : b ≤ 1 := by
              exact (exception_le_ceiling (by omega : 0 < a) hh hp hpd).trans
                (ceil_le_one hp.pos (by omega))
            have hzero : b.choose 2 = 0 := Nat.choose_eq_zero_of_lt (by omega)
            omega
      change ((b+5)/6).choose 2 ≤ (b/3).choose 2 at hhalf
      omega

#print axioms inactive_mem
#print axioms active_mem
#print axioms extra_single
#print axioms extra_pair
#print axioms refund_single
#print axioms basic_bill
#print axioms enhanced_bill
#print axioms exception_le_ceiling
#print axioms star_index_bound
end
end JSP233.StarCore158375
