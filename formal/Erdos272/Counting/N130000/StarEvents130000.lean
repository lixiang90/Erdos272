module

public import Erdos272.Counting.N130000.StarArithmetic130000
public import Erdos272.Counting.N158375.StarEvents158375

@[expose] public section

namespace JSP233.StarEvents130000
open StarCompletion APGeometry SourceBridge208 IntrinsicTriples208
open IndexedCorePairs200000 PrimePairEvents200000 PrimePairResidue200000
open PairEventCount200000 PairUnionSieve200000 CoreUnionSource200000
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

theorem root_union_bound {α β : Type*} [DecidableEq α] [DecidableEq β]
    (I : Finset α) (E : Finset β) (F : α → Finset β) :
    (E ∪ I.biUnion F).card+(∑ i ∈ I, (E ∩ F i).card) ≤
      E.card+(∑ i ∈ I, (F i).card) := by
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
      have hsub : E ∩ F i ⊆ (E ∪ I.biUnion F) ∩ F i := by
        intro x hx
        exact Finset.mem_inter.mpr
          ⟨Finset.mem_union_left _ (Finset.mem_inter.mp hx).1, (Finset.mem_inter.mp hx).2⟩
      have hc := Finset.card_le_card hsub
      have he := Finset.card_union_add_card_inter (E ∪ I.biUnion F) (F i)
      have hu : E ∪ (insert i I).biUnion F = (E ∪ I.biUnion F) ∪ F i := by
        rw [Finset.biUnion_insert]
        ac_rfl
      rw [hu, Finset.sum_insert hi, Finset.sum_insert hi]
      omega

theorem selected_union_bound {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s Q : Finset α) (E : α → Finset β) {p : α}
    (hp : p ∈ s) (hQ : Q ⊆ s.erase p) :
    (s.biUnion E).card+(∑ q ∈ Q, (E p ∩ E q).card) ≤ ∑ i ∈ s, (E i).card := by
  have hs := root_union_bound (s.erase p) (E p) E
  have hsel := Finset.sum_le_sum_of_subset hQ (f := fun q => (E p ∩ E q).card)
  have he := Finset.sum_erase_add s (fun i => (E i).card) hp
  have hu : E p ∪ (s.erase p).biUnion E = s.biUnion E := by
    rw [← Finset.biUnion_insert, Finset.insert_erase hp]
  rw [hu] at hs
  omega

theorem primitive_star_bill {Q : Finset ℕ} {a b l h : ℕ} {ell : ℤ}
    (hlen : l+b ≤ a) (hc : Int.gcd (h : ℤ) ell = 1)
    (h₂ : 2 ∈ Primes a h) (hQ : Q ⊆ (Primes a h).erase 2) :
    a.choose 2+(∑ q ∈ Q,
      ((BadEvent (Finset.range a) (Finset.Ico l (l+b)) h ell 2) ∩
        (BadEvent (Finset.range a) (Finset.Ico l (l+b)) h ell q)).card)+
      (∑ q ∈ Primes a h, (b/q).choose 2) ≤
      (GoodIndex a h ell (Finset.Ico l (l+b))).card+b.choose 2+
        (∑ q ∈ Primes a h, Weight a q) := by
  let J := Finset.Ico l (l+b)
  let E := BadEvent (Finset.range a) J h ell
  have hJ : J ⊆ Finset.range a := by
    intro i hi
    exact Finset.mem_range.mpr (by have := (Finset.mem_Ico.mp hi).2; omega)
  have hspace : (Space (Finset.range a) J).card = a.choose 2-b.choose 2 := by
    simpa only [J, Finset.card_range, Nat.card_Ico, Nat.add_sub_cancel_left] using space_card hJ
  have hbc : b.choose 2 ≤ a.choose 2 := Nat.choose_le_choose 2 (by omega)
  have hcover := ((Finset.card_le_card (space_cover (a := a) hc J)).trans
    (Finset.card_union_le _ _))
  change (Space (Finset.range a) J).card ≤
    (GoodIndex a h ell J).card+((Primes a h).biUnion E).card at hcover
  have hstar := selected_union_bound (Primes a h) Q E h₂ hQ
  have hbad : (∑ q ∈ Primes a h, (E q).card)+
      (∑ q ∈ Primes a h, (b/q).choose 2) ≤ ∑ q ∈ Primes a h, Weight a q := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro q hq
    obtain ⟨_hr, hp, hn⟩ := Finset.mem_filter.mp hq
    have hb := (bad_event_interval_bounds hlen hp hn ell).2
    have hdiv : b/q ≤ (a+q-1)/q := by
      apply Nat.div_le_div_right
      have := hp.two_le
      omega
    have hchoose := Nat.choose_le_choose 2 hdiv
    change (E q).card ≤ Weight a q-(b/q).choose 2 at hb
    change (b/q).choose 2 ≤ Weight a q at hchoose
    omega
  change a.choose 2+(∑ q ∈ Q, (E 2 ∩ E q).card)+_ ≤
    (GoodIndex a h ell J).card+b.choose 2+_
  omega

theorem bad_two_prime_eq_product (A J : Finset ℕ) (h : ℕ) (ell : ℤ)
    {q : ℕ} (hq : q.Prime) (hne : q ≠ 2) :
    BadEvent A J h ell 2 ∩ BadEvent A J h ell q =
      (Space A J).filter (fun P => ∀ i : ℕ, i ∈ P →
        ((2*q : ℕ) : ℤ) ∣ ell-(h : ℤ)*(i : ℤ)) := by
  have hnot : ¬2 ∣ q := by
    intro hh
    have hm := Nat.mod_eq_zero_of_dvd hh
    have ho := hq.eq_two_or_odd
    omega
  have hcop : IsCoprime (2 : ℤ) (q : ℤ) :=
    (Nat.prime_two.coprime_iff_not_dvd.mpr hnot).isCoprime
  have h₂d : (2 : ℤ) ∣ ((2*q : ℕ) : ℤ) := ⟨(q : ℤ), by push_cast; ring⟩
  have hqd : (q : ℤ) ∣ ((2*q : ℕ) : ℤ) := ⟨2, by push_cast; ring⟩
  ext P
  simp only [Finset.mem_inter, BadEvent, Finset.mem_filter, Bad]
  constructor
  · rintro ⟨⟨hP, h₂⟩, _, hq'⟩
    refine ⟨hP, ?_⟩
    intro i hi
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hcop.mul_dvd (h₂ i hi) (hq' i hi)
  · rintro ⟨hP, hprod⟩
    exact ⟨⟨hP, fun i hi => h₂d.trans (hprod i hi)⟩,
      hP, fun i hi => hqd.trans (hprod i hi)⟩

theorem star_intersection_lower {a b l h q : ℕ} {ell : ℤ}
    (hlen : l+b ≤ a) (hq : q.Prime) (hne : q ≠ 2)
    (h₂ : ¬2 ∣ h) (hn : ¬q ∣ h) :
    (a/(2*q)).choose 2 ≤
      ((BadEvent (Finset.range a) (Finset.Ico l (l+b)) h ell 2) ∩
        (BadEvent (Finset.range a) (Finset.Ico l (l+b)) h ell q)).card+
      ((b+2*q-1)/(2*q)).choose 2 := by
  have hc₂ : h.Coprime 2 := (Nat.prime_two.coprime_iff_not_dvd.mpr h₂).symm
  have hcq : h.Coprime q := (hq.coprime_iff_not_dvd.mpr hn).symm
  have hc : h.Coprime (2*q) := Nat.coprime_mul_iff_right.mpr ⟨hc₂, hcq⟩
  have hcg : Int.gcd (h : ℤ) ((2*q : ℕ) : ℤ) = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact hc.gcd_eq_one
  obtain ⟨u, _hu, hres⟩ := linear_bad_residue (by have := hq.pos; omega : 0 < 2*q) hcg ell
  have he : BadEvent (Finset.range a) (Finset.Ico l (l+b)) h ell 2 ∩
      BadEvent (Finset.range a) (Finset.Ico l (l+b)) h ell q =
      Event (Finset.range a) (Finset.Ico l (l+b)) (2*q) (u : ℤ) := by
    rw [bad_two_prime_eq_product _ _ _ _ hq hne]
    ext P
    simp only [Event, Finset.mem_filter, hres]
  rw [he]
  have hb := (interval_event_bounds hlen (by have := hq.pos; omega : 0 < 2*q) (u : ℤ)).1
  omega

#print axioms root_union_bound
#print axioms selected_union_bound
#print axioms primitive_star_bill
#print axioms bad_two_prime_eq_product
#print axioms star_intersection_lower
end
end JSP233.StarEvents130000
