module

public import Erdos272.Core.N130000.StarCore130000

@[expose] public section

namespace JSP233.ThreeFiveEvents82427
open StarCompletion APGeometry SourceBridge208 IntrinsicTriples208
open IndexedCorePairs200000 PrimePairEvents200000 PrimePairResidue200000
open PairEventCount200000 PairUnionSieve200000 CoreUnionSource200000
open StarCore158375
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

theorem selected_union_chord_bound {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s Q : Finset α) (E : α → Finset β) {p q r : α}
    (hp : p∈s) (hQ : Q⊆s.erase p) (hq : q∈Q) (hr : r∈Q) (hqr : q≠r) :
    (s.biUnion E).card+(∑ i∈Q, (E p∩E i).card)+(E q∩E r).card ≤
      (∑ i∈s, (E i).card)+(E p∩(E q∩E r)).card := by
  let D : α → Finset β := fun i => E i\E p
  let R := s.erase p
  have hqR : q∈R := hQ hq
  have hrR : r∈R := hQ hr
  have hbound := StarEvents158375.union_intersection_bound R D hqR hrR hqr
  have hu : s.biUnion E=E p∪R.biUnion D := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hx
      by_cases hxp : x∈E p
      · exact Finset.mem_union_left _ hxp
      · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨i, Finset.mem_erase.mpr ⟨by intro he; exact hxp (he ▸ hxi), hi⟩,
            Finset.mem_sdiff.mpr ⟨hxi, hxp⟩⟩)
    · intro hx
      rcases Finset.mem_union.mp hx with hxp | hxR
      · exact Finset.mem_biUnion.mpr ⟨p, hp, hxp⟩
      · obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hxR
        exact Finset.mem_biUnion.mpr
          ⟨i, (Finset.mem_erase.mp hi).2, (Finset.mem_sdiff.mp hxi).1⟩
  have hdis : Disjoint (E p) (R.biUnion D) := by
    apply Finset.disjoint_left.mpr
    intro x hxp hxR
    obtain ⟨i, _, hxi⟩ := Finset.mem_biUnion.mp hxR
    exact (Finset.mem_sdiff.mp hxi).2 hxp
  have hcard : (s.biUnion E).card=(E p).card+(R.biUnion D).card := by
    rw [hu, Finset.card_union_of_disjoint hdis]
  have hparts : (∑ i∈R, (D i).card)+(∑ i∈R, (E p∩E i).card)=
      ∑ i∈R, (E i).card := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simpa only [D, Finset.inter_comm] using Finset.card_sdiff_add_card_inter (E i) (E p)
  have hsel : (∑ i∈Q, (E p∩E i).card)≤∑ i∈R, (E p∩E i).card :=
    Finset.sum_le_sum_of_subset hQ
  have hsum := Finset.sum_erase_add s (fun i => (E i).card) hp
  have heq : D q∩D r=(E q∩E r)\E p := by
    ext x
    simp only [D, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have hchord := Finset.card_sdiff_add_card_inter (E q∩E r) (E p)
  rw [← heq, Finset.inter_comm (E q∩E r) (E p)] at hchord
  dsimp only [R] at hparts hcard hbound hsel
  omega

theorem primitive_chord_bill {Q : Finset ℕ} {a b l h : ℕ} {ell : ℤ}
    (hlen : l+b≤a) (hc : Int.gcd (h : ℤ) ell=1)
    (h₂ : 2∈Primes a h) (hQ : Q⊆(Primes a h).erase 2)
    (h₃ : 3∈Q) (h₅ : 5∈Q) :
    let E := BadEvent (Finset.range a) (Finset.Ico l (l+b)) h ell
    a.choose 2+(∑ q∈Q, (E 2∩E q).card)+(E 3∩E 5).card+
        (∑ q∈Primes a h, (b/q).choose 2) ≤
      (GoodIndex a h ell (Finset.Ico l (l+b))).card+b.choose 2+
        (∑ q∈Primes a h, Weight a q)+(E 2∩(E 3∩E 5)).card := by
  let J := Finset.Ico l (l+b)
  let E := BadEvent (Finset.range a) J h ell
  have hJ : J⊆Finset.range a := by
    intro i hi
    exact Finset.mem_range.mpr (by have := (Finset.mem_Ico.mp hi).2; omega)
  have hs : (Space (Finset.range a) J).card=a.choose 2-b.choose 2 := by
    simpa only [J, Finset.card_range, Nat.card_Ico, Nat.add_sub_cancel_left] using space_card hJ
  have hbc : b.choose 2≤a.choose 2 := Nat.choose_le_choose 2 (by omega)
  have hcover := (Finset.card_le_card (space_cover (a := a) hc J)).trans
    (Finset.card_union_le _ _)
  change (Space (Finset.range a) J).card≤
    (GoodIndex a h ell J).card+((Primes a h).biUnion E).card at hcover
  have hchord := selected_union_chord_bound (Primes a h) Q E h₂ hQ h₃ h₅ (by decide)
  have hbad : (∑ q∈Primes a h, (E q).card)+
      (∑ q∈Primes a h, (b/q).choose 2)≤∑ q∈Primes a h, Weight a q := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro q hq
    obtain ⟨_, hp, hn⟩ := Finset.mem_filter.mp hq
    have hb := (bad_event_interval_bounds hlen hp hn ell).2
    have hchoose : (b/q).choose 2≤Weight a q :=
      Nat.choose_le_choose 2 (Nat.div_le_div_right (by have := hp.two_le; omega))
    change (E q).card≤Weight a q-(b/q).choose 2 at hb
    omega
  change a.choose 2+(∑ q∈Q, (E 2∩E q).card)+(E 3∩E 5).card+_≤
    (GoodIndex a h ell J).card+b.choose 2+_+(E 2∩(E 3∩E 5)).card
  omega

theorem primitive_pair_bill {a b l h p q : ℕ} {ell : ℤ}
    (hlen : l+b≤a) (hc : Int.gcd (h : ℤ) ell=1)
    (hp : p∈Primes a h) (hq : q∈Primes a h) (hpq : p≠q) :
    let E := BadEvent (Finset.range a) (Finset.Ico l (l+b)) h ell
    a.choose 2+(E p∩E q).card+(∑ r∈Primes a h, (b/r).choose 2) ≤
      (GoodIndex a h ell (Finset.Ico l (l+b))).card+b.choose 2+
        (∑ r∈Primes a h, Weight a r) := by
  let J := Finset.Ico l (l+b)
  let E := BadEvent (Finset.range a) J h ell
  have hJ : J⊆Finset.range a := by
    intro i hi
    exact Finset.mem_range.mpr (by have := (Finset.mem_Ico.mp hi).2; omega)
  have hs : (Space (Finset.range a) J).card=a.choose 2-b.choose 2 := by
    simpa only [J, Finset.card_range, Nat.card_Ico, Nat.add_sub_cancel_left] using space_card hJ
  have hbc : b.choose 2≤a.choose 2 := Nat.choose_le_choose 2 (by omega)
  have hcover := (Finset.card_le_card (space_cover (a := a) hc J)).trans
    (Finset.card_union_le _ _)
  change (Space (Finset.range a) J).card≤
    (GoodIndex a h ell J).card+((Primes a h).biUnion E).card at hcover
  have hpair := StarEvents158375.union_intersection_bound (Primes a h) E hp hq hpq
  have hbad : (∑ r∈Primes a h, (E r).card)+
      (∑ r∈Primes a h, (b/r).choose 2)≤∑ r∈Primes a h, Weight a r := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro r hr
    obtain ⟨_, hrp, hrn⟩ := Finset.mem_filter.mp hr
    have hb := (bad_event_interval_bounds hlen hrp hrn ell).2
    have hchoose : (b/r).choose 2≤Weight a r :=
      Nat.choose_le_choose 2 (Nat.div_le_div_right (by have := hrp.two_le; omega))
    change (E r).card≤Weight a r-(b/r).choose 2 at hb
    omega
  change a.choose 2+(E p∩E q).card+_≤(GoodIndex a h ell J).card+b.choose 2+_
  omega

theorem enhanced_chord_bill {Q : Finset ℕ} {a b l h : ℕ} {ell : ℤ}
    (hlen : l+b≤a) (hc : Int.gcd (h : ℤ) ell=1)
    (hu : (∑ q∈AllPrimes a, Weight a q)≤a.choose 2)
    (h₂ : 2∈Primes a h) (hQ : Q⊆(Primes a h).erase 2) (h₃ : 3∈Q) (h₅ : 5∈Q) :
    let E := BadEvent (Finset.range a) (Finset.Ico l (l+b)) h ell
    UnitBound a+Extra a h+Refund a h b+(∑ q∈Q, (E 2∩E q).card)+(E 3∩E 5).card ≤
      (GoodIndex a h ell (Finset.Ico l (l+b))).card+b.choose 2+(E 2∩(E 3∩E 5)).card := by
  have hf := primitive_chord_bill hlen hc h₂ hQ h₃ h₅
  have ha := Nat.sub_add_cancel hu
  have hsum := Finset.sum_sdiff (active_primes_subset a h) (f := Weight a)
  change Extra a h+(∑ q∈Primes a h, Weight a q)=_ at hsum
  unfold UnitBound Refund
  dsimp only at hf ⊢
  omega

theorem enhanced_pair_bill {a b l h p q : ℕ} {ell : ℤ}
    (hlen : l+b≤a) (hc : Int.gcd (h : ℤ) ell=1)
    (hu : (∑ r∈AllPrimes a, Weight a r)≤a.choose 2)
    (hp : p∈Primes a h) (hq : q∈Primes a h) (hpq : p≠q) :
    let E := BadEvent (Finset.range a) (Finset.Ico l (l+b)) h ell
    UnitBound a+Extra a h+Refund a h b+(E p∩E q).card≤
      (GoodIndex a h ell (Finset.Ico l (l+b))).card+b.choose 2 := by
  have hf := primitive_pair_bill hlen hc hp hq hpq
  have ha := Nat.sub_add_cancel hu
  have hsum := Finset.sum_sdiff (active_primes_subset a h) (f := Weight a)
  change Extra a h+(∑ r∈Primes a h, Weight a r)=_ at hsum
  unfold UnitBound Refund
  dsimp only at hf ⊢
  omega

theorem three_five_eq_fifteen (A J : Finset ℕ) (h : ℕ) (ell : ℤ) :
    BadEvent A J h ell 3∩BadEvent A J h ell 5=
      (Space A J).filter (fun P => ∀ i : ℕ, i∈P → (15 : ℤ)∣ell-(h : ℤ)*i) := by
  ext P
  simp only [Finset.mem_inter, BadEvent, Finset.mem_filter, Bad]
  constructor
  · rintro ⟨⟨hP, h₃⟩, _, h₅⟩
    exact ⟨hP, fun i hi => by have := h₃ i hi; have := h₅ i hi; omega⟩
  · rintro ⟨hP, h₁₅⟩
    exact ⟨⟨hP, fun i hi => by have := h₁₅ i hi; omega⟩,
      hP, fun i hi => by have := h₁₅ i hi; omega⟩

theorem two_three_five_eq_thirty (A J : Finset ℕ) (h : ℕ) (ell : ℤ) :
    BadEvent A J h ell 2∩(BadEvent A J h ell 3∩BadEvent A J h ell 5)=
      (Space A J).filter (fun P => ∀ i : ℕ, i∈P → (30 : ℤ)∣ell-(h : ℤ)*i) := by
  rw [three_five_eq_fifteen]
  ext P
  simp only [Finset.mem_inter, BadEvent, Finset.mem_filter, Bad]
  constructor
  · rintro ⟨⟨hP, h₂⟩, _, h₁₅⟩
    exact ⟨hP, fun i hi => by have := h₂ i hi; have := h₁₅ i hi; omega⟩
  · rintro ⟨hP, h₃₀⟩
    exact ⟨⟨hP, fun i hi => by have := h₃₀ i hi; omega⟩,
      hP, fun i hi => by have := h₃₀ i hi; omega⟩

theorem three_five_lower {a b l h : ℕ} {ell : ℤ} (hlen : l+b≤a)
    (h₃ : ¬3∣h) (h₅ : ¬5∣h) :
    (a/15).choose 2≤
      (BadEvent (Finset.range a) (Finset.Ico l (l+b)) h ell 3∩
        BadEvent (Finset.range a) (Finset.Ico l (l+b)) h ell 5).card+
      ((b+14)/15).choose 2 := by
  have hc₃ : h.Coprime 3 := ((by decide : Nat.Prime 3).coprime_iff_not_dvd.mpr h₃).symm
  have hc₅ : h.Coprime 5 := ((by decide : Nat.Prime 5).coprime_iff_not_dvd.mpr h₅).symm
  have hcop : h.Coprime 15 := Nat.coprime_mul_iff_right.mpr ⟨hc₃, hc₅⟩
  have hcg : Int.gcd (h : ℤ) (15 : ℤ)=1 := by
    change Int.gcd (h : ℤ) ((15 : ℕ) : ℤ)=1
    rw [Int.gcd_natCast_natCast]
    exact hcop.gcd_eq_one
  obtain ⟨u, _, hres⟩ := linear_bad_residue (by decide : 0<(15 : ℕ)) hcg ell
  norm_num only [Nat.cast_ofNat] at hres
  have he : BadEvent (Finset.range a) (Finset.Ico l (l+b)) h ell 3∩
      BadEvent (Finset.range a) (Finset.Ico l (l+b)) h ell 5=
      Event (Finset.range a) (Finset.Ico l (l+b)) 15 (u : ℤ) := by
    rw [three_five_eq_fifteen]
    ext P
    simp only [Event, Finset.mem_filter, Nat.cast_ofNat, hres]
  rw [he]
  have hb := (interval_event_bounds hlen (by decide : 0<(15 : ℕ)) (u : ℤ)).1
  rw [show b+15-1=b+14 by omega] at hb
  omega

theorem two_three_five_upper {a b l h : ℕ} {ell : ℤ} (hlen : l+b≤a)
    (h₂ : ¬2∣h) (h₃ : ¬3∣h) (h₅ : ¬5∣h) :
    (BadEvent (Finset.range a) (Finset.Ico l (l+b)) h ell 2∩
      (BadEvent (Finset.range a) (Finset.Ico l (l+b)) h ell 3∩
        BadEvent (Finset.range a) (Finset.Ico l (l+b)) h ell 5)).card≤
      (a/30+1).choose 2 := by
  have hc₂ : h.Coprime 2 := (Nat.prime_two.coprime_iff_not_dvd.mpr h₂).symm
  have hc₃ : h.Coprime 3 := ((by decide : Nat.Prime 3).coprime_iff_not_dvd.mpr h₃).symm
  have hc₅ : h.Coprime 5 := ((by decide : Nat.Prime 5).coprime_iff_not_dvd.mpr h₅).symm
  have hcop : h.Coprime 30 := Nat.coprime_mul_iff_right.mpr
    ⟨hc₂, Nat.coprime_mul_iff_right.mpr ⟨hc₃, hc₅⟩⟩
  have hcg : Int.gcd (h : ℤ) (30 : ℤ)=1 := by
    change Int.gcd (h : ℤ) ((30 : ℕ) : ℤ)=1
    rw [Int.gcd_natCast_natCast]
    exact hcop.gcd_eq_one
  obtain ⟨u, _, hres⟩ := linear_bad_residue (by decide : 0<(30 : ℕ)) hcg ell
  norm_num only [Nat.cast_ofNat] at hres
  have he : BadEvent (Finset.range a) (Finset.Ico l (l+b)) h ell 2∩
      (BadEvent (Finset.range a) (Finset.Ico l (l+b)) h ell 3∩
        BadEvent (Finset.range a) (Finset.Ico l (l+b)) h ell 5)=
      Event (Finset.range a) (Finset.Ico l (l+b)) 30 (u : ℤ) := by
    rw [two_three_five_eq_thirty]
    ext P
    simp only [Event, Finset.mem_filter, Nat.cast_ofNat, hres]
  rw [he]
  have hb := (interval_event_bounds hlen (by decide : 0<(30 : ℕ)) (u : ℤ)).2
  rw [show a+30-1=a+29 by omega] at hb
  have hc : ((a+29)/30).choose 2≤(a/30+1).choose 2 := Nat.choose_le_choose 2 (by omega)
  omega

#print axioms selected_union_chord_bound
#print axioms primitive_chord_bill
#print axioms primitive_pair_bill
#print axioms enhanced_chord_bill
#print axioms enhanced_pair_bill
#print axioms three_five_eq_fifteen
#print axioms two_three_five_eq_thirty
#print axioms three_five_lower
#print axioms two_three_five_upper
end
end JSP233.ThreeFiveEvents82427
