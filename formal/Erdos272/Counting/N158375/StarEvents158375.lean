module

public import Erdos272.Counting.N158375.StarArithmetic158375
public import Erdos272.Core.N200000.PairUnionSieve200000

@[expose] public section

namespace JSP233.StarEvents158375
open StarCompletion APGeometry SourceBridge208 IntrinsicTriples208
open IndexedCorePairs200000 PrimePairEvents200000 PrimePairResidue200000
open PairEventCount200000 PairUnionSieve200000 CoreUnionSource200000
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem union_intersection_bound {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (E : α → Finset β) {p q : α}
    (hp : p ∈ s) (hq : q ∈ s) (hne : p ≠ q) :
    (s.biUnion E).card+(E p ∩ E q).card ≤ ∑ i ∈ s, (E i).card := by
  have hcover : s.biUnion E ⊆ (E p ∪ E q) ∪ ((s.erase p).erase q).biUnion E := by
    intro x hx
    obtain ⟨i, hi, hx⟩ := Finset.mem_biUnion.mp hx
    by_cases hip : i = p
    · subst i; exact Finset.mem_union_left _ (Finset.mem_union_left _ hx)
    by_cases hiq : i = q
    · subst i; exact Finset.mem_union_left _ (Finset.mem_union_right _ hx)
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨i, Finset.mem_erase.mpr ⟨hiq, Finset.mem_erase.mpr ⟨hip, hi⟩⟩, hx⟩)
  have hc := (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
  have hb : (((s.erase p).erase q).biUnion E).card ≤
      ∑ i ∈ (s.erase p).erase q, (E i).card := Finset.card_biUnion_le
  have he := Finset.card_union_add_card_inter (E p) (E q)
  have hqe : q ∈ s.erase p := Finset.mem_erase.mpr ⟨hne.symm, hq⟩
  have hs₁ := Finset.sum_erase_add s (fun i => (E i).card) hp
  have hs₂ := Finset.sum_erase_add (s.erase p) (fun i => (E i).card) hqe
  omega

theorem primitive_star_bill {a b l h : ℕ} {ell : ℤ}
    (hlen : l+b ≤ a) (hc : Int.gcd (h : ℤ) ell = 1)
    (h₂ : 2 ∈ Primes a h) (h₃ : 3 ∈ Primes a h) :
    a.choose 2 + ((BadEvent (Finset.range a) (Finset.Ico l (l+b)) h ell 2) ∩
        (BadEvent (Finset.range a) (Finset.Ico l (l+b)) h ell 3)).card +
        ∑ q ∈ Primes a h, (b/q).choose 2 ≤
      (GoodIndex a h ell (Finset.Ico l (l+b))).card + b.choose 2 +
        ∑ q ∈ Primes a h, Weight a q := by
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
  have hstar := union_intersection_bound (Primes a h) E h₂ h₃ (by decide : (2:ℕ) ≠ 3)
  have hbad : (∑ q ∈ Primes a h, (E q).card) +
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
  change a.choose 2+(E 2 ∩ E 3).card+_ ≤
    (GoodIndex a h ell J).card+b.choose 2+_
  omega

theorem bad_two_three_eq_six (A J : Finset ℕ) (h : ℕ) (ell : ℤ) :
    BadEvent A J h ell 2 ∩ BadEvent A J h ell 3 =
      (Space A J).filter (fun Q => ∀ i : ℕ, i ∈ Q → (6:ℤ) ∣ ell-(h:ℤ)*(i:ℤ)) := by
  ext Q
  simp only [Finset.mem_inter, BadEvent, Finset.mem_filter, Bad]
  constructor
  · rintro ⟨⟨hQ, h₂⟩, _, h₃⟩
    refine ⟨hQ, ?_⟩
    intro i hi
    have h2 := h₂ i hi
    have h3 := h₃ i hi
    omega
  · rintro ⟨hQ, h₆⟩
    constructor <;> refine ⟨hQ, ?_⟩ <;> intro i hi <;> have := h₆ i hi <;> omega

theorem star_intersection_lower {a b l h : ℕ} {ell : ℤ}
    (hlen : l+b ≤ a) (h₂ : ¬2 ∣ h) (h₃ : ¬3 ∣ h) :
    (a/6).choose 2 ≤
      ((BadEvent (Finset.range a) (Finset.Ico l (l+b)) h ell 2) ∩
        (BadEvent (Finset.range a) (Finset.Ico l (l+b)) h ell 3)).card +
      ((b+5)/6).choose 2 := by
  have hc₂ : h.Coprime 2 := (Nat.prime_two.coprime_iff_not_dvd.mpr h₂).symm
  have hc₃ : h.Coprime 3 := ((by decide : Nat.Prime 3).coprime_iff_not_dvd.mpr h₃).symm
  have hc : h.Coprime 6 := by
    exact (Nat.coprime_mul_iff_right.mpr ⟨hc₂, hc₃⟩)
  have hcg : Int.gcd (h:ℤ) (6:ℤ) = 1 := by
    change Int.gcd (h:ℤ) ((6:ℕ):ℤ) = 1
    rw [Int.gcd_natCast_natCast]
    exact hc.gcd_eq_one
  obtain ⟨u, _hu, hres⟩ := linear_bad_residue (by decide : 0 < (6:ℕ)) hcg ell
  norm_num only [Nat.cast_ofNat] at hres
  have he : BadEvent (Finset.range a) (Finset.Ico l (l+b)) h ell 2 ∩
      BadEvent (Finset.range a) (Finset.Ico l (l+b)) h ell 3 =
      Event (Finset.range a) (Finset.Ico l (l+b)) 6 (u:ℤ) := by
    rw [bad_two_three_eq_six]
    ext Q
    simp only [Event, Finset.mem_filter, Nat.cast_ofNat, hres]
  rw [he]
  have hb := (interval_event_bounds hlen (by decide : 0 < (6:ℕ)) (u:ℤ)).1
  have hbe : b+6-1 = b+5 := by omega
  rw [hbe] at hb
  omega

#print axioms union_intersection_bound
#print axioms primitive_star_bill
#print axioms bad_two_three_eq_six
#print axioms star_intersection_lower
end
end JSP233.StarEvents158375
