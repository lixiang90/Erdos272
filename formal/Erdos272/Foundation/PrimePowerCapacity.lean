module

public import Erdos272.Foundation.ChainCapacity
public import Mathlib.Data.Nat.Prime.Basic

@[expose] public section

namespace JSP233.PrimePowerCapacity

open StarCompletion PrivateFinset ChainGeometry

theorem positive_divisors_prime_power_chain
    (p e : Nat) (hp : p.Prime) (d f : Int)
    (hd : 0 < d) (hf : 0 < f)
    (hdivd : d ∣ ((p^e : Nat) : Int)) (hdivf : f ∣ ((p^e : Nat) : Int)) :
    d ∣ f ∨ f ∣ d := by
  obtain ⟨i,hi,hdi⟩ := (Nat.dvd_prime_pow hp).mp (Int.dvd_natCast.mp hdivd)
  obtain ⟨j,hj,hfj⟩ := (Nat.dvd_prime_pow hp).mp (Int.dvd_natCast.mp hdivf)
  have hdabs : (d.natAbs : Int) = d := Int.ofNat_natAbs_of_nonneg (by omega)
  have hfabs : (f.natAbs : Int) = f := Int.ofNat_natAbs_of_nonneg (by omega)
  have hdeq : d = ((p^i : Nat) : Int) := by rw [hdi] at hdabs; omega
  have hfeq : f = ((p^j : Nat) : Int) := by rw [hfj] at hfabs; omega
  rw [hdeq,hfeq]
  rcases le_total i j with hij | hji
  · left; exact_mod_cast (pow_dvd_pow p hij)
  · right; exact_mod_cast (pow_dvd_pow p hji)

/-- Actual AP pair steps divide any common nonzero gap. -/
theorem pair_step_dvd_common_gap (D : Finset (Finset Int)) (a g d : Int)
    (ha : ∀ S ∈ D, a ∈ S) (hg : ∀ S ∈ D, a+g ∈ S)
    (hd : IsPairStep D d) : 0 < d ∧ d ∣ g := by
  obtain ⟨S,hS,T,hT,_,r,hstep⟩ := hd
  have hreb := PrivateUnion.APAt_rebase d r a _ hstep ⟨ha S hS,ha T hT⟩
  obtain ⟨hpos,lo,hi,hr⟩ := hreb
  exact ⟨hpos,by simpa using ((hr (a+g)).mp ⟨hg S hS,hg T hT⟩).2.2⟩

/-- The true pair-step chain is derived from a shared prime-power gap;
it is not an input to the prime-power capacity theorem. Exponent zero
includes the common-adjacent-integers case. -/
theorem shared_prime_power_gap_chain
    (D : Finset (Finset Int)) (p e : Nat) (hp : p.Prime) (a : Int)
    (ha : ∀ S ∈ D, a ∈ S) (hg : ∀ S ∈ D, a+((p^e : Nat) : Int) ∈ S) :
    PairStepChain D := by
  intro d f hd hf
  have hd' := pair_step_dvd_common_gap D a ((p^e : Nat) : Int) d ha hg hd
  have hf' := pair_step_dvd_common_gap D a ((p^e : Nat) : Int) f ha hg hf
  exact positive_divisors_prime_power_chain p e hp d f hd'.1 hf'.1 hd'.2 hf'.2

/-- Actual common-kernel capacity for every prime power. The kernel may
have any size at least two; no fine-member or density premise is used. -/
theorem actual_kernel_card_bound
    (Ω : Finset Int) (D : Finset (Finset Int)) (p e : Nat) (hp : p.Prime) (a : Int)
    (hm : 2 ≤ D.card) (hk : 2 ≤ (Kernel Ω D).card)
    (hground : ∀ S ∈ D, S ⊆ Ω) (hcrooked : ∀ S ∈ D, ¬ IsAP S)
    (hpair : ∀ S ∈ D, ∀ T ∈ D, S ≠ T → IsAP (S ∩ T))
    (ha : a ∈ Kernel Ω D) (hg : a+((p^e : Nat) : Int) ∈ Kernel Ω D) :
    D.card + (Kernel Ω D).card ≤ Ω.card := by
  apply ChainCapacity.actual_kernel_card_bound Ω D hm hk hground hcrooked hpair
  exact shared_prime_power_gap_chain D p e hp a (Finset.mem_filter.mp ha).2
    (Finset.mem_filter.mp hg).2

theorem avoiding_root_card_bound
    (Ω : Finset Int) (D : Finset (Finset Int)) (c : Int)
    (p e : Nat) (hp : p.Prime) (a : Int)
    (hc : c ∈ Ω) (hm : 2 ≤ D.card) (hk : 2 ≤ (Kernel Ω D).card)
    (hground : ∀ S ∈ D, S ⊆ Ω) (havoid : ∀ S ∈ D, c ∉ S)
    (hcrooked : ∀ S ∈ D, ¬ IsAP S)
    (hpair : ∀ S ∈ D, ∀ T ∈ D, S ≠ T → IsAP (S ∩ T))
    (ha : a ∈ Kernel Ω D) (hg : a+((p^e : Nat) : Int) ∈ Kernel Ω D) :
    D.card + (Kernel Ω D).card + 1 ≤ Ω.card := by
  apply ChainCapacity.avoiding_root_card_bound Ω D c hc hm hk hground havoid hcrooked hpair
  exact shared_prime_power_gap_chain D p e hp a (Finset.mem_filter.mp ha).2
    (Finset.mem_filter.mp hg).2

/-- From the actual AP representation, extract its consecutive common
points automatically before applying the general prime-power theorem. -/
theorem represented_kernel_capacity
    (Ω : Finset Int) (D : Finset (Finset Int)) (c r : Int)
    (p e : Nat) (hp : p.Prime)
    (hc : c ∈ Ω) (hm : 2 ≤ D.card) (hk : 2 ≤ (Kernel Ω D).card)
    (hground : ∀ S ∈ D, S ⊆ Ω) (havoid : ∀ S ∈ D, c ∉ S)
    (hcrooked : ∀ S ∈ D, ¬ IsAP S)
    (hpair : ∀ S ∈ D, ∀ T ∈ D, S ≠ T → IsAP (S ∩ T))
    (hstep : APGeometry.APAt ((p^e : Nat) : Int) r (Kernel Ω D)) :
    D.card + (Kernel Ω D).card + 1 ≤ Ω.card := by
  obtain ⟨a,b,ha,hg,_,_,_⟩ := APGeometry.apAt_adjacent_min hstep hk
  exact avoiding_root_card_bound Ω D c p e hp a hc hm hk hground havoid hcrooked hpair ha hg

theorem prime_power_avoiders_payment
    (Ω : Finset Int) (F : Finset (Finset Int)) (c r : Int) (B p e : Nat)
    (hp : p.Prime) (hc : c ∈ Ω) (hF : Legal Ω F) (hstar : StarBound Ω B)
    (hm : 2 ≤ (Avoiders F c).card) (hk : 2 ≤ (CommonKernel Ω F c).card)
    (hcrooked : ∀ S ∈ Avoiders F c, ¬ IsAP S)
    (hstep : APGeometry.APAt ((p^e : Nat) : Int) r (CommonKernel Ω F c)) :
    F.card + 1 ≤ B := by
  have hcap := represented_kernel_capacity Ω (Avoiders F c) c r p e hp hc hm hk
    (fun S hS => hF.1 S (Finset.mem_filter.mp hS).1)
    (fun S hS => (Finset.mem_filter.mp hS).2) hcrooked
    (fun S hS T hT hne => hF.2 S (Finset.mem_filter.mp hS).1
      T (Finset.mem_filter.mp hT).1 hne) hstep
  change (Avoiders F c).card + (CommonKernel Ω F c).card + 1 ≤ Ω.card at hcap
  have hpay := completion_payment Ω F c B hc hF hstar
  omega

#print axioms positive_divisors_prime_power_chain
#print axioms pair_step_dvd_common_gap
#print axioms shared_prime_power_gap_chain
#print axioms actual_kernel_card_bound
#print axioms avoiding_root_card_bound
#print axioms represented_kernel_capacity
#print axioms prime_power_avoiders_payment

end JSP233.PrimePowerCapacity
