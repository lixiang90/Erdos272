module

public import Erdos272.Arithmetic.PrimePrefix35
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.Prime.Nth
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Data.Nat.GCD.BigOperators

@[expose] public section
namespace JSP233.PrimorialPrefix46
open PrimePrefix35
open scoped Classical
noncomputable section

theorem prefix_mono (M k l : ℕ) (hkl : k≤l) :
    (CoprimePrefix M k).card≤(CoprimePrefix M l).card := by
  apply Finset.card_le_card
  intro x hx
  obtain ⟨hi,hc⟩ := Finset.mem_filter.mp hx
  obtain ⟨h1,hk⟩ := Finset.mem_Icc.mp hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h1,hk.trans hkl⟩,hc⟩

theorem prime_multiple_image (M p K : ℕ) (hp : p.Prime) (hpm : ¬p∣M) :
    (CoprimePrefix M (K/p)).image (fun x=>p*x)=
      (CoprimePrefix M K).filter (fun x=>p∣x) := by
  ext n
  constructor
  · intro hn
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hxI,hxc⟩ := Finset.mem_filter.mp hx
    obtain ⟨hx1,hxK⟩ := Finset.mem_Icc.mp hxI
    have hpM := hp.coprime_iff_not_dvd.mpr hpm
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_,?_⟩,hpM.mul_left hxc⟩,dvd_mul_right p x⟩
    · have := Nat.mul_le_mul hp.one_lt.le hx1
      simpa using this
    · simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hp.pos).mp hxK
  · intro hn
    obtain ⟨hnM,hpn⟩ := Finset.mem_filter.mp hn
    obtain ⟨hnI,hnc⟩ := Finset.mem_filter.mp hnM
    obtain ⟨hn1,hnK⟩ := Finset.mem_Icc.mp hnI
    obtain ⟨x,rfl⟩ := hpn
    have hxpos : 1≤x := by
      by_contra hn
      have hx0 : x=0 := by omega
      rw [hx0,Nat.mul_zero] at hn1
      omega
    apply Finset.mem_image.mpr
    refine ⟨x,Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hxpos,?_⟩,(Nat.coprime_mul_iff_left.mp hnc).2⟩,rfl⟩
    apply (Nat.le_div_iff_mul_le hp.pos).mpr
    simpa only [Nat.mul_comm] using hnK

theorem prefix_prime_partition (M p K : ℕ) (hp : p.Prime) (hpm : ¬p∣M) :
    (CoprimePrefix (M*p) K).card+(CoprimePrefix M (K/p)).card=
      (CoprimePrefix M K).card := by
  have hf : (CoprimePrefix M K).filter (fun x=>¬p∣x)=CoprimePrefix (M*p) K := by
    ext n
    simp only [CoprimePrefix,Finset.mem_filter,Nat.coprime_mul_iff_right]
    constructor
    · rintro ⟨⟨hi,hM⟩,hpnot⟩
      exact ⟨hi,hM,(hp.coprime_iff_not_dvd.mpr hpnot).symm⟩
    · rintro ⟨hi,hM,hpC⟩
      exact ⟨⟨hi,hM⟩,hp.coprime_iff_not_dvd.mp hpC.symm⟩
  have hc := Finset.card_filter_add_card_filter_not (s:=CoprimePrefix M K) (fun x=>p∣x)
  rw [hf] at hc
  have hi := prime_multiple_image M p K hp hpm
  have him := Finset.card_image_of_injective (CoprimePrefix M (K/p))
    (fun x y he=>Nat.eq_of_mul_eq_mul_left hp.pos he)
  rw [hi] at him
  omega

theorem actual_prime_swap (M p q K : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hpm : ¬p∣M) (hqm : ¬q∣M) (hpq : p≤q) :
    (CoprimePrefix (M*p) K).card≤(CoprimePrefix (M*q) K).card := by
  have hk : K/q≤K/p := Nat.div_le_div_left hpq hp.pos
  have hm := prefix_mono M (K/q) (K/p) hk
  have ha := prefix_prime_partition M p K hp hpm
  have hb := prefix_prime_partition M q K hq hqm
  omega

theorem prefix_prod_antitone (S T : Finset ℕ) (K : ℕ) (hST : S⊆T) :
    (CoprimePrefix (∏ p∈T,p) K).card≤(CoprimePrefix (∏ p∈S,p) K).card := by
  apply Finset.card_le_card
  intro x hx
  obtain ⟨hxI,hcop⟩ := Finset.mem_filter.mp hx
  apply Finset.mem_filter.mpr
  refine ⟨hxI,Nat.coprime_prod_right_iff.mpr ?_⟩
  intro p hp
  exact Nat.coprime_prod_right_iff.mp hcop p (hST hp)

theorem prime_not_dvd_prod (S : Finset ℕ) (p : ℕ) (hp : p.Prime)
    (hS : ∀ q∈S,q.Prime) (hpS : p∉S) : ¬p∣∏ q∈S,q := by
  apply hp.coprime_iff_not_dvd.mp
  apply Nat.coprime_prod_right_iff.mpr
  intro q hq
  apply (Nat.coprime_primes hp (hS q hq)).mpr
  intro he
  exact hpS (he ▸ hq)

theorem initial_prime_set_compression (T S : Finset ℕ) (K : ℕ)
    (hT : ∀ p∈T,p.Prime) (hS : ∀ p∈S,p.Prime)
    (hcard : S.card≤T.card)
    (hinitial : ∀ p∈T,∀ q,q.Prime→q∉T→p≤q) :
    (CoprimePrefix (∏ p∈T,p) K).card≤(CoprimePrefix (∏ p∈S,p) K).card := by
  classical
  suffices ∀ n : ℕ,∀ A : Finset ℕ,(A\T).card=n →
      (∀ p∈A,p.Prime) → A.card≤T.card →
      (CoprimePrefix (∏ p∈T,p) K).card≤(CoprimePrefix (∏ p∈A,p) K).card by
    exact this (S\T).card S rfl hS hcard
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro A hn hA hc
    by_cases hAT : A⊆T
    · exact prefix_prod_antitone A T K hAT
    obtain ⟨q,hqA,hqT⟩ := Finset.not_subset.mp hAT
    have hTA : ¬T⊆A := by
      intro hsub
      have he : T=A := Finset.eq_of_subset_of_card_le hsub hc
      exact hAT he.symm.subset
    obtain ⟨p,hpT,hpA⟩ := Finset.not_subset.mp hTA
    let A' := insert p (A.erase q)
    have hpE : p∉A.erase q := fun hh=>hpA (Finset.mem_of_mem_erase hh)
    have hpq : p≠q := fun he=>hpA (he ▸ hqA)
    have hA' : ∀ x∈A',x.Prime := by
      intro x hx
      rcases Finset.mem_insert.mp hx with hx|hx
      · exact hx ▸ hT p hpT
      · exact hA x (Finset.mem_of_mem_erase hx)
    have hc' : A'.card=A.card := by
      rw [Finset.card_insert_of_notMem hpE,Finset.card_erase_of_mem hqA]
      have := Finset.card_pos.mpr ⟨q,hqA⟩
      omega
    have hout : A'\T=(A\T).erase q := by
      ext x
      simp only [A',Finset.mem_sdiff,Finset.mem_insert,Finset.mem_erase]
      constructor
      · rintro ⟨hx,hxT⟩
        rcases hx with rfl|⟨hxq,hxA⟩
        · exact False.elim (hxT hpT)
        · exact ⟨hxq,hxA,hxT⟩
      · rintro ⟨hxq,hxA,hxT⟩
        exact ⟨Or.inr ⟨hxq,hxA⟩,hxT⟩
    have hlt : (A'\T).card<n := by
      rw [hout,←hn]
      exact Finset.card_erase_lt_of_mem (Finset.mem_sdiff.mpr ⟨hqA,hqT⟩)
    have hrec := ih (A'\T).card hlt A' rfl hA' (hc'.trans_le hc)
    have hprimeE : ∀ x∈A.erase q,x.Prime :=
      fun x hx=>hA x (Finset.mem_of_mem_erase hx)
    have hswap := actual_prime_swap (∏ x∈A.erase q,x) p q K (hT p hpT) (hA q hqA)
      (prime_not_dvd_prod _ p (hT p hpT) hprimeE hpE)
      (prime_not_dvd_prod _ q (hA q hqA) hprimeE (Finset.notMem_erase q A))
      (hinitial p hpT q (hA q hqA) hqT)
    have hprodA : (∏ x∈A.erase q,x)*q=∏ x∈A,x := by
      simpa only [Nat.mul_comm] using Finset.mul_prod_erase A (fun x : ℕ=>x) hqA
    have hprodA' : (∏ x∈A.erase q,x)*p=∏ x∈A',x := by
      simp only [A',Finset.prod_insert hpE]
      exact Nat.mul_comm _ _
    rw [hprodA,hprodA'] at hswap
    exact hrec.trans hswap

def FirstPrimes (v : ℕ) : Finset ℕ :=
  (Finset.range v).image (Nat.nth Nat.Prime)

def Primorial (v : ℕ) : ℕ := ∏ p∈FirstPrimes v,p

theorem first_primes_card (v : ℕ) : (FirstPrimes v).card=v := by
  rw [FirstPrimes,Finset.card_image_of_injective _ (Nat.nth_injective Nat.infinite_setOf_prime)]
  exact Finset.card_range v

theorem first_primes_prime (v p : ℕ) (hp : p∈FirstPrimes v) : p.Prime := by
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
  exact Nat.nth_mem_of_infinite Nat.infinite_setOf_prime i

theorem first_primes_initial (v p q : ℕ) (hp : p∈FirstPrimes v)
    (hq : q.Prime) (hqT : q∉FirstPrimes v) : p≤q := by
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hp
  have hv : v≤Nat.count Nat.Prime q := by
    by_contra hn
    apply hqT
    exact Finset.mem_image.mpr ⟨Nat.count Nat.Prime q,
      Finset.mem_range.mpr (by omega),Nat.nth_count hq⟩
  have hh := Nat.nth_monotone Nat.infinite_setOf_prime
    (show i≤Nat.count Nat.Prime q by have := Finset.mem_range.mp hi; omega)
  simpa only [Nat.nth_count hq] using hh

theorem coprime_radical_iff (m x : ℕ) (hm : 0<m) :
    Nat.Coprime x (∏ p∈m.primeFactors,p) ↔ Nat.Coprime x m := by
  constructor
  · intro hc
    by_contra hn
    obtain ⟨p,hp,hpx,hpm⟩ := Nat.Prime.not_coprime_iff_dvd.mp hn
    have hpf : p∈m.primeFactors := Nat.mem_primeFactors.mpr ⟨hp,hpm,by omega⟩
    have hh := Nat.coprime_prod_right_iff.mp hc p hpf
    exact (hp.coprime_iff_not_dvd.mp hh.symm) hpx
  · intro hc
    apply Nat.coprime_prod_right_iff.mpr
    intro p hp
    exact hc.of_dvd_right (Nat.mem_primeFactors.mp hp).2.1

theorem prefix_radical_eq (m k : ℕ) (hm : 0<m) :
    CoprimePrefix (∏ p∈m.primeFactors,p) k=CoprimePrefix m k := by
  ext x
  simp only [CoprimePrefix,Finset.mem_filter,coprime_radical_iff m x hm]

theorem actual_primorial_prefix_compression (m v k : ℕ) (hm : 0<m)
    (hw : m.primeFactors.card≤v) :
    (CoprimePrefix (Primorial v) k).card≤(CoprimePrefix m k).card := by
  have hh := initial_prime_set_compression (FirstPrimes v) m.primeFactors k
    (fun p hp=>first_primes_prime v p hp)
    (fun p hp=>Nat.prime_of_mem_primeFactors hp)
    (by simpa only [first_primes_card] using hw)
    (fun p hp q hq hqT=>first_primes_initial v p q hp hq hqT)
  rw [prefix_radical_eq m k hm] at hh
  exact hh

#print axioms prefix_mono
#print axioms prime_multiple_image
#print axioms prefix_prime_partition
#print axioms actual_prime_swap
#print axioms prefix_prod_antitone
#print axioms prime_not_dvd_prod
#print axioms initial_prime_set_compression
#print axioms first_primes_card
#print axioms first_primes_prime
#print axioms first_primes_initial
#print axioms coprime_radical_iff
#print axioms prefix_radical_eq
#print axioms actual_primorial_prefix_compression
end
end JSP233.PrimorialPrefix46

