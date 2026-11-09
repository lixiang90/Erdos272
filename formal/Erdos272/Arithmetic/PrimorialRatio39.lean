module

public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Data.Nat.Totient
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Erdos272.Foundation.ProofTactics
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

/-! Actual prime-factor cardinalities and real totient ratios from primorial exclusion.
Maximum-prime induction supplies the comparison; no ordering premise is exported. -/
namespace JSP233.PrimorialRatio39
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 1600000

def PrimeAt (i : ℕ) : ℕ := Nat.nth Nat.Prime i
def Primorial (k : ℕ) : ℕ := ∏ i∈Finset.range k, PrimeAt i
def Ratio (k : ℕ) : ℝ := ∏ i∈Finset.range k, (PrimeAt i:ℝ)/((PrimeAt i:ℝ)-1)

theorem prime_at_prime (i : ℕ) : Nat.Prime (PrimeAt i) := Nat.prime_nth_prime i

theorem prime_at_le_max (s : Finset ℕ) (a : ℕ) (ha : Nat.Prime a)
    (hs : ∀ p∈s,Nat.Prime p) (hmax : ∀ p∈s,p<a) : PrimeAt s.card≤a := by
  have hsub : s⊆Nat.primesLE (a-1) := by
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨by have hh:=hmax p hp; omega,hs p hp⟩
  have hc := Finset.card_le_card hsub
  rw [Nat.primesLE_card_eq_primeCounting,Nat.primeCounting_sub_one] at hc
  exact (Nat.nth_monotone Nat.infinite_setOf_prime hc).trans_eq (Nat.nth_count ha)

theorem primorial_le_prime_product (s : Finset ℕ) (hs : ∀ p∈s,Nat.Prime p) :
    Primorial s.card≤∏ p∈s,p := by
  induction s using Finset.induction_on_max with
  | empty => simp [Primorial]
  | insert a s hmax ih =>
    have hnot : a∉s := by intro ha; exact (lt_irrefl a) (hmax a ha)
    have ha := hs a (Finset.mem_insert_self a s)
    have hs0 : ∀ p∈s,Nat.Prime p := fun p hp=>hs p (Finset.mem_insert_of_mem hp)
    have hp := prime_at_le_max s a ha hs0 hmax
    rw [Finset.card_insert_of_notMem hnot,Primorial,Finset.prod_range_succ,
      Finset.prod_insert hnot]
    exact (Nat.mul_le_mul (ih hs0) hp).trans_eq (Nat.mul_comm _ _)

theorem real_ratio_antitone {p a : ℕ} (hp : 2≤p) (hpa : p≤a) :
    (a:ℝ)/((a:ℝ)-1)≤(p:ℝ)/((p:ℝ)-1) := by
  have hpR : (2:ℝ)≤p := by exact_mod_cast hp
  have hpaR : (p:ℝ)≤a := by exact_mod_cast hpa
  apply (div_le_div_iff₀ (by linarith : (0:ℝ)<(a:ℝ)-1)
    (by linarith : (0:ℝ)<(p:ℝ)-1)).mpr
  nlinarith

theorem ratio_nonneg (k : ℕ) : 0≤Ratio k := by
  apply Finset.prod_nonneg
  intro i hi
  have hp := (prime_at_prime i).two_le
  have hpR : (2:ℝ)≤PrimeAt i := by exact_mod_cast hp
  exact div_nonneg (by positivity) (by linarith)

theorem prime_product_ratio_le (s : Finset ℕ) (hs : ∀ p∈s,Nat.Prime p) :
    (∏ p∈s,(p:ℝ)/((p:ℝ)-1))≤Ratio s.card := by
  induction s using Finset.induction_on_max with
  | empty => simp [Ratio]
  | insert a s hmax ih =>
    have hnot : a∉s := by intro ha; exact (lt_irrefl a) (hmax a ha)
    have ha := hs a (Finset.mem_insert_self a s)
    have hs0 : ∀ p∈s,Nat.Prime p := fun p hp=>hs p (Finset.mem_insert_of_mem hp)
    have hp := prime_at_le_max s a ha hs0 hmax
    have hrat := real_ratio_antitone (prime_at_prime s.card).two_le hp
    have haR : (2:ℝ)≤a := by exact_mod_cast ha.two_le
    have ha0 : 0≤(a:ℝ)/((a:ℝ)-1) := div_nonneg (by positivity) (by linarith)
    have hh := mul_le_mul (ih hs0) hrat ha0 (ratio_nonneg s.card)
    rw [Finset.card_insert_of_notMem hnot,Ratio,Finset.prod_range_succ,
      Finset.prod_insert hnot]
    simpa only [Ratio,mul_comm] using hh

theorem primorial_mono {a b : ℕ} (hab : a≤b) : Primorial a≤Primorial b := by
  apply Finset.prod_le_prod_of_subset_of_one_le' (Finset.range_mono hab)
  intro i hi hia
  exact (prime_at_prime i).one_lt.le

theorem ratio_mono {a b : ℕ} (hab : a≤b) : Ratio a≤Ratio b := by
  apply Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.range_mono hab)
  · intro i hi
    have hpR : (2:ℝ)≤PrimeAt i := by exact_mod_cast (prime_at_prime i).two_le
    exact div_nonneg (by positivity) (by linarith)
  · intro i hi hia
    have hpR : (2:ℝ)≤PrimeAt i := by exact_mod_cast (prime_at_prime i).two_le
    apply (le_div_iff₀ (by linarith : (0:ℝ)<(PrimeAt i:ℝ)-1)).mpr
    linarith

theorem actual_omega_of_lt_primorial (m w : ℕ) (hm : 0<m)
    (hbound : m<Primorial (w+1)) : m.primeFactors.card≤w := by
  have hp := primorial_le_prime_product m.primeFactors
    (fun p hp=>Nat.prime_of_mem_primeFactors hp)
  have hr : (∏ p∈m.primeFactors,p)≤m :=
    Nat.le_of_dvd hm (Nat.prod_primeFactors_dvd m)
  by_contra hn
  have hh := primorial_mono (by omega : w+1≤m.primeFactors.card)
  omega

theorem actual_totient_product_ratio (m : ℕ) :
    (m:ℝ)=Nat.totient m*(∏ p∈m.primeFactors,(p:ℝ)/((p:ℝ)-1)) := by
  have hh := Nat.totient_mul_prod_primeFactors m
  have he : (Nat.totient m:ℝ)*(∏ p∈m.primeFactors,(p:ℝ))=
      (m:ℝ)*(∏ p∈m.primeFactors,((p:ℝ)-1)) := by
    have hhR := congrArg (fun n:ℕ=>(n:ℝ)) hh
    simp only [Nat.cast_mul,Nat.cast_prod] at hhR
    have hc : (∏ p∈m.primeFactors,((p-1:ℕ):ℝ))=
        ∏ p∈m.primeFactors,((p:ℝ)-1) := by
      apply Finset.prod_congr rfl
      intro p hp
      simpa only [Nat.cast_one] using
        (Nat.cast_sub (R:=ℝ) (Nat.prime_of_mem_primeFactors hp).one_lt.le)
    rwa [hc] at hhR
  have hp : (0:ℝ)<∏ p∈m.primeFactors,((p:ℝ)-1) := by
    apply Finset.prod_pos
    intro p hp
    have hpp : (2:ℝ)≤p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    linarith
  rw [Finset.prod_div_distrib,←mul_div_assoc]
  exact (eq_div_iff (ne_of_gt hp)).mpr he.symm

theorem actual_totient_ratio_of_omega (m w : ℕ) (hw : m.primeFactors.card≤w) :
    (m:ℝ)≤Ratio w*Nat.totient m := by
  have hh := (prime_product_ratio_le m.primeFactors
    (fun p hp=>Nat.prime_of_mem_primeFactors hp)).trans (ratio_mono hw)
  have hmul := mul_le_mul_of_nonneg_left hh (show (0:ℝ)≤Nat.totient m by positivity)
  rw [←actual_totient_product_ratio] at hmul
  simpa only [mul_comm] using hmul

theorem uniform_omega_and_ratio (N w : ℕ) (hN : N<Primorial (w+1)) :
    (∀ m≤N,m.primeFactors.card≤w) ∧
    (∀ m≤N,(m:ℝ)≤Ratio w*Nat.totient m) := by
  have hw : ∀ m≤N,m.primeFactors.card≤w := by
    intro m hmN
    by_cases hm : m=0
    · simp [hm]
    · exact actual_omega_of_lt_primorial m w (Nat.pos_of_ne_zero hm) (hmN.trans_lt hN)
  exact ⟨hw,fun m hm=>actual_totient_ratio_of_omega m w (hw m hm)⟩

theorem prime_at_of_count (p i : ℕ) (hp : Nat.Prime p)
    (hi : Nat.count Nat.Prime p=i) : PrimeAt i=p := by
  simpa only [PrimeAt,hi] using Nat.nth_count hp

def SeedPrime : Fin 22→ℕ := ![2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79]

theorem prime_at_seed (i : Fin 22) : PrimeAt i=SeedPrime i := by
  fin_cases i <;> norm_num only [SeedPrime,Matrix.cons_val_zero,Matrix.cons_val_succ]
  all_goals apply prime_at_of_count <;> decide

theorem prime_at_seed_nat (i : ℕ) (hi : i<22) : PrimeAt i=SeedPrime ⟨i,hi⟩ :=
  prime_at_seed ⟨i,hi⟩

theorem seed_primorial_fourteen : 2^50≤Primorial 14 := by
  norm_num [Primorial,Finset.prod_range_succ,prime_at_seed_nat,SeedPrime]

theorem seed_ratio_thirteen : Ratio 13=131710070791/19110297600 := by
  norm_num [Ratio,Finset.prod_range_succ,prime_at_seed_nat,SeedPrime]

theorem seed_primorial_twenty_two : 2^100≤Primorial 22 := by
  norm_num [Primorial,Finset.prod_range_succ,prime_at_seed_nat,SeedPrime]

theorem uniform_q49 (N : ℕ) (hN : N<2^50) :
    (∀ m≤N,m.primeFactors.card≤13) ∧
    (∀ m≤N,(m:ℝ)≤(131710070791/19110297600:ℝ)*Nat.totient m) ∧
    (∀ m≤N^2,m.primeFactors.card≤21) := by
  obtain ⟨hw,hr⟩ := uniform_omega_and_ratio N 13 (hN.trans_le seed_primorial_fourteen)
  have hNsquare : N^2<2^100 := by
    have hh := Nat.mul_self_lt_mul_self hN
    norm_num [←pow_two] at hh ⊢
    exact hh
  have hp := (uniform_omega_and_ratio (N^2) 21
    (hNsquare.trans_le seed_primorial_twenty_two)).1
  exact ⟨hw,by simpa only [seed_ratio_thirteen] using hr,hp⟩

#print axioms prime_at_prime
#print axioms prime_at_le_max
#print axioms primorial_le_prime_product
#print axioms real_ratio_antitone
#print axioms ratio_nonneg
#print axioms prime_product_ratio_le
#print axioms primorial_mono
#print axioms ratio_mono
#print axioms actual_omega_of_lt_primorial
#print axioms actual_totient_product_ratio
#print axioms actual_totient_ratio_of_omega
#print axioms uniform_omega_and_ratio
#print axioms prime_at_of_count
#print axioms prime_at_seed
#print axioms prime_at_seed_nat
#print axioms seed_primorial_fourteen
#print axioms seed_ratio_thirteen
#print axioms seed_primorial_twenty_two
#print axioms uniform_q49
end
end JSP233.PrimorialRatio39
