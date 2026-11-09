module

public import Erdos272.Traces.AffinePayment47
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic.NormNum.Prime

@[expose] public section

/-! Seventeen-prime affine8/error52 rows from the frozen nineteen-prime
ordinary-kernel certificate. Only the two actual extra coprimes61 and67
and the finite prefix through66 are new. -/
namespace JSP233.FiniteSeventeen52
open PrimePrefix35 PrimorialPrefix46 PrimorialValue47 AffineTrace46
open StarCompletion APGeometry LongTerminal35 TraceWitnessCodes36
open DyadicTraceSupply36 NearAP36 FarCore37
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 3000

def Primes17 : Finset ℕ := {2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59}

theorem primes17_finite_data : Primes17.card=17 ∧
    (∀p∈Primes17,p.Prime ∧ p≤59) ∧
    (∀q∈Finset.range 60,q.Prime → q∈Primes17) := by decide

theorem actual_first_primes17 : FirstPrimes 17=Primes17 := by
  have hi : ∀p∈Primes17,∀q,q.Prime → q∉Primes17 → p≤q := by
    intro p hp q hq hqn
    have hp59 := (primes17_finite_data.2.1 p hp).2
    have hq59 : 59<q := by
      by_contra hn
      exact hqn (primes17_finite_data.2.2 q (Finset.mem_range.mpr (by omega)) hq)
    omega
  have hs : Primes17⊆FirstPrimes 17 := by
    intro p hp
    by_contra hpn
    have hn : ¬FirstPrimes 17⊆Primes17 := by
      intro hsub
      have heq := Finset.eq_of_subset_of_card_le hsub
        (by rw [first_primes_card,primes17_finite_data.1])
      exact hpn (by rw [heq];exact hp)
    obtain ⟨q,hq,hqn⟩ := Finset.not_subset.mp hn
    have hpq := hi p hp q (first_primes_prime 17 q hq) hqn
    have hqp := first_primes_initial 17 q p hq (primes17_finite_data.2.1 p hp).1 hpn
    exact hqn ((Nat.le_antisymm hpq hqp) ▸ hp)
  exact (Finset.eq_of_subset_of_card_le hs
    (by rw [first_primes_card,primes17_finite_data.1])).symm

theorem actual_primorial17 : Primorial 17=1922760350154212639070 := by
  unfold Primorial
  rw [actual_first_primes17]
  norm_num [Primes17]

theorem primorial17_dvd19 : Primorial 17∣Primorial 19 := by
  rw [actual_primorial17,actual_primorial19]
  exact ⟨4087,by decide⟩

theorem prefix19_subset17 (k : ℕ) :
    CoprimePrefix (Primorial 19) k⊆CoprimePrefix (Primorial 17) k := by
  intro x hx
  obtain ⟨hi,hcop⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_filter.mpr ⟨hi,hcop.of_dvd_right primorial17_dvd19⟩

theorem prefix17_two_extra {k : ℕ} (hk : 67≤k) :
    (CoprimePrefix (Primorial 19) k).card+2≤(CoprimePrefix (Primorial 17) k).card := by
  have h61 : 61∈CoprimePrefix (Primorial 17) k := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨by decide,by omega⟩,?_⟩
    rw [actual_primorial17]
    decide
  have h67 : 67∈CoprimePrefix (Primorial 17) k := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨by decide,hk⟩,?_⟩
    rw [actual_primorial17]
    decide
  have hn61 : 61∉CoprimePrefix (Primorial 19) k := by
    intro h
    have hh := (Finset.mem_filter.mp h).2
    have hn : ¬Nat.Coprime 61 (Primorial 19) := by rw [actual_primorial19];decide
    exact hn hh
  have hn67 : 67∉CoprimePrefix (Primorial 19) k := by
    intro h
    have hh := (Finset.mem_filter.mp h).2
    have hn : ¬Nat.Coprime 67 (Primorial 19) := by rw [actual_primorial19];decide
    exact hn hh
  have hs : insert 61 (insert 67 (CoprimePrefix (Primorial 19) k))⊆CoprimePrefix (Primorial 17) k := by
    intro x hx
    rcases Finset.mem_insert.mp hx with h | h
    · exact h ▸ h61
    · rcases Finset.mem_insert.mp h with h | h
      · exact h ▸ h67
      · exact prefix19_subset17 k h
  have hc := Finset.card_le_card hs
  have hn : 61∉insert 67 (CoprimePrefix (Primorial 19) k) := by simp [hn61]
  rw [Finset.card_insert_of_notMem hn,Finset.card_insert_of_notMem hn67] at hc
  omega

theorem actual_primorial17_prefix (k : ℕ) (hk : k≤2^19) :
    k≤8*(CoprimePrefix (Primorial 17) k).card+52 := by
  by_cases h67 : 67≤k
  · have hh := AffinePayment47.actual_primorial19_prefix k hk
    have hmore := prefix17_two_extra h67
    omega
  by_cases h61 : 61≤k
  · have hs : ({1,61}:Finset ℕ)⊆CoprimePrefix (Primorial 17) k := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by decide,by omega⟩,by simp⟩
      · have he : x=61 := Finset.mem_singleton.mp hx
        subst x
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_Icc.mpr ⟨by decide,h61⟩,?_⟩
        rw [actual_primorial17]
        decide
    have hc := Finset.card_le_card hs
    norm_num at hc
    omega
  by_cases h0 : k=0
  · omega
  have h1 : 1∈CoprimePrefix (Primorial 17) k :=
    Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by decide,by omega⟩,by simp⟩
  have hc := Finset.card_pos.mpr ⟨1,h1⟩
  omega

theorem actual_defect17_8_le52 : AffineDefect 17 (2^19) 8≤52 := by
  unfold AffineDefect
  apply Finset.sup_le
  intro k hk
  have hh := actual_primorial17_prefix k (Finset.mem_range.mp hk).le
  omega

theorem actual_positive_modulus_row8 (m k : ℕ) (hm : 0<m)
    (hw : m.primeFactors.card≤17) (hk : k<2^19) :
    k≤8*(CoprimePrefix m k).card+52 := by
  exact (actual_affine_row m 17 (2^19) 8 k hm hw hk).trans
    (Nat.add_le_add_left actual_defect17_8_le52 _)

theorem actual_minimal_trace8 (c : ℤ) (M m K B : ℕ)
    (I : Finset ℕ) (P : ℕ→Prop) (k : ℕ→ℕ)
    (hM : 0<M) (hm : 0<m) (hB : 0<B) (hK : B^2≤K)
    (hdiv : ∀d∈I,d∣M) (htrace : ∀d∈I,P d)
    (hminimal : ∀d∈I,∀e,0<e → e∣d → P e → d≤e)
    (hend : ∀d∈I,c+(M:ℤ)∈Prefix c d (k d))
    (hfinite : ∀d∈I,k d<2^19) (homega : m.primeFactors.card≤17)
    (hunion : K≤(I.biUnion (fun d=>Prefix c d (k d))).card) :
    (B-52)*K≤8*(B+1)*(∑d∈I,(CoprimePrefix m (k d)).card) := by
  have hh := actual_minimal_trace_affine c M m K 17 (2^19) 8 B I P k
    hM hm hB hK hdiv htrace hminimal hend hfinite homega hunion
  exact (Nat.mul_le_mul_right K (by have hd:=actual_defect17_8_le52;omega :
    B-52≤B-AffineDefect 17 (2^19) 8)).trans hh

theorem actual_short_prefix8 {S : Finset ℤ} {c p : ℤ} {K B : ℕ}
    (hcp : c<p) (hc : c∈S) (hp : p∈S) (hK : 0<K)
    (hhead : 2*K≤(S∩Finset.Icc c p).card)
    (htail : 4*K≤(S.filter (fun z=>p≤z)).card)
    (hneighbors : (WitnessNeighbors S c p).card≤K)
    (hno : ∀d:ℕ,0<d → ¬Prefix c d K⊆S)
    (hB : 0<B) (hfinite : K≤2^19)
    (homega : ∀z∈S,p≤z → ((p-c).natAbs*(z-c).natAbs).primeFactors.card≤17)
    (hsize : B^2≤K) :
    2*(B-52)*K^2≤8*(B+1)*(StructuralPairs c S).card := by
  have hh := actual_short_prefix_affine hcp hc hp hK hhead htail hneighbors
    hno hB hfinite homega hsize (a:=8)
  have hs : B-52≤B-AffineDefect 17 (2^19) 8 := by have hd:=actual_defect17_8_le52;omega
  exact (Nat.mul_le_mul_right (K^2) (Nat.mul_le_mul_left 2 hs)).trans hh

theorem actual_no_long_right_prefix8 {S : Finset ℤ} {c : ℤ} {K B : ℕ}
    (hc : c∈S) (hK : 0<K) (hright : 8*K≤(S.filter (fun x=>c<x)).card)
    (hno : ∀d:ℕ,0<d → ¬Prefix c d K⊆S)
    (hB : 0<B) (hfinite : K≤2^19)
    (homega : ∀p∈S,c<p → ∀z∈S,p≤z →
      ((p-c).natAbs*(z-c).natAbs).primeFactors.card≤17)
    (hsize : B^2≤K) :
    2*(B-52)*K^2≤8*(B+1)*(StructuralPairs c S).card := by
  have hh := actual_no_long_right_prefix_affine hc hK hright hno
    (by norm_num : 4≤8) hB hfinite homega hsize
  have hs : B-52≤B-AffineDefect 17 (2^19) 8 := by have hd:=actual_defect17_8_le52;omega
  exact (Nat.mul_le_mul_right (K^2) (Nat.mul_le_mul_left 2 hs)).trans hh

#print axioms primes17_finite_data
#print axioms actual_first_primes17
#print axioms actual_primorial17
#print axioms primorial17_dvd19
#print axioms prefix19_subset17
#print axioms prefix17_two_extra
#print axioms actual_primorial17_prefix
#print axioms actual_defect17_8_le52
#print axioms actual_positive_modulus_row8
#print axioms actual_minimal_trace8
#print axioms actual_short_prefix8
#print axioms actual_no_long_right_prefix8
end
end JSP233.FiniteSeventeen52
