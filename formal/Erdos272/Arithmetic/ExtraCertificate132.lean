import Erdos272.Arithmetic.PoolExtension132
namespace JSP233.ExtraCertificate132
open PoolExtension132 SimplexMoment57
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 20000

def baseCheck (p:ℕ) : Bool :=
  decide (2≤p) && decide (Nat.Coprime p 2 ∧ Nat.Coprime p 3 ∧ Nat.Coprime p 5 ∧ Nat.Coprime p 7)

def extrasCheck (P:List ℕ) : Bool := P.all baseCheck && decide (P.Pairwise Nat.Coprime)

noncomputable section
open scoped Classical

theorem extras_check_sound {P:List ℕ} (h:extrasCheck P=true) :
    (∀p∈P,2≤p) ∧
      (∀p∈P,Nat.Coprime p 2 ∧ Nat.Coprime p 3 ∧ Nat.Coprime p 5 ∧ Nat.Coprime p 7) ∧
        P.Pairwise Nat.Coprime := by
  simp only [extrasCheck,Bool.and_eq_true,decide_eq_true_eq] at h
  have hall := List.all_eq_true.mp h.1
  have hbase : ∀p∈P,2≤p ∧
      (Nat.Coprime p 2 ∧ Nat.Coprime p 3 ∧ Nat.Coprime p 5 ∧ Nat.Coprime p 7) := by
    intro p hp
    have ht := hall p hp
    simpa only [baseCheck,Bool.and_eq_true,decide_eq_true_eq] using ht
  exact ⟨fun p hp=>(hbase p hp).1,fun p hp=>(hbase p hp).2,h.2⟩

theorem actual_second_moment_extras_of_check_nat (N:ℕ) (P:List ℕ) (h:extrasCheck P=true) :
    (∑n∈Finset.Icc 1 N,n.divisors.card^2)+OldLower N+ExtraTerms N P≤
      OldUpper N+CrossTerms N P+PairTerms N P := by
  obtain ⟨hp,hb,hc⟩ := extras_check_sound h
  exact actual_second_moment_extras_nat N P hp hb hc

theorem actual_second_moment_extras_of_check (N:ℕ) (P:List ℕ) (h:extrasCheck P=true) :
    (∑n∈Finset.Icc 1 N,(n.divisors.card:ℝ)^2)+(OldLower N:ℝ)+(ExtraTerms N P:ℝ)≤
      (OldUpper N:ℝ)+(CrossTerms N P:ℝ)+(PairTerms N P:ℝ) := by
  exact_mod_cast actual_second_moment_extras_of_check_nat N P h

#print axioms extras_check_sound
#print axioms actual_second_moment_extras_of_check_nat
#print axioms actual_second_moment_extras_of_check
end
end JSP233.ExtraCertificate132
