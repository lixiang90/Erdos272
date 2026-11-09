module

public import Erdos272.Arithmetic.StepCensus208
public import Erdos272.Resources.ResidualSpan208
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.Order.Floor.Semifield

@[expose] public section

namespace JSP233.ResidualCensus208
open StepClass208 StepCensus208 ResidualSpan208
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

def Classes : Finset ℕ := {2,3,5,7,11}

theorem span_ge (a b p : ℕ) : a ≤ Span a b p := by
  have hd := Nat.div_le_self a p
  have hm := min_le_right ((b-1)/(p-1)) (a/p)
  unfold Span
  omega

theorem class_cut (N D p k : ℕ) (hk : 0 < k) :
    ((Finset.Icc 1 D).filter (fun d => PrimeGate d=p ∧ d*k ≤ N)).card ≤ Count p (N/k) := by
  rw [count_eq_card]
  apply Finset.card_le_card
  intro d hd
  obtain ⟨hdD,hp,hbound⟩ := Finset.mem_filter.mp hd
  refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hdD).1,?_⟩,hp⟩
  exact (Nat.le_div_iff_mul_le hk).mpr hbound

theorem gate_cut_identity (N D : ℕ) (K : ℕ → ℕ) :
    (∑ d ∈ Finset.Icc 1 D, if d*K (PrimeGate d) ≤ N then 1 else 0)=
      ∑ p ∈ Classes,
        ((Finset.Icc 1 D).filter (fun d => PrimeGate d=p ∧ d*K p ≤ N)).card := by
  let A := (Finset.Icc 1 D).filter (fun d => d*K (PrimeGate d) ≤ N)
  have hpart : A.card=∑ p ∈ Classes, (A.filter (fun d => PrimeGate d=p)).card :=
    Finset.card_eq_sum_card_fiberwise (fun d hd => primeGate_range d)
  rw [← Finset.sum_filter]
  have hsum : (∑ _d ∈ A, (1 : ℕ))=A.card := by simp
  change (∑ _d ∈ A, (1 : ℕ))=_
  rw [hsum,hpart]
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  ext d
  simp only [A,Finset.mem_filter]
  constructor
  · rintro ⟨⟨hd,hk⟩,hg⟩
    exact ⟨hd,hg,by simpa only [hg] using hk⟩
  · rintro ⟨hd,hg,hk⟩
    exact ⟨⟨hd,by simpa only [hg] using hk⟩,hg⟩

theorem gate_cut_upper (N D : ℕ) (K : ℕ → ℕ) (hK : ∀ p ∈ Classes, 0 < K p) :
    (∑ d ∈ Finset.Icc 1 D, if d*K (PrimeGate d) ≤ N then 1 else 0) ≤
      ∑ p ∈ Classes, Count p (N/K p) := by
  rw [gate_cut_identity]
  exact Finset.sum_le_sum (fun p hp => class_cut N D p (K p) (hK p hp))

theorem class_div_upper (N k p : ℕ) (hp : p ∈ Classes) :
    (Count p (N/k) : ℝ) ≤ (N : ℝ)*Rho p/k+Error p := by
  have hh := real_count_upper p ((N : ℝ)/k) (by positivity) hp
  rw [Nat.floor_div_eq_div] at hh
  convert hh using 1 <;> ring

theorem gate_cut_real_upper (N D : ℕ) (K : ℕ → ℕ) (hK : ∀ p ∈ Classes, 0 < K p) :
    ((∑ d ∈ Finset.Icc 1 D, if d*K (PrimeGate d) ≤ N then 1 else 0 : ℕ) : ℝ) ≤
      (N : ℝ)*(∑ p ∈ Classes, Rho p/K p)+∑ p ∈ Classes, Error p := by
  have hnat := gate_cut_upper N D K hK
  have hR : ((∑ d ∈ Finset.Icc 1 D, if d*K (PrimeGate d) ≤ N then 1 else 0 : ℕ) : ℝ) ≤
      ∑ p ∈ Classes, (Count p (N/K p) : ℝ) := by exact_mod_cast hnat
  have hh := Finset.sum_le_sum (fun p hp => class_div_upper N (K p) p hp)
  have he : (∑ p ∈ Classes, ((N : ℝ)*Rho p/K p+Error p))=
      (N : ℝ)*(∑ p ∈ Classes, Rho p/K p)+∑ p ∈ Classes, Error p := by
    rw [Finset.sum_add_distrib,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro p hp
    ring
  rw [he] at hh
  exact hR.trans hh

#print axioms span_ge
#print axioms gate_cut_identity
#print axioms gate_cut_upper
#print axioms gate_cut_real_upper
end
end JSP233.ResidualCensus208
