module

public import Erdos272.Core.N180000.AnalyticCore180000

@[expose] public section

namespace JSP233.DensePool158375
open StarCompletion APGeometry PureSource208 SourceBridge208 IntrinsicTriples208
open CoreUnionSource200000 MixedCore200000
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem two_le_totient {q : ℕ} (hq : 3 ≤ q) : 2 ≤ Nat.totient q := by
  have hp := Nat.totient_pos.mpr (show 0 < q by omega)
  by_contra hsmall
  have heq : Nat.totient q = 1 := by omega
  rcases Nat.totient_eq_one_iff.mp heq with h | h <;> omega

theorem multiplicity_first_step {s e : ℕ} (he : e ≤ s) (hs : 1 ≤ s) :
    e ≤ intervalMultiplicity s (s-e) := by
  have hmem : 1 ∈ Finset.Icc 1 s := Finset.mem_Icc.mpr ⟨by omega, hs⟩
  have hterm : s-1*(s-e) ≤ ∑ d ∈ Finset.Icc 1 s, (s-d*(s-e)) :=
    Finset.single_le_sum (f := fun d : ℕ => s-d*(s-e))
      (fun _ _ => Nat.zero_le _) hmem
  have hid : s-1*(s-e) = e := by omega
  simpa only [intervalMultiplicity, hid] using hterm

theorem physical_quadratic {s e : ℕ} (hs : e+3 ≤ s) :
    e*(e+1) ≤ physicalK s e := by
  induction e generalizing s with
  | zero => simp
  | succ e ih =>
      have hp := ih (s := s) (by omega)
      have ht := two_le_totient (q := s-(e+1)) (by omega)
      have hm := multiplicity_first_step (s := s) (e := e+1) (by omega) (by omega)
      have hmul := Nat.mul_le_mul ht hm
      rw [physicalK_succ (by omega : e < s)]
      nlinarith only [hp, hmul]

theorem actual_large_member {N : ℕ} {S : Finset ℤ}
    (hN : N ≤ 2^18) (hground : S ⊆ Ground N)
    (hbad : ¬IsAP S) (hsize : 1250 ≤ S.card) :
    180200 ≤ (Pool S).card := by
  have htwo : 2 ≤ S.card := by omega
  have hmax := maxAPSize_le_card S
  have he : 1 ≤ Defect S := crooked_defect_positive htwo hbad
  have hsplit : MaxAPSize S+Defect S = S.card := by
    unfold Defect
    omega
  by_cases hlarge : 424 ≤ Defect S
  · have hp := physical_quadratic (s := S.card) (e := 424) (by omega)
    norm_num at hp
    exact hp.trans (actual_source_of_defect htwo hlarge)
  · have ha : 827 ≤ MaxAPSize S := by omega
    have hcard : S.card ≤ N := by
      simpa only [ground_card] using Finset.card_le_card hground
    have haUpper : MaxAPSize S ≤ 2^18 := hmax.trans (hcard.trans hN)
    have hu : 180200 ≤ UnitBound (MaxAPSize S) :=
      AnalyticCore180000.floor_large ha haUpper (by decide) (by decide)
    have hm : UnitBound (MaxAPSize S) ≤ Defect S*UnitBound (MaxAPSize S) := by
      simpa only [one_mul] using Nat.mul_le_mul_right (UnitBound (MaxAPSize S)) he
    exact hu.trans (hm.trans (actual_union_core_source htwo))

#print axioms two_le_totient
#print axioms multiplicity_first_step
#print axioms physical_quadratic
#print axioms actual_large_member
end
end JSP233.DensePool158375
