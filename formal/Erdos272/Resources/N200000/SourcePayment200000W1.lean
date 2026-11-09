module

public import Erdos272.Resources.N200000.Layer200000
public import Erdos272.Resources.N200000.SourceData200000W1
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

namespace JSP233.SourcePayment200000W1
open StarCompletion APGeometry SevenFamily208 SourceData200000W1
open SourceBridge208 IntrinsicTriples208 MixedCore200000 SourceQueryData200000
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Cost (N i : ℕ) : ℝ := if i=0 then 0 else Layer200000.Upper N (7+(i-1))
def Weighted (N : ℕ) : ℝ := 6*G*(∑ i ∈ Finset.range 8, (Psi (i+1)-Psi i)*Cost N i)

theorem fee (N : ℕ) : Weighted N = SourceUpper N := by
  simp only [Weighted, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [G, Psi, potential, Cost, Layer200000.Upper, CleanupRows200000.data,
    CleanupRows200000.data00, CleanupRows200000.data01, CleanupRows200000.data02, CleanupRows200000.data03, CleanupRows200000.data04, CleanupRows200000.data05, CleanupRows200000.data06, CleanupRows200000.data07, CleanupRows200000.data08, CleanupRows200000.data09, CleanupRows200000.data10, CleanupRows200000.data11, CleanupRows200000.data12, CleanupRows200000.data13, CleanupRows200000.data14, CleanupRows200000.data15, CleanupRows200000.data16, CleanupRows200000.data17, CleanupRows200000.data18, CleanupRows200000.data19, CleanupRows200000.data20, SourceUpper, CoeffA, CoeffB, CoeffC]
  ring

theorem free_empty {N : ℕ} {A : Finset (Finset ℤ)} (hhi : N ≤ 220000)
    (hlegal : Legal (Ground N) A) (hbad : ∀ S ∈ A, ¬IsAP S)
    (hsize : ∀ S ∈ A, 137 ≤ S.card) : PoolNear A Psi 0 = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro S hS
  obtain ⟨hSA, hnear⟩ := Finset.mem_filter.mp hS
  have hcard : 2 ≤ S.card := by have hh := hsize S hSA; omega
  have hb := actual_plan_source (query 50) (conditions (by decide)) (RowSources200000.floors (by decide))
    (N := N) (S := S) (by norm_num at *; omega) (hlegal.1 S hSA) hcard
    (by change 137 ≤ S.card; exact hsize S hSA)
    (by change 1 ≤ Defect S; exact crooked_defect_positive hcard (hbad S hSA))
  have hp : (3520 : ℕ) ≤ (Pool S).card := hb
  norm_num [Psi, potential] at hnear
  omega

theorem actual_obligation {N : ℕ} {A : Finset (Finset ℤ)}
    (hlo : 210001 ≤ N) (hhi : N ≤ 220000)
    (hlegal : Legal (Ground N) A) (hbad : ∀ S ∈ A, ¬IsAP S)
    (hsize : ∀ S ∈ A, 137 ≤ S.card) (hsparse : ∀ S ∈ A, 12*S.card ≤ N) :
    UnitNearObligation N A G CoeffA CoeffB CoeffC := by
  refine ⟨Psi, 8, psi_mono, psi_zero, reciprocal, ?_⟩
  have hs : (∑ i ∈ Finset.range 8, (Psi (i+1)-Psi i)*((PoolNear A Psi i).card : ℝ)) ≤
      ∑ i ∈ Finset.range 8, (Psi (i+1)-Psi i)*Cost N i := by
    apply Finset.sum_le_sum
    intro i hi
    have hi8 := Finset.mem_range.mp hi
    by_cases he : i=0
    · subst i
      simp [free_empty hhi hlegal hbad hsize, Cost]
    · have hi7 : i-1 < 7 := by omega
      have hl := links hi7
      have hb := Layer200000.actual_upper (N := N) (k := 7+(i-1)) (ell := i) (psi := Psi)
        (by omega) (by simpa only [hl.1] using hlo) (by simpa only [hl.2.1] using hhi)
        hlegal hbad (by simpa only [hl.2.2.1] using hsize) hsparse (by
          have hindex : i-1+2 = i+1 := by omega
          dsimp only [Psi]
          rw [← hindex]
          exact_mod_cast hl.2.2.2)
      simp only [Cost, if_neg he]
      change _ ≤ (Psi (i+1)-Psi i)*Layer200000.Upper N (7+(i-1))
      exact mul_le_mul_of_nonneg_left hb (sub_nonneg.mpr (psi_mono (Nat.le_succ i)))
  have hp := mul_le_mul_of_nonneg_left hs (show 0 ≤ 6*G by have hh := g_positive; positivity)
  exact hp.trans_eq (fee N)

theorem actual_source {N : ℕ} {A F : Finset (Finset ℤ)}
    (hlo : 210001 ≤ N) (hhi : N ≤ 220000)
    (hlegal : Legal (Ground N) A) (hbad : ∀ S ∈ A, ¬IsAP S)
    (hsize : ∀ S ∈ A, 137 ≤ S.card) (hsparse : ∀ S ∈ A, 12*S.card ≤ N) (hAF : A ⊆ F) :
    (A.card : ℝ) ≤ 6*G*(∑ S ∈ F, ((Pool S).card : ℝ))+SourceUpper N := by
  have hb := SevenFamily208.actual_unit_source hAF g_positive.le (actual_obligation hlo hhi hlegal hbad hsize hsparse)
  simpa only [SourceUpper, add_assoc] using hb

#print axioms fee
#print axioms free_empty
#print axioms actual_obligation
#print axioms actual_source
end
end JSP233.SourcePayment200000W1
