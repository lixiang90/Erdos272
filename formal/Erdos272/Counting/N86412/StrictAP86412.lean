module

public import Erdos272.Counting.N86412.APOptimalShape86412
public import Erdos272.Counting.N86412.EndTemplate86412
public import Erdos272.Counting.N86412.APSingleHole86412
public import Erdos272.Counting.N86412.APDoubleHole86412

@[expose] public section

namespace JSP233.StrictAP86412
open StarCompletion SourceBridge208 ActualAPCount208 APInterval208 PureSource208
open APOptimalShape86412 EndTemplate86412 APTemplatePrefix86412 APTemplateSets86412
open APSingleHole86412 APDoubleHole86412
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem optimal_nonAP_rigidity {S : Finset ℤ} {q : ℕ}
    (hq : 3≤q) (hqs : q<S.card) (hnot : ¬IsAP S)
    (heq : (Codes S q).card=intervalMultiplicity S.card q) :
    q∣S.card ∧ S.card-1≤MaxAPSize S := by
  have hn : 4≤S.card := by omega
  obtain ⟨d, hd, hshape⟩ := optimal_shape q S hq hqs heq
  obtain ⟨a, l, r, hl, hr, hraw⟩ := gap_shape_template hd hshape hn
  have hform : S=Template a d S.card l r := hraw
  have hdouble : ¬(l=1 ∧ r=1) := by
    rintro ⟨hl1, hr1⟩
    rw [hl1, hr1] at hform
    exact no_double_hole hd hq hqs rfl hform heq
  have hedge : l=0 ∨ r=0 := by omega
  have hlarge := template_large_AP (a := a) hd hn hedge
  rw [← hform] at hlarge
  refine ⟨?_, hlarge⟩
  by_cases hl0 : l=0
  · by_cases hr0 : r=0
    · rw [hl0, hr0] at hform
      have hap := template_isAP (a := a) hd hn
      rw [← hform] at hap
      exact (hnot hap).elim
    · have hr1 : r=1 := by omega
      rw [hl0, hr1] at hform
      exact right_hole_divides hd hq hqs rfl hform heq
  · have hl1 : l=1 := by omega
    have hr0 : r=0 := by omega
    rw [hl1, hr0] at hform
    exact left_hole_divides hd hq hqs rfl hform heq

theorem actual_strict_count {S : Finset ℤ} {q : ℕ}
    (hq : 3≤q) (hqs : q<S.card) (hnot : ¬IsAP S)
    (hstrict : 2≤Defect S ∨ ¬q∣S.card) :
    (Codes S q).card+1≤ intervalMultiplicity S.card q := by
  have hbase := actual_AP_count_le_interval (by omega : 1≤q) S
  by_contra hh
  have heq : (Codes S q).card=intervalMultiplicity S.card q := by omega
  have hrigid := optimal_nonAP_rigidity hq hqs hnot heq
  rcases hstrict with hdef | hdiv
  · have hmax := maxAPSize_le_card S
    unfold Defect at hdef
    omega
  · exact hdiv hrigid.1

def Eps (s e q : ℕ) : ℕ := if 3≤q ∧ (2≤e ∨ ¬q∣s) then 1 else 0
def CountBound (s e q : ℕ) : ℕ := intervalMultiplicity s q-Eps s e q

theorem interval_zero_of_le {s q : ℕ} (h : s≤q) : intervalMultiplicity s q=0 := by
  unfold intervalMultiplicity
  apply Finset.sum_eq_zero
  intro d hd
  have hd1 : 1≤d := (Finset.mem_Icc.mp hd).1
  have hp : q≤d*q := by simpa only [one_mul] using Nat.mul_le_mul_right q hd1
  exact Nat.sub_eq_zero_of_le (h.trans hp)

theorem notAP_of_defect {S : Finset ℤ} {e : ℕ} (he : 1≤e) (heD : e≤Defect S) :
    ¬IsAP S := by
  intro hap
  have hself := AP_card_le_max hap (Finset.Subset.refl S)
  have hmax := maxAPSize_le_card S
  unfold Defect at heD
  omega

theorem actual_count_le {S : Finset ℤ} {e q : ℕ}
    (he : 1≤e) (heD : e≤Defect S) (hq : 1≤q) :
    (Codes S q).card≤CountBound S.card e q := by
  have hbase := actual_AP_count_le_interval hq S
  unfold CountBound Eps
  split_ifs with hstrict
  · by_cases hqs : q<S.card
    · have hh := actual_strict_count hstrict.1 hqs (notAP_of_defect he heD)
        (by rcases hstrict.2 with he2 | hdiv
            · exact Or.inl (he2.trans heD)
            · exact Or.inr hdiv)
      omega
    · have hz : intervalMultiplicity S.card q=0 := interval_zero_of_le (by omega : S.card≤q)
      have hc0 : (Codes S q).card=0 := by omega
      rw [hc0]
      exact Nat.zero_le _
  · simpa only [Nat.sub_zero] using hbase

#print axioms optimal_nonAP_rigidity
#print axioms actual_strict_count
#print axioms interval_zero_of_le
#print axioms notAP_of_defect
#print axioms actual_count_le
end
end JSP233.StrictAP86412
