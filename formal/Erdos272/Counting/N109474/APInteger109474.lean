module

public import Erdos272.Counting.N118533.APCodeContraction118533

@[expose] public section

namespace JSP233.APInteger109474
open StarCompletion SourceBridge208 ActualAPCount208 APCodeContraction118533
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

theorem count_integer_bound {S : Finset ℤ} {a h q B : ℕ}
    (hh : 1 ≤ h) (hhq : h ≤ q) (hqa : q < a) (hmax : MaxAPSize S ≤ a)
    (hbound : (Codes S h).card ≤ B) :
    (Codes S q).card ≤ (a-q)*(B/(a-h))+(B%(a-h)-(q-h)) := by
  let b := B/(a-h)
  let r := B%(a-h)
  change (Codes S q).card ≤ (a-q)*b+(r-(q-h))
  have hz := codes_empty_of_max hmax
  have ht := count_eq_sum_ends hqa.le hz
  have hh' := count_eq_sum_ends (hhq.trans hqa.le) hz
  by_cases hd : (Ends S q).card ≤ b
  · have htail : (Codes S q).card ≤ (a-q)*b := by
      rw [ht]
      calc
        _ ≤ ∑ _j ∈ Finset.Ico q a, b := by
          apply Finset.sum_le_sum
          intro j hj
          exact (ends_card_antitone (hh.trans hhq) (Finset.mem_Ico.mp hj).1).trans hd
        _ = _ := by simp
    exact htail.trans (Nat.le_add_right _ _)
  · have hd' : b+1 ≤ (Ends S q).card := by omega
    have hhead : (q-h)*(b+1) ≤ ∑ j ∈ Finset.Ico h q, (Ends S j).card := by
      calc
        _ = ∑ _j ∈ Finset.Ico h q, (b+1) := by simp
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro j hj
          exact hd'.trans (ends_card_antitone (hh.trans (Finset.mem_Ico.mp hj).1)
            (Finset.mem_Ico.mp hj).2.le)
    have hsplit := Finset.sum_Ico_consecutive (fun j => (Ends S j).card) hhq hqa.le
    rw [← hh', ← ht] at hsplit
    have he : B = (a-h)*b+r := by
      dsimp only [b, r]
      have hm := Nat.mod_add_div B (a-h)
      omega
    have hpre : (Codes S q).card+(q-h)*(b+1) ≤ (a-h)*b+r := by omega
    have hcoef : a-h = (q-h)+(a-q) := by omega
    have hbase : (a-h)*b = (q-h)*b+(a-q)*b := by rw [hcoef]; ring
    have hstep : (q-h)*(b+1) = (q-h)*b+(q-h) := by ring
    rw [hbase, hstep] at hpre
    omega

#print axioms count_integer_bound
end
end JSP233.APInteger109474
