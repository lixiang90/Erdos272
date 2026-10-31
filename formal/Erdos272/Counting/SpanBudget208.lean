import Erdos272.Counting.ConflictBudget208

/-! Finite integer unit segments give the exact span sum. This is the
finite double-sum form of the phase integral, including ordered-pair correction. -/
namespace JSP233.SpanBudget208
open ConflictBudget208
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

variable {α : Type*} [DecidableEq α]

def Active (C : Finset α) (lo hi : α→ℤ) (z : ℤ) : Finset α :=
  C.filter (fun i => lo i≤z ∧ z<hi i)

theorem interval_card_real {a b : ℤ} (hab : a≤b) :
    ((Finset.Ico a b).card : ℝ)=(b : ℝ)-a := by
  have hZ : ((Finset.Ico a b).card : ℤ)=b-a := by
    rw [Int.card_Ico,Int.toNat_of_nonneg (sub_nonneg.mpr hab)]
  exact_mod_cast hZ

theorem active_weight_sum (C : Finset α) (lo hi : α→ℤ) (L R : ℤ) (w : α→ℝ)
    (hspan : ∀i∈C,L≤lo i ∧ lo i≤hi i ∧ hi i≤R) :
    (∑z∈Finset.Ico L R,∑i∈Active C lo hi z,w i)=
      ∑i∈C,w i*((hi i : ℝ)-lo i) := by
  simp only [Active,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hiC
  have hs := hspan i hiC
  have hI : (Finset.Ico L R).filter (fun z => lo i≤z ∧ z<hi i)=Finset.Ico (lo i) (hi i) := by
    ext z
    simp only [Finset.mem_filter,Finset.mem_Ico]
    omega
  rw [←Finset.sum_filter,hI]
  simp only [Finset.sum_const,nsmul_eq_mul,interval_card_real hs.2.1]
  ring

theorem active_pair_sum (Rel : α→α→Prop) (C : Finset α) (lo hi : α→ℤ)
    (L R : ℤ) (w : α→ℝ)
    (hspan : ∀i∈C,L≤lo i ∧ lo i≤hi i ∧ hi i≤R) :
    (∑z∈Finset.Ico L R,PairCost Rel w (Active C lo hi z))=
      ∑i∈C,∑j∈C,Cost Rel w i j*
        (((Finset.Ico (lo i) (hi i))∩Finset.Ico (lo j) (hi j)).card : ℝ) := by
  have hpoint : ∀z,PairCost Rel w (Active C lo hi z)=
      ∑i∈C,∑j∈C,if (lo i≤z ∧ z<hi i) ∧ (lo j≤z ∧ z<hi j) then Cost Rel w i j else 0 := by
    intro z
    simp only [PairCost,Active,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hp : lo i≤z ∧ z<hi i <;> simp [hp]
  simp_rw [hpoint]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hiC
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hjC
  have hiS := hspan i hiC
  have hjS := hspan j hjC
  have hI : (Finset.Ico L R).filter (fun z => (lo i≤z ∧ z<hi i) ∧ (lo j≤z ∧ z<hi j))=
      (Finset.Ico (lo i) (hi i))∩Finset.Ico (lo j) (hi j) := by
    ext z
    simp only [Finset.mem_filter,Finset.mem_Ico,Finset.mem_inter]
    omega
  rw [←Finset.sum_filter,hI]
  simp only [Finset.sum_const,nsmul_eq_mul,mul_comm]

theorem pair_overlap_sum_bound (Rel : α→α→Prop) (C : Finset α) (lo hi : α→ℤ)
    (w : α→ℝ) (K : ℝ)
    (hover : ∀i∈C,∀j∈C,i≠j → Cost Rel w i j*
      (((Finset.Ico (lo i) (hi i))∩Finset.Ico (lo j) (hi j)).card : ℝ)≤K) :
    (∑i∈C,∑j∈C,Cost Rel w i j*
      (((Finset.Ico (lo i) (hi i))∩Finset.Ico (lo j) (hi j)).card : ℝ))≤
      K*((C.card : ℝ)^2-C.card) := by
  let f := fun p : α×α => Cost Rel w p.1 p.2*
    (((Finset.Ico (lo p.1) (hi p.1))∩Finset.Ico (lo p.2) (hi p.2)).card : ℝ)
  have heq : C.offDiag=(C.product C).filter (fun p => p.1≠p.2) := by
    ext p
    simp only [Finset.mem_offDiag,Finset.mem_filter,Finset.product_eq_sprod,Finset.mem_product]
    tauto
  have hs : (∑i∈C,∑j∈C,Cost Rel w i j*
      (((Finset.Ico (lo i) (hi i))∩Finset.Ico (lo j) (hi j)).card : ℝ))=
      ∑p∈C.offDiag,f p := by
    rw [heq,Finset.sum_filter,Finset.product_eq_sprod,Finset.sum_product]
    apply Finset.sum_congr rfl
    intro i hiC
    apply Finset.sum_congr rfl
    intro j hjC
    by_cases hij : i=j <;> simp [f,Cost,hij]
  rw [hs]
  have hb := Finset.sum_le_sum (s := C.offDiag) (fun p hp =>
    hover p.1 (Finset.mem_offDiag.mp hp).1 p.2 (Finset.mem_offDiag.mp hp).2.1
      (Finset.mem_offDiag.mp hp).2.2)
  have hsq : C.card≤C.card*C.card := by
    by_cases h0 : C.card=0
    · simp [h0]
    · have h1 : 1≤C.card := by omega
      nlinarith only [h1]
  have hc : (C.offDiag.card : ℝ)=(C.card : ℝ)^2-C.card := by
    rw [Finset.offDiag_card,Nat.cast_sub hsq,Nat.cast_mul]
    ring
  simp only [Finset.sum_const,nsmul_eq_mul] at hb
  rw [hc] at hb
  simpa only [f,mul_comm] using hb

theorem span_budget (Rel : α→α→Prop) (C : Finset α) (lo hi : α→ℤ)
    (L R : ℤ) (w : α→ℝ) (mu K : ℝ) (hLR : L≤R)
    (hspan : ∀i∈C,L≤lo i ∧ lo i≤hi i ∧ hi i≤R)
    (hlocal : ∀z∈Finset.Ico L R,(∑i∈Active C lo hi z,w i)≤mu+PairCost Rel w (Active C lo hi z)/2)
    (hover : ∀i∈C,∀j∈C,i≠j → Cost Rel w i j*
      (((Finset.Ico (lo i) (hi i))∩Finset.Ico (lo j) (hi j)).card : ℝ)≤K) :
    (∑i∈C,w i*((hi i : ℝ)-lo i))≤
      mu*((R : ℝ)-L)+K/2*((C.card : ℝ)^2-C.card) := by
  have hs := Finset.sum_le_sum hlocal
  rw [active_weight_sum C lo hi L R w hspan,Finset.sum_add_distrib,
    Finset.sum_const,nsmul_eq_mul,interval_card_real hLR,←Finset.sum_div,
    active_pair_sum Rel C lo hi L R w hspan] at hs
  have hp := pair_overlap_sum_bound Rel C lo hi w K hover
  linarith only [hs,hp]

#print axioms active_weight_sum
#print axioms active_pair_sum
#print axioms pair_overlap_sum_bound
#print axioms span_budget
end
end JSP233.SpanBudget208
