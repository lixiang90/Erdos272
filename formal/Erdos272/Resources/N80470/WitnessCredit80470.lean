module

public import Erdos272.Counting.HeavyCredit208

@[expose] public section

namespace JSP233.WitnessCredit80470
open StarCompletion APGeometry
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem actual_disjoint_core_fiber_cap {Ω A₀ W : Finset ℤ}
    {F H : Finset (Finset ℤ)} (core : Finset ℤ→Finset ℤ)
    (hlegal : Legal Ω F) (hHF : H⊆F) (hA : A₀∈F)
    (hsub : ∀ S∈H, core S⊆S) (hne : ∀ S∈H, (core S).Nonempty)
    (hwindow : ∀ S∈H, core S⊆W) (havoid : Disjoint W A₀)
    (hdisjoint : ∀ S∈H, ∀ T∈H, S≠T→Disjoint (S\core S) (T\core T)) :
    H.card≤A₀.card := by
  have hex : ∀ S : H, ∃ x : A₀, x.val∈S.val\core S.val := by
    intro S
    have hSA : S.val≠A₀ := by
      intro he
      obtain ⟨z,hz⟩ := hne S.val S.property
      have hzA : z∈A₀ := he ▸ hsub S.val S.property hz
      exact Finset.disjoint_left.mp havoid (hwindow S.val S.property hz) hzA
    obtain ⟨x,hx⟩ := isAP_nonempty (hlegal.2 S.val (hHF S.property) A₀ hA hSA)
    obtain ⟨hxS,hxA⟩ := Finset.mem_inter.mp hx
    have hxcore : x∉core S.val := by
      intro hx
      exact Finset.disjoint_left.mp havoid (hwindow S.val S.property hx) hxA
    exact ⟨⟨x,hxA⟩,Finset.mem_sdiff.mpr ⟨hxS,hxcore⟩⟩
  choose f hf using hex
  apply Finset.card_le_card_of_injective (f:=f)
  intro S T hST
  apply Subtype.ext
  by_contra hneST
  have hd := hdisjoint S.val S.property T.val T.property hneST
  apply Finset.disjoint_left.mp hd (hf S)
  rw [show (f S).val=(f T).val from congrArg Subtype.val hST]
  exact hf T

def Cost (θ W : ℕ) (hit : Prop) : ℕ := min θ W+if hit then θ-W else 0

theorem cost_le_threshold (θ W : ℕ) (hit : Prop) : Cost θ W hit≤θ := by
  by_cases hhit : hit
  · simp only [Cost,if_pos hhit]
    omega
  · simp only [Cost,if_neg hhit,add_zero]
    exact min_le_left _ _

theorem cost_eq_of_hit {θ W : ℕ} {hit : Prop} (hhit : hit) : Cost θ W hit=θ := by
  simp only [Cost,if_pos hhit]
  omega

theorem cost_eq_of_small {θ W : ℕ} {hit : Prop} (hθ : θ≤W) : Cost θ W hit=θ := by
  simp only [Cost,min_eq_left hθ,Nat.sub_eq_zero_of_le hθ]
  split_ifs <;> omega

theorem actual_light_credit {ι : Type*} [DecidableEq ι] {F : Finset (Finset ℤ)}
    (label : Finset ℤ→ι) (I H : Finset ι) (θ T : ι→ℕ) (W : ℕ) (hit : ι→Prop)
    (hmap : ∀ S∈F, label S∈I)
    (hlight : ∀ i∈I, i∉H→(F.filter (fun S => label S=i)).card≤θ i)
    (hheavy : ∀ i∈I, i∈H→θ i<(F.filter (fun S => label S=i)).card)
    (hcredit : ∀ i∈I, i∈H→T i≤θ i)
    (hmiss : ∀ i∈I, ¬hit i→(F.filter (fun S => label S=i)).card≤W) :
    F.card+(∑ i∈I, if i∈H then T i else 0)≤
      (∑ i∈I, Cost (θ i) W (hit i))+(F.filter (fun S => label S∈H)).card := by
  apply HeavyCredit208.actual_light_credit label I H (fun i => Cost (θ i) W (hit i)) T hmap
  · intro i hi hnot
    by_cases hhit : hit i
    · rw [cost_eq_of_hit hhit]
      exact hlight i hi hnot
    · have hθ := hlight i hi hnot
      have hW := hmiss i hi hhit
      simp only [Cost,if_neg hhit,add_zero]
      exact le_min hθ hW
  · intro i hi hh
    by_cases hhit : hit i
    · rw [cost_eq_of_hit hhit]
      exact hcredit i hi hh
    · have hW := hmiss i hi hhit
      have hθ := hheavy i hi hh
      have hsmall : θ i≤W := by omega
      rw [cost_eq_of_small hsmall]
      exact hcredit i hi hh

theorem cost_sum_upper {ι : Type*} [DecidableEq ι] (I : Finset ι)
    (θ : ι→ℕ) (W U m : ℕ) (hit : ι→Prop)
    (hupper : ∀ i∈I, θ i≤U) (hhits : (I.filter hit).card≤W*m) :
    (∑ i∈I, Cost (θ i) W (hit i))≤(∑ i∈I, min (θ i) W)+W*m*(U-W) := by
  have heq : (∑ i∈I, Cost (θ i) W (hit i))=
      (∑ i∈I, min (θ i) W)+(∑ i∈I.filter hit, (θ i-W)) := by
    simp only [Cost,Finset.sum_add_distrib,Finset.sum_filter]
  rw [heq]
  apply Nat.add_le_add_left
  calc
    (∑ i∈I.filter hit, (θ i-W))≤∑ i∈I.filter hit, (U-W) := by
      apply Finset.sum_le_sum
      intro i hi
      exact Nat.sub_le_sub_right (hupper i (Finset.mem_filter.mp hi).1) W
    _=(I.filter hit).card*(U-W) := by simp [Nat.mul_comm]
    _≤W*m*(U-W) := Nat.mul_le_mul_right _ hhits

theorem hitting_windows_card {ι : Type*} [DecidableEq ι] (I : Finset ι)
    (window : ι→Finset ℤ) (A₀ : Finset ℤ) (W m : ℕ)
    (hcard : A₀.card≤W)
    (hpoint : ∀ x∈A₀, (I.filter (fun i => x∈window i)).card≤m) :
    (I.filter (fun i => ((window i)∩A₀).Nonempty)).card≤W*m := by
  have heq : I.filter (fun i => ((window i)∩A₀).Nonempty)=
      A₀.biUnion (fun x => I.filter (fun i => x∈window i)) := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_biUnion,Finset.nonempty_def,Finset.mem_inter]
    aesop
  rw [heq]
  calc
    (A₀.biUnion (fun x => I.filter (fun i => x∈window i))).card≤
        ∑ x∈A₀, (I.filter (fun i => x∈window i)).card := Finset.card_biUnion_le
    _≤∑ _x∈A₀, m := Finset.sum_le_sum hpoint
    _=A₀.card*m := by simp [Nat.mul_comm]
    _≤W*m := Nat.mul_le_mul_right _ hcard

#print axioms actual_disjoint_core_fiber_cap
#print axioms cost_le_threshold
#print axioms cost_eq_of_hit
#print axioms cost_eq_of_small
#print axioms actual_light_credit
#print axioms cost_sum_upper
#print axioms hitting_windows_card
end
end JSP233.WitnessCredit80470
