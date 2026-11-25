module

public import Erdos272.Counting.N20258.ConcentratedMarks20258
public import Erdos272.Counting.N20258.MarkedPopulation20258

@[expose] public section
namespace JSP233.ConcentratedPopulation20258
open StarCompletion APGeometry SourceBridge208 FarCapacity112
open scoped Classical BigOperators
set_option autoImplicit false

/-- Using 2 as a lower bound for every proper divisor ratio suffices here. -/
def occupancy (n a k d : ℕ) : ℕ :=
  (if d*a<n then 1 else 0)+(if d*(2*a-min k (a/2))<n then 1 else 0)

def perStride (n a k top d : ℕ) : ℕ :=
  let o := occupancy n a k d
  let s := min top ((n-1)/d+1+k)
  let u := n*o/(a+1)
  n*o+k*(2*(k+1)*(2*s*o)+k*u)

def budget (n a k top : ℕ) := ∑ d∈Finset.Icc 1 ((n-1)/a),perStride n a k top d

private theorem span {S P : Finset ℤ} {n a d : ℕ} (ground : S⊆Ground n)
    (core : MaximumAPCore S P) (stride : ∃ p,APAt (d:ℤ) p P) (len : a+1≤P.card) : d*a<n := by
  obtain ⟨p,ap⟩ := stride
  obtain ⟨t,ht⟩ := isAP_nonempty core.2.1
  have h := ResidualOccupancy208.actual_single_span ground core.1 (apAt_rebase ap ht) ht len
  rw [← Nat.cast_mul] at h
  omega

private theorem stride {n a k top d : ℕ} {A : Finset (Finset ℤ)} {P : Finset ℤ → Finset ℤ}
    (legal : Legal (Ground n) A) (pos : 0<d) (core : ∀ S∈A,MaximumAPCore S (P S))
    (step : ∀ S∈A,∃ p,APAt (d:ℤ) p (P S)) (large : ∀ S∈A,a+1≤(P S).card)
    (few : ∀ S∈A,(S\P S).card≤k) (size : ∀ S∈A,S.card≤top) :
    ∑ S∈A,(S\P S).card≤perStride n a k top d := by
  classical
  let H (t : ℤ) := A.filter (fun S => t∈P S)
  have sub (t : ℤ) : H t⊆A := Finset.filter_subset _ _
  have pair (t x : ℤ) : ((H t).filter (fun S => x∈S\P S)).card≤occupancy n a k d := by
    have hit (S : Finset ℤ) (hs : S∈H t) : t∈P S := (Finset.mem_filter.mp hs).2
    have legalH : Legal (Ground n) (H t) := ⟨fun S hs => legal.1 S (sub t hs),
      fun S hs T ht => legal.2 S (sub t hs) T (sub t ht)⟩
    have bound := ResidualOccupancy208.actual_cumulative_occupancy (b:=k+1) legalH (by decide : 2≤2) P
      (fun S hs => maximum_core_is_maximal (core S (sub t hs))) (fun S hs => by
        obtain ⟨p,ap⟩ := step S (sub t hs)
        exact apAt_rebase ap (hit S hs)) hit (fun S hs => large S (sub t hs))
      (fun S hs R ap inc => (core S (sub t hs)).2.2 R inc ap) (fun _ => StepClass208.ratio_two) x
    apply (Finset.card_le_card ?_).trans (bound.trans_eq ?_)
    · intro S hs
      obtain ⟨mem,mark⟩ := Finset.mem_filter.mp hs
      exact Finset.mem_filter.mpr ⟨mem,mark,Nat.lt_succ_of_le (few S (sub t mem))⟩
    · simp only [occupancy,ResidualSpan208.Span,Nat.add_sub_cancel,Nat.reduceSub,Nat.div_one,←Nat.cast_mul (α:=ℤ)]
      split_ifs <;> omega
  have outer (x : ℤ) : (A.filter (fun S => x∈S\P S)).card≤n*occupancy n a k d/(a+1) := by
    let G := A.filter (fun S => x∈S\P S)
    have ga : G⊆A := Finset.filter_subset _ _
    apply (Nat.le_div_iff_mul_le (Nat.succ_pos a)).mpr
    calc
      _ = ∑ _S∈G,(a+1) := by simp [G]
      _ ≤ ∑ S∈G,(P S).card := Finset.sum_le_sum (fun S hs => large S (ga hs))
      _ ≤ occupancy n a k d*(Ground n).card := ResidualPool208.incidence_capacity G (Ground n) P _
        (fun S hs => (core S (ga hs)).1.trans (legal.1 S (ga hs))) (fun t _ => by
          have eq : G.filter (fun S => t∈P S)=(H t).filter (fun S => x∈S\P S) := by
            ext S; simp [G,H,and_comm,and_left_comm]
          rw [eq]; exact pair t x)
      _ = _ := by rw [ground_card,Nat.mul_comm]
  apply ConcentratedMarks20258.weight (fun S hs => isAP_nonempty (core S hs).2.1) step ?_ few ?_ ?_ pair outer
  · intro S hs T ht
    by_cases eq : S=T
    · subst T; simpa using (isAP_nonempty (core S hs).2.1).mono (core S hs).1
    · exact isAP_nonempty (legal.2 S hs T ht eq)
  · intro S hs
    apply le_min (size S hs)
    have h := span (legal.1 S hs) (core S hs) (step S hs)
      (show (P S).card-1+1≤(P S).card by have := large S hs; omega)
    have limit := (Nat.le_div_iff_mul_le pos).mpr
      (show ((P S).card-1)*d≤n-1 by rw [Nat.mul_comm]; omega)
    have parts := Finset.card_sdiff_add_card_eq_card (core S hs).1
    have := few S hs
    omega
  · intro t
    simpa only [ground_card,Nat.mul_comm n] using ResidualPool208.incidence_capacity
      (H t) (Ground n) (fun S => S\P S) _ (fun S hs => Finset.sdiff_subset.trans (legal.1 S (sub t hs)))
      (fun x _ => pair t x)

/-- Sum over one actual maximum core per member. Each stride contributes
one full pivot charge and a bounded-depth remainder. -/
theorem actual {n a k top : ℕ} {A : Finset (Finset ℤ)} (legal : Legal (Ground n) A)
    (pos : 0<a) (large : ∀ S∈A,a+1+k≤S.card) (size : ∀ S∈A,S.card≤top)
    (few : ∀ S∈A,Defect S≤k) : ∑ S∈A,Defect S≤budget n a k top := by
  classical
  obtain ⟨P,step,chosen⟩ := FarJoint112.exists_maximum_core_selection
    (F:=A) (fun S hs => Finset.card_pos.mp (by have := large S hs; omega))
  have card (S : Finset ℤ) (hs : S∈A) : (P S).card=MaxAPSize S := by
    have h := (chosen S hs).1
    exact le_antisymm (AP_card_le_max h.2.1 h.1) (Finset.sup_le (fun R hr =>
      h.2.2 R (Finset.mem_powerset.mp (Finset.mem_filter.mp hr).1) (Finset.mem_filter.mp hr).2))
  have remnant (S : Finset ℤ) (hs : S∈A) : (S\P S).card=Defect S := by
    rw [Finset.card_sdiff_of_subset (chosen S hs).1.1,card S hs]; rfl
  have len (S : Finset ℤ) (hs : S∈A) : a+1≤(P S).card := by
    have h := few S hs
    unfold Defect at h
    rw [card S hs]
    have := large S hs
    omega
  let D := Finset.Icc 1 ((n-1)/a)
  have maps (S : Finset ℤ) (hs : S∈A) : step S∈D := by
    obtain ⟨p,ap⟩ := (chosen S hs).2
    have h := span (legal.1 S hs) (chosen S hs).1 (chosen S hs).2 (len S hs)
    have := ap.1
    exact Finset.mem_Icc.mpr ⟨by omega,(Nat.le_div_iff_mul_le pos).mpr (by omega)⟩
  change _≤∑ d∈D,perStride n a k top d
  rw [←Finset.sum_fiberwise_of_maps_to maps Defect]
  apply Finset.sum_le_sum
  intro d hd
  let G := A.filter (fun S => step S=d)
  have sub : G⊆A := Finset.filter_subset _ _
  have legalG : Legal (Ground n) G := ⟨fun S hs => legal.1 S (sub hs),fun S hs T ht => legal.2 S (sub hs) T (sub ht)⟩
  change ∑ S∈G,Defect S≤_
  rw [Finset.sum_congr rfl (fun S (hs : S∈G) => (remnant S (sub hs)).symm)]
  exact stride legalG (Finset.mem_Icc.mp hd).1 (fun S hs => (chosen S (sub hs)).1)
    (fun S hs => by rw [←(Finset.mem_filter.mp hs).2]; exact (chosen S (sub hs)).2)
    (fun S hs => len S (sub hs)) (fun S hs => (remnant S (sub hs)).le.trans (few S (sub hs)))
    (fun S hs => size S (sub hs))

#print axioms actual
end JSP233.ConcentratedPopulation20258
