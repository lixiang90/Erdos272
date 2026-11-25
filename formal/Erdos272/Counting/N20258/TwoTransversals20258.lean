module

public import Erdos272.Counting.N20258.ShortTransversal20258

@[expose] public section
namespace JSP233.TwoTransversals20258
open StarCompletion PrivatePairExistence AnchorCompletion38 ShortTransversal20258
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false

/-- A member hits the overlap or an ordered pair of points in the two differences. -/
theorem two_transversals {α : Type*} [DecidableEq α]
    (H : Finset (Finset α)) (P Q : Finset α) (R D : ℕ)
    (hitP : ∀ S ∈ H, (S ∩ P).Nonempty) (hitQ : ∀ S ∈ H, (S ∩ Q).Nonempty)
    (single : ∀ x ∈ P ∩ Q, (H.filter fun S => x ∈ S).card ≤ R)
    (pair : ∀ x ∈ P \ Q, ∀ y ∈ Q \ P, (H.filter fun S => x ∈ S ∧ y ∈ S).card ≤ D) :
    H.card ≤ (P ∩ Q).card*R + (P \ Q).card*(Q \ P).card*D := by
  classical
  let A := P ∩ Q
  let B := (P \ Q) ×ˢ (Q \ P)
  let U := fun x : α => H.filter fun S => x ∈ S
  let V := fun xy : α × α => H.filter fun S => xy.1 ∈ S ∧ xy.2 ∈ S
  have cover : H ⊆ A.biUnion U ∪ B.biUnion V := by
    intro S hS
    by_cases hc : (S ∩ A).Nonempty
    · obtain ⟨x,hx⟩ := hc
      obtain ⟨hxS,hxA⟩ := Finset.mem_inter.mp hx
      exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
        ⟨x,hxA,Finset.mem_filter.mpr ⟨hS,hxS⟩⟩)
    · obtain ⟨x,hx⟩ := hitP S hS
      obtain ⟨y,hy⟩ := hitQ S hS
      obtain ⟨hxS,hxP⟩ := Finset.mem_inter.mp hx
      obtain ⟨hyS,hyQ⟩ := Finset.mem_inter.mp hy
      have hxQ : x ∉ Q := fun h => hc
        ⟨x,Finset.mem_inter.mpr ⟨hxS,Finset.mem_inter.mpr ⟨hxP,h⟩⟩⟩
      have hyP : y ∉ P := fun h => hc
        ⟨y,Finset.mem_inter.mpr ⟨hyS,Finset.mem_inter.mpr ⟨h,hyQ⟩⟩⟩
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨(x,y), Finset.mem_product.mpr ⟨Finset.mem_sdiff.mpr ⟨hxP,hxQ⟩,
          Finset.mem_sdiff.mpr ⟨hyQ,hyP⟩⟩, Finset.mem_filter.mpr ⟨hS,hxS,hyS⟩⟩)
  have numU : (A.biUnion U).card ≤ A.card*R := by
    apply Finset.card_biUnion_le.trans
    simpa using Finset.sum_le_sum (s := A) single
  have numV : (B.biUnion V).card ≤ B.card*D := by
    apply Finset.card_biUnion_le.trans
    have bound (xy : α × α) (hxy : xy ∈ B) : (V xy).card ≤ D :=
      pair xy.1 (Finset.mem_product.mp hxy).1 xy.2 (Finset.mem_product.mp hxy).2
    simpa using Finset.sum_le_sum bound
  have bound := (Finset.card_le_card cover).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add numU numV))
  simpa only [A,B,Finset.card_product] using bound

/-- The two test sets may be any nonempty members of the original family. -/
theorem actual_two {N m : ℕ} {F : Finset (Finset ℤ)} {P Q : Finset ℤ}
    (hN : 2 ≤ N) (hm : m+1 ≤ N) (hF : Legal (Ground N) F)
    (hP : P ∈ F) (pne : P.Nonempty) (hQ : Q ∈ F) (qne : Q.Nonempty)
    (omits : ∀ x ∈ Ground N, ∃ T ∈ CrookedMembers F, x ∉ T ∧ T.card ≤ m) :
    (CrookedMembers F).card ≤ (P ∩ Q).card*(m*(N-2)-m.choose 2) +
      (P \ Q).card*(Q \ P).card*(N-2) := by
  let H := CrookedMembers F
  have sub : H ⊆ F := Finset.filter_subset _ _
  have legal : Legal (Ground N) H :=
    ⟨fun S hS => hF.1 S (sub hS), fun S hS T hT => hF.2 S (sub hS) T (sub hT)⟩
  have bad : ∀ S ∈ H, ¬IsAP S := fun _ hS => (Finset.mem_filter.mp hS).2
  have hits (U : Finset ℤ) (hU : U ∈ F) (ne : U.Nonempty) (S : Finset ℤ) (hS : S ∈ H) :
      (S ∩ U).Nonempty := by
    by_cases h : S=U
    · simpa [h] using ne
    · exact isAP_nonempty (hF.2 S (sub hS) U hU h)
  apply two_transversals H P Q _ _ (hits P hP pne) (hits Q hQ qne)
  · intro x hx
    obtain ⟨T,hT,miss,small⟩ := omits x (hF.1 P hP (Finset.mem_inter.mp hx).1)
    have b := (SparseSmall39.actual_degree_from_omitter legal bad hT miss).trans
      (SparseSmall39.degreeBudget_mono N small)
    have eqn := SparseSmall39.degreeBudget_closed N m hN hm
    change (RootPart H x).card ≤ _
    omega
  · intro x hx y hy
    let C := H.filter (fun S => x ∈ S ∧ y ∈ S)
    change C.card ≤ _
    by_cases ne : C.Nonempty
    · have csub : C ⊆ H := Finset.filter_subset _ _
      have cl : Legal (Ground N) C :=
        ⟨fun S hS => legal.1 S (csub hS), fun S hS T hT => legal.2 S (csub hS) T (csub hT)⟩
      have xy : x ≠ y := fun eq => (Finset.mem_sdiff.mp hx).2 (eq ▸ (Finset.mem_sdiff.mp hy).1)
      have h := actual_two_point_crooked_ground_capacity (Ground N) C x y xy ne cl
        (fun S hS => bad S (csub hS)) (fun _ hS => (Finset.mem_filter.mp hS).2.1)
        (fun _ hS => (Finset.mem_filter.mp hS).2.2)
      rw [ground_card] at h
      omega
    · simp [Finset.not_nonempty_iff_eq_empty.mp ne]

/-- Choosing a small omitter of a point of the test member saves a full
incidence for each point after the first. -/
theorem actual_member {N m : ℕ} {F : Finset (Finset ℤ)} {P : Finset ℤ}
    (hN : 2 ≤ N) (hm : m+1 ≤ N) (hF : Legal (Ground N) F) (hP : P ∈ F) (ne : P.Nonempty)
    (omits : ∀ x ∈ Ground N, ∃ T ∈ CrookedMembers F, x ∉ T ∧ T.card ≤ m) :
    (CrookedMembers F).card ≤ ((m-1)*P.card+1)*(N-2) := by
  obtain ⟨x,hx⟩ := ne
  obtain ⟨Q,hQ,miss,qm⟩ := omits x (hF.1 P hP hx)
  have hQF := (Finset.mem_filter.mp hQ).1
  have meet := isAP_nonempty (hF.2 P hP Q hQF (by rintro rfl; exact miss hx))
  have qne : Q.Nonempty := meet.mono Finset.inter_subset_right
  have h := actual_two hN hm hF hP ⟨x,hx⟩ hQF qne omits
  let i := (P ∩ Q).card
  have ip : i < P.card := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
    ⟨Finset.inter_subset_left,fun eq => miss (Finset.mem_inter.mp (eq ▸ hx)).2⟩)
  have pos : 1 ≤ i := Finset.card_pos.mpr meet
  have eqp : (P \ Q).card+i=P.card := Finset.card_sdiff_add_card_inter P Q
  have eqq : (Q \ P).card+i=Q.card := by
    simpa [i,Finset.inter_comm] using Finset.card_sdiff_add_card_inter Q P
  have im : i ≤ m := by omega
  have bound : i*m+(P \ Q).card*(Q \ P).card ≤ (m-1)*P.card+1 := by
    have qbound : (Q \ P).card ≤ m-i := by omega
    have prod := Nat.mul_le_mul_left (P \ Q).card qbound
    have ident : (m-i)+i=m := by omega
    have mpred : m-1+1=m := by omega
    have gap : (P \ Q).card≥1 := by omega
    have posprod := Nat.mul_le_mul_left (i-1) gap
    have ipred : i-1+1=i := by omega
    nlinarith only [prod,posprod,ident,mpred,eqp,ipred]
  have cost := Nat.mul_le_mul_left i (Nat.sub_le (m*(N-2)) (m.choose 2))
  change (CrookedMembers F).card ≤ i*_+_ at h
  exact h.trans ((Nat.add_le_add_right cost _).trans
    (by simpa only [Nat.add_mul,Nat.mul_assoc] using Nat.mul_le_mul_right (N-2) bound))

theorem actual_short_member {N m : ℕ} {F : Finset (Finset ℤ)} {P : Finset ℤ}
    (hN : 2 ≤ N) (hm : m+1 ≤ N) (hF : Legal (Ground N) F) (hP : P ∈ F) (ap : IsAP P)
    (omits : ∀ x ∈ Ground N, ∃ T ∈ CrookedMembers F, x ∉ T ∧ T.card ≤ m) :
    (CrookedMembers F).card ≤ ((m-1)*P.card+1)*(N-2) :=
  actual_member hN hm hF hP (isAP_nonempty ap) omits

#print axioms actual_two
#print axioms actual_member
#print axioms actual_short_member

end
end JSP233.TwoTransversals20258
