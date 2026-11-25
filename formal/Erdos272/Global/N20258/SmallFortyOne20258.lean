module

public import Erdos272.Counting.N20258.LengthTailBound20258
public import Erdos272.Counting.N20258.TwoTransversals20258
public import Erdos272.Capacity.N20258.LargeOmitter20258

@[expose] public section
namespace JSP233.SmallFortyOne20258
open StarCompletion PrivatePairExistence APClasses88404 IntrinsicTriples208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- One small actual member suffices in the branch in which every point
has a crooked omitter of at most 45 points. The length estimate pays all
integer grounds in the range at once. -/
theorem actual_upper {N : ℕ} {F : Finset (Finset ℤ)} {P : Finset ℤ}
    (lo : 20258 ≤ N) (hi : N < 2^16) (legal : Legal (Ground N) F)
    (hp : P ∈ F) (ps : P.card ≤ 41)
    (omits : ∀ x ∈ Ground N, ∃ T ∈ CrookedMembers F, x ∉ T ∧ T.card ≤ 45) : F.card ≤ B N := by
  by_contra counter
  have lower : (N.choose 2 : ℝ) < F.card := by
    exact_mod_cast (show N.choose 2 < F.card by unfold B at counter; omega)
  rw [Nat.cast_choose_two] at lower
  have nlo : (20258 : ℝ) ≤ N := by exact_mod_cast lo
  let H := CrookedMembers F
  have split : ((F.filter IsAP).card : ℝ)+H.card=F.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := F) IsAP
  have degree (S : Finset ℤ) (hs : S ∈ F) (ne : S.Nonempty) {k : ℕ} (sz : S.card ≤ k) :
      (H.card : ℝ) ≤ (44*(k : ℝ)+1)*((N : ℝ)-2) := by
    have b := TwoTransversals20258.actual_member (by omega : 2 ≤ N) (by omega : 45+1 ≤ N)
      legal hs ne omits
    have bound : H.card ≤ (44*k+1)*(N-2) := b.trans
      (Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.mul_le_mul_left 44 sz) _))
    have r : (H.card : ℝ) ≤ ((44*k+1)*(N-2) : ℕ) := by exact_mod_cast bound
    simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one,Nat.cast_sub (by omega : 2 ≤ N)] using r
  by_cases h : ∃ S ∈ F, IsAP S ∧ S.card ≤ 40
  · obtain ⟨S,hs,ap,sz⟩ := h
    have hD := degree S hs (isAP_nonempty ap) sz
    have joint := LargeOmitter20258.actual_joint (by omega : 1000 ≤ N) hi legal
    have mass : 0 ≤ 6*(1/(5*(N : ℝ)))*(∑ U ∈ F, ((Pool U).card : ℝ)) :=
      mul_nonneg (by positivity) (Finset.sum_nonneg (fun U _ => Nat.cast_nonneg _))
    have sq := mul_le_mul_of_nonneg_right nlo (Nat.cast_nonneg (α := ℝ) N)
    norm_num only [Nat.cast_ofNat] at hD
    nlinarith only [lower,hD,joint,mass,sq,split,nlo]
  · have positive : P.Nonempty := by
      by_contra no
      have empty := Finset.not_nonempty_iff_eq_empty.mp no
      have one : F.card ≤ 1 := Finset.card_le_one.mpr (by
        intro S hs T ht
        have eq (U : Finset ℤ) (hu : U ∈ F) : U=P := by
          by_contra different
          have m := isAP_nonempty (legal.2 U hu P hp different)
          simp [empty] at m
        exact (eq S hs).trans (eq T ht).symm)
      have r : (F.card : ℝ) ≤ 1 := by exact_mod_cast one
      have sq := mul_le_mul_of_nonneg_right nlo (Nat.cast_nonneg (α := ℝ) N)
      nlinarith only [r,lower,nlo,sq]
    have hD := degree P hp positive ps
    have part := ProgressionPartition20258.actual_AP_partition (N := N) (k := 40)
      (by omega : 1 ≤ N) legal ∅ (by simp) (by
        intro d _ S hs
        by_contra notlong
        exact h ⟨S,APClasses88404.subset F d hs,is_ap hs,by omega⟩)
    simp only [Finset.sum_empty,Nat.add_zero] at part
    have r : ((F.filter IsAP).card : ℝ) ≤ 1+(ProgressionPartition20258.offTail (N-1) 40 ∅ : ℕ) := by
      exact_mod_cast part
    have tail := LengthTailBound20258.forty (show N-1 < 2^16 by omega)
    rw [Nat.cast_sub (by omega : 1 ≤ N),Nat.cast_one] at tail
    norm_num only [Nat.cast_ofNat] at hD
    have gap := mul_nonneg (sub_nonneg.mpr nlo) (show 0 ≤ (N : ℝ)-1 by linarith only [nlo])
    nlinarith only [tail,hD,r,split,lower,gap,nlo]

#print axioms actual_upper

/-- A counterexample in the lower public window needs an omitter cutoff of at least 44. -/
theorem first_at_least_44 {N m : ℕ} {F : Finset (Finset ℤ)}
    (lo : 20258 ≤ N) (hi : N ≤ 21000) (legal : Legal (Ground N) F) (counter : B N < F.card)
    (covers : ∀ x ∈ Ground N, ∃ S ∈ CrookedMembers F, x ∉ S ∧ S.card ≤ m) : 44 ≤ m := by
  by_contra! small
  have smallOmitter (x : ℤ) (hx : x ∈ Ground N) :
      ∃ S ∈ CrookedMembers F, x ∉ S ∧ S.card ≤ 43 := by
    obtain ⟨S,hS,miss,sz⟩ := covers x hx
    exact ⟨S,hS,miss,by omega⟩
  have size (P : Finset ℤ) (hp : P ∈ F) : 41 < P.card := by
    by_contra! tiny
    exact (not_lt_of_ge (actual_upper lo (by omega) legal hp tiny (by
      intro x hx
      obtain ⟨T,hT,miss,sz⟩ := smallOmitter x hx
      exact ⟨T,hT,miss,by omega⟩))) counter
  obtain ⟨P,hP,_,sz⟩ := smallOmitter 1 ((mem_ground N 1).mpr ⟨by decide,by omega⟩)
  have mem := (Finset.mem_filter.mp hP).1
  have positive := size P mem
  have degree := TwoTransversals20258.actual_member (by omega : 2 ≤ N) (by omega : 43+1 ≤ N)
    legal mem (Finset.card_pos.mp (by omega)) smallOmitter
  have lim : ((CrookedMembers F).card : ℝ) ≤ 1807*((N : ℝ)-2) := by
    have coeff : (43-1)*P.card+1 ≤ 1807 := by omega
    have u := degree.trans (Nat.mul_le_mul_right (N-2) coeff)
    have uR : ((CrookedMembers F).card : ℝ) ≤ ((1807*(N-2) : ℕ) : ℝ) := by exact_mod_cast u
    simpa only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_sub (by omega : 2 ≤ N)] using uR
  have part := ProgressionPartition20258.actual_AP_partition (N := N) (k := 41)
    (by omega : 1 ≤ N) legal ∅ (by simp) (fun d _ S hS => size S (APClasses88404.subset F d hS))
  simp only [Finset.sum_empty,Nat.add_zero] at part
  have ap : ((F.filter IsAP).card : ℝ) ≤ 1+(ProgressionPartition20258.offTail (N-1) 41 ∅ : ℕ) := by
    exact_mod_cast part
  have tail := LengthTailBound20258.forty_one (show N-1 < 2^15 by omega)
  rw [Nat.cast_sub (by omega : 1 ≤ N),Nat.cast_one] at tail
  have sum : ((F.filter IsAP).card : ℝ)+(CrookedMembers F).card = F.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := F) IsAP
  have target : (N.choose 2 : ℝ) < F.card := by
    exact_mod_cast (show N.choose 2 < F.card by unfold B at counter; omega)
  rw [Nat.cast_choose_two] at target
  have hN : (20258 : ℝ) ≤ N := by exact_mod_cast lo
  have gap := mul_nonneg (sub_nonneg.mpr hN) (show 0 ≤ (N : ℝ)-1 by linarith only [hN])
  nlinarith only [lim,ap,tail,sum,target,hN,gap]

#print axioms first_at_least_44
end
end JSP233.SmallFortyOne20258
