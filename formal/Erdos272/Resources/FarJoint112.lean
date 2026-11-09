module

public import Erdos272.Resources.FarCapacity112
public import Erdos272.Retention.LongTerminal35

@[expose] public section

/-! One actual physical slot pool for Long core-shell codes and Short intrinsic
codes.  The latter exclude every other actual source, including AP members.
No common root, omitted member or abstract capacity assumption is used.

This module proves the joint pool itself.  Source-wise Short mass is left as
an explicit interface for the separate actual adjacent-gap geometry module.
-/
namespace JSP233.FarJoint112
open StarCompletion APGeometry NearAP36 FarSlot112 FarCapacity112 LongTerminal35
open scoped Classical BigOperators
noncomputable section

def IntrinsicSlotCodes (N D : ℕ) (S : Finset ℤ) : Finset (ℕ × (ℤ × ℤ)) :=
  (PhysicalSlots N D).filter (fun q => q.2.1 ∈ S ∧
    IntrinsicPair q.2.1 S {q.2.1 + (q.1 : ℤ), q.2.2})

theorem mem_intrinsicSlotCodes {N D : ℕ} {S : Finset ℤ} {q : ℕ × (ℤ × ℤ)} :
    q ∈ IntrinsicSlotCodes N D S ↔ q ∈ PhysicalSlots N D ∧ q.2.1 ∈ S ∧
      IntrinsicPair q.2.1 S {q.2.1 + (q.1 : ℤ), q.2.2} := by
  exact Finset.mem_filter

/-- An intrinsic triple of one actual source cannot occur in another actual
member.  The distinguished point is local to the code, not a family root. -/
theorem actual_intrinsic_slot_private {Ω : Finset ℤ} {F : Finset (Finset ℤ)}
    {S T : Finset ℤ} {a b x : ℤ} (hF : Legal Ω F)
    (hS : S ∈ F) (hT : T ∈ F) (hne : S ≠ T) (haS : a ∈ S)
    (hI : IntrinsicPair a S {b, x}) (haT : a ∈ T) (hbT : b ∈ T) (hxT : x ∈ T) :
    False := by
  apply hI.2.2.2
  refine ⟨S ∩ T, hF.2 S hS T hT hne, ?_, Finset.inter_subset_left⟩
  apply Finset.insert_subset_iff.mpr
  refine ⟨Finset.mem_inter.mpr ⟨haS, haT⟩, ?_⟩
  intro y hy
  apply Finset.mem_inter.mpr
  refine ⟨hI.2.2.1 hy, ?_⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with rfl | rfl
  · exact hbT
  · exact hxT

def JointCodes (N D : ℕ) (core : Finset ℤ → Finset ℤ)
    (step : Finset ℤ → ℕ) (short : Finset ℤ → Prop) (S : Finset ℤ) :
    Finset (ℕ × (ℤ × ℤ)) :=
  if short S then IntrinsicSlotCodes N D S else CoreShellCodes S (core S) (step S)

theorem joint_code_points {N D : ℕ} {S : Finset ℤ}
    {core : Finset ℤ → Finset ℤ} {step : Finset ℤ → ℕ}
    {short : Finset ℤ → Prop} {q : ℕ × (ℤ × ℤ)} (hcore : core S ⊆ S)
    (hq : q ∈ JointCodes N D core step short S) :
    q.2.1 ∈ S ∧ q.2.1 + (q.1 : ℤ) ∈ S ∧ q.2.2 ∈ S := by
  by_cases hs : short S
  · have hi := mem_intrinsicSlotCodes.mp (by simpa only [JointCodes, if_pos hs] using hq)
    exact ⟨hi.2.1, hi.2.2.2.2.1 (by simp), hi.2.2.2.2.1 (by simp)⟩
  · have hc := mem_coreShellCodes.mp (by simpa only [JointCodes, if_neg hs] using hq)
    refine ⟨hcore hc.2.1, ?_, (Finset.mem_sdiff.mp hc.2.2.2).1⟩
    apply hcore
    simpa only [hc.1] using hc.2.2.1

/-- A mixed slot fiber has at most two actual sources.  If any Short source
uses it, intrinsic exclusion gives capacity one; otherwise use FarSlot112. -/
theorem actual_joint_fiber_card_le_two {N D : ℕ} {Ω : Finset ℤ}
    {F : Finset (Finset ℤ)} (hF : Legal Ω F)
    (core : Finset ℤ → Finset ℤ) (step : Finset ℤ → ℕ) (short : Finset ℤ → Prop)
    (hcore : ∀ S ∈ F, MaximalAPCore S (core S))
    (hAt : ∀ S ∈ F, ∃ p, APAt (step S) p (core S)) (q : ℕ × (ℤ × ℤ)) :
    (F.filter (fun S => q ∈ JointCodes N D core step short S)).card ≤ 2 := by
  let H := F.filter (fun S => q ∈ JointCodes N D core step short S)
  have hsub : H ⊆ F := Finset.filter_subset _ _
  have hpoints : ∀ S ∈ H, q.2.1 ∈ S ∧ q.2.1 + (q.1 : ℤ) ∈ S ∧ q.2.2 ∈ S := by
    intro S hS
    exact joint_code_points (hcore S (hsub hS)).1 (Finset.mem_filter.mp hS).2
  by_cases hex : ∃ S ∈ H, short S
  · obtain ⟨S, hS, hs⟩ := hex
    have hI := mem_intrinsicSlotCodes.mp (show q ∈ IntrinsicSlotCodes N D S by
      simpa only [JointCodes, if_pos hs] using (Finset.mem_filter.mp hS).2)
    have heq : ∀ T ∈ H, T = S := by
      intro T hT
      by_contra hne
      exact actual_intrinsic_slot_private hF (hsub hS) (hsub hT) (Ne.symm hne)
        hI.2.1 hI.2.2 (hpoints T hT).1 (hpoints T hT).2.1 (hpoints T hT).2.2
    have hcard : H.card ≤ 1 := Finset.card_le_one.mpr
      (fun T hT U hU => (heq T hT).trans (heq U hU).symm)
    exact hcard.trans (by omega)
  · have hlong : H ⊆ F.filter (fun S => q ∈ CoreShellCodes S (core S) (step S)) := by
      intro S hS
      have hs : ¬ short S := fun h => hex ⟨S, hS, h⟩
      exact Finset.mem_filter.mpr ⟨hsub hS, by
        simpa only [JointCodes, if_neg hs] using (Finset.mem_filter.mp hS).2⟩
    exact (Finset.card_le_card hlong).trans
      (actual_code_fiber_card_le_two hF core step hcore hAt q)

theorem joint_codes_subset_slots {N D : ℕ} {F : Finset (Finset ℤ)}
    (hF : ∀ S ∈ F, S ⊆ Ground N) (core : Finset ℤ → Finset ℤ)
    (step : Finset ℤ → ℕ) (short : Finset ℤ → Prop)
    (hcore : ∀ S ∈ F, core S ⊆ S)
    (hcut : ∀ S ∈ F, ¬ short S → 1 ≤ step S ∧ step S ≤ D) :
    ∀ S ∈ F, JointCodes N D core step short S ⊆ PhysicalSlots N D := by
  intro S hS
  by_cases hs : short S
  · simp only [JointCodes, if_pos hs]
    exact Finset.filter_subset _ _
  · simp only [JointCodes, if_neg hs]
    exact coreShellCodes_subset_slots (hF S hS) (hcore S hS)
      (hcut S hS hs).1 (hcut S hS hs).2

/-- The actual joint pool bound.  The source-wise mass premise is explicit;
its Short branch must be supplied by actual adjacent-gap geometry, not by an
assumed capacity or an unchecked count. -/
theorem actual_joint_count_of_mass {N D μ : ℕ} {F : Finset (Finset ℤ)}
    (hF : Legal (Ground N) F) (core : Finset ℤ → Finset ℤ)
    (step : Finset ℤ → ℕ) (short : Finset ℤ → Prop)
    (hcore : ∀ S ∈ F, MaximalAPCore S (core S))
    (hAt : ∀ S ∈ F, ∃ p, APAt (step S) p (core S))
    (hcut : ∀ S ∈ F, ¬ short S → 1 ≤ step S ∧ step S ≤ D)
    (hmass : ∀ S ∈ F, μ ≤ (JointCodes N D core step short S).card) :
    μ * F.card ≤ 2 * D * N ^ 2 := by
  let slots := PhysicalSlots N D
  let rel : Finset ℤ → (ℕ × (ℤ × ℤ)) → Prop :=
    fun S q => q ∈ JointCodes N D core step short S
  have hcodes := joint_codes_subset_slots hF.1 core step short
    (fun S hS => (hcore S hS).1) hcut
  have hcount := Finset.card_mul_le_card_mul (s := F) (t := slots) (r := rel)
    (m := μ) (n := 2)
    (by
      intro S hS
      have he : slots.bipartiteAbove rel S = JointCodes N D core step short S := by
        ext q
        simp only [Finset.mem_bipartiteAbove]
        exact and_iff_right_of_imp (fun hq => hcodes S hS hq)
      rw [he]
      exact hmass S hS)
    (by
      intro q _
      exact actual_joint_fiber_card_le_two hF core step short hcore hAt q)
  dsimp [slots] at hcount
  rw [physicalSlots_card] at hcount
  nlinarith

/-- Maximum-cardinality cores and positive natural steps can be selected from
the actual nonempty sources; they are not additional objects postulated by
the joint count.  Values outside the actual finite family are irrelevant. -/
theorem exists_maximum_core_selection {F : Finset (Finset ℤ)}
    (hne : ∀ S ∈ F, S.Nonempty) :
    ∃ (core : Finset ℤ → Finset ℤ) (step : Finset ℤ → ℕ),
      ∀ S ∈ F, MaximumAPCore S (core S) ∧ ∃ p, APAt (step S) p (core S) := by
  have hex : ∀ S : F, ∃ (P : Finset ℤ) (d : ℕ),
      MaximumAPCore S.val P ∧ ∃ p, APAt d p P := by
    intro S
    obtain ⟨P, hP⟩ := exists_maximum_AP_core (hne S.val S.property)
    obtain ⟨d, p, hAt, _⟩ := (isAP_iff_exists_APAt P).mp hP.2.1
    have hd : (d.toNat : ℤ) = d := Int.toNat_of_nonneg (le_of_lt hAt.1)
    exact ⟨P, d.toNat, hP, p, by simpa only [hd] using hAt⟩
  choose core step hcoords using hex
  let c : Finset ℤ → Finset ℤ := fun S => if h : S ∈ F then core ⟨S, h⟩ else ∅
  let d : Finset ℤ → ℕ := fun S => if h : S ∈ F then step ⟨S, h⟩ else 1
  refine ⟨c, d, ?_⟩
  intro S hS
  simpa only [c, d, dif_pos hS] using hcoords ⟨S, hS⟩

/-- The no-square-root cutoff works also for K=1 and M=2. -/
theorem far_cutoff_arithmetic {K : ℕ} (hK : 0 < K) :
    let t := 5 * K / 3
    1 ≤ t ∧ t + 1 ≤ 3 * K ∧ K * t ≤ (3 * K - t) ^ 2 := by
  dsimp
  let t := 5 * K / 3
  have ht : 1 ≤ t := by dsimp [t]; omega
  have hM : t + 1 ≤ 3 * K := by dsimp [t]; omega
  have ht3 : 3 * t ≤ 5 * K := by dsimp [t]; omega
  let u := 3 * K - t
  have hu : 4 * K ≤ 3 * u := by dsimp [u]; omega
  refine ⟨ht, hM, ?_⟩
  change K * t ≤ u ^ 2
  have hsq := Nat.mul_le_mul hu hu
  have hmul := Nat.mul_le_mul_left K ht3
  nlinarith

#print axioms mem_intrinsicSlotCodes
#print axioms actual_intrinsic_slot_private
#print axioms joint_code_points
#print axioms actual_joint_fiber_card_le_two
#print axioms joint_codes_subset_slots
#print axioms actual_joint_count_of_mass
#print axioms exists_maximum_core_selection
#print axioms far_cutoff_arithmetic

end
end JSP233.FarJoint112
