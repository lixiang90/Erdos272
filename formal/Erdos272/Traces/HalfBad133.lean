import Erdos272.Traces.UnorderedTrace133

namespace JSP233.HalfBad133
open StarCompletion APGeometry RestrictedWitness44 UnorderedTrace133
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

def HalfWitnessException (Ω : Finset ℤ) (c : ℤ) : ℕ :=
  (∑q∈Ω,((Distance c q).divisors.card).choose 2)+
    2*∑q∈Ω,(Distance c q).divisors.card

theorem actual_restricted_bad_crooked_bound_half {Ω : Finset ℤ}
    {F : Finset (Finset ℤ)} (c : ℤ) (P : Finset ℤ) (hF : Legal Ω F) :
    (CrookedTraceBad F c P).card≤
      ∑q∈Ω,((Distance c q).divisors.card).choose 2 := by
  let C := CrookedTraceBad F c P
  have hCF : C⊆F := fun S hS=>(Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).1
  have hlegal : Legal Ω C := ⟨fun S hS=>hF.1 S (hCF hS),
    fun S hS T hT he=>hF.2 S (hCF hS) T (hCF hT) he⟩
  apply actual_crooked_trace_family_bound_unordered hlegal
    (fun S hS=>(Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2.1)
    (fun S=>Anchor S.val c P)
  · intro S
    have ha := Finset.mem_inter.mp (actual_bad_anchor_mem (Finset.mem_filter.mp S.property).1)
    exact ⟨(Finset.mem_erase.mp ha.1).2,(Finset.mem_erase.mp ha.1).1⟩
  · intro S
    exact actual_bad_anchor_covered (Finset.mem_filter.mp S.property).1
  · intro S
    exact (Finset.mem_filter.mp S.property).2

theorem actual_restricted_bad_family_bound_half {Ω : Finset ℤ}
    {F : Finset (Finset ℤ)} (c : ℤ) (P : Finset ℤ) (hF : Legal Ω F) :
    (BadMembers F c P).card≤HalfWitnessException Ω c := by
  have hC := actual_restricted_bad_crooked_bound_half c P hF
  have hA := actual_restricted_bad_AP_trace_bound c P hF
  have hp := actual_bad_trace_partition F c P
  dsimp only [HalfWitnessException]
  omega

theorem actual_segment_step_antitone {c p : ℤ} {d e : ℕ} (hde : d∣e) :
    Segment c p e⊆Segment c p d := by
  have hdeZ : (d:ℤ)∣(e:ℤ) := by exact_mod_cast hde
  intro x hx
  obtain ⟨hxI,hex⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_filter.mpr ⟨hxI,hdeZ.trans hex⟩

theorem actual_incompatible_code_not_dvd {S : Finset ℤ} {c p : ℤ} {d e : ℕ}
    (hd : 0<d) (h : IncompatibleCode S c p d e) : ¬d∣e := by
  intro hde
  apply h.2.2
  refine ⟨Segment c p d,actual_segment_isAP c p hd,?_,h.1⟩
  exact Finset.union_subset (Finset.Subset.refl _) (actual_segment_step_antitone hde)

theorem actual_incompatible_code_neither_dvd {S : Finset ℤ} {c p : ℤ} {d e : ℕ}
    (hd : 0<d) (he : 0<e) (h : IncompatibleCode S c p d e) :
    ¬d∣e ∧ ¬e∣d := by
  exact ⟨actual_incompatible_code_not_dvd hd h,
    actual_incompatible_code_not_dvd he (actual_incompatible_code_symm h)⟩

#print axioms actual_restricted_bad_crooked_bound_half
#print axioms actual_restricted_bad_family_bound_half
#print axioms actual_segment_step_antitone
#print axioms actual_incompatible_code_not_dvd
#print axioms actual_incompatible_code_neither_dvd
end
end JSP233.HalfBad133
