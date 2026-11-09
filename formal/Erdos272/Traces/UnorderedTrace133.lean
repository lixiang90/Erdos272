module

public import Erdos272.Traces.RestrictedWitness44
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

namespace JSP233.UnorderedTrace133
open StarCompletion APGeometry RestrictedWitness44
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem actual_segment_isAP (c p : ℤ) {d : ℕ} (hd : 0<d) :
    IsAP (Segment c p d) := by
  refine ⟨(d:ℤ),c,by exact_mod_cast hd,min c p,max c p,?_,?_⟩
  · intro x
    simp only [Segment,Finset.mem_filter,Finset.mem_Icc,and_assoc]
  · exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨min_le_left _ _,le_max_left _ _⟩,by simp⟩

theorem actual_incompatible_code_symm {S : Finset ℤ} {c p : ℤ} {d e : ℕ}
    (h : IncompatibleCode S c p d e) : IncompatibleCode S c p e d := by
  refine ⟨h.2.1,h.1,?_⟩
  simpa only [Finset.union_comm] using h.2.2

theorem actual_incompatible_code_ne {S : Finset ℤ} {c p : ℤ} {d e : ℕ}
    (hd : 0<d) (h : IncompatibleCode S c p d e) : d≠e := by
  intro he
  subst e
  apply h.2.2
  exact ⟨Segment c p d,actual_segment_isAP c p hd,by simp,h.1⟩

theorem actual_incompatible_trace_code_sorted {S : Finset ℤ} {c p : ℤ}
    (hc : c∈S) (hcover : AllCovered S c p)
    (hbad : ¬IsAP (Trace S c p)) :
    ∃d e:ℕ,0<d ∧ d<e ∧ d∣Distance c p ∧ e∣Distance c p ∧
      IncompatibleCode S c p d e := by
  obtain ⟨d,e,hd,he,hdd,hed,hcode⟩ := actual_incompatible_trace_code hc hcover hbad
  have hne := actual_incompatible_code_ne hd hcode
  by_cases hde : d<e
  · exact ⟨d,e,hd,hde,hdd,hed,hcode⟩
  · exact ⟨e,d,he,by omega,hed,hdd,actual_incompatible_code_symm hcode⟩

theorem actual_crooked_trace_family_bound_unordered {Ω : Finset ℤ}
    {F : Finset (Finset ℤ)} {c : ℤ} (hF : Legal Ω F)
    (hc : ∀S∈F,c∈S) (p : {S // S∈F}→ℤ)
    (hp : ∀S,p S∈S.val ∧ p S≠c)
    (hcover : ∀S,AllCovered S.val c (p S))
    (hbad : ∀S,¬IsAP (Trace S.val c (p S))) :
    F.card≤∑q∈Ω,((Distance c q).divisors.card).choose 2 := by
  let X := {S // S∈F}
  have hex : ∀S:X,∃d e:ℕ,0<d ∧ d<e ∧ d∣Distance c (p S) ∧
      e∣Distance c (p S) ∧ IncompatibleCode S.val c (p S) d e :=
    fun S=>actual_incompatible_trace_code_sorted (hc S.val S.property) (hcover S) (hbad S)
  choose d e _hd hde hdd hed hcode using hex
  let U : Finset (Σ _ : ℤ,Finset ℕ) :=
    Ω.sigma (fun q=>(Distance c q).divisors.powersetCard 2)
  let f : X→(Σ _ : ℤ,Finset ℕ) := fun S=>⟨p S,{d S,e S}⟩
  have hm : Set.MapsTo f (↑(Finset.univ:Finset X):Set X) U := by
    intro S _hS
    have hD : Distance c (p S)≠0 := Int.natAbs_ne_zero.mpr (sub_ne_zero.mpr (hp S).2)
    apply Finset.mem_sigma.mpr
    refine ⟨hF.1 S.val S.property (hp S).1,Finset.mem_powersetCard.mpr ⟨?_,?_⟩⟩
    · intro k hk
      change k∈({d S,e S}:Finset ℕ) at hk
      simp only [Finset.mem_insert,Finset.mem_singleton] at hk
      rcases hk with rfl|rfl
      · exact Nat.mem_divisors.mpr ⟨hdd S,hD⟩
      · exact Nat.mem_divisors.mpr ⟨hed S,hD⟩
    · exact Finset.card_pair_eq_two_iff.mpr (Nat.ne_of_lt (hde S))
  have hi : Function.Injective f := by
    intro S T heq
    have hpST : p S=p T := congrArg Sigma.fst heq
    have hpair : ({d S,e S}:Finset ℕ)={d T,e T} :=
      congrArg (fun q:Σ _:ℤ,Finset ℕ=>q.2) heq
    have hsteps : ∀k∈({d S,e S}:Finset ℕ),Segment c (p S) k⊆T.val := by
      intro k hk
      rw [hpair] at hk
      simp only [Finset.mem_insert,Finset.mem_singleton] at hk
      rcases hk with rfl|rfl
      · simpa only [hpST] using (hcode T).1
      · simpa only [hpST] using (hcode T).2.1
    apply Subtype.ext
    exact actual_trace_code_private hF S.property T.property (hcode S)
      (hsteps (d S) (by simp)) (hsteps (e S) (by simp))
  have hh := Finset.card_le_card_of_injOn f hm hi.injOn
  simpa [X,U,Finset.card_sigma,Finset.card_powersetCard] using hh

#print axioms actual_segment_isAP
#print axioms actual_incompatible_code_symm
#print axioms actual_incompatible_code_ne
#print axioms actual_incompatible_trace_code_sorted
#print axioms actual_crooked_trace_family_bound_unordered
end
end JSP233.UnorderedTrace133
