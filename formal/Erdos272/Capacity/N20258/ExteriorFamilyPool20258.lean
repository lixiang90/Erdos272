module

public import Erdos272.Geometry.N20258.ExteriorDichotomy20258
public import Erdos272.Capacity.N20258.TwoOutsidePool20258

@[expose] public section
namespace JSP233.ExteriorFamilyPool20258
open StarCompletion SourceBridge208 IntrinsicTriples208 PrivatePairExistence PaddedSource20258
open ExteriorStrides20258
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false

private theorem midpoint : ∀ i : Fin 15,
    924≤(44+i.val).choose 2-(44+i.val)/2 := by decide +kernel

private def Cheap (S : Finset ℤ) := (Pool S).card+ (if S.card=44 then 42 else 0) < 924

private theorem exceptional {S : Finset ℤ} {N : ℕ} (hi : N≤2^18) (inN : S⊆Ground N)
    (bad : ¬IsAP S) (size : 44≤S.card) (cheap : Cheap S) :
    S.card≤59 ∧ ∃ d : ℕ, 0<d ∧ (fits S (S.card-2) (S.card-2) d ∨ fits S (S.card-2) (S.card-2) (-(d:ℤ))) := by
  unfold Cheap at cheap
  have small : S.card≤59 := by
    by_contra! big
    have h := UniformCardPool20258.pool_floor (s:=60) (h:=924) hi inN bad (by decide)
      (by decide) big (by decide +kernel)
    omega
  refine ⟨small,?_⟩
  have one := MixedCore200000.crooked_defect_positive (by omega : 2≤S.card) bad
  by_cases two : 2≤Defect S
  · have plenty := TwoOutsidePool20258.short (by omega) small two
    by_cases eqn : S.card=44
    · rw [eqn] at plenty
      norm_num [Nat.choose_two_right] at plenty
      simp only [eqn,if_true] at cheap
      omega
    · have p : (44:ℕ).choose 2≤(Pool S).card :=
        (Nat.choose_le_choose 2 (show 44≤S.card-1 by omega)).trans plenty
      norm_num [Nat.choose_two_right] at p
      omega
  obtain h|h := ExteriorDichotomy20258.actual (by omega) bad (by omega)
  · by_cases eqn : S.card=44
    · rw [eqn] at h
      norm_num [Nat.choose_two_right] at h
      simp only [eqn,if_true] at cheap
      omega
    · let i : Fin 15 := ⟨S.card-45,by omega⟩
      have p := midpoint i
      rw [show 44+i.val=S.card-1 by dsimp [i]; omega] at p
      omega
  · exact h

/-- The 44-site layer pays an additional 42 per member. All other missing
triples come from the near exterior shapes at at most sixteen sizes. -/
theorem actual {N : ℕ} {F G : Finset (Finset ℤ)} (hi : N≤2^18) (legal : Legal (Ground N) F)
    (sub : G⊆CrookedMembers F) (size : ∀ S∈G,44≤S.card) :
    924*(G.card:ℝ) ≤ mass F+24576*(N:ℝ)+42*((G.filter (fun S => S.card=44)).card:ℝ) := by
  let E := G.filter Cheap
  have subF : G⊆F := sub.trans (Finset.filter_subset _ _)
  have data (S : Finset ℤ) (hs : S∈E) :=
    exceptional hi (legal.1 S (subF (Finset.mem_filter.mp hs).1))
      (Finset.mem_filter.mp (sub (Finset.mem_filter.mp hs).1)).2
      (size S (Finset.mem_filter.mp hs).1) (Finset.mem_filter.mp hs).2
  let sizes := Finset.Icc 44 59
  have partition : E.card=∑ s∈sizes,(E.filter (fun S => S.card=s)).card :=
    Finset.card_eq_sum_card_fiberwise (fun S hs => Finset.mem_Icc.mpr
      ⟨size S (Finset.mem_filter.mp hs).1,(data S hs).1⟩)
  have each (s : ℕ) (_ : s∈sizes) : (E.filter (fun S => S.card=s)).card≤4*N := by
    apply four_per_site (m:=s-2) legal
      ((Finset.filter_subset _ _).trans ((Finset.filter_subset _ _).trans subF))
    intro S hs
    obtain ⟨mem,eqn⟩ := Finset.mem_filter.mp hs
    simpa only [←eqn] using (data S mem).2
  have rare : E.card≤64*N := by
    have sum := Finset.sum_le_sum each
    rw [←partition] at sum
    simp only [Finset.sum_const,nsmul_eq_mul,Nat.cast_id,show sizes.card=16 by decide] at sum
    omega
  have unit (S : Finset ℤ) (hs : S∈G) : (924:ℝ)≤((Pool S).card:ℝ)+
      (if S.card=44 then 42 else 0)+(if Cheap S then 384 else 0) := by
    have paid := UniformCardPool20258.pool_floor (s:=44) (h:=540) hi (legal.1 S (subF hs))
      (Finset.mem_filter.mp (sub hs)).2 (by decide) (by decide) (size S hs) (by decide +kernel)
    by_cases short : Cheap S
    · rw [if_pos short]
      have base : (540:ℝ)≤(Pool S).card := by exact_mod_cast paid
      split_ifs <;> linarith only [base]
    · rw [if_neg short,add_zero]
      have p : 924≤(Pool S).card+(if S.card=44 then 42 else 0) := Nat.le_of_not_gt short
      by_cases eqn : S.card=44
      · rw [if_pos eqn]
        have base : (882:ℝ)≤(Pool S).card := by
          exact_mod_cast (show 882≤(Pool S).card by simpa [eqn] using p)
        linarith only [base]
      · rw [if_neg eqn,add_zero]
        exact_mod_cast (show 924≤(Pool S).card by simpa [eqn] using p)
  have total := Finset.sum_le_sum unit
  simp only [Finset.sum_add_distrib,←Finset.sum_filter,Finset.sum_const,nsmul_eq_mul] at total
  have fr : (E.card:ℝ)≤64*(N:ℝ) := by exact_mod_cast rare
  have massBound := UniformCardPool20258.mass_mono subF
  unfold mass at massBound ⊢
  change _ ≤ _ + _ + (E.card:ℝ)*384 at total
  linarith only [total,fr,massBound]

#print axioms actual
end
end JSP233.ExteriorFamilyPool20258
