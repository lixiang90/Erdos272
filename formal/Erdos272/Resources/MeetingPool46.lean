import Erdos272.Counting.WitnessInterval43

/-! Exact counting of the actual unordered meeting/outside pair pool. -/
namespace JSP233.MeetingPool46
open WitnessInterval43
open scoped Classical
noncomputable section

theorem actual_meeting_pairs_card_add (U P : Finset ℤ) :
    ((U.powersetCard 2).filter (fun Q=>¬Disjoint Q P)).card+
      (U\P).card.choose 2=U.card.choose 2 := by
  have he : (U.powersetCard 2).filter (fun Q=>Disjoint Q P)=(U\P).powersetCard 2 := by
    ext Q
    simp only [Finset.mem_filter,Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨hQU,hcard⟩,hdis⟩
      refine ⟨?_,hcard⟩
      intro x hx
      exact Finset.mem_sdiff.mpr ⟨hQU hx,fun hxP=>Finset.disjoint_left.mp hdis hx hxP⟩
    · rintro ⟨hQ,hcard⟩
      refine ⟨⟨fun x hx=>(Finset.mem_sdiff.mp (hQ hx)).1,hcard⟩,?_⟩
      exact Finset.disjoint_left.mpr (fun x hx hxP=>(Finset.mem_sdiff.mp (hQ hx)).2 hxP)
  have hh := Finset.card_filter_add_card_filter_not (s:=U.powersetCard 2)
    (fun Q=>Disjoint Q P)
  rw [he,Finset.card_powersetCard,Finset.card_powersetCard] at hh
  omega

theorem actual_meeting_pairs_card_real {U P : Finset ℤ} (hPU : P⊆U) :
    (((U.powersetCard 2).filter (fun Q=>¬Disjoint Q P)).card:ℝ)=
      (P.card:ℝ)*U.card-(P.card:ℝ)^2/2-(P.card:ℝ)/2 := by
  have hcard := actual_meeting_pairs_card_add U P
  have hpart : ((U\P).card:ℝ)+(P.card:ℝ)=U.card :=
    by exact_mod_cast Finset.card_sdiff_add_card_eq_card hPU
  have hcount : (((U.powersetCard 2).filter (fun Q=>¬Disjoint Q P)).card:ℝ)+
      ((U\P).card:ℝ)*((U\P).card-1)/2=(U.card:ℝ)*(U.card-1)/2 := by
    have hh : (((U.powersetCard 2).filter (fun Q=>¬Disjoint Q P)).card:ℝ)+
        (((U\P).card.choose 2:ℕ):ℝ)=((U.card.choose 2:ℕ):ℝ) := by exact_mod_cast hcard
    simpa only [Nat.cast_choose_two] using hh
  nlinarith only [hcount,hpart]

theorem actual_meeting_outside_card_add {U B : Finset ℤ} (hBU : B⊆U) (P : Finset ℤ) :
    (MeetingOutsidePairs U B P).card+
      ((B.powersetCard 2).filter (fun Q=>¬Disjoint Q (P∩B))).card=
      ((U.powersetCard 2).filter (fun Q=>¬Disjoint Q P)).card := by
  let M := (U.powersetCard 2).filter (fun Q=>¬Disjoint Q P)
  have hin : M.filter (fun Q=>Q⊆B)=(B.powersetCard 2).filter (fun Q=>¬Disjoint Q (P∩B)) := by
    ext Q
    constructor
    · intro hQ
      obtain ⟨hQM,hQB⟩ := Finset.mem_filter.mp hQ
      obtain ⟨hQU,hQP⟩ := Finset.mem_filter.mp hQM
      refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr
        ⟨hQB,(Finset.mem_powersetCard.mp hQU).2⟩,?_⟩
      intro hd
      exact hQP (Finset.disjoint_left.mpr (fun x hxQ hxP=>
        Finset.disjoint_left.mp hd hxQ (Finset.mem_inter.mpr ⟨hxP,hQB hxQ⟩)))
    · intro hQ
      obtain ⟨hQB,hQP⟩ := Finset.mem_filter.mp hQ
      obtain ⟨hsub,hcard⟩ := Finset.mem_powersetCard.mp hQB
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_powersetCard.mpr ⟨hsub.trans hBU,hcard⟩,?_⟩,hsub⟩
      intro hd
      exact hQP (Finset.disjoint_left.mpr (fun x hxQ hxPB=>
        Finset.disjoint_left.mp hd hxQ (Finset.mem_inter.mp hxPB).1))
  have hout : M.filter (fun Q=>¬Q⊆B)=MeetingOutsidePairs U B P := by
    simp only [M,MeetingOutsidePairs,Finset.filter_filter]
  have hh := Finset.card_filter_add_card_filter_not (s:=M) (fun Q=>Q⊆B)
  rw [hin,hout] at hh
  dsimp only [M] at hh
  omega

theorem actual_meeting_outside_card_real {U B P : Finset ℤ} (hBU : B⊆U) (hPU : P⊆U) :
    ((MeetingOutsidePairs U B P).card:ℝ)=
      ((P\B).card:ℝ)*U.card-((P\B).card:ℝ)^2/2-((P\B).card:ℝ)/2+
        ((P∩B).card:ℝ)*((U\B).card-((P\B).card:ℝ)) := by
  have hh : ((MeetingOutsidePairs U B P).card:ℝ)+
      (((B.powersetCard 2).filter (fun Q=>¬Disjoint Q (P∩B))).card:ℝ)=
      (((U.powersetCard 2).filter (fun Q=>¬Disjoint Q P)).card:ℝ) :=
    by exact_mod_cast actual_meeting_outside_card_add hBU P
  rw [actual_meeting_pairs_card_real hPU,
    actual_meeting_pairs_card_real Finset.inter_subset_right] at hh
  have hP : (P.card:ℝ)=((P\B).card:ℝ)+(P∩B).card :=
    by exact_mod_cast (Finset.card_sdiff_add_card_inter P B).symm
  have hU : (U.card:ℝ)=((U\B).card:ℝ)+B.card :=
    by exact_mod_cast (Finset.card_sdiff_add_card_eq_card hBU).symm
  rw [hP,hU] at hh
  rw [hU]
  nlinarith only [hh]

theorem actual_meeting_outside_card_le {U B P : Finset ℤ} (hBU : B⊆U) (hPU : P⊆U) :
    ((MeetingOutsidePairs U B P).card:ℝ)≤
      ((P\B).card:ℝ)*U.card-((P\B).card:ℝ)^2/2+
        ((P∩B).card:ℝ)*((U\B).card-((P\B).card:ℝ)) := by
  rw [actual_meeting_outside_card_real hBU hPU]
  linarith only [Nat.cast_nonneg (α:=ℝ) (P\B).card]

theorem actual_meeting_outside_card_twice {U B P : Finset ℤ} (hBU : B⊆U) (hPU : P⊆U) :
    2*(MeetingOutsidePairs U B P).card+(P\B).card^2+(P\B).card+
      2*(P∩B).card*(P\B).card=
        2*(P\B).card*U.card+2*(P∩B).card*(U\B).card := by
  have hh := actual_meeting_outside_card_real hBU hPU
  have hr : ((2*(MeetingOutsidePairs U B P).card+(P\B).card^2+(P\B).card+
      2*(P∩B).card*(P\B).card:ℕ):ℝ)=
        ((2*(P\B).card*U.card+2*(P∩B).card*(U\B).card:ℕ):ℝ) := by
    push_cast
    nlinarith only [hh]
  exact_mod_cast hr

#print axioms actual_meeting_pairs_card_add
#print axioms actual_meeting_pairs_card_real
#print axioms actual_meeting_outside_card_add
#print axioms actual_meeting_outside_card_real
#print axioms actual_meeting_outside_card_le
#print axioms actual_meeting_outside_card_twice
end
end JSP233.MeetingPool46
