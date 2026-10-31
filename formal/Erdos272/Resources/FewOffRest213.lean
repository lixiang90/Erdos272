import Erdos272.Resources.FewOff213
import Erdos272.Resources.AlignedPlans213
import Erdos272.Resources.ActualGrid213
namespace JSP233.FewOffRest213
open StarCompletion APGeometry ActualGrid212 FewOffGeometry212 FewOffGates212 OffResidue44 AlignedPlans212
open FewOff212 (Few source_count_lower)
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem actual_few_count {N L R k : ℕ} {F : Finset (Finset ℤ)}
    (d : Finset ℤ→ℕ) (a : Finset ℤ→ℤ)
    (hN : 646000≤N) (hk2 : 2≤k) (hk11 : k≤11)
    (hL : 1≤L) (hLR : L≤R) (hRN : R≤N) (hF : Legal (Ground N) F)
    (htrace : ∀S∈F,APAt (d S : ℤ) (a S) (S∩Finset.Icc (L : ℤ) (R : ℤ)))
    (hdense : ∀S∈F,(N : ℝ)<(k : ℝ)*S.card)
    (hwidth : (L : ℝ)+(N-R)<(N : ℝ)/(2951/100)) :
    ((Few N F (fun S => (d S : ℤ)) a).card : ℝ)≤
      ((SourceCount k : ℝ)-1)*((L : ℝ)+(N-R)-1) := by
  let E := Few N F (fun S => (d S : ℤ)) a
  let X := Ground N\Finset.Icc (L : ℤ) (R : ℤ)
  have hcover : E⊆X.biUnion (OffPoint E (fun S => (d S : ℤ)) a) := by
    intro S hS
    obtain ⟨hSF,hpos,hfew⟩ := Finset.mem_filter.mp hS
    obtain ⟨y,hy⟩ := Finset.card_pos.mp hpos
    obtain ⟨hyS,hyOff⟩ := Finset.mem_filter.mp hy
    have hyI : y∉Finset.Icc (L : ℤ) (R : ℤ) := by
      intro hyI
      exact hyOff (origin_dvd (htrace S hSF) (Finset.mem_inter.mpr ⟨hyS,hyI⟩))
    exact Finset.mem_biUnion.mpr ⟨y,Finset.mem_sdiff.mpr ⟨hF.1 S hSF hyS,hyI⟩,
      Finset.mem_filter.mpr ⟨hS,hyS,hyOff⟩⟩
  have hs : E.card≤(SourceCount k-1)*X.card := by
    calc
      _ ≤ (X.biUnion (OffPoint E (fun S => (d S : ℤ)) a)).card := Finset.card_le_card hcover
      _ ≤ ∑y∈X,(OffPoint E (fun S => (d S : ℤ)) a y).card := Finset.card_biUnion_le
      _ ≤ ∑_y∈X,(SourceCount k-1) := Finset.sum_le_sum (fun y _ =>
        FewOff213.actual_few_bucket d a y hN hk2 hk11 hL hLR hRN hF htrace hdense hwidth)
      _ = _ := by simp [Nat.mul_comm]
  have hsR : (E.card : ℝ)≤((SourceCount k-1 : ℕ) : ℝ)*X.card := by exact_mod_cast hs
  rw [Nat.cast_sub (by have hh := source_count_lower hk2 hk11;omega : 1≤SourceCount k),
    Nat.cast_one] at hsR
  rw [(actual_interval_ground_card hL hLR hRN).2] at hsR
  exact hsR

theorem actual_off_count {N L R k : ℕ} {F : Finset (Finset ℤ)}
    (d : Finset ℤ→ℕ) (a : Finset ℤ→ℤ)
    (hN : 646000≤N) (hk2 : 2≤k) (hk11 : k≤11)
    (hL : 1≤L) (hLR : L≤R) (hRN : R≤N) (hF : Legal (Ground N) F)
    (htrace : ∀S∈F,APAt (d S : ℤ) (a S) (S∩Finset.Icc (L : ℤ) (R : ℤ)))
    (hdense : ∀S∈F,(N : ℝ)<(k : ℝ)*S.card)
    (hwidth : (L : ℝ)+(N-R)<(N : ℝ)/(2951/100)) :
    ((OffMembers F (fun S => (d S : ℤ)) a).card : ℝ)≤
      ((SourceCount k : ℝ)-1)*((L : ℝ)+(N-R)-1)+904 := by
  let A := Few N F (fun S => (d S : ℤ)) a
  let H := HeavyOffMembers F (fun S => (d S : ℤ)) a ((3/5000 : ℝ)*N)
  have hth : (0 : ℝ)≤(3/5000 : ℝ)*N := by positivity
  have hmem : ∀S,S∈OffMembers F (fun S => (d S : ℤ)) a ↔
      S∈F ∧ 0<(ActualOffPoints S (d S) (a S)).card := by
    intro S
    simp only [OffMembers,Finset.mem_filter]
    constructor
    · rintro ⟨hSF,y,hy,hoff⟩
      exact ⟨hSF,Finset.card_pos.mpr ⟨y,Finset.mem_filter.mpr ⟨hy,hoff⟩⟩⟩
    · rintro ⟨hSF,hpos⟩
      obtain ⟨y,hy⟩ := Finset.card_pos.mp hpos
      exact ⟨hSF,y,(Finset.mem_filter.mp hy).1,(Finset.mem_filter.mp hy).2⟩
  have hpart : OffMembers F (fun S => (d S : ℤ)) a=A∪H := by
    ext S
    rw [hmem,Finset.mem_union]
    simp only [A,Few,H,HeavyOffMembers,Finset.mem_filter]
    constructor
    · rintro ⟨hSF,hpos⟩
      by_cases hfew : ((ActualOffPoints S (d S) (a S)).card : ℝ)≤(3/5000 : ℝ)*N
      · exact Or.inl ⟨hSF,hpos,hfew⟩
      · exact Or.inr ⟨hSF,lt_of_not_ge hfew⟩
    · rintro (⟨hSF,hpos,hfew⟩ | ⟨hSF,hlarge⟩)
      · exact ⟨hSF,hpos⟩
      · exact ⟨hSF,by exact_mod_cast (hth.trans_lt hlarge)⟩
  have hdisj : Disjoint A H := by
    apply Finset.disjoint_left.mpr
    intro S hA hH
    have hl := (Finset.mem_filter.mp hA).2.2
    have hh := (Finset.mem_filter.mp hH).2
    linarith only [hl,hh]
  have hd11 : ∀S∈F,(N : ℝ)<11*S.card := by
    intro S hS
    have hkR : (k : ℝ)≤11 := by exact_mod_cast hk11
    exact (hdense S hS).trans_le (mul_le_mul_of_nonneg_right hkR (Nat.cast_nonneg S.card))
  have hh := ActualGrid213.actual_heavy_off_count904 F (fun S => (d S : ℤ)) a (by omega : 640000≤N) hL hLR hRN hF htrace hd11 hwidth
  have hl := actual_few_count d a hN hk2 hk11 hL hLR hRN hF htrace hdense hwidth
  have hc : ((OffMembers F (fun S => (d S : ℤ)) a).card : ℝ)=(A.card : ℝ)+H.card := by
    rw [hpart,Finset.card_union_of_disjoint hdisj,Nat.cast_add]
  have hhR : (H.card : ℝ)≤904 := by exact_mod_cast hh
  change (A.card : ℝ)≤_ at hl
  linarith only [hc,hl,hhR]

theorem actual_terminal_family {N L R k : ℕ} {F : Finset (Finset ℤ)}
    (d : Finset ℤ→ℕ) (a : Finset ℤ→ℤ)
    (hN : 646000≤N) (hk2 : 2≤k) (hk11 : k≤11)
    (hL : 1≤L) (hLR : L≤R) (hRN : R≤N) (hF : Legal (Ground N) F)
    (hbad : ∀S∈F,¬IsAP S)
    (htrace : ∀S∈F,APAt (d S : ℤ) (a S) (S∩Finset.Icc (L : ℤ) (R : ℤ)))
    (hdense : ∀S∈F,(N : ℝ)<(k : ℝ)*S.card)
    (hwidth : (L : ℝ)+(N-R)<(N : ℝ)/(2951/100)) :
    (F.card : ℝ)≤(TerminalA k+(SourceCount k : ℝ)-1)*((L : ℝ)+(N-R))+
      TerminalB k-(SourceCount k : ℝ)+1+904 := by
  let A := F.filter (fun S => ∀y∈S,(d S : ℤ)∣y-a S)
  have hAF : A⊆F := Finset.filter_subset _ _
  have hA : Legal (Ground N) A := ⟨fun S hS => hF.1 S (hAF hS),
    fun S hS T hT hST => hF.2 S (hAF hS) T (hAF hT) hST⟩
  have ha := AlignedPlans213.actual_terminal_count d a (by omega : 640000≤N) hk2 hk11 hL hLR hRN hA
    (fun S hS => hbad S (hAF hS)) (fun S hS => htrace S (hAF hS))
    (fun S hS => (Finset.mem_filter.mp hS).2) (fun S hS => hdense S (hAF hS))
    (by linarith only [hwidth])
  have ho := actual_off_count d a hN hk2 hk11 hL hLR hRN hF htrace hdense hwidth
  have hoff : F.filter (fun S => ¬∀y∈S,(d S : ℤ)∣y-a S)=OffMembers F (fun S => (d S : ℤ)) a := by
    ext S
    simp only [Finset.mem_filter,OffMembers]
    push Not
    rfl
  have hc := Finset.card_filter_add_card_filter_not (s := F) (fun S => ∀y∈S,(d S : ℤ)∣y-a S)
  rw [hoff] at hc
  have hcR : (A.card : ℝ)+(OffMembers F (fun S => (d S : ℤ)) a).card=F.card := by exact_mod_cast hc
  nlinarith only [ha,ho,hcR]

theorem actual_terminal_k11 {N L R : ℕ} {F : Finset (Finset ℤ)}
    (d : Finset ℤ→ℕ) (a : Finset ℤ→ℤ)
    (hN : 646000≤N) (hL : 1≤L) (hLR : L≤R) (hRN : R≤N)
    (hF : Legal (Ground N) F) (hbad : ∀S∈F,¬IsAP S)
    (htrace : ∀S∈F,APAt (d S : ℤ) (a S) (S∩Finset.Icc (L : ℤ) (R : ℤ)))
    (hdense : ∀S∈F,(N : ℝ)<11*S.card)
    (hwidth : (L : ℝ)+(N-R)<(N : ℝ)/(2951/100)) :
    (F.card : ℝ)≤(16571/504 : ℝ)*((L : ℝ)+(N-R))+150757/168 := by
  have hh := actual_terminal_family (k := 11) d a hN (by decide) (by decide) hL hLR hRN hF hbad
    htrace hdense hwidth
  norm_num [SourceCount,TerminalA,TerminalB] at hh
  linarith only [hh]

#print axioms actual_few_count
#print axioms actual_off_count
#print axioms actual_terminal_family
#print axioms actual_terminal_k11
end
end JSP233.FewOffRest213
