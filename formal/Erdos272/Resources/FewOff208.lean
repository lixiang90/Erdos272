import Erdos272.Counting.ActualPhase208
import Erdos272.Resources.FewOffGeometry208
import Erdos272.Arithmetic.FewOffGates208
import Erdos272.Resources.AlignedPlans208

/-! Actual few-off buckets, followed by the disjoint heavy/few split.
The phase d,a is fixed before either count is performed. -/
namespace JSP233.FewOff208
open StarCompletion APGeometry ActualGrid208 FewOffGeometry208 FewOffGates208
open OffResidue44 AlignedPlans208
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

def Few (N : ℕ) (F : Finset (Finset ℤ)) (d a : Finset ℤ→ℤ) : Finset (Finset ℤ) :=
  F.filter (fun S => 0<(ActualOffPoints S (d S) (a S)).card ∧
    ((ActualOffPoints S (d S) (a S)).card : ℝ)≤(3/5000 : ℝ)*N)

theorem source_count_lower {k : ℕ} (hk2 : 2≤k) (hk11 : k≤11) : 2≤SourceCount k := by
  interval_cases k <;> norm_num [SourceCount]

theorem actual_few_bucket {N L R k : ℕ} {F : Finset (Finset ℤ)}
    (d : Finset ℤ→ℕ) (a : Finset ℤ→ℤ) (y : ℤ)
    (hN : 659912≤N) (hk2 : 2≤k) (hk11 : k≤11)
    (hL : 1≤L) (hLR : L≤R) (hRN : R≤N) (hF : Legal (Ground N) F)
    (htrace : ∀S∈F,APAt (d S : ℤ) (a S) (S∩Finset.Icc (L : ℤ) (R : ℤ)))
    (hdense : ∀S∈F,(N : ℝ)<(k : ℝ)*S.card)
    (hwidth : (L : ℝ)+(N-R)<(N : ℝ)/(148/5)) :
    (OffPoint (Few N F (fun S => (d S : ℤ)) a) (fun S => (d S : ℤ)) a y).card≤SourceCount k-1 := by
  let E := Few N F (fun S => (d S : ℤ)) a
  let B := OffPoint E (fun S => (d S : ℤ)) a y
  have hEF : E⊆F := Finset.filter_subset _ _
  have hBF : B⊆F := (Finset.filter_subset _ _).trans hEF
  by_contra hbig
  have hn := source_count_lower hk2 hk11
  obtain ⟨C,hCB,hCc⟩ := Finset.exists_subset_card_eq
    (show SourceCount k≤B.card by change ¬B.card≤SourceCount k-1 at hbig;omega)
  let T := fun S : Finset ℤ => S∩Finset.Icc (L : ℤ) (R : ℤ)
  have hCF : C⊆F := hCB.trans hBF
  have hfew : ∀S∈C,0<(ActualOffPoints S (d S) (a S)).card ∧
      ((ActualOffPoints S (d S) (a S)).card : ℝ)≤(3/5000 : ℝ)*N := by
    intro S hS
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp (hCB hS)).1).2
  have hsteps : ∀S∈C,2≤d S ∧ d S≤11 := by
    intro S hS
    have hdpos : 0<d S := by exact_mod_cast (htrace S (hCF hS)).1
    exact actual_few_step_domain hN (hF.1 S (hCF hS)) hdpos hk11
      (hdense S (hCF hS)) (hfew S hS).2 (hfew S hS).1
  have hlower : ∀S∈C,(N : ℝ)/k-(3/5000 : ℝ)*N-((L : ℝ)+(N-R))/2-3<(T S).card-1 := by
    intro S hS
    exact actual_few_trace_lower hL hLR hRN (hsteps S hS).1 (by omega : 0<k)
      (hF.1 S (hCF hS)) (htrace S (hCF hS)) (hdense S (hCF hS)) (hfew S hS).2
  have hbase : (0 : ℝ)≤(N : ℝ)/k-(3/5000 : ℝ)*N-((L : ℝ)+(N-R))/2-3 := by
    have hnR : (659912 : ℝ)≤N := by exact_mod_cast hN
    have hkR : (k : ℝ)≤11 := by exact_mod_cast hk11
    have hkp : (0 : ℝ)<k := by exact_mod_cast (show 0<k by omega)
    have hdiv := div_le_div_of_nonneg_left (Nat.cast_nonneg N : (0 : ℝ)≤N) hkp hkR
    norm_num at hwidth
    nlinarith only [hnR,hdiv,hwidth]
  have hne : ∀S∈C,(T S).Nonempty := by
    intro S hS
    have hh := hlower S hS
    apply Finset.card_pos.mp
    have hhR : (0 : ℝ)<(T S).card := by linarith only [hh,hbase]
    exact_mod_cast hhR
  have hoff : ∀S∈C,¬(d S : ℤ)∣y-a S := by
    intro S hS
    exact (Finset.mem_filter.mp (hCB hS)).2.2
  have hpair : ∀S∈C,∀U∈C,S≠U → ((T S)∩T U).card≤1 := by
    intro S hS U hU hSU
    obtain ⟨hSE,hyS,hoffS⟩ := Finset.mem_filter.mp (hCB hS)
    obtain ⟨hUE,hyU,hoffU⟩ := Finset.mem_filter.mp (hCB hU)
    exact off_point_trace_inter_card (htrace S (hCF hS))
      (hF.2 S (hCF hS) U (hCF hU) hSU) hyS hyU hoffS
  have hs := ActualPhase208.actual_span_phase_sum C T d a y (L : ℤ) (R : ℤ)
    (by exact_mod_cast hLR) (fun S hS => htrace S (hCF hS)) hsteps
    (fun S hS => Finset.inter_subset_right) hne hoff hpair
  have hCne : C.Nonempty := Finset.card_pos.mp (by omega : 0<C.card)
  obtain ⟨S,hSC⟩ := hCne
  have hl := Finset.sum_lt_sum (fun S hS => (hlower S hS).le) ⟨S,hSC,hlower S hSC⟩
  simp only [Finset.sum_const,nsmul_eq_mul,hCc] at hl
  rw [hCc] at hs
  have hg := full_phase_gate hN hk2 hk11 hwidth
  push_cast at hs
  nlinarith only [hs,hl,hg]

#print axioms actual_few_bucket

theorem actual_few_count {N L R k : ℕ} {F : Finset (Finset ℤ)}
    (d : Finset ℤ→ℕ) (a : Finset ℤ→ℤ)
    (hN : 659912≤N) (hk2 : 2≤k) (hk11 : k≤11)
    (hL : 1≤L) (hLR : L≤R) (hRN : R≤N) (hF : Legal (Ground N) F)
    (htrace : ∀S∈F,APAt (d S : ℤ) (a S) (S∩Finset.Icc (L : ℤ) (R : ℤ)))
    (hdense : ∀S∈F,(N : ℝ)<(k : ℝ)*S.card)
    (hwidth : (L : ℝ)+(N-R)<(N : ℝ)/(148/5)) :
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
        actual_few_bucket d a y hN hk2 hk11 hL hLR hRN hF htrace hdense hwidth)
      _ = _ := by simp [Nat.mul_comm]
  have hsR : (E.card : ℝ)≤((SourceCount k-1 : ℕ) : ℝ)*X.card := by exact_mod_cast hs
  rw [Nat.cast_sub (by have hh := source_count_lower hk2 hk11;omega : 1≤SourceCount k),
    Nat.cast_one] at hsR
  rw [(actual_interval_ground_card hL hLR hRN).2] at hsR
  exact hsR

theorem actual_off_count {N L R k : ℕ} {F : Finset (Finset ℤ)}
    (d : Finset ℤ→ℕ) (a : Finset ℤ→ℤ)
    (hN : 659912≤N) (hk2 : 2≤k) (hk11 : k≤11)
    (hL : 1≤L) (hLR : L≤R) (hRN : R≤N) (hF : Legal (Ground N) F)
    (htrace : ∀S∈F,APAt (d S : ℤ) (a S) (S∩Finset.Icc (L : ℤ) (R : ℤ)))
    (hdense : ∀S∈F,(N : ℝ)<(k : ℝ)*S.card)
    (hwidth : (L : ℝ)+(N-R)<(N : ℝ)/(148/5)) :
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
  have hh := actual_heavy_off_count904 F (fun S => (d S : ℤ)) a hN hL hLR hRN hF htrace hd11 hwidth
  have hl := actual_few_count d a hN hk2 hk11 hL hLR hRN hF htrace hdense hwidth
  have hc : ((OffMembers F (fun S => (d S : ℤ)) a).card : ℝ)=(A.card : ℝ)+H.card := by
    rw [hpart,Finset.card_union_of_disjoint hdisj,Nat.cast_add]
  have hhR : (H.card : ℝ)≤904 := by exact_mod_cast hh
  change (A.card : ℝ)≤_ at hl
  linarith only [hc,hl,hhR]

theorem actual_terminal_family {N L R k : ℕ} {F : Finset (Finset ℤ)}
    (d : Finset ℤ→ℕ) (a : Finset ℤ→ℤ)
    (hN : 659912≤N) (hk2 : 2≤k) (hk11 : k≤11)
    (hL : 1≤L) (hLR : L≤R) (hRN : R≤N) (hF : Legal (Ground N) F)
    (hbad : ∀S∈F,¬IsAP S)
    (htrace : ∀S∈F,APAt (d S : ℤ) (a S) (S∩Finset.Icc (L : ℤ) (R : ℤ)))
    (hdense : ∀S∈F,(N : ℝ)<(k : ℝ)*S.card)
    (hwidth : (L : ℝ)+(N-R)<(N : ℝ)/(148/5)) :
    (F.card : ℝ)≤(TerminalA k+(SourceCount k : ℝ)-1)*((L : ℝ)+(N-R))+
      TerminalB k-(SourceCount k : ℝ)+1+904 := by
  let A := F.filter (fun S => ∀y∈S,(d S : ℤ)∣y-a S)
  have hAF : A⊆F := Finset.filter_subset _ _
  have hA : Legal (Ground N) A := ⟨fun S hS => hF.1 S (hAF hS),
    fun S hS T hT hST => hF.2 S (hAF hS) T (hAF hT) hST⟩
  have ha := actual_terminal_count d a hN hk2 hk11 hL hLR hRN hA
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
    (hN : 659912≤N) (hL : 1≤L) (hLR : L≤R) (hRN : R≤N)
    (hF : Legal (Ground N) F) (hbad : ∀S∈F,¬IsAP S)
    (htrace : ∀S∈F,APAt (d S : ℤ) (a S) (S∩Finset.Icc (L : ℤ) (R : ℤ)))
    (hdense : ∀S∈F,(N : ℝ)<11*S.card)
    (hwidth : (L : ℝ)+(N-R)<(N : ℝ)/(148/5)) :
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
end JSP233.FewOff208
