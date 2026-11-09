module

public import Erdos272.Retention.RelativeFringe114

@[expose] public section

/-! Short interval traces must use almost all exterior points.  If both real
exterior arms are sufficiently populated, two such actual sources would have
a unit-step intersection crossing the entire interval. -/
namespace JSP233.BadFringe115
open StarCompletion APGeometry ThinFringe33 KKRetention32 Restore33
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem common_arm_card {O A S T : Finset ℤ} {b : ℕ}
    (hA : A⊆O) (hS : (O\S).card≤b) (hT : (O\T).card≤b) :
    A.card≤((S∩T)∩A).card+2*b := by
  have hcover : A⊆((S∩T)∩A)∪((O\S)∪(O\T)) := by
    intro x hx
    by_cases hxS : x∈S
    · by_cases hxT : x∈T
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨hxS,hxT⟩,hx⟩)
      · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hA hx,hxT⟩))
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hA hx,hxS⟩))
  have hc := Finset.card_le_card hcover
  have h1 := Finset.card_union_le ((S∩T)∩A) ((O\S)∪(O\T))
  have h2 := Finset.card_union_le (O\S) (O\T)
  omega

theorem restrict_APAt {d p a z : ℤ} {S : Finset ℤ} (h : APAt d p S) :
    APAt d p (S∩Finset.Icc a z) := by
  obtain ⟨hd,lo,hi,hr⟩ := h
  refine ⟨hd,max lo a,min hi z,?_⟩
  intro x
  simp only [Finset.mem_inter,Finset.mem_Icc,hr]
  omega

theorem step_one_of_dense_arm {S : Finset ℤ} {d p a z : ℤ} {b : ℕ}
    (hAP : APAt d p S) (haz : a≤z)
    (hsize : 4*b+2≤(Finset.Icc a z).card)
    (hcover : (Finset.Icc a z).card≤(S∩Finset.Icc a z).card+2*b) : d=1 := by
  have hne : (S∩Finset.Icc a z).Nonempty := Finset.card_pos.mp (by omega)
  have hp := restrict_APAt (a:=a) (z:=z) hAP
  have hspan := apAt_span_eq hp hne
  have hlo := Finset.mem_Icc.mp (Finset.mem_inter.mp (Finset.min'_mem _ hne)).2
  have hhi := Finset.mem_Icc.mp (Finset.mem_inter.mp (Finset.max'_mem _ hne)).2
  have hcard : ((Finset.Icc a z).card:ℤ)=z-a+1 := by
    simp only [Int.card_Icc]
    omega
  have hbound : d*((S∩Finset.Icc a z).card-1:ℤ)≤((Finset.Icc a z).card:ℤ)-1 := by
    omega
  have hd := hAP.1
  by_contra hn
  have hd2 : (2:ℤ)≤d := by omega
  have hnonneg : (0:ℤ)≤(S∩Finset.Icc a z).card-1 := by
    have hh := Finset.card_pos.mpr hne
    omega
  have hmul := mul_le_mul_of_nonneg_right hd2 hnonneg
  have hs : (4:ℤ)*b+2≤(Finset.Icc a z).card := by exact_mod_cast hsize
  have hc : ((Finset.Icc a z).card:ℤ)≤(S∩Finset.Icc a z).card+2*b := by exact_mod_cast hcover
  omega

theorem actual_short_trace_family_card_le_one
    {N L R b : ℕ} {F E : Finset (Finset ℤ)}
    (hL : 1≤L) (hLR : L≤R) (hRN : R≤N)
    (hlegal : Legal (Ground N) F) (hEF : E⊆F)
    (hmiss : ∀S∈E,((Ground N\Finset.Icc (L:ℤ) (R:ℤ))\S).card≤b)
    (hshort : ∀S∈E,(S∩Finset.Icc (L:ℤ) (R:ℤ)).card<(Finset.Icc (L:ℤ) (R:ℤ)).card)
    (hleft : 2*b+1≤L-1) (hright : 2*b+1≤N-R)
    (hlong : 4*b+2≤L-1 ∨ 4*b+2≤N-R) : E.card≤1 := by
  let O := Ground N\Finset.Icc (L:ℤ) (R:ℤ)
  let A := Finset.Icc (1:ℤ) ((L:ℤ)-1)
  let B := Finset.Icc ((R:ℤ)+1) (N:ℤ)
  have hA : A⊆O := by
    intro x hx
    have hh := Finset.mem_Icc.mp hx
    exact Finset.mem_sdiff.mpr ⟨(mem_ground N x).mpr ⟨hh.1,by omega⟩,by simp only [Finset.mem_Icc];omega⟩
  have hB : B⊆O := by
    intro x hx
    have hh := Finset.mem_Icc.mp hx
    exact Finset.mem_sdiff.mpr ⟨(mem_ground N x).mpr ⟨by omega,hh.2⟩,by simp only [Finset.mem_Icc];omega⟩
  have hAc : A.card=L-1 := by dsimp only [A];simp only [Int.card_Icc];omega
  have hBc : B.card=N-R := by dsimp only [B];simp only [Int.card_Icc];omega
  apply Finset.card_le_one.mpr
  intro S hS T hT
  by_contra hne
  have ha := common_arm_card hA (hmiss S hS) (hmiss T hT)
  have hb := common_arm_card hB (hmiss S hS) (hmiss T hT)
  have hane : ((S∩T)∩A).Nonempty := Finset.card_pos.mp (by omega)
  have hbne : ((S∩T)∩B).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨d,p,hAP,_hp⟩ := (isAP_iff_exists_APAt _).mp (hlegal.2 S (hEF hS) T (hEF hT) hne)
  have hd : d=1 := by
    rcases hlong with hl | hr
    · exact step_one_of_dense_arm hAP (by omega) (by rwa [hAc]) ha
    · exact step_one_of_dense_arm hAP (by omega) (by rwa [hBc]) hb
  obtain ⟨a,ha⟩ := hane
  obtain ⟨z,hz⟩ := hbne
  have haST := (Finset.mem_inter.mp ha).1
  have hzST := (Finset.mem_inter.mp hz).1
  have haI := Finset.mem_Icc.mp (Finset.mem_inter.mp ha).2
  have hzI := Finset.mem_Icc.mp (Finset.mem_inter.mp hz).2
  have hfill : Finset.Icc (L:ℤ) (R:ℤ)⊆S∩T := by
    intro x hx
    have hh := Finset.mem_Icc.mp hx
    exact apAt_fill hAP haST hzST (by omega) (by omega) (by simp [hd])
  have hsub : Finset.Icc (L:ℤ) (R:ℤ)⊆S∩Finset.Icc (L:ℤ) (R:ℤ) := by
    intro x hx
    exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp (hfill hx)).1,hx⟩
  have hc := Finset.card_le_card hsub
  have hh := hshort S hS
  omega

#print axioms common_arm_card
#print axioms restrict_APAt
#print axioms step_one_of_dense_arm
#print axioms actual_short_trace_family_card_le_one
end
end JSP233.BadFringe115
