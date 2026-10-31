import Erdos272.Resources.ActualGrid212
import Erdos272.Resources.Aligned208

/-! The same actual whole residue class is used for both external capacity
and off-point counting. No aligned-only trace bound is used for off sources. -/
namespace JSP233.FewOffGeometry212
open StarCompletion APGeometry ActualGrid212 Aligned208
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

def SameOutside (S : Finset ℤ) (L R : ℤ) (d a : ℤ) : Finset ℤ :=
  (S\Finset.Icc L R).filter (fun y => d∣y-a)

theorem actual_three_part_card (S : Finset ℤ) (L R d a : ℤ)
    (htrace : APAt d a (S∩Finset.Icc L R)) :
    (S∩Finset.Icc L R).card+(SameOutside S L R d a).card+
      (ActualOffPoints S d a).card=S.card := by
  let B := S.filter (fun y => d∣y-a)
  have hBI : B∩Finset.Icc L R = S∩Finset.Icc L R := by
    ext y
    simp only [B,Finset.mem_inter,Finset.mem_filter]
    constructor
    · rintro ⟨⟨hyS,_⟩,hyI⟩
      exact ⟨hyS,hyI⟩
    · rintro ⟨hyS,hyI⟩
      exact ⟨⟨hyS,OffResidue44.origin_dvd htrace (Finset.mem_inter.mpr ⟨hyS,hyI⟩)⟩,hyI⟩
  have hBO : B\Finset.Icc L R = SameOutside S L R d a := by
    ext y
    simp only [B,SameOutside,Finset.mem_sdiff,Finset.mem_filter]
    tauto
  have hpart := Finset.card_sdiff_add_card_inter B (Finset.Icc L R)
  have hfull := Finset.card_filter_add_card_filter_not (s := S) (fun y => d∣y-a)
  rw [hBI,hBO] at hpart
  change B.card+(ActualOffPoints S d a).card=S.card at hfull
  omega

theorem actual_same_outside_bound {N L R d : ℕ} {S : Finset ℤ} (a : ℤ)
    (hL : 1≤L) (hLR : L≤R) (hRN : R≤N) (hd : 0<d) (hS : S⊆Ground N) :
    ((SameOutside S L R d a).card : ℝ) ≤ ((L : ℝ)+(N-R))/d+2-3/d := by
  have hsub : SameOutside S L R d a ⊆ ResidueOutside N L R d a := by
    intro y hy
    obtain ⟨hyS,hyphase⟩ := Finset.mem_filter.mp hy
    obtain ⟨hyS,hyI⟩ := Finset.mem_sdiff.mp hyS
    exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hS hyS,hyI⟩,hyphase⟩
  have hc : ((SameOutside S L R d a).card : ℝ) ≤ (ResidueOutside N L R d a).card := by
    exact_mod_cast Finset.card_le_card hsub
  have hm := residue_outside_real hL hLR hRN hd a
  have he : ((L : ℝ)+(N-R))/d+2-3/d=((L : ℝ)+N-R)/d+2-3/d := by ring
  rw [he]
  exact hc.trans hm

theorem actual_few_trace_lower {N L R d k : ℕ} {S : Finset ℤ} {a : ℤ}
    (hL : 1≤L) (hLR : L≤R) (hRN : R≤N) (hd : 2≤d) (hk : 0<k)
    (hS : S⊆Ground N) (htrace : APAt (d : ℤ) a (S∩Finset.Icc (L : ℤ) (R : ℤ)))
    (hdense : (N : ℝ)<(k : ℝ)*S.card)
    (hfew : ((ActualOffPoints S d a).card : ℝ)≤(3/5000 : ℝ)*N) :
    (N : ℝ)/k-(3/5000 : ℝ)*N-((L : ℝ)+(N-R))/2-3 <
      ((S∩Finset.Icc (L : ℤ) (R : ℤ)).card : ℝ)-1 := by
  have hpart : ((S∩Finset.Icc (L : ℤ) (R : ℤ)).card : ℝ)+
      (SameOutside S L R d a).card+(ActualOffPoints S d a).card=S.card := by
    exact_mod_cast actual_three_part_card S L R d a htrace
  have ha := actual_same_outside_bound a hL hLR hRN (by omega : 0<d) hS
  have hw : (0 : ℝ)≤(L : ℝ)+(N-R) := by
    have hRN' : (R : ℝ)≤N := by exact_mod_cast hRN
    have hL0 : (0 : ℝ)≤L := Nat.cast_nonneg _
    linarith only [hRN',hL0]
  have hdR : (2 : ℝ)≤d := by exact_mod_cast hd
  have hdiv := div_le_div_of_nonneg_left hw (by norm_num : (0 : ℝ)<2) hdR
  have hthree : (0 : ℝ)≤3/(d : ℝ) := by positivity
  have hsize : (N : ℝ)/k<S.card := (div_lt_iff₀ (by exact_mod_cast hk : (0 : ℝ)<k)).mpr
    (by simpa only [mul_comm] using hdense)
  linarith only [hpart,ha,hdiv,hthree,hsize,hfew]

theorem actual_few_step_domain {N d k : ℕ} {S : Finset ℤ} {a : ℤ}
    (hN : 656184≤N) (hS : S⊆Ground N) (hd : 0<d) (hk11 : k≤11)
    (hdense : (N : ℝ)<(k : ℝ)*S.card)
    (hfew : ((ActualOffPoints S d a).card : ℝ)≤(3/5000 : ℝ)*N)
    (hpos : 0<(ActualOffPoints S d a).card) : 2≤d ∧ d≤11 := by
  have hkR : (k : ℝ)≤11 := by exact_mod_cast hk11
  have hm := mul_le_mul_of_nonneg_right hkR (Nat.cast_nonneg S.card : (0 : ℝ)≤S.card)
  have hdZ : (0 : ℤ)<d := by exact_mod_cast hd
  have hh := actual_few_positive_off_step_range hN hS hdZ (hdense.trans_le hm) hfew hpos
  exact_mod_cast hh

#print axioms actual_three_part_card
#print axioms actual_same_outside_bound
#print axioms actual_few_trace_lower
#print axioms actual_few_step_domain
end
end JSP233.FewOffGeometry212
