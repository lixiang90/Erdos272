module

public import Erdos272.Counting.N94488.HalfTrace94488
public import Erdos272.Retention.N291012.FringeGeneric291012

@[expose] public section

namespace JSP233.MinimumPaymentWide67702
open StarCompletion APGeometry ThinFringe33 RootModel291012 AlignedPlans212
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem middle_fringe {N L R : ℕ} {F E : Finset (Finset ℤ)}
    (hN : 160 ≤ N) (hL : 1 ≤ L) (hLR : L ≤ R) (hRN : R ≤ N)
    (hF : Legal (Ground N) F) (hEF : E ⊆ F) (hbad : ∀ S ∈ E, ¬IsAP S)
    (hdense : ∀ S ∈ E, (41/100 : ℝ)*N < S.card)
    (hcore : ∃ H ∈ F, IsAP H ∧ Finset.Icc (L : ℤ) (R : ℤ) ⊆ H)
    (hw : Width N L R < (11/100 : ℝ)*N) :
    (E.card : ℝ) ≤ (9/2 : ℝ)*Width N L R-7/2 := by
  have hn : (160 : ℝ) ≤ N := by exact_mod_cast hN
  have hplan : ∀ d ∈ Finset.Icc 1 (3-1), d < 3 ∧
      GateConstant d 3 < (N : ℝ)*GateCoefficient (100/41) (100/11) d 3 := by
    intro d hd
    obtain ⟨hd1,hd2⟩ := Finset.mem_Icc.mp hd
    interval_cases d <;> norm_num [GateConstant,GateCoefficient] <;> linarith only [hn]
  have hoff : ((3 : ℝ)-1)*((3 : ℝ)-2)/2 <
      (N : ℝ)*((3 : ℝ)/(100/41)-1-((3 : ℝ)-1)/(100/11)) := by
    norm_num
    linarith only [hn]
  have hh := FringeGeneric291012.actual_fringe_count
    (K:=3) (k:=(100/41 : ℝ)) (p:=3) (u:=(100/11 : ℝ)) (fun _ => 3)
    (by norm_num) (by norm_num) (by decide) hL hLR hRN hF hEF hbad
    (by intro S hS; have hd := hdense S hS; nlinarith only [hd]) hcore
    (by dsimp only [Width] at hw; nlinarith only [hw]) hplan hoff
  norm_num [Slope,Constant,Finset.sum_Icc_succ_top] at hh
  dsimp only [Width]
  nlinarith only [hh]

theorem actual_minimum_payment {N L R : ℕ} {F E : Finset (Finset ℤ)} {U : Finset ℤ}
    (hN : 160 ≤ N) (hL : 1 ≤ L) (hLR : L ≤ R) (hRN : R ≤ N)
    (hF : Legal (Ground N) F) (hEF : E ⊆ F) (hbad : ∀ S ∈ E, ¬IsAP S)
    (hcore : ∃ H ∈ F, IsAP H ∧ Finset.Icc (L : ℤ) (R : ℤ) ⊆ H)
    (hU : U ∈ E) (hmin : ∀ S ∈ E, U.card ≤ S.card)
    (hw : Width N L R < (11/100 : ℝ)*N)
    (he : (E.card : ℝ) ≤ (13/2 : ℝ)*Width N L R-11/2) :
    4*(U.card : ℝ)+4*Width N L R+4*E.card+8 < 5*N := by
  have hn : (160 : ℝ) ≤ N := by exact_mod_cast hN
  by_cases hhigh : ((N : ℝ)+Width N L R)/2 < U.card
  · have hd : ∀ S ∈ E, ((N : ℝ)+Width N L R)/2 < S.card := by
      intro S hS
      exact hhigh.trans_le (by exact_mod_cast hmin S hS)
    have hb := HalfTrace94488.actual_high_density_card hL hLR hRN hF hEF hbad hcore hd
    have hsize : (U.card : ℝ) ≤ N := by
      exact_mod_cast (show U.card ≤ N by
        have hh := Finset.card_le_card (hF.1 U (hEF hU)); rwa [ground_card] at hh)
    linarith only [hn,hw,hb,hsize]
  · have hhalf := le_of_not_gt hhigh
    by_cases hlow : (U.card : ℝ) ≤ (41/100 : ℝ)*N
    · linarith only [hn,hw,he,hlow]
    · have hd : ∀ S ∈ E, (41/100 : ℝ)*N < S.card := by
        intro S hS
        exact (lt_of_not_ge hlow).trans_le (by exact_mod_cast hmin S hS)
      have hb := middle_fringe hN hL hLR hRN hF hEF hbad hd hcore hw
      linarith only [hn,hw,hhalf,hb]

#print axioms middle_fringe
#print axioms actual_minimum_payment
end
end JSP233.MinimumPaymentWide67702
