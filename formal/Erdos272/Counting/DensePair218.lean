module

public import Erdos272.Counting.UnitCount218
public import Erdos272.Geometry.PairShadowGeometry218
public import Erdos272.Resources.DenseOmitted214
public import Erdos272.Resources.InitialProfile218
public import Mathlib.Data.Nat.Choose.Cast

@[expose] public section

namespace JSP233.DensePair218
open StarCompletion APGeometry DenseDeletion40 Density41 SparseSmall39
open UnitCount218 PairShadowBudget218 PairShadowGeometry218 WitnessInterval43
open InitialProfile218 RecoveryCaps213 HarmonicAbel29
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

def Tau : ℝ := 19/100
def Mu : ℝ := 28
def Delta : ℝ := 69/400
def Loss : ℝ := 2*HCap+1211/5

theorem actual_sparse_pair_density {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (hN : 642498≤N) (hhigh : N≤653292) (g : Start N c L R F P T)
    (hua : ((AvoidUnitAP F (c : ℤ)).card : ℝ) ≤
      ((L : ℝ)+(N-R))^2/4+((L : ℝ)+(N-R))) :
    Delta*(N : ℝ)^2-Loss*N-3869/2 ≤ (SparseCrooked N 11 F).card := by
  have hc := RecoveryCaps213.actual_caps (by omega : 100000≤N) (by omega : N≤656184)
  have hw := (actual_coarse_bounds hN hhigh g).2
  have hu := actual_unit_cap_of_shadow (by omega : 10902≤N) g.root_mem g.legal g.near_card g.root
    (by simpa only [Nat.cast_sub (show 1≤N by omega),Nat.cast_one]
      using actual_root_unit_pair_shadow g.root_mem g.legal)
  have hAP := actual_AP_count (by omega : 1≤N) g.legal
  have hd := DenseDeletion208.actual_deleted11_affine (by omega : 10902≤N) g.legal
  have hdR : ((Deleted N 11 F).card : ℝ)≤121*(N : ℝ)+968 := by exact_mod_cast hd
  have hp := actual_original_three_part_partition N 11 F
  have hpR : ((APPart F).card : ℝ)+(SparseCrooked N 11 F).card+(Deleted N 11 F).card=F.card := by
    exact_mod_cast hp
  change ((F.filter IsAP).card : ℝ)+(SparseCrooked N 11 F).card+(Deleted N 11 F).card=F.card at hpR
  have hnear : (N : ℝ)*((N : ℝ)-1)/2+1≤F.card := by
    have hb : (N.choose 2 : ℝ)+1≤F.card := by
      exact_mod_cast (show N.choose 2+1≤F.card by have hh := g.near_card; unfold B at hh; omega)
    simpa only [Nat.cast_choose_two] using hb
  have hN0 : (0 : ℝ)≤N := Nat.cast_nonneg _
  have hL0 : (0 : ℝ)≤L := Nat.cast_nonneg _
  have hRN : (R : ℝ)≤N := by exact_mod_cast g.right_ground
  have hw0 : (0 : ℝ)≤(L : ℝ)+(N-R) := by linarith only [hL0,hRN]
  have hw2 : ((L : ℝ)+(N-R))^2≤(N : ℝ)^2/100 := by
    nlinarith only [hw.le,hw0,hN0,sq_nonneg ((N : ℝ)/10-((L : ℝ)+(N-R)))]
  have hh := mul_le_mul_of_nonneg_right hc.harmonic_le hN0
  dsimp only [Delta,Loss]
  nlinarith only [hua,hu,hAP,hdR,hpR,hnear,hw.le,hw2,hh]

theorem actual_omitter_size {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T U : Finset ℤ}
    (hN : 642498≤N) (hhigh : N≤653292) (g : Start N c L R F P T)
    (hua : ((AvoidUnitAP F (c : ℤ)).card : ℝ) ≤
      ((L : ℝ)+(N-R))^2/4+((L : ℝ)+(N-R)))
    (hUF : U∈F) (hbad : ¬IsAP U) (hcU : (c : ℤ)∉U) : Tau*(N : ℝ)<U.card := by
  by_contra hn
  have hsmall : (U.card : ℝ)≤Tau*(N : ℝ) := le_of_not_gt hn
  have hnR : (642498 : ℝ)≤N := by exact_mod_cast hN
  have hNp : (0 : ℝ)<N := by linarith only [hnR]
  let C := F.filter fun S => ¬IsAP S
  have hCF : C⊆F := Finset.filter_subset _ _
  have hCL : Legal (Ground N) C :=
    ⟨fun S hS => g.legal.1 S (hCF hS),fun S hS V hV hSV => g.legal.2 S (hCF hS) V (hCF hV) hSV⟩
  have hCB : ∀S∈C,¬IsAP S := fun S hS => (Finset.mem_filter.mp hS).2
  have hUC : U∈C := Finset.mem_filter.mpr ⟨hUF,hbad⟩
  have hsub : SparseCrooked N 11 F⊆RootPart C (c : ℤ) := by
    intro S hS
    obtain ⟨hret,hbadS⟩ := Finset.mem_filter.mp hS
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨actual_sparse_subset N 11 F (Finset.mem_filter.mpr ⟨hret,hbadS⟩),hbadS⟩,g.root S hret hbadS⟩
  have hsR : ((SparseCrooked N 11 F).card : ℝ)≤(RootPart C (c : ℤ)).card := by
    exact_mod_cast Finset.card_le_card hsub
  have hsize : U.card+1≤N := by
    have hh : (U.card : ℝ)+1≤N := by norm_num [Tau] at hsmall; linarith only [hsmall,hnR]
    exact_mod_cast hh
  have hz : (U.card : ℝ)/(N : ℝ)≤Tau := (div_le_iff₀ hNp).mpr hsmall
  have hq := RootQuadratic208.actual_normalized_root (by omega : 2≤N) hCL hCB hUC hcU hsize hz
    (by norm_num [Tau] : Tau≤1)
  have hqR := (div_le_iff₀ (sq_pos_of_pos hNp)).mp hq
  have hd := actual_sparse_pair_density hN hhigh g hua
  have hlinear : 0<(Delta-RootQuadratic208.Q Tau)*(N : ℝ)-Loss-(3869/2 : ℝ)/642498 := by
    norm_num [Delta,RootQuadratic208.Q,Tau,Loss,HCap,LogCap]
    linarith only [hnR]
  have hconst : (3869/2 : ℝ)≤((3869/2 : ℝ)/642498)*(N : ℝ) := by
    nlinarith only [hnR]
  have hmul := mul_pos hlinear hNp
  nlinarith only [hsR,hqR,hd,hconst,hmul]

theorem actual_E_bound {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (hN : 642498≤N) (hhigh : N≤653292) (g : Start N c L R F P T)
    (hua : ((AvoidUnitAP F (c : ℤ)).card : ℝ) ≤
      ((L : ℝ)+(N-R))^2/4+((L : ℝ)+(N-R))) :
    ((TerminalDeficit51.OmittedAvoiders N 11 F (c : ℤ)).card : ℝ)≤Mu*N := by
  let E := TerminalDeficit51.OmittedAvoiders N 11 F (c : ℤ)
  have hEF : E⊆F := (Finset.filter_subset _ _).trans (actual_deleted_subset N 11 F)
  have hEL : Legal (Ground N) E :=
    ⟨fun S hS => g.legal.1 S (hEF hS),fun S hS U hU hSU => g.legal.2 S (hEF hS) U (hEF hU) hSU⟩
  have hEB : ∀S∈E,¬IsAP S := fun S hS => (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2.1
  have hs : ∀S∈E,Tau*(N : ℝ)<S.card := by
    intro S hS
    exact actual_omitter_size hN hhigh g hua (hEF hS) (hEB S hS) (Finset.mem_filter.mp hS).2
  have hnR : (642498 : ℝ)≤N := by exact_mod_cast hN
  have ht : 1<Tau*(N : ℝ) := by norm_num [Tau]; linarith only [hnR]
  have hb := DenseOmitted214.actual_all_pair_density_budget (by omega : 2≤N) ht hEL hEB
    (fun S hS => (hs S hS).le)
  have hpoly : ((N : ℝ)-1)*((N : ℝ)-2)≤Mu*(N : ℝ)*Tau*(Tau*(N : ℝ)-1) := by
    have hn0 : 0≤(N : ℝ)-642498 := sub_nonneg.mpr hnR
    have he : Mu*(N : ℝ)*Tau*(Tau*(N : ℝ)-1)-((N : ℝ)-1)*((N : ℝ)-2)=
        (27/2500 : ℝ)*((N : ℝ)-642498)^2+(8672273/625 : ℝ)*((N : ℝ)-642498)+
          (2785493216677/625 : ℝ) := by
      norm_num [Mu,Tau]
      ring
    apply sub_nonneg.mp
    rw [he]
    positivity
  have hc : 0<Tau*(Tau*(N : ℝ)-1) := mul_pos (by norm_num [Tau]) (by linarith only [ht])
  change (E.card : ℝ)≤Mu*N
  by_contra hh
  have hp := mul_pos (sub_pos.mpr (lt_of_not_ge hh)) hc
  nlinarith only [hb,hpoly,hp]

#print axioms actual_sparse_pair_density
#print axioms actual_omitter_size
#print axioms actual_E_bound
end
end JSP233.DensePair218
