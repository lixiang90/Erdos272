module

public import Erdos272.Capacity.N20258.RootHeightBudget20258
public import Erdos272.Capacity.N20258.RootAvoiderCount20258
public import Erdos272.Counting.ShortAP208

@[expose] public section
namespace JSP233.RootObstruction20258
open StarCompletion StarResources30 CrossLine30 JointResources31 PrivatePairExistence
open HarmonicAbel29 DenseDeletion40
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false

private theorem debt_le {c : ℕ} (hc : 1 ≤ c) :
    RootHeightBudget20258.debt ((c : ℝ)-1) ≤ (109/50)*(c : ℝ)^2+207*c+9100 := by
  have one : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have x := sub_nonneg.mpr one
  have q := mul_le_mul_of_nonneg_right
    (show RootHeight20258.quadratic*(5/3) ≤ 109/50 by norm_num [RootHeight20258.quadratic])
    (sq_nonneg ((c : ℝ)-1))
  have e := mul_le_mul_of_nonneg_right
    (show RootHeight20258.linear*(7493/1600) ≤ 207 by norm_num [RootHeight20258.linear]) x
  have z : 60*RootHeight20258.constant ≤ 9100 := by norm_num [RootHeight20258.constant]
  unfold RootHeightBudget20258.debt
  linarith only [q,e,z,one]

private theorem rooted_partition {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (lo : 19 ≤ N) (legal : Legal (Ground N) F) :
    F.card ≤ (RootPart (CrookedMembers F) c).card+(Avoiders F c).card+
      (APLarge (RootPart F c)).card+2*N := by
  let G := RootPart F c
  let A := G.filter IsAP
  let H := A.filter (fun S => ¬4 ≤ S.card)
  have hF : H ⊆ F := (Finset.filter_subset _ _).trans
    ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _))
  have legalH : Legal (Ground N) H :=
    ⟨fun S hS => legal.1 S (hF hS),fun S hS T hT => legal.2 S (hF hS) T (hF hT)⟩
  have short := ShortAP208.actual_small_AP_family_count lo legalH
    (fun _ hs => (Finset.mem_filter.mp (Finset.mem_filter.mp hs).1).2)
    (fun _ hs => by have h := (Finset.mem_filter.mp hs).2; omega)
  have crooked : G.filter (fun S => ¬IsAP S)=RootPart (CrookedMembers F) c := by
    ext S
    simp only [G,RootPart,CrookedMembers,Finset.mem_filter]
    tauto
  have ap : A.filter (fun S => 4 ≤ S.card) = APLarge G := by
    ext S
    simp [A,APLarge,and_assoc]
  have p := Finset.card_filter_add_card_filter_not (s := G) IsAP
  rw [crooked] at p
  have p' := Finset.card_filter_add_card_filter_not (s := A) (fun S => 4 ≤ S.card)
  rw [ap] at p'
  have all := root_avoider_card_partition F c
  change A.card+_=G.card at p
  change (APLarge G).card+H.card=A.card at p'
  change G.card+_=F.card at all
  change F.card ≤ _+_+(APLarge G).card+_
  omega

/-- Necessary inequality on the original family. The only two counts on
the right are rooted crooked members and root-avoiding progressions. -/
theorem actual {N c : ℕ} {F : Finset (Finset ℤ)} (lo : 11000 ≤ N) (hi : N < 2^16)
    (hc : (c : ℤ) ∈ Ground N) (legal : Legal (Ground N) F) (near : B N ≤ F.card)
    (root : ∀ S ∈ Retained N 12 F, ¬IsAP S → (c : ℤ) ∈ S) :
    (1/2-1/242)*(N : ℝ)^2 ≤ ((RootPart (CrookedMembers F) (c : ℤ)).card : ℝ)+
      2*((Avoiders (F.filter IsAP) (c : ℤ)).card : ℝ)+44*N+(109/50)*(c : ℝ)^2+207*c+9100 := by
  let A := APLarge (RootPart F (c : ℤ))
  let q := (Avoiders F (c : ℤ)).card
  let k := (CommonKernel (Ground N) F (c : ℤ)).card
  let C := (RootPart (CrookedMembers F) (c : ℤ)).card
  let n : ℝ := (N-1 : ℕ)
  let s := ∑ d ∈ StarMidpoint67702.LowActive 60 (c : ℤ) A,
    ((StepClass A (trueStep c) (d : ℤ)).card : ℝ)
  have ground : ∀ S ∈ A, S ⊆ Ground N := fun S hS =>
    legal.1 S (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).1
  have tail := StarMidpoint67702.actual_AP_total 60 N (c : ℤ) A ground
    (fun _ hs => (Finset.mem_filter.mp hs).2.1)
    (fun _ hs => (Finset.mem_filter.mp (Finset.mem_filter.mp hs).1).2)
    (fun _ hs => (Finset.mem_filter.mp hs).2.2) hc
  norm_num only [Nat.cast_ofNat] at tail
  change (A.card : ℝ) ≤ s+n^2/242+2*n*Harmonic (N-1)+n at tail
  have hH : Harmonic (N-1) ≤ 12 :=
    (HarmonicSharp39.actual_harmonic_tight (N-1) 16 (by omega)).trans (by norm_num)
  have harm := mul_le_mul_of_nonneg_left hH (show 0 ≤ 2*n by dsimp [n]; positivity)
  have budget := RootHeightBudget20258.actual_budget hc legal
  change (F.card : ℝ)+s ≤ q+k+((N-1).choose 2 : ℕ)+n/4+_ at budget
  have kN : (k : ℝ) ≤ N := by
    exact_mod_cast ((Finset.card_le_card (kernel_subset_ambient (Ground N) F (c : ℤ))).trans_eq (ground_card N))
  have low : (N.choose 2 : ℝ) ≤ F.card := by
    exact_mod_cast (show N.choose 2 ≤ F.card by unfold B at near; omega)
  have p : (F.card : ℝ) ≤ C+q+A.card+2*(N : ℝ) := by
    exact_mod_cast rooted_partition (c := (c : ℤ)) (by omega : 19 ≤ N) legal
  have ap : (Avoiders F (c : ℤ)).filter IsAP = Avoiders (F.filter IsAP) (c : ℤ) := by
    ext S
    simp only [Avoiders,Finset.mem_filter]
    tauto
  have bad : (Avoiders F (c : ℤ)).filter (fun S => ¬IsAP S) =
      (CrookedMembers F).filter (fun S => (c : ℤ) ∉ S) := by
    ext S
    simp only [CrookedMembers,Avoiders,Finset.mem_filter]
    tauto
  have split := Finset.card_filter_add_card_filter_not (s := Avoiders F (c : ℤ)) IsAP
  rw [ap,bad] at split
  have om := RootAvoiderCount20258.actual_eight (by omega : 9000 ≤ N) hi hc legal near root
  have qr : (q : ℝ) ≤ (Avoiders (F.filter IsAP) (c : ℤ)).card+8*(N : ℝ) := by
    exact_mod_cast (show q ≤ (Avoiders (F.filter IsAP) (c : ℤ)).card+8*N by
      dsimp only [q]; omega)
  have cost := debt_le (c := c) (by exact_mod_cast ((mem_ground N _).mp hc).1)
  have nr : n = (N : ℝ)-1 := by dsimp only [n]; rw [Nat.cast_sub (by omega : 1 ≤ N),Nat.cast_one]
  rw [Nat.cast_choose_two] at low budget
  change (F.card : ℝ)+s ≤ q+k+n*(n-1)/2+n/4+_ at budget
  rw [nr] at budget tail harm
  change _ ≤ (C : ℝ)+2*((Avoiders (F.filter IsAP) (c : ℤ)).card : ℝ)+
    44*N+(109/50)*(c : ℝ)^2+207*c+9100
  linarith only [low,budget,tail,harm,p,kN,qr,cost,Nat.cast_nonneg (α := ℝ) N]

#print axioms actual
end
end JSP233.RootObstruction20258
