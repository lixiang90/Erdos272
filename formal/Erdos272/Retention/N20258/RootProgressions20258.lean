module

public import Erdos272.Capacity.N20258.RootObstruction20258
public import Erdos272.Counting.N20258.RootAvoidingSteps20258
public import Erdos272.Arithmetic.N20258.RootRecoverySquares20258

@[expose] public section
namespace JSP233.RootProgressions20258
open StarCompletion APGeometry APCount41 DenseDeletion40 PrivatePairExistence
open scoped Classical
noncomputable section
set_option autoImplicit false

private theorem root_price {n s u : ℝ} (su : s ≤ u) (up : s+u+3 ≤ 2*n) :
    s*n-(s^2+3*s)/2 ≤ u*n-(u^2+3*u)/2 := by
  nlinarith only [mul_nonneg (sub_nonneg.mpr su) (sub_nonneg.mpr up)]

/-- Every progression in the original family missing the common crooked
root has unit spacing. Both endpoint estimates concern this very family. -/
theorem actual_unit {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (lo : 19227 ≤ N) (hi : N < 2^16) (g : RootModel291012.Start N c L R F P T)
    (raw : RootRecoverySquares20258.profile L ((N : ℝ)-R) ≤
      RootRecoverySquares20258.rate N*(N : ℝ)+71*L+12*((N : ℝ)-R)+872) :
    ∀ S ∈ F, IsAP S → (c : ℤ) ∉ S → Step S=1 := by
  intro S hs ap miss
  by_contra ne
  have size := RootPreparation20258.actual_omitter_size (by omega : 11000 ≤ N) hi
    g.legal g.near_card g.root hs miss
  have pos := (actual_step ap).1
  have two : (2 : ℤ) ≤ Step S := by exact_mod_cast (show 2 ≤ Step S by omega)
  have sub := g.legal.1 S hs
  have live := isAP_nonempty ap
  have low := (mem_ground N _).mp (sub (low_spec live).1)
  have high := (mem_ground N _).mp (sub (high_spec live).1)
  have span := (ShortAP208.actual_root_position sub ap (by omega) (low_spec live).1).2.2.2
  have sep := mul_le_mul_of_nonneg_left two (Int.natCast_nonneg (S.card-1))
  have half : 2*S.card ≤ N+1 := by omega
  have quad := MixedOmitter20258.actual_quadratic (by omega : 2 ≤ N) g.legal hs miss (by omega)
  have halfR : 2*(S.card : ℝ) ≤ N+1 := by exact_mod_cast half
  have nlo : (19227 : ℝ) ≤ N := by exact_mod_cast lo
  have pay := root_price (s := (S.card : ℝ)) (u := ((N : ℝ)+1)/2) (n := (N : ℝ))
    (by linarith only [halfR]) (by linarith only [halfR,nlo])
  unfold ShortTransversal20258.rootPrice at quad
  have crooked : ((RootPart (CrookedMembers F) (c : ℤ)).card : ℝ) ≤ (3/8)*(N : ℝ)^2 := by
    linarith only [quad,pay,nlo]
  have obs := RootObstruction20258.actual (by omega : 11000 ≤ N) hi g.root_mem g.legal g.near_card g.root
  have q := RootAvoidingSteps20258.actual_progressions (by omega : 11000 ≤ N) hi g
  exact RootRecoverySquares20258.no_nonunit nlo (Nat.cast_nonneg c)
    (by exact_mod_cast g.root_left.le : (c : ℝ) ≤ L) raw (by linarith only [obs,q,crooked])

/-- The improved count of interval avoiders forces each original member
missing the root to occupy more than two thirds of the ground set. -/
theorem actual_size {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (lo : 19227 ≤ N) (hi : N < 2^16) (g : RootModel291012.Start N c L R F P T)
    (raw : RootRecoverySquares20258.profile L ((N : ℝ)-R) ≤
      RootRecoverySquares20258.rate N*(N : ℝ)+71*L+12*((N : ℝ)-R)+872) :
    ∀ S ∈ F, (c : ℤ) ∉ S → 2*N < 3*S.card := by
  have u := RootAvoidingSteps20258.actual_unit_progressions g (actual_unit lo hi g raw)
  have q : ((Avoiders (F.filter IsAP) (c : ℤ)).card : ℝ) ≤ ((L : ℝ)-c)*((N : ℝ)-R+1) := by
    have r : ((Avoiders (F.filter IsAP) (c : ℤ)).card : ℝ) ≤ ((L-c)*(N-R+1) : ℕ) := by
      exact_mod_cast u
    simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_sub g.root_left.le,
      Nat.cast_sub g.right_ground] using r
  intro S hs miss
  by_contra h
  have small : 3*S.card ≤ 2*N := by omega
  have smallR : 3*(S.card : ℝ) ≤ 2*N := by exact_mod_cast small
  have nlo : (19227 : ℝ) ≤ N := by exact_mod_cast lo
  have quad := MixedOmitter20258.actual_quadratic (by omega : 2 ≤ N) g.legal hs miss (by omega)
  have pay := root_price (s := (S.card : ℝ)) (u := 2*(N : ℝ)/3) (n := (N : ℝ))
    (by linarith only [smallR]) (by linarith only [smallR,nlo])
  unfold ShortTransversal20258.rootPrice at quad
  have crooked : ((RootPart (CrookedMembers F) (c : ℤ)).card : ℝ) ≤ (4/9)*(N : ℝ)^2 := by
    linarith only [quad,pay,nlo]
  have obs := RootObstruction20258.actual (by omega : 11000 ≤ N) hi g.root_mem g.legal g.near_card g.root
  exact RootRecoverySquares20258.no_two_thirds nlo (Nat.cast_nonneg c)
    (by exact_mod_cast g.root_left.le : (c : ℝ) ≤ L) raw (by linarith only [obs,q,crooked])

#print axioms actual_unit
#print axioms actual_size
end
end JSP233.RootProgressions20258
