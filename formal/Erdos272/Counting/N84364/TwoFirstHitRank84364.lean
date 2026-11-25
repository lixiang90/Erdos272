module

public import Erdos272.Resources.N84364.KeysRankBudget84364
public import Erdos272.Counting.N84364.KeysCover84364
public import Erdos272.Counting.N84364.SmallRankScalars84364

@[expose] public section

namespace JSP233.TwoFirstHitRank84364
open StarCompletion SparseSmall39 SharpSmall212 KeysOrder84364
open KeysRankBudget84364 KeysCover84364 SmallRankScalars84364
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem actual_two_first_hit_rank {N L : ℕ} {F : Finset (Finset ℤ)} {A : Finset ℤ}
    (hL : 2≤L) (hN : 2*L+1≤N) (hlegal : Legal (Ground N) F)
    (hbad : ∀ S ∈ F, ¬IsAP S) (hA : A∈F) (hAN : A.Nonempty) (hAL : A.card≤L)
    (T : ℤ→Finset ℤ) (hT : ∀ x ∈ A, T x∈F) (hxT : ∀ x ∈ A, x∉T x)
    (hsize : ∀ x ∈ A, (T x).card≤L) (htwo : ∀ x ∈ A, 2≤(T x∩A).card) :
    let m : ℝ := ((L-1 : ℕ) : ℝ)
    2*(F.card : ℝ)+(A.card : ℝ)*m*((A.card : ℝ)+m+2)
      ≤2*(A.card : ℝ)*m*(N : ℝ)+2*(((A.card-1)^2/4 : ℕ) : ℝ) := by
  let m : ℝ := ((L-1 : ℕ) : ℝ)
  change 2*(F.card : ℝ)+(A.card : ℝ)*m*((A.card : ℝ)+m+2)
      ≤2*(A.card : ℝ)*m*(N : ℝ)+2*(((A.card-1)^2/4 : ℕ) : ℝ)
  have ha : 1≤A.card := Finset.card_pos.mpr hAN
  have hp : ∀ x ∈ A,
      ((Bucket F A x false).card : ℝ)+((Bucket F A x true).card : ℝ)+
        m*((A.card : ℝ)+m+2)≤2*m*(N : ℝ)+
          (rankExcess A.card (Before A x false).card : ℝ) := by
    intro x hx
    have hlo := actual_keys_bucket_budget hlegal hbad hA (hT x hx) hx (hxT x hx) false
    have hhi := actual_keys_bucket_budget hlegal hbad hA (hT x hx) hx (hxT x hx) true
    have hloR : ((Bucket F A x false).card : ℝ)+
        ((Keys A (T x) x false).card : ℝ)*((Before A x false).card+2)+
        ((Keys A (T x) x false).card.choose 2 : ℝ)
        ≤((Keys A (T x) x false).card : ℝ)*N := by exact_mod_cast hlo
    have hhiR : ((Bucket F A x true).card : ℝ)+
        ((Keys A (T x) x true).card : ℝ)*((Before A x true).card+2)+
        ((Keys A (T x) x true).card.choose 2 : ℝ)
        ≤((Keys A (T x) x true).card : ℝ)*N := by exact_mod_cast hhi
    rw [Nat.cast_choose_two] at hloR hhiR
    push_cast at hloR hhiR
    have hk : (Keys A (T x) x false).card≤L :=
      (Finset.card_le_card (Finset.filter_subset _ _)).trans (hsize x hx)
    have hl : (Keys A (T x) x true).card≤L :=
      (Finset.card_le_card (Finset.filter_subset _ _)).trans (hsize x hx)
    have hsum : (Keys A (T x) x false).card+(Keys A (T x) x true).card≤2*(L-1) := by
      have hid := keys_identity (A := A) (hxT x hx)
      have hs := hsize x hx
      have ht := htwo x hx
      omega
    have hc := two_direction_cost hL hN ha hAL (before_card_pair hx) hk hl hsum
    dsimp only [m] at *
    nlinarith only [hloR, hhiR, hc]
  have hs := Finset.sum_le_sum hp
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hs
  have hrNat : (∑ x ∈ A, rankExcess A.card (Before A x false).card)=
      2*((A.card-1)^2/4) := by
    simp only [before_false]
    rw [sum_earlier_function A (rankExcess A.card), rank_excess_sum]
  have hr : (∑ x ∈ A, (rankExcess A.card (Before A x false).card : ℝ))=
      2*(((A.card-1)^2/4 : ℕ) : ℝ) := by exact_mod_cast hrNat
  rw [hr] at hs
  have hlo : (F.card : ℝ)≤∑ x ∈ A, ((Bucket F A x false).card : ℝ) := by
    exact_mod_cast actual_bucket_cover_card hlegal hA hAN false
  have hhi : (F.card : ℝ)≤∑ x ∈ A, ((Bucket F A x true).card : ℝ) := by
    exact_mod_cast actual_bucket_cover_card hlegal hA hAN true
  nlinarith only [hs, hlo, hhi]

#print axioms actual_two_first_hit_rank
end
end JSP233.TwoFirstHitRank84364
