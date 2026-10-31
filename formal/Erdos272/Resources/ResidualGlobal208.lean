import Erdos272.Counting.ResidualTwoCensus208
import Erdos272.Arithmetic.ResidualAggregate208

namespace JSP233.ResidualGlobal208
open StarCompletion APGeometry NearAP36 ResidualWeights208 ResidualStratum208
open ResidualPrice208 ResidualTwoCensus208 ResidualAggregate208
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

theorem cumulative_step_partition {α β : Type*} [DecidableEq α] [DecidableEq β]
    (F : Finset α) (piece : α → Finset β) (step : α → ℕ) (D : ℕ)
    (hstep : ∀ S ∈ F, step S ∈ Finset.Icc 1 D) (x : β) (b : ℕ) :
    Cumulative F piece x b=∑ d ∈ Finset.Icc 1 D,
      Cumulative (F.filter (fun S => step S=d)) piece x b := by
  let A := F.filter (fun S => x ∈ piece S ∧ (piece S).card < b)
  have hpart : A.card=∑ d ∈ Finset.Icc 1 D, (A.filter (fun S => step S=d)).card :=
    Finset.card_eq_sum_card_fiberwise (fun S hS => hstep S (Finset.mem_filter.mp hS).1)
  change A.card=_
  rw [hpart]
  apply Finset.sum_congr rfl
  intro d hd
  unfold Cumulative
  congr 1
  ext S
  simp only [A,Finset.mem_filter]
  tauto

theorem actual_global_residual {N M e D : ℕ} {F : Finset (Finset ℤ)}
    (hF : Legal (Ground N) F) (he : 2 ≤ e) (heM : e < M)
    (core : Finset ℤ → Finset ℤ) (step : Finset ℤ → ℕ) (point : ℕ → ℤ)
    (hstep : ∀ S ∈ F, step S ∈ Finset.Icc 1 D)
    (hsub : ∀ S ∈ F, core S ⊆ S)
    (hAt : ∀ S ∈ F, APAt (step S : ℤ) (point (step S)) (core S))
    (ht : ∀ S ∈ F, point (step S) ∈ core S)
    (hsize : ∀ S ∈ F, M ≤ S.card) (hbad : ∀ S ∈ F, ¬IsAP S)
    (hsmall : ∀ S ∈ F, (S \ core S).card < e)
    (hmax : ∀ S ∈ F, ∀ R : Finset ℤ, IsAP R → R ⊆ S → R.card ≤ (core S).card) :
    (F.card : ℝ) ≤ (N : ℝ)^2*Price e (H M)+(253/35 : ℝ)*N := by
  let piece := fun S => S \ core S
  have hpos : ∀ S ∈ F, 0 < (piece S).card := by
    intro S hS
    by_contra hn
    have hz : (S \ core S).card=0 := by dsimp [piece] at hn; omega
    have hcard := Finset.card_sdiff_add_card_eq_card (hsub S hS)
    have heq : core S=S := Finset.eq_of_subset_of_card_le (hsub S hS) (by omega)
    apply hbad S hS
    rw [←heq]
    exact (isAP_iff_exists_APAt _).mpr ⟨step S,point (step S),hAt S hS,ht S hS⟩
  have hcap : ∀ x ∈ Ground N, ∀ b, 2 ≤ b → b ≤ e →
      (Cumulative F piece x b : ℝ) ≤ (N : ℝ)*H M b+253/35 := by
    intro x hx b hb hbe
    have hpoint : ∀ d ∈ Finset.Icc 1 D,
        Cumulative (F.filter (fun S => step S=d)) piece x b ≤ Occupancy N M d b := by
      intro d hd
      let G := F.filter (fun S => step S=d)
      have hGF : G ⊆ F := Finset.filter_subset _ _
      have hG : Legal (Ground N) G := ⟨fun S hS => hF.1 S (hGF hS),
        fun S hS T hT hST => hF.2 S (hGF hS) T (hGF hT) hST⟩
      have hGAt : ∀ S ∈ G, APAt (d : ℤ) (point d) (core S) := by
        intro S hS
        simpa only [(Finset.mem_filter.mp hS).2] using hAt S (hGF hS)
      have hGt : ∀ S ∈ G, point d ∈ core S := by
        intro S hS
        simpa only [(Finset.mem_filter.mp hS).2] using ht S (hGF hS)
      exact actual_defect_stratum hG (le_trans hbe heM.le) core
        (fun S hS => hsub S (hGF hS)) hGAt hGt
        (fun S hS => hsize S (hGF hS)) (fun S hS => hmax S (hGF hS)) x
    have hs := Finset.sum_le_sum hpoint
    rw [← cumulative_step_partition F piece step D hstep x b] at hs
    have hR : (Cumulative F piece x b : ℝ) ≤
        ((∑ d ∈ Finset.Icc 1 D, Occupancy N M d b : ℕ) : ℝ) := by exact_mod_cast hs
    exact hR.trans (occupancy_census N D M b (lt_of_le_of_lt hbe heM))
  have hp := actual_quadratic_payment F (Ground N) piece e (H M) (253/35) he
    (fun S hS => Finset.sdiff_subset.trans (hF.1 S hS)) hpos hsmall
    (by simpa only [ground_card] using hcap)
  simpa only [ground_card,mul_comm] using hp

#print axioms cumulative_step_partition
#print axioms actual_global_residual
end
end JSP233.ResidualGlobal208
