import Erdos272.Resources.ResidualPool208
import Mathlib.Algebra.BigOperators.Intervals

namespace JSP233.ResidualWeights208
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

theorem inverse_telescope {f k : ℕ} (hf : 0 < f) (hfk : f ≤ k) :
    1/(f : ℝ) = 1/(k : ℝ)+
      ∑ b ∈ Finset.Ico (f+1) (k+1), 1/((b : ℝ)*(b-1)) := by
  induction k, hfk using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hk1 : (0 : ℝ) < k+1 := by positivity
    rw [Finset.sum_Ico_succ_top (by omega : f+1 ≤ k+1)]
    push_cast
    rw [show (k : ℝ)+1-1=(k : ℝ) by ring]
    calc
      _ = 1/(k : ℝ)+∑ b ∈ Finset.Ico (f+1) (k+1), 1/((b : ℝ)*(b-1)) := ih
      _ = _ := by field_simp; ring

theorem inverse_cumulative {f e : ℕ} (hf : 0 < f) (hfe : f < e) :
    1/(f : ℝ) = 1/((e-1 : ℕ) : ℝ)+
      ∑ b ∈ Finset.Ico 2 e, if f < b then 1/((b : ℝ)*(b-1)) else 0 := by
  have he : e-1+1=e := by omega
  have ht := inverse_telescope hf (show f ≤ e-1 by omega)
  rw [he] at ht
  rw [← Finset.sum_filter]
  have hset : (Finset.Ico 2 e).filter (fun b => f < b)=Finset.Ico (f+1) e := by
    ext b
    simp only [Finset.mem_filter,Finset.mem_Ico]
    omega
  rw [hset]
  exact ht

def Cumulative {α β : Type*} [DecidableEq α] [DecidableEq β]
    (F : Finset α) (piece : α → Finset β) (x : β) (b : ℕ) : ℕ :=
  (F.filter (fun S => x ∈ piece S ∧ (piece S).card < b)).card

def PointWeight {α β : Type*} [DecidableEq α] [DecidableEq β]
    (F : Finset α) (piece : α → Finset β) (x : β) : ℝ :=
  ∑ S ∈ F, if x ∈ piece S then 1/((piece S).card : ℝ) else 0

theorem indicator_sum {α : Type*} [DecidableEq α] (F : Finset α)
    (P : α → Prop) [DecidablePred P] (w : ℝ) :
    (∑ S ∈ F, if P S then w else 0) = ((F.filter P).card : ℝ)*w := by
  rw [← Finset.sum_filter]
  simp

theorem point_weight_cumulative {α β : Type*} [DecidableEq α] [DecidableEq β]
    (F : Finset α) (piece : α → Finset β) (x : β) (e : ℕ)
    (hpos : ∀ S ∈ F, 0 < (piece S).card)
    (hsmall : ∀ S ∈ F, (piece S).card < e) :
    PointWeight F piece x = (Cumulative F piece x e : ℝ)/((e-1 : ℕ) : ℝ)+
      ∑ b ∈ Finset.Ico 2 e, (Cumulative F piece x b : ℝ)/((b : ℝ)*(b-1)) := by
  have hterm : ∀ S ∈ F,
      (if x ∈ piece S then 1/((piece S).card : ℝ) else 0) =
      (if x ∈ piece S then 1/((e-1 : ℕ) : ℝ) else 0)+
        ∑ b ∈ Finset.Ico 2 e,
          if x ∈ piece S ∧ (piece S).card < b then 1/((b : ℝ)*(b-1)) else 0 := by
    intro S hS
    by_cases hx : x ∈ piece S
    · simpa only [hx,if_true,true_and] using inverse_cumulative (hpos S hS) (hsmall S hS)
    · simp only [hx,if_false,false_and,Finset.sum_const_zero,zero_add]
  have heq : F.filter (fun S => x ∈ piece S)=
      F.filter (fun S => x ∈ piece S ∧ (piece S).card < e) := by
    apply Finset.filter_congr
    intro S hS
    simp only [hsmall S hS,and_true]
  unfold PointWeight
  rw [Finset.sum_congr rfl hterm,Finset.sum_add_distrib,Finset.sum_comm]
  rw [indicator_sum,heq]
  simp only [indicator_sum,Cumulative,div_eq_mul_inv,one_mul]

theorem source_count_identity {α β : Type*} [DecidableEq α] [DecidableEq β]
    (F : Finset α) (Ω : Finset β) (piece : α → Finset β)
    (hsub : ∀ S ∈ F, piece S ⊆ Ω) (hpos : ∀ S ∈ F, 0 < (piece S).card) :
    (F.card : ℝ) = ∑ x ∈ Ω, PointWeight F piece x := by
  unfold PointWeight
  rw [Finset.sum_comm]
  have hterm : ∀ S ∈ F,
      (∑ x ∈ Ω, if x ∈ piece S then 1/((piece S).card : ℝ) else 0) = 1 := by
    intro S hS
    rw [indicator_sum]
    have heq : Ω.filter (fun x => x ∈ piece S)=piece S := by
      ext x
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2,fun h => ⟨hsub S hS h,h⟩⟩
    rw [heq]
    have hn : ((piece S).card : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hpos S hS))
    field_simp
  rw [Finset.sum_congr rfl hterm]
  simp

theorem cumulative_source_bound {α β : Type*} [DecidableEq α] [DecidableEq β]
    (F : Finset α) (Ω : Finset β) (piece : α → Finset β) (e : ℕ) (B : ℕ → ℝ)
    (he : 2 ≤ e) (hsub : ∀ S ∈ F, piece S ⊆ Ω)
    (hpos : ∀ S ∈ F, 0 < (piece S).card)
    (hsmall : ∀ S ∈ F, (piece S).card < e)
    (hcap : ∀ x ∈ Ω, ∀ b, 2 ≤ b → b ≤ e → (Cumulative F piece x b : ℝ) ≤ B b) :
    (F.card : ℝ) ≤ (Ω.card : ℝ)*(B e/((e-1 : ℕ) : ℝ)+
      ∑ b ∈ Finset.Ico 2 e, B b/((b : ℝ)*(b-1))) := by
  have hpoint : ∀ x ∈ Ω, PointWeight F piece x ≤ B e/((e-1 : ℕ) : ℝ)+
      ∑ b ∈ Finset.Ico 2 e, B b/((b : ℝ)*(b-1)) := by
    intro x hx
    rw [point_weight_cumulative F piece x e hpos hsmall]
    apply add_le_add
    · exact div_le_div_of_nonneg_right (hcap x hx e he le_rfl) (Nat.cast_nonneg _)
    · apply Finset.sum_le_sum
      intro b hb
      obtain ⟨hb2,hbe⟩ := Finset.mem_Ico.mp hb
      have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb2
      exact div_le_div_of_nonneg_right (hcap x hx b hb2 hbe.le)
        (mul_nonneg (by positivity) (by linarith only [hbR]))
  rw [source_count_identity F Ω piece hsub hpos]
  have hh := Finset.sum_le_sum hpoint
  simpa only [Finset.sum_const,nsmul_eq_mul] using hh

#print axioms inverse_telescope
#print axioms inverse_cumulative
#print axioms point_weight_cumulative
#print axioms source_count_identity
#print axioms cumulative_source_bound
end
end JSP233.ResidualWeights208
