import Erdos272.Global.PaddedCommon212
import Erdos272.Global.RootQuadratic208
import Erdos272.Resources.DenseDeletion208

/-! Actual deleted avoiders are not rooted. The root of the retained sparse
family forces every such omitter to be larger, before all-pair counting. -/
namespace JSP233.DenseOmitted214
open StarCompletion APGeometry DenseDeletion40 Density41 SparseSmall39
open SevenPrices208 GlobalSeven208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

def Tau : ℝ := 371/4000
def Mu : ℝ := 465/4

theorem actual_crooked_omitter_size {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ} {T : Finset ℤ}
    (hN : 506104 ≤ N) (hhi : N ≤ 705097) (hF : Legal (Ground N) F) (hcard : B N ≤ F.card)
    (hroot : ∀ S ∈ Retained N 11 F, ¬IsAP S → c ∈ S)
    (hT : T ∈ F) (hbadT : ¬IsAP T) (hcT : c ∉ T) :
    Tau*(N : ℝ) < T.card := by
  by_contra hn
  have hsmall : (T.card : ℝ) ≤ Tau*(N : ℝ) := le_of_not_gt hn
  have hnR : (506104 : ℝ) ≤ N := by exact_mod_cast hN
  have hnpos : (0 : ℝ) < N := by linarith only [hnR]
  let C := F.filter (fun S => ¬IsAP S)
  have hCF : C ⊆ F := Finset.filter_subset _ _
  have hCL : Legal (Ground N) C :=
    ⟨fun S hS => hF.1 S (hCF hS), fun S hS U hU hSU => hF.2 S (hCF hS) U (hCF hU) hSU⟩
  have hCB : ∀ S ∈ C, ¬IsAP S := fun S hS => (Finset.mem_filter.mp hS).2
  have hTC : T ∈ C := Finset.mem_filter.mpr ⟨hT, hbadT⟩
  have hsub : SparseCrooked N 11 F ⊆ RootPart C c := by
    intro S hS
    have hSF := actual_sparse_subset N 11 F hS
    obtain ⟨hret, hbad⟩ := Finset.mem_filter.mp hS
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hSF, hbad⟩, hroot S hret hbad⟩
  have hsubR : ((SparseCrooked N 11 F).card : ℝ) ≤ (RootPart C c).card := by
    exact_mod_cast Finset.card_le_card hsub
  have hsize : T.card+1 ≤ N := by
    have ht : (T.card : ℝ)+1 ≤ N := by norm_num [Tau] at hsmall; linarith only [hsmall, hnR]
    exact_mod_cast ht
  have hz : (T.card : ℝ)/(N : ℝ) ≤ Tau := (div_le_iff₀ hnpos).mpr hsmall
  have hquad := RootQuadratic208.actual_normalized_root (by omega : 2 ≤ N)
    hCL hCB hTC hcT hsize hz (by norm_num [Tau] : Tau ≤ 1)
  have hquadR := (div_le_iff₀ (sq_pos_of_pos hnpos)).mp hquad
  have hd := PaddedCommon212.actual_sparse_density (by omega : 100000 ≤ N) hhi hF hcard
  have hgap : 0 < ((71/800 : ℝ)-RootQuadratic208.Q Tau)*(N : ℝ)-Loss := by
    norm_num [RootQuadratic208.Q, Tau, Loss]
    linarith only [hnR]
  have hp := mul_pos hgap hnpos
  nlinarith only [hsubR, hquadR, hd, hp]

theorem actual_omitted_avoider_size {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (hN : 506104 ≤ N) (hhi : N ≤ 705097) (hF : Legal (Ground N) F) (hcard : B N ≤ F.card)
    (hroot : ∀ S ∈ Retained N 11 F, ¬IsAP S → c ∈ S) :
    ∀ S ∈ TerminalDeficit51.OmittedAvoiders N 11 F c, Tau*(N : ℝ) < S.card := by
  intro S hS
  obtain ⟨hSD, hcS⟩ := Finset.mem_filter.mp hS
  have hSF := actual_deleted_subset N 11 F hSD
  have hbad := (Finset.mem_filter.mp hSD).2.1
  exact actual_crooked_omitter_size hN hhi hF hcard hroot hSF hbad hcS

/-- General real-density all-pair count, applied below to the actual E. -/
theorem actual_all_pair_density_budget {N : ℕ} {a : ℝ} {E : Finset (Finset ℤ)}
    (hN : 2 ≤ N) (ha : 1 < a*(N : ℝ)) (hE : Legal (Ground N) E)
    (hbad : ∀ S ∈ E, ¬IsAP S) (hsize : ∀ S ∈ E, a*(N : ℝ) ≤ S.card) :
    (E.card : ℝ)*a*(a*(N : ℝ)-1) ≤ ((N : ℝ)-1)*((N : ℝ)-2) := by
  let rel : Finset ℤ → ℤ × ℤ → Prop := fun S p => p.1 ∈ S ∧ p.2 ∈ S
  have hnpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have habove : ∀ S ∈ E, (Ground N).offDiag.bipartiteAbove rel S = S.offDiag := by
    intro S hS
    ext p
    simp only [Finset.mem_bipartiteAbove, Finset.mem_offDiag, rel]
    constructor
    · rintro ⟨⟨_, _, hne⟩, hu, hv⟩
      exact ⟨hu, hv, hne⟩
    · rintro ⟨hu, hv, hne⟩
      exact ⟨⟨hE.1 S hS hu, hE.1 S hS hv, hne⟩, hu, hv⟩
  have hcard (S : Finset ℤ) : (S.offDiag.card : ℝ) = (S.card : ℝ)^2-S.card := by
    rw [Finset.offDiag_card, Nat.cast_sub (Nat.le_mul_self _), Nat.cast_mul]
    ring
  have hsupply : ∀ S ∈ E, (a*(N : ℝ))*(a*(N : ℝ)-1) ≤
      ((Ground N).offDiag.bipartiteAbove rel S).card := by
    intro S hS
    rw [habove S hS, hcard]
    have hs := hsize S hS
    have hp := mul_le_mul hs (show a*(N : ℝ)-1 ≤ (S.card : ℝ)-1 by linarith only [hs])
      (show 0 ≤ a*(N : ℝ)-1 by linarith only [ha]) (Nat.cast_nonneg S.card)
    nlinarith only [hp]
  have hcap : ∀ p ∈ (Ground N).offDiag, ((E.bipartiteBelow rel p).card : ℝ) ≤ (N : ℝ)-2 := by
    intro p hp
    have hne := (Finset.mem_offDiag.mp hp).2.2
    have hc := DenseDeletion208.actual_all_pair_capacity hE hbad hne
    have hcR : ((E.filter (fun S => p.1 ∈ S ∧ p.2 ∈ S)).card : ℝ) ≤ ((N-2 : ℕ) : ℝ) := by
      exact_mod_cast hc
    simpa only [Finset.bipartiteBelow, rel, Nat.cast_sub hN, Nat.cast_ofNat] using hcR
  have hd := Finset.card_nsmul_le_card_nsmul (R := ℝ) (r := rel)
    (s := E) (t := (Ground N).offDiag) hsupply hcap
  simp only [nsmul_eq_mul] at hd
  rw [hcard, ground_card] at hd
  have heq : (E.card : ℝ)*(a*(N : ℝ)*(a*(N : ℝ)-1)) =
      (N : ℝ)*((E.card : ℝ)*a*(a*(N : ℝ)-1)) := by ring
  have heq' : ((N : ℝ)^2-N)*((N : ℝ)-2) =
      (N : ℝ)*(((N : ℝ)-1)*((N : ℝ)-2)) := by ring
  rw [heq, heq'] at hd
  exact (mul_le_mul_iff_right₀ hnpos).mp hd

theorem actual_omitted_avoiders_bound {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (hN : 506104 ≤ N) (hhi : N ≤ 705097) (hF : Legal (Ground N) F) (hcard : B N ≤ F.card)
    (hroot : ∀ S ∈ Retained N 11 F, ¬IsAP S → c ∈ S) :
    ((TerminalDeficit51.OmittedAvoiders N 11 F c).card : ℝ) ≤ (465/4 : ℝ)*N := by
  let E := TerminalDeficit51.OmittedAvoiders N 11 F c
  have hEF : E ⊆ F := (Finset.filter_subset _ _).trans (actual_deleted_subset N 11 F)
  have hEL : Legal (Ground N) E :=
    ⟨fun S hS => hF.1 S (hEF hS), fun S hS U hU hSU => hF.2 S (hEF hS) U (hEF hU) hSU⟩
  have hEB : ∀ S ∈ E, ¬IsAP S := fun S hS => (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2.1
  have hs := actual_omitted_avoider_size hN hhi hF hcard hroot
  have hn : (506104 : ℝ) ≤ N := by exact_mod_cast hN
  have ht : 1 < Tau*(N : ℝ) := by norm_num [Tau]; linarith only [hn]
  have hb := actual_all_pair_density_budget (by omega : 2 ≤ N) ht hEL hEB (fun S hS => (hs S hS).le)
  have hpoly : ((N : ℝ)-1)*((N : ℝ)-2) ≤ Mu*(N : ℝ)*Tau*(Tau*(N : ℝ)-1) := by
    have hz : 0 ≤ (N : ℝ)-506104 := sub_nonneg.mpr hn
    have he : Mu*(N : ℝ)*Tau*(Tau*(N : ℝ)-1)-((N : ℝ)-1)*((N : ℝ)-2) =
        (613/12800000 : ℝ)*((N : ℝ)-506104)^2+
        (32554469/800000 : ℝ)*((N : ℝ)-506104)+1665633350097/200000 := by
      norm_num [Mu, Tau]
      ring
    apply sub_nonneg.mp
    rw [he]
    positivity
  have hcoef : 0 < Tau*(Tau*(N : ℝ)-1) :=
    mul_pos (by norm_num [Tau]) (by linarith only [ht])
  change (E.card : ℝ) ≤ Mu*(N : ℝ)
  by_contra hh
  have hp := mul_pos (sub_pos.mpr (lt_of_not_ge hh)) hcoef
  nlinarith only [hb, hpoly, hp]

#print axioms actual_crooked_omitter_size
#print axioms actual_omitted_avoider_size
#print axioms actual_all_pair_density_budget
#print axioms actual_omitted_avoiders_bound
end
end JSP233.DenseOmitted214
