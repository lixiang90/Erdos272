import Erdos272.Resources.FewOff212
import Erdos272.Arithmetic.NativeGates212
import Erdos272.Core.Terminal29Native117

namespace JSP233.NativeRestore212
open StarCompletion APGeometry LongTerminal35 DenseDeletion40 RestoreTerminal35 TerminalDeficit51 KKRetention32
open NativeGates212 ActualGrid212 OffResidue44 ThinFringe33
open scoped Classical
noncomputable section
set_option maxHeartbeats 0

theorem actual_restore {N c L R : ℕ} {F G E : Finset (Finset ℤ)}
    (hN : 656184 ≤ N) (hhi : N < 2^50) (hc : 1 ≤ c) (hcL : c < L)
    (hLR : L ≤ R) (hRN : R ≤ N)
    (hwidth : (L : ℝ)+(N-R) < (N : ℝ)/(2951/100))
    (hG : G=F\E) (hEF : E ⊆ F) (hF : Legal (Ground N) F)
    (hbad : ∀ S ∈ E, ¬IsAP S) (hdense : ∀ S ∈ E, N < 11*S.card)
    (havoid : ∀ S ∈ E, (c : ℤ) ∉ S)
    (hne : (Avoiders G (c : ℤ)).Nonempty)
    (hi : ∀ S ∈ Avoiders G (c : ℤ), ∃ a b : ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=Interval (a,b)) : F.card ≤ B N := by
  let w := L+N-R
  have hw : (w : ℝ)=(L : ℝ)+(N-R) := by
    dsimp [w]
    rw [Nat.cast_sub (by omega : R ≤ L+N)]
    push_cast
    ring
  have hthin : 29*w ≤ N := by
    have hh : 29*(w : ℝ) ≤ N := by rw [hw]; nlinarith only [hwidth]
    exact_mod_cast hh
  have hGF : G ⊆ F := by rw [hG]; exact Finset.sdiff_subset
  have hGlegal : Legal (Ground N) G :=
    ⟨fun S hS => hF.1 S (hGF hS),fun S hS T hT hST => hF.2 S (hGF hS) T (hGF hT) hST⟩
  have hcard := deletion_card_exact F E hEF
  rw [←hG] at hcard
  by_cases he : E.Nonempty
  · obtain ⟨P,hPE,hmin⟩ := Finset.exists_min_image E Finset.card he
    have hp0 : 0 < P.card := by have hh := hdense P hPE; omega
    have hpN : P.card ≤ N := by simpa only [ground_card] using Finset.card_le_card (hF.1 P (hEF hPE))
    let k := N/P.card+1
    have hk2 : 2 ≤ k := by
      have hh := (Nat.le_div_iff_mul_le hp0).mpr (show 1*P.card ≤ N by simpa using hpN)
      dsimp [k]
      omega
    have hk11 : k ≤ 11 := by
      have hh := (Nat.div_lt_iff_lt_mul hp0).mpr (hdense P hPE)
      dsimp [k]
      omega
    have hNP : N < k*P.card := (Nat.div_lt_iff_lt_mul hp0).mp
      (by dsimp [k]; omega : N/P.card < k)
    have hdenseK : ∀ S ∈ E, (N : ℝ) < (k : ℝ)*S.card := by
      intro S hS
      exact_mod_cast hNP.trans_le (Nat.mul_le_mul_left k (hmin S hS))
    obtain ⟨H,hHG,hHAP,hIH⟩ := actual_interval_core_member N c L R G hLR hne hi
    have hHF := hGF hHG
    have hHnot : H ∉ E := by rw [hG] at hHG; exact (Finset.mem_sdiff.mp hHG).2
    have hElegal : Legal (Ground N) E :=
      ⟨fun S hS => hF.1 S (hEF hS),fun S hS T hT hST => hF.2 S (hEF hS) T (hEF hT) hST⟩
    have hcoords : ∀ S, ∃ d : ℕ, ∃ a : ℤ, S ∈ E →
        APAt (d : ℤ) a (S ∩ Finset.Icc (L : ℤ) (R : ℤ)) := by
      intro S
      by_cases hS : S ∈ E
      · have hSH : S ≠ H := by intro heq; exact hHnot (heq ▸ hS)
        obtain ⟨d,a,hAP⟩ := apAt_interval_trace (hF.2 S (hEF hS) H hHF hSH) hIH
        exact ⟨d.toNat,a,fun _ => by simpa only [Int.toNat_of_nonneg hAP.1.le] using hAP⟩
      · exact ⟨1,0,fun hs => False.elim (hS hs)⟩
    choose d a htrace using hcoords
    have hEbound := FewOff212.actual_terminal_family d a hN hk2 hk11 (by omega : 1 ≤ L)
      hLR hRN hElegal hbad (fun S hS => htrace S hS) hdenseK hwidth
    have hs : (P.card : ℝ) ≤ (N : ℝ)/(k-1 : ℕ) := by
      have hkpos : (0 : ℝ) < (k-1 : ℕ) := by exact_mod_cast (show 0 < k-1 by omega)
      apply (le_div_iff₀ hkpos).mpr
      have hm : (k-1)*P.card ≤ N := by dsimp [k]; simpa using Nat.div_mul_le_self N P.card
      exact_mod_cast (by simpa only [Nat.mul_comm] using hm : P.card*(k-1) ≤ N)
    have hpay := all_rank_native_gate hN hk2 hk11 hs hwidth hEbound
    have hterm := Terminal29Native117.actual_native_terminal_deficit N c L R F G P
      hhi hc hcL hLR hRN hthin hF hGF (hEF hPE) (havoid P hPE) hi
    have htermR : (G.card : ℝ)+N ≤ (N.choose 2 : ℝ)+P.card+(w : ℝ) := by exact_mod_cast hterm
    have hcardR : (G.card : ℝ)+E.card=F.card := by exact_mod_cast hcard.symm
    have hquarter : 4*(F.card : ℝ) < 4*(N.choose 2 : ℝ)+N := by
      rw [←hw] at hpay
      linarith only [htermR,hcardR,hpay]
    have hquarterN : 4*F.card < 4*N.choose 2+N := by exact_mod_cast hquarter
    unfold B
    omega
  · have hE : E=∅ := Finset.not_nonempty_iff_eq_empty.mp he
    have ht := Terminal29Native117.actual_native_interval_terminal N c L R G
      hhi hc hcL hLR hRN hthin hGlegal hne hi
    simp only [hE,Finset.card_empty,add_zero] at hcard
    unfold B
    omega

#print axioms actual_restore
end
end JSP233.NativeRestore212
