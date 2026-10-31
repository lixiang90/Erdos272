import Erdos272.Resources.CoreFringe208
import Erdos272.Core.NearAP36

/-! The enlarged integer block is applicable to actual same-code cores.
There is no supplied remainder-disjointness or block cardinality budget. -/
namespace JSP233.CoreBlock208
open StarCompletion APGeometry NearAP36 CoreFringe208
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

theorem common_grid {a b d m n B : ℕ} (hB : 0 < B) (hm : B < m) (hn : m ≤ n)
    (hcode : StartCode d B a = StartCode d B b) :
    Grid (max a b) d (m-B+1) ⊆ Grid a d m ∩ Grid b d n := by
  obtain ⟨i, hi, ha⟩ := start_decomposition (a := a) (d := d) hB
  obtain ⟨j, hj, hb⟩ := start_decomposition (a := b) (d := d) hB
  rw [← hcode] at hb
  intro x hx
  obtain ⟨k, hk, hx⟩ := (mem_grid _ _ _ _).mp hx
  have haZ : (a : ℤ) = (StartCode d B a).1 +
      ((StartCode d B a).2 * (B : ℤ) + i) * d := by exact_mod_cast ha
  have hbZ : (b : ℤ) = (StartCode d B a).1 +
      ((StartCode d B a).2 * (B : ℤ) + j) * d := by exact_mod_cast hb
  by_cases hij : i ≤ j
  · have hab : a ≤ b := by
      have hh := Nat.mul_le_mul_right d (Nat.add_le_add_left hij ((StartCode d B a).2*B))
      omega
    rw [max_eq_right hab] at hx
    have heij : ((j-i : ℕ) : ℤ) + i = j := by omega
    apply Finset.mem_inter.mpr
    constructor
    · apply (mem_grid _ _ _ _).mpr
      refine ⟨j-i+k, by omega, ?_⟩
      push_cast
      nlinarith only [haZ, hbZ, hx, heij]
    · exact (mem_grid _ _ _ _).mpr ⟨k, by omega, hx⟩
  · have hji : j ≤ i := by omega
    have hba : b ≤ a := by
      have hh := Nat.mul_le_mul_right d (Nat.add_le_add_left hji ((StartCode d B a).2*B))
      omega
    rw [max_eq_left hba] at hx
    have heij : ((i-j : ℕ) : ℤ) + j = i := by omega
    apply Finset.mem_inter.mpr
    constructor
    · exact (mem_grid _ _ _ _).mpr ⟨k, by omega, hx⟩
    · apply (mem_grid _ _ _ _).mpr
      refine ⟨i-j+k, by omega, ?_⟩
      push_cast
      nlinarith only [haZ, hbZ, hx, heij]

theorem actual_pair_remainders_disjoint {N a b d m n A B E p : ℕ}
    {F : Finset (Finset ℤ)} {S T : Finset ℤ}
    (hF : Legal (Ground N) F) (hS : S ∈ F) (hT : T ∈ F) (hne : S ≠ T)
    (hd : 0 < d) (hB : 0 < B) (hBA : B ≤ A) (hp : 2 ≤ p)
    (hm : A+1 ≤ m) (hn : A+1 ≤ n)
    (hcode : StartCode d B a = StartCode d B b)
    (hPS : Grid a d m ⊆ S) (hQT : Grid b d n ⊆ T)
    (hsmallS : (S \ Grid a d m).card < E) (hsmallT : (T \ Grid b d n).card < E)
    (hgate : (p - 1) * (A + 1 - B) ≥ E ∨ p * B ≤ (p - 1) * (A + 1))
    (hproper : ∀ delta : ℤ, 0 < delta → delta ∣ (d : ℤ) → delta < d → (p : ℤ) * delta ≤ d)
    (hmaxS : ∀ R : Finset ℤ, IsAP R → R ⊆ S → R.card ≤ m)
    (hmaxT : ∀ R : Finset ℤ, IsAP R → R ⊆ T → R.card ≤ n) :
    Disjoint (S \ Grid a d m) (T \ Grid b d n) := by
  have ordered : ∀ {S T : Finset ℤ} {a b m n : ℕ}, S ∈ F → T ∈ F → S ≠ T →
      A+1 ≤ m → m ≤ n → StartCode d B a = StartCode d B b →
      Grid a d m ⊆ S → Grid b d n ⊆ T → (S \ Grid a d m).card < E →
      (∀ R : Finset ℤ, IsAP R → R ⊆ S → R.card ≤ m) →
      Disjoint (S \ Grid a d m) T := by
    intro S T a b m n hS hT hne hm hmn hcode hPS hQT hsmall hmax
    let P := Grid a d m
    let Q := S ∩ T
    let c := max a b
    let K := m-B
    have hcommon := common_grid hB (by omega : B < m) hmn hcode
    have hK : 0 < K := by dsimp [K]; omega
    have hcP : (c : ℤ) ∈ P := (Finset.mem_inter.mp (hcommon
      ((mem_grid _ _ _ _).mpr ⟨0, by dsimp [K] at hK; omega, by simp [c]⟩))).1
    have hsub : Grid c d (K+1) ⊆ Q := by
      intro x hx
      obtain ⟨hxP,hxQ⟩ := Finset.mem_inter.mp (hcommon hx)
      exact Finset.mem_inter.mpr ⟨hPS hxP,hQT hxQ⟩
    have hcQ : (c : ℤ) ∈ Q := hsub ((mem_grid _ _ _ _).mpr ⟨0, by omega, by simp⟩)
    have hadQ : (c : ℤ)+d ∈ Q := hsub ((mem_grid _ _ _ _).mpr ⟨1, by omega, by simp⟩)
    have hendQ : (c : ℤ)+(K : ℤ)*d ∈ Q := hsub ((mem_grid _ _ _ _).mpr ⟨K, by omega, rfl⟩)
    have hQsub : Q ⊆ P := unit_gate_overlap_subset hp hBA
      (by simpa only [P,grid_card _ _ _ hd] using hm)
      (by dsimp [P,K]; rw [grid_card _ _ _ hd]; omega) hsmall hgate
      (grid_APAt a d m hd) hPS Finset.inter_subset_left (hF.2 S hS T hT hne)
      hcP hcQ hadQ hendQ hproper (by simpa only [P,grid_card _ _ _ hd] using hmax)
    apply Finset.disjoint_left.mpr
    intro x hx hxT
    obtain ⟨hxS,hxP⟩ := Finset.mem_sdiff.mp hx
    exact hxP (hQsub (Finset.mem_inter.mpr ⟨hxS,hxT⟩))
  rcases le_total m n with hmn | hnm
  · exact Finset.disjoint_left.mpr (fun x hx hy =>
      Finset.disjoint_left.mp (ordered hS hT hne hm hmn hcode hPS hQT hsmallS hmaxS)
        hx (Finset.mem_sdiff.mp hy).1)
  · exact (Finset.disjoint_left.mpr (fun x hx hy =>
      Finset.disjoint_left.mp (ordered hT hS hne.symm hn hnm hcode.symm hQT hPS hsmallT hmaxT)
        hx (Finset.mem_sdiff.mp hy).1)).symm

#print axioms common_grid
#print axioms actual_pair_remainders_disjoint
end
end JSP233.CoreBlock208
