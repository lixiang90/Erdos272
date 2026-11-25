module

public import Erdos272.Capacity.N88404.OrderedShadow88404
public import Erdos272.Counting.N88404.ResidueCard88404

@[expose] public section

namespace JSP233.ResidueMaps88404
open StarCompletion OrderedShadow88404
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

def Phase (q : ℕ) (r x : ℤ) : Prop := (q : ℤ) ∣ x-r

def PhaseTriple (q : ℕ) (r : ℤ) (p : PointTriple) : Prop :=
  Phase q r p.1 ∧ Phase q r p.2.1 ∧ Phase q r p.2.2

def ResidueCodes (M q : ℕ) (r : ℤ) (T : Finset (Finset ℤ)) : Finset PointTriple :=
  (Codes M T).filter (PhaseTriple q r)

def Offsets (q : ℕ) : Finset PointTriple :=
  Finset.Ico 0 (q : ℤ) ×ˢ (Finset.Ico 0 (q : ℤ) ×ˢ Finset.Ico 0 (q : ℤ))

def Expand (p a : PointTriple) : PointTriple :=
  (p.1+a.1, p.2.1+a.2.1, p.2.2-a.2.2)

def UpOffset (q : ℕ) (r x : ℤ) : ℤ := (r-x) % (q : ℤ)
def DownOffset (q : ℕ) (r x : ℤ) : ℤ := (x-r) % (q : ℤ)

def Round (q : ℕ) (r : ℤ) (p : PointTriple) : PointTriple :=
  (p.1+UpOffset q r p.1, p.2.1+UpOffset q r p.2.1,
    p.2.2-DownOffset q r p.2.2)

def RoundOffsets (q : ℕ) (r : ℤ) (p : PointTriple) : PointTriple :=
  (UpOffset q r p.1, UpOffset q r p.2.1, DownOffset q r p.2.2)

theorem mem_residue {M q : ℕ} {r : ℤ} {T : Finset (Finset ℤ)} {p : PointTriple} :
    p ∈ ResidueCodes M q r T ↔ p ∈ Codes M T ∧ PhaseTriple q r p := by
  exact Finset.mem_filter

theorem mem_offsets {q : ℕ} {a : PointTriple} : a ∈ Offsets q ↔
    (0 ≤ a.1 ∧ a.1 < q) ∧ (0 ≤ a.2.1 ∧ a.2.1 < q) ∧
      (0 ≤ a.2.2 ∧ a.2.2 < q) := by
  simp only [Offsets, Finset.mem_product, Finset.mem_Ico]

theorem offsets_card (q : ℕ) : (Offsets q).card = q^3 := by
  simp only [Offsets, Finset.card_product, Int.card_Ico, sub_zero, Int.toNat_natCast]
  ring

theorem phase_gap {q : ℕ} {r x y : ℤ} (hq : 0 < q)
    (hx : Phase q r x) (hy : Phase q r y) (hxy : x < y) : (q : ℤ) ≤ y-x := by
  have hd : (q : ℤ) ∣ y-x := by
    have hh := dvd_sub hy hx
    have he : (y-r)-(x-r) = y-x := by ring
    rw [he] at hh
    exact hh
  obtain ⟨k, hk⟩ := hd
  have hqZ : (0 : ℤ) < q := by exact_mod_cast hq
  have hk0 : 0 < k := by
    apply (mul_lt_mul_iff_right₀ hqZ).mp
    nlinarith only [hk, hxy]
  have hk1 : 1 ≤ k := by omega
  nlinarith only [hk, hk1, hqZ]

theorem offset_unique {q : ℕ} {r x y a b : ℤ}
    (hx : Phase q r x) (hy : Phase q r y)
    (ha : 0 ≤ a ∧ a < q) (hb : 0 ≤ b ∧ b < q)
    (he : x+a = y+b) : x = y ∧ a = b := by
  have hd : (q : ℤ) ∣ b-a := by
    have hh := dvd_sub hx hy
    have he' : (x-r)-(y-r) = b-a := by omega
    rw [he'] at hh
    exact hh
  by_cases hab : a ≤ b
  · have hz := Int.eq_zero_of_dvd_of_nonneg_of_lt
      (by omega : 0 ≤ b-a) (by omega : b-a < (q : ℤ)) hd
    omega
  · have hd' : (q : ℤ) ∣ a-b := by
      have hh := dvd_neg.mpr hd
      have he' : -(b-a) = a-b := by ring
      rw [he'] at hh
      exact hh
    have hz := Int.eq_zero_of_dvd_of_nonneg_of_lt
      (by omega : 0 ≤ a-b) (by omega : a-b < (q : ℤ)) hd'
    omega

theorem expand_injective {q : ℕ} {r : ℤ} {p s a b : PointTriple}
    (hp : PhaseTriple q r p) (hs : PhaseTriple q r s)
    (ha : a ∈ Offsets q) (hb : b ∈ Offsets q)
    (he : Expand p a = Expand s b) : p = s ∧ a = b := by
  obtain ⟨ha₁, ha₂, ha₃⟩ := mem_offsets.mp ha
  obtain ⟨hb₁, hb₂, hb₃⟩ := mem_offsets.mp hb
  have h₁ := congrArg Prod.fst he
  have h₂ := congrArg (fun v : PointTriple => v.2.1) he
  have h₃ := congrArg (fun v : PointTriple => v.2.2) he
  dsimp only [Expand] at h₁ h₂ h₃
  obtain ⟨hp₁, ha₁⟩ := offset_unique hp.1 hs.1 ha₁ hb₁ h₁
  obtain ⟨hp₂, ha₂⟩ := offset_unique hp.2.1 hs.2.1 ha₂ hb₂ h₂
  obtain ⟨hp₃, ha₃⟩ := offset_unique hp.2.2 hs.2.2 hb₃ ha₃
    (by omega : p.2.2+b.2.2 = s.2.2+a.2.2)
  exact ⟨Prod.ext hp₁ (Prod.ext hp₂ hp₃), Prod.ext ha₁ (Prod.ext ha₂ ha₃.symm)⟩

theorem expand_mem {M q : ℕ} {r : ℤ} {T : Finset (Finset ℤ)}
    (hq : 0 < q) (hclosed : Closed T) {p a : PointTriple}
    (hp : p ∈ ResidueCodes M q r T) (ha : a ∈ Offsets q)
    (hgap : 2*(q : ℤ) ≤ p.2.2-p.2.1) : Expand p a ∈ Codes M T := by
  obtain ⟨hpC, hpR⟩ := mem_residue.mp hp
  have hps := (mem_codes.mp hpC).2.2.2.1
  have hg := phase_gap hq hpR.1 hpR.2.1 hps.1
  obtain ⟨ha₁, ha₂, ha₃⟩ := mem_offsets.mp ha
  apply mem_codes_of_inner hclosed hpC
  · dsimp only [Expand]; omega
  · constructor <;> dsimp only [Expand] <;> omega
  · dsimp only [Expand]; omega

theorem round_offsets_mem {q : ℕ} (hq : 0 < q) (r : ℤ) (p : PointTriple) :
    RoundOffsets q r p ∈ Offsets q := by
  have hqZ : (0 : ℤ) < q := by exact_mod_cast hq
  apply mem_offsets.mpr
  exact ⟨⟨Int.emod_nonneg _ hqZ.ne', Int.emod_lt_of_pos _ hqZ⟩,
    ⟨Int.emod_nonneg _ hqZ.ne', Int.emod_lt_of_pos _ hqZ⟩,
    ⟨Int.emod_nonneg _ hqZ.ne', Int.emod_lt_of_pos _ hqZ⟩⟩

theorem round_phase (q : ℕ) (r : ℤ) (p : PointTriple) :
    PhaseTriple q r (Round q r p) := by
  have h₁ := Int.emod_add_mul_ediv (r-p.1) (q : ℤ)
  have h₂ := Int.emod_add_mul_ediv (r-p.2.1) (q : ℤ)
  have h₃ := Int.emod_add_mul_ediv (p.2.2-r) (q : ℤ)
  refine ⟨⟨-((r-p.1)/(q : ℤ)), ?_⟩,
    ⟨-((r-p.2.1)/(q : ℤ)), ?_⟩, ⟨(p.2.2-r)/(q : ℤ), ?_⟩⟩
  all_goals dsimp only [Round, UpOffset, DownOffset]; nlinarith only [h₁,h₂,h₃]

theorem round_mem {M q : ℕ} {r : ℤ} {T : Finset (Finset ℤ)}
    (hq : 0 < q) (hclosed : Closed T) {p : PointTriple}
    (hp : p ∈ Codes M T) (hfirst : (q : ℤ) ≤ p.2.1-p.1)
    (hsecond : 2*(q : ℤ) ≤ p.2.2-p.2.1) :
    Round q r p ∈ ResidueCodes M q r T := by
  have ho := mem_offsets.mp (round_offsets_mem hq r p)
  dsimp only [RoundOffsets] at ho
  apply mem_residue.mpr
  refine ⟨mem_codes_of_inner hclosed hp ?_ ?_ ?_, round_phase q r p⟩
  · dsimp only [Round]; exact le_add_of_nonneg_right ho.1.1
  · constructor <;> dsimp only [Round] <;> omega
  · dsimp only [Round]; exact sub_le_self _ ho.2.2.1

theorem round_record_injective (q : ℕ) (r : ℤ) :
    Function.Injective (fun p : PointTriple => (Round q r p, RoundOffsets q r p)) := by
  intro p s he
  have h₁ := congrArg (fun v : PointTriple × PointTriple => v.1.1) he
  have h₂ := congrArg (fun v : PointTriple × PointTriple => v.1.2.1) he
  have h₃ := congrArg (fun v : PointTriple × PointTriple => v.1.2.2) he
  have ha := congrArg (fun v : PointTriple × PointTriple => v.2.1) he
  have hb := congrArg (fun v : PointTriple × PointTriple => v.2.2.1) he
  have hc := congrArg (fun v : PointTriple × PointTriple => v.2.2.2) he
  dsimp only [Round, RoundOffsets] at h₁ h₂ h₃ ha hb hc
  apply Prod.ext
  · omega
  · apply Prod.ext <;> omega

#print axioms mem_residue
#print axioms mem_offsets
#print axioms offsets_card
#print axioms phase_gap
#print axioms offset_unique
#print axioms expand_injective
#print axioms expand_mem
#print axioms round_offsets_mem
#print axioms round_phase
#print axioms round_mem
#print axioms round_record_injective
end
end JSP233.ResidueMaps88404
