module

public import Erdos272.Resources.IntrinsicTriples208
public import Erdos272.Arithmetic.APInterval208
public import Mathlib.Data.Int.GCD
public import Erdos272.Foundation.ProofTactics

@[expose] public section

/-! # The actual primitive AP encoding of coverable triples

Primitive middle indices count Euler's totient. An AP covering a triple
contains its shortest AP, whose step is the gcd of the two endpoint gaps.
-/
namespace JSP233.TripleCodes208
open StarCompletion IntrinsicTriples208 ActualAPCount208 PureSource208 APInterval208
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

def Indices (q : ℕ) : Finset ℕ := (Finset.range q).filter (q.Coprime ·)

@[simp] theorem indices_card (q : ℕ) : (Indices q).card = Nat.totient q := rfl

def Triple (q : ℕ) (p : ℤ × ℤ) (i : ℕ) : Finset ℤ :=
  {Point p q, Point p q + (i : ℤ) * (p.2 - p.1), p.2}

theorem sorted_three {Q : Finset ℤ} (hQ : Q.card = 3) :
    ∃ a b c : ℤ, a < b ∧ b < c ∧ Q = {a, b, c} := by
  obtain ⟨x, y, z, hxy, hxz, hyz, hQ⟩ := Finset.card_eq_three.mp hQ
  have hperm : ∀ a b c : ℤ, (a = x ∨ a = y ∨ a = z) →
      (b = x ∨ b = y ∨ b = z) → (c = x ∨ c = y ∨ c = z) →
      a ≠ b → a ≠ c → b ≠ c → Q = {a, b, c} := by
    intro a b c ha hb hc hab hac hbc
    apply Finset.ext
    intro t
    rw [hQ]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases ha with rfl | rfl | rfl <;>
      rcases hb with rfl | rfl | rfl <;>
      rcases hc with rfl | rfl | rfl <;> tauto
  by_cases h₁ : x < y
  · by_cases h₂ : y < z
    · exact ⟨x, y, z, h₁, h₂, hQ⟩
    · by_cases h₃ : x < z
      · exact ⟨x, z, y, h₃, by omega,
          hperm x z y (by tauto) (by tauto) (by tauto) hxz hxy hyz.symm⟩
      · exact ⟨z, x, y, by omega, h₁,
          hperm z x y (by tauto) (by tauto) (by tauto) hxz.symm hyz.symm hxy⟩
  · by_cases h₂ : x < z
    · exact ⟨y, x, z, by omega, h₂,
        hperm y x z (by tauto) (by tauto) (by tauto) hxy.symm hyz hxz⟩
    · by_cases h₃ : y < z
      · exact ⟨y, z, x, h₃, by omega,
          hperm y z x (by tauto) (by tauto) (by tauto) hyz hxy.symm hxz.symm⟩
      · exact ⟨z, y, x, by omega, by omega,
          hperm z y x (by tauto) (by tauto) (by tauto) hyz.symm hxz.symm hxy.symm⟩

/-- A coverable triple is represented by one actual positive-step AP and
one primitive middle index. The represented AP has no more points than
the original AP cover. -/
theorem covered_triple_code {S Q R : Finset ℤ} (hQ : Q.card = 3)
    (hR : IsAP R) (hQR : Q ⊆ R) (hRS : R ⊆ S) :
    ∃ q, 2 ≤ q ∧ q + 1 ≤ R.card ∧
      ∃ p ∈ Codes S q, ∃ i ∈ Indices q, Triple q p i = Q := by
  obtain ⟨a, b, c, hab, hbc, hQeq⟩ := sorted_three hQ
  have haR : a ∈ R := hQR (by rw [hQeq]; simp)
  have hbR : b ∈ R := hQR (by rw [hQeq]; simp)
  have hcR : c ∈ R := hQR (by rw [hQeq]; simp)
  let A := (b - a).toNat
  let C := (c - a).toNat
  have hA : (A : ℤ) = b - a := Int.toNat_of_nonneg (by omega)
  have hC : (C : ℤ) = c - a := Int.toNat_of_nonneg (by omega)
  have hA0 : 0 < A := by omega
  have hAC : A < C := by omega
  let g := A.gcd C
  have hg : 0 < g := Nat.gcd_pos_of_pos_right A (by omega : 0 < C)
  let i := A / g
  let q := C / g
  have hi : i * g = A := Nat.div_mul_cancel (Nat.gcd_dvd_left A C)
  have hq : q * g = C := Nat.div_mul_cancel (Nat.gcd_dvd_right A C)
  have hi0 : 0 < i := by nlinarith
  have hiq : i < q := by nlinarith
  have hq2 : 2 ≤ q := by omega
  have hcop : q.Coprime i := (Nat.coprime_div_gcd_div_gcd hg).symm
  have hgZ : (0 : ℤ) < g := by exact_mod_cast hg
  have hiZ : (i : ℤ) * g = b - a := by
    calc
      (i : ℤ) * g = (i * g : ℕ) := (Nat.cast_mul i g).symm
      _ = (A : ℤ) := congrArg (fun z : ℕ => (z : ℤ)) hi
      _ = b - a := hA
  have hqZ : (q : ℤ) * g = c - a := by
    calc
      (q : ℤ) * g = (q * g : ℕ) := (Nat.cast_mul q g).symm
      _ = (C : ℤ) := congrArg (fun z : ℕ => (z : ℤ)) hq
      _ = c - a := hC
  obtain ⟨d, t, hd, lo, high, hrepr, _⟩ := hR
  have hda : d ∣ b - a := by
    have hh := dvd_sub ((hrepr b).mp hbR).2.2 ((hrepr a).mp haR).2.2
    simpa only [show (b - t) - (a - t) = b - a by ring] using hh
  have hdc : d ∣ c - a := by
    have hh := dvd_sub ((hrepr c).mp hcR).2.2 ((hrepr a).mp haR).2.2
    simpa only [show (c - t) - (a - t) = c - a by ring] using hh
  have hdcast : (d.toNat : ℤ) = d := Int.toNat_of_nonneg hd.le
  have hdaN : d.toNat ∣ A := by
    apply Int.natCast_dvd_natCast.mp
    simpa only [hdcast, hA] using hda
  have hdcN : d.toNat ∣ C := by
    apply Int.natCast_dvd_natCast.mp
    simpa only [hdcast, hC] using hdc
  have hdg : d ∣ (g : ℤ) := by
    have hn := Nat.dvd_gcd hdaN hdcN
    have hz : (d.toNat : ℤ) ∣ (g : ℤ) := Int.natCast_dvd_natCast.mpr hn
    simpa only [hdcast] using hz
  have hfill : ∀ j ≤ q, c - (j : ℤ) * g ∈ R := by
    intro j hj
    apply (hrepr _).mpr
    have hjZ : (j : ℤ) ≤ q := by exact_mod_cast hj
    have hj0 : (0 : ℤ) ≤ j := by positivity
    refine ⟨?_, ?_, ?_⟩
    · have haLo := ((hrepr a).mp haR).1
      nlinarith
    · have hcHi := ((hrepr c).mp hcR).2.1
      nlinarith
    · have hz := dvd_sub ((hrepr c).mp hcR).2.2 (dvd_mul_of_dvd_right hdg (j : ℤ))
      simpa only [show (c - t) - (j : ℤ) * g = c - (j : ℤ) * g - t by ring] using hz
  let f : ℕ → ℤ := fun j => c - (j : ℤ) * g
  have hfinj : Function.Injective f := by
    intro j k he
    dsimp only [f] at he
    have hjk : (j : ℤ) = k := by nlinarith
    exact_mod_cast hjk
  have hsub : (Finset.range (q + 1)).image f ⊆ R := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    exact hfill j (by have hh := Finset.mem_range.mp hj; omega)
  have hcard : q + 1 ≤ R.card := by
    have hh := Finset.card_le_card hsub
    simpa only [Finset.card_image_of_injective _ hfinj, Finset.card_range] using hh
  let p : ℤ × ℤ := (c - g, c)
  have hpPoint : ∀ j, Point p j = c - (j : ℤ) * g := by
    intro j
    dsimp [Point, p]
    ring
  have hp : p ∈ Codes S q := by
    apply mem_codes.mpr
    refine ⟨?_, hRS hcR, by dsimp [p]; omega, ?_⟩
    · simpa only [p, Nat.cast_one, one_mul] using hRS (hfill 1 (by omega))
    intro j hj
    rw [hpPoint]
    exact hRS (hfill j hj)
  refine ⟨q, hq2, hcard, p, hp, i, ?_, ?_⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hiq, hcop⟩
  · unfold Triple
    rw [hpPoint, hQeq]
    dsimp only [p]
    have hfirst : c - (q : ℤ) * g = a := by nlinarith
    have hmid : c - (q : ℤ) * g + (i : ℤ) * (c - (c - g)) = b := by
      nlinarith only [hiZ, hqZ]
    rw [hmid, hfirst]

def Covered (S : Finset ℤ) : Finset (Finset ℤ) :=
  (S.powersetCard 3).filter fun Q =>
    ∃ R : Finset ℤ, IsAP R ∧ Q ⊆ R ∧ R ⊆ S

def Generated (S : Finset ℤ) (q : ℕ) : Finset (Finset ℤ) :=
  ((Codes S q).product (Indices q)).image fun z => Triple q z.1 z.2

theorem actual_partition (S : Finset ℤ) :
    (Pool S).card + (Covered S).card = S.card.choose 3 := by
  have h := Finset.card_filter_add_card_filter_not (s := S.powersetCard 3)
    (fun Q => ∃ R : Finset ℤ, IsAP R ∧ Q ⊆ R ∧ R ⊆ S)
  simpa only [Pool, Covered, Finset.card_powersetCard, Nat.add_comm] using h

theorem generated_card_le (S : Finset ℤ) (q : ℕ) :
    (Generated S q).card ≤ Nat.totient q * intervalMultiplicity S.card q := by
  calc
    (Generated S q).card ≤ ((Codes S q).product (Indices q)).card := Finset.card_image_le
    _ = (Codes S q).card * Nat.totient q := by
      rw [Finset.product_eq_sprod, Finset.card_product, indices_card]
    _ ≤ Nat.totient q * intervalMultiplicity S.card q := by
      by_cases hq : 1 ≤ q
      · simpa only [Nat.mul_comm] using
          Nat.mul_le_mul_right (Nat.totient q) (actual_AP_count_le_interval hq S)
      · have hq0 : q = 0 := by omega
        simp [hq0]

theorem covered_subset_generated {S : Finset ℤ} {m : ℕ}
    (hm : ∀ R : Finset ℤ, IsAP R → R ⊆ S → R.card ≤ m) :
    Covered S ⊆ (Finset.Ico 2 m).biUnion (Generated S) := by
  intro Q hQ
  obtain ⟨hQpow, R, hR, hQR, hRS⟩ := Finset.mem_filter.mp hQ
  have hQcard : Q.card = 3 := (Finset.mem_powersetCard.mp hQpow).2
  obtain ⟨q, hq2, hqR, p, hp, i, hi, hTriple⟩ := covered_triple_code hQcard hR hQR hRS
  apply Finset.mem_biUnion.mpr
  refine ⟨q, Finset.mem_Ico.mpr ⟨hq2, by have hh := hm R hR hRS; omega⟩, ?_⟩
  apply Finset.mem_image.mpr
  exact ⟨(p, i), Finset.mem_product.mpr ⟨hp, hi⟩, hTriple⟩

theorem actual_covered_count_le {S : Finset ℤ} {m : ℕ}
    (hm : ∀ R : Finset ℤ, IsAP R → R ⊆ S → R.card ≤ m) :
    (Covered S).card ≤
      ∑ q ∈ Finset.Ico 2 m, Nat.totient q * intervalMultiplicity S.card q := by
  calc
    (Covered S).card ≤ ((Finset.Ico 2 m).biUnion (Generated S)).card :=
      Finset.card_le_card (covered_subset_generated hm)
    _ ≤ ∑ q ∈ Finset.Ico 2 m, (Generated S q).card := Finset.card_biUnion_le
    _ ≤ _ := Finset.sum_le_sum (fun q _ => generated_card_le S q)

/-- The actual source lower bound before the final totient convolution is
rewritten as a tail sum. No AP counting theorem is assumed here. -/
theorem actual_intrinsic_lower {S : Finset ℤ} {m : ℕ}
    (hm : ∀ R : Finset ℤ, IsAP R → R ⊆ S → R.card ≤ m) :
    S.card.choose 3 ≤ (Pool S).card +
      ∑ q ∈ Finset.Ico 2 m, Nat.totient q * intervalMultiplicity S.card q := by
  have hp := actual_partition S
  have hc := actual_covered_count_le hm
  omega

#print axioms sorted_three
#print axioms covered_triple_code
#print axioms actual_covered_count_le
#print axioms actual_intrinsic_lower
end
end JSP233.TripleCodes208
