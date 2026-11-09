module

public import Erdos272.Core.N200000.ActualCorePairs200000

@[expose] public section

/-! Primitive core index pairs are exactly those avoiding the actual
bad-prime pair events. Every relevant prime is below the core length. -/
namespace JSP233.PrimePairEvents200000
open StarCompletion APGeometry SourceBridge208 IndexedCorePairs200000
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

def Primes (a h : ℕ) : Finset ℕ := (Finset.range a).filter (fun q => q.Prime ∧ ¬q ∣ h)

def Bad (h : ℕ) (ell : ℤ) (q : ℕ) (Q : Finset ℕ) : Prop :=
  ∀ i ∈ Q, (q : ℤ) ∣ ell - (h : ℤ) * i

theorem bad_not_div_step {h q : ℕ} {ell : ℤ} (hc : Int.gcd (h : ℤ) ell = 1)
    (hq : 2 ≤ q) (i : ℤ) (hbad : (q : ℤ) ∣ ell - (h : ℤ) * i) : ¬q ∣ h := by
  intro hqh
  have hstep : (q : ℤ) ∣ (h : ℤ) := Int.natCast_dvd_natCast.mpr hqh
  have hell : (q : ℤ) ∣ ell := by
    have hh := dvd_add hbad (dvd_mul_of_dvd_left hstep i)
    simpa only [sub_add_cancel] using hh
  have hdiv := Int.dvd_coe_gcd hstep hell
  rw [hc, Nat.cast_one] at hdiv
  have hone : q = 1 := Nat.dvd_one.mp (Int.natCast_dvd_natCast.mp hdiv)
  omega

theorem primitive_pair_iff {h i j : ℕ} {ell : ℤ} (hij : i < j) :
    Primitive h ell {i, j} ↔ Int.gcd ((j : ℤ) - i) (ell - (h : ℤ) * i) = 1 := by
  constructor
  · intro hc
    exact hc i (by simp) j (by simp) hij
  · intro hc a ha b hb hab
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    all_goals first | exact hc | omega

theorem primitive_no_bad {a h q : ℕ} {ell : ℤ} {Q : Finset ℕ}
    (hQ : Q.card = 2) (hprim : Primitive h ell Q) (hq : q ∈ Primes a h) : ¬Bad h ell q Q := by
  intro hbad
  obtain ⟨i, j, hij, he⟩ := sorted_index_pair hQ
  have hi : i ∈ Q := by rw [he]; simp
  have hj : j ∈ Q := by rw [he]; simp
  obtain ⟨_hqa, hp, hnot⟩ := Finset.mem_filter.mp hq
  have hbi := hbad i hi
  have hbj := hbad j hj
  have hmult : (q : ℤ) ∣ (h : ℤ) * ((j : ℤ) - i) := by
    have hh := dvd_sub hbi hbj
    have heq : (ell - (h : ℤ) * i) - (ell - (h : ℤ) * j) = (h : ℤ) * ((j : ℤ) - i) := by ring
    simpa only [heq] using hh
  have hdelta : ((j - i : ℕ) : ℤ) = (j : ℤ) - i := by omega
  have hmultN : q ∣ h * (j - i) := by
    apply Int.natCast_dvd_natCast.mp
    simpa only [Nat.cast_mul, hdelta] using hmult
  have hdivN : q ∣ j - i := (hp.dvd_mul.mp hmultN).resolve_left hnot
  have hdiv : (q : ℤ) ∣ (j : ℤ) - i := by
    simpa only [hdelta] using (Int.natCast_dvd_natCast.mpr hdivN)
  have hcommon := Int.dvd_coe_gcd hdiv hbi
  rw [hprim i hi j hj hij, Nat.cast_one] at hcommon
  have hone : q = 1 := Nat.dvd_one.mp (Int.natCast_dvd_natCast.mp hcommon)
  have htwo := hp.two_le
  omega

theorem not_primitive_has_bad {a h : ℕ} {ell : ℤ} {Q : Finset ℕ}
    (hc : Int.gcd (h : ℤ) ell = 1) (hsub : Q ⊆ Finset.range a) (hQ : Q.card = 2)
    (hn : ¬Primitive h ell Q) : ∃ q ∈ Primes a h, Bad h ell q Q := by
  obtain ⟨i, j, hij, he⟩ := sorted_index_pair hQ
  have hi : i ∈ Q := by rw [he]; simp
  have hj : j ∈ Q := by rw [he]; simp
  have hgn : Int.gcd ((j : ℤ) - i) (ell - (h : ℤ) * i) ≠ 1 := by
    intro hg
    apply hn
    rw [he]
    exact (primitive_pair_iff hij).mpr hg
  let G := Int.gcd ((j : ℤ) - i) (ell - (h : ℤ) * i)
  let q := G.minFac
  have hp : q.Prime := Nat.minFac_prime hgn
  have hqG : (q : ℤ) ∣ (G : ℤ) := Int.natCast_dvd_natCast.mpr (Nat.minFac_dvd G)
  have hdiff : (q : ℤ) ∣ (j : ℤ) - i := dvd_trans hqG (Int.gcd_dvd_left _ _)
  have hbi : (q : ℤ) ∣ ell - (h : ℤ) * i := dvd_trans hqG (Int.gcd_dvd_right _ _)
  have hbj : (q : ℤ) ∣ ell - (h : ℤ) * j := by
    have hh := dvd_sub hbi (dvd_mul_of_dvd_right hdiff (h : ℤ))
    have heq : (ell - (h : ℤ) * i) - (h : ℤ) * ((j : ℤ) - i) = ell - (h : ℤ) * j := by ring
    simpa only [heq] using hh
  have hdelta : ((j - i : ℕ) : ℤ) = (j : ℤ) - i := by omega
  have hqDelta : q ∣ j - i := by
    apply Int.natCast_dvd_natCast.mp
    simpa only [hdelta] using hdiff
  have hqle := Nat.le_of_dvd (by omega : 0 < j - i) hqDelta
  have hja := Finset.mem_range.mp (hsub hj)
  have hqa : q < a := by omega
  have hnot : ¬q ∣ h := bad_not_div_step hc hp.two_le (i : ℤ) hbi
  refine ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hqa, hp, hnot⟩, ?_⟩
  intro k hk
  rw [he] at hk
  rcases Finset.mem_insert.mp hk with rfl | hk
  · exact hbi
  · have hkEq := Finset.mem_singleton.mp hk
    simpa only [hkEq] using hbj

theorem primitive_iff_no_prime_event {a h : ℕ} {ell : ℤ} {Q : Finset ℕ}
    (hc : Int.gcd (h : ℤ) ell = 1) (hsub : Q ⊆ Finset.range a) (hQ : Q.card = 2) :
    Primitive h ell Q ↔ ∀ q ∈ Primes a h, ¬Bad h ell q Q := by
  constructor
  · exact fun hp q hq => primitive_no_bad hQ hp hq
  · intro hn
    by_contra hp
    obtain ⟨q, hq, hbad⟩ := not_primitive_has_bad hc hsub hQ hp
    exact hn q hq hbad

#print axioms bad_not_div_step
#print axioms primitive_pair_iff
#print axioms primitive_no_bad
#print axioms not_primitive_has_bad
#print axioms primitive_iff_no_prime_event
end
end JSP233.PrimePairEvents200000
