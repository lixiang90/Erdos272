module

public import Mathlib.Data.Nat.ChineseRemainder
public import Mathlib.Data.Int.ModEq
public import Mathlib.RingTheory.Coprime.Lemmas
public import Erdos272.Foundation.ProofTactics

@[expose] public section

namespace JSP233.AffineCRT88404
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem product_dvd_iff {ι : Type*} [DecidableEq ι] (J : Finset ι) (m : ι→ℕ)
    (hpair : Set.Pairwise (↑J) (fun i j => Nat.Coprime (m i) (m j))) (z : ℤ) :
    ((∏ j∈J, m j : ℕ) : ℤ)∣z ↔ ∀j∈J, (m j : ℤ)∣z := by
  rw [Nat.cast_prod]
  constructor
  · intro h j hj
    exact (Finset.dvd_prod_of_mem (fun i => (m i : ℤ)) hj).trans h
  · intro h
    exact Finset.prod_dvd_of_coprime
      (fun i hi j hj hij => (hpair hi hj hij).isCoprime) h

theorem product_crt_exists {ι : Type*} [DecidableEq ι] (J : Finset ι) (m : ι→ℕ)
    (hpos : ∀j∈J, 0<m j)
    (hpair : Set.Pairwise (↑J) (fun i j => Nat.Coprime (m i) (m j))) (r : ι→ℤ) :
    ∃a : ℤ, ∀j∈J, (m j : ℤ)∣a-r j := by
  let residues : ι→ℕ := fun j => (r j % (m j : ℤ)).toNat
  let c := Nat.chineseRemainderOfFinset residues m J
    (fun j hj => (hpos j hj).ne') hpair
  refine ⟨(c.val : ℤ), ?_⟩
  intro j hj
  have hc : Int.ModEq (m j : ℤ) (c.val : ℤ) (residues j : ℤ) :=
    Int.natCast_modEq_iff.mpr (c.property j hj)
  have hr : (residues j : ℤ)=r j % (m j : ℤ) := by
    apply Int.toNat_of_nonneg
    exact Int.emod_nonneg _ (by exact_mod_cast (hpos j hj).ne')
  rw [hr] at hc
  exact Int.modEq_iff_dvd.mp (hc.trans (Int.mod_modEq _ _)).symm

theorem affine_inverse_iff {M d : ℕ} (hcop : Nat.Coprime d M) (c : ℤ) :
    ∃b : ℤ, ∀x : ℤ, (M : ℤ)∣(d : ℤ)*x-c ↔ (M : ℤ)∣x-b := by
  obtain ⟨u, hu⟩ := Int.mod_coprime hcop
  have hi : (M : ℤ)∣(d : ℤ)*u-1 := Int.modEq_iff_dvd.mp hu.symm
  refine ⟨u*c, ?_⟩
  intro x
  constructor
  · intro hx
    have hs : (M : ℤ)∣u*((d : ℤ)*x-c)-((d : ℤ)*u-1)*x :=
      dvd_sub (dvd_mul_of_dvd_right hx u) (dvd_mul_of_dvd_left hi x)
    have he : u*((d : ℤ)*x-c)-((d : ℤ)*u-1)*x=x-u*c := by ring
    rw [he] at hs
    exact hs
  · intro hx
    have hs : (M : ℤ)∣(d : ℤ)*(x-u*c)+((d : ℤ)*u-1)*c :=
      dvd_add (dvd_mul_of_dvd_right hx (d : ℤ)) (dvd_mul_of_dvd_left hi c)
    have he : (d : ℤ)*(x-u*c)+((d : ℤ)*u-1)*c=(d : ℤ)*x-c := by ring
    rw [he] at hs
    exact hs

theorem affine_crt {ι : Type*} [DecidableEq ι] (J : Finset ι) (m : ι→ℕ)
    (hpos : ∀j∈J, 0<m j)
    (hpair : Set.Pairwise (↑J) (fun i j => Nat.Coprime (m i) (m j)))
    (d : ℕ) (hd : 0<d) (hdcop : ∀j∈J, Nat.Coprime d (m j))
    (p : ℤ) (r : ι→ℤ) :
    ∃b : ℤ, ∀x : ℤ, (∀j∈J, (m j : ℤ)∣p+(d : ℤ)*x-r j) ↔
      ((∏j∈J, m j : ℕ) : ℤ)∣x-b := by
  obtain ⟨a, ha⟩ := product_crt_exists J m hpos hpair (fun j => r j-p)
  have hcop : Nat.Coprime d (∏j∈J, m j) := Nat.Coprime.prod_right hdcop
  obtain ⟨b, hb⟩ := affine_inverse_iff hcop a
  refine ⟨b, ?_⟩
  intro x
  constructor
  · intro h
    apply (hb x).mp
    apply (product_dvd_iff J m hpair _).mpr
    intro j hj
    have hs : (m j : ℤ)∣(p+(d : ℤ)*x-r j)-(a-(r j-p)) := dvd_sub (h j hj) (ha j hj)
    have he : (p+(d : ℤ)*x-r j)-(a-(r j-p))=(d : ℤ)*x-a := by ring
    rw [he] at hs
    exact hs
  · intro h j hj
    have ht := (product_dvd_iff J m hpair _).mp ((hb x).mpr h) j hj
    have hs : (m j : ℤ)∣((d : ℤ)*x-a)+(a-(r j-p)) := dvd_add ht (ha j hj)
    have he : ((d : ℤ)*x-a)+(a-(r j-p))=p+(d : ℤ)*x-r j := by ring
    rw [he] at hs
    exact hs

#print axioms product_dvd_iff
#print axioms product_crt_exists
#print axioms affine_inverse_iff
#print axioms affine_crt
end
end JSP233.AffineCRT88404
