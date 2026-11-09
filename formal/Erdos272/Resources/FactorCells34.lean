module

public import Erdos272.Resources.DivisorCells34
public import Mathlib.Data.Nat.Factorization.Divisors

@[expose] public section

/-! Actual gcd-cell Euler weights and faithful reverse factor coordinates. -/
namespace JSP233.FactorCells34
open DivisorCells34
open scoped Classical BigOperators
noncomputable section

abbrev PrimeCoordinates (g : ℕ) := ↥g.primeFactors→ℕ

def Exponent (g d : ℕ) : PrimeCoordinates g := fun p => (g/d).factorization p.val

def CoordinateWeight (g : ℕ) (a : PrimeCoordinates g) : ℕ :=
  ∏ p : ↥g.primeFactors, Nat.totient (p.val^(a p))

theorem quotient_pos (g d : ℕ) (hg : 0<g) (hd : d∈g.divisors) : 0<g/d :=
  Nat.div_pos (Nat.le_of_dvd hg (Nat.dvd_of_mem_divisors hd)) (Nat.pos_of_mem_divisors hd)

theorem quotient_dvd (g d : ℕ) (hd : d∈g.divisors) : g/d∣g :=
  ⟨d,(Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)).symm⟩

theorem totient_eq_primeFactors_product (g n : ℕ) (hg : 0<g) (hn : 0<n) (hng : n∣g) :
    Nat.totient n=∏ p∈g.primeFactors, Nat.totient (p^(n.factorization p)) := by
  have he : Nat.totient n=n.factorization.prod (fun p k => Nat.totient (p^k)) :=
    Nat.multiplicative_factorization Nat.totient (@Nat.totient_mul) Nat.totient_one hn.ne'
  rw [he,Finsupp.prod,Nat.support_factorization]
  apply Finset.prod_subset (Nat.primeFactors_mono hng hg.ne')
  intro p hpg hpn
  have hz : n.factorization p=0 := by
    apply Finsupp.notMem_support_iff.mp
    simpa only [Nat.support_factorization] using hpn
  simp [hz]

theorem actual_cell_prime_power_weight (u : ℤ) (g M d : ℕ) (hg : 0<g)
    (hd : d∈g.divisors) (hne : d≠g) :
    (Cell u g M d).card=M*(∏ p∈g.primeFactors, Nat.totient (p^((g/d).factorization p))) := by
  rw [cell_proper_card u g M d hg (Nat.pos_of_mem_divisors hd) (Nat.dvd_of_mem_divisors hd) hne]
  rw [totient_eq_primeFactors_product g (g/d) hg (quotient_pos g d hg hd) (quotient_dvd g d hd)]

theorem quotient_factorization_le_iff (g d e : ℕ) (hg : 0<g)
    (hd : d∈g.divisors) (he : e∈g.divisors) :
    (g/d).factorization≤(g/e).factorization ↔ e∣d := by
  have hdg := Nat.dvd_of_mem_divisors hd
  have heg := Nat.dvd_of_mem_divisors he
  have hd0 := (Nat.pos_of_mem_divisors hd).ne'
  have he0 := (Nat.pos_of_mem_divisors he).ne'
  have hdb := (Nat.factorization_le_iff_dvd hd0 hg.ne').mpr hdg
  have heb := (Nat.factorization_le_iff_dvd he0 hg.ne').mpr heg
  rw [Nat.factorization_div hdg,Nat.factorization_div heg]
  constructor
  · intro hh
    apply (Nat.factorization_le_iff_dvd he0 hd0).mp
    intro p
    have hdp := hdb p
    have hep := heb p
    have hhp := hh p
    simp only [Finsupp.tsub_apply] at hhp
    omega
  · intro hed
    have hebd := (Nat.factorization_le_iff_dvd he0 hd0).mpr hed
    intro p
    have hdp := hdb p
    have hep := heb p
    have hhp := hebd p
    simp only [Finsupp.tsub_apply]
    omega

theorem quotient_factorization_le_base (g d : ℕ) (hg : 0<g) (hd : d∈g.divisors) :
    (g/d).factorization≤g.factorization :=
  (Nat.factorization_le_iff_dvd (quotient_pos g d hg hd).ne' hg.ne').mpr (quotient_dvd g d hd)

theorem factorization_zero_outside {g n p : ℕ} (hng : n.factorization≤g.factorization)
    (hp : p∉g.primeFactors) : n.factorization p=0 := by
  have hz : g.factorization p=0 := by
    apply Finsupp.notMem_support_iff.mp
    simpa only [Nat.support_factorization] using hp
  have hh := hng p
  rw [hz] at hh
  omega

theorem exponent_le_iff (g d e : ℕ) (hg : 0<g)
    (hd : d∈g.divisors) (he : e∈g.divisors) : Exponent g d≤Exponent g e ↔ e∣d := by
  constructor
  · intro hle
    apply (quotient_factorization_le_iff g d e hg hd he).mp
    intro p
    by_cases hp : p∈g.primeFactors
    · exact hle ⟨p,hp⟩
    · rw [factorization_zero_outside (quotient_factorization_le_base g d hg hd) hp,
        factorization_zero_outside (quotient_factorization_le_base g e hg he) hp]
  · intro hed p
    exact ((quotient_factorization_le_iff g d e hg hd he).mpr hed) p.val

theorem exponent_injective (g : ℕ) (hg : 0<g) :
    Set.InjOn (Exponent g) (g.divisors : Set ℕ) := by
  intro d hd e he heq
  have hed := (exponent_le_iff g d e hg hd he).mp (le_of_eq heq)
  have hde := (exponent_le_iff g e d hg he hd).mp (le_of_eq heq.symm)
  exact Nat.dvd_antisymm hde hed

theorem totient_coordinate_weight (g d : ℕ) (hg : 0<g) (hd : d∈g.divisors) :
    Nat.totient (g/d)=CoordinateWeight g (Exponent g d) := by
  rw [totient_eq_primeFactors_product g (g/d) hg (quotient_pos g d hg hd) (quotient_dvd g d hd)]
  exact (Finset.prod_coe_sort g.primeFactors (fun p => Nat.totient (p^((g/d).factorization p)))).symm

theorem actual_cell_coordinate_weight (u : ℤ) (g M d : ℕ) (hg : 0<g)
    (hd : d∈g.divisors) (hne : d≠g) :
    (Cell u g M d).card=M*CoordinateWeight g (Exponent g d) := by
  rw [cell_proper_card u g M d hg (Nat.pos_of_mem_divisors hd) (Nat.dvd_of_mem_divisors hd) hne,
    totient_coordinate_weight g d hg hd]

theorem selected_cells_coordinate_score (u : ℤ) (g M : ℕ) (A : Finset ℕ) (hg : 0<g)
    (hA : A⊆g.divisors) (hgap : g∉A) :
    (A.biUnion (Cell u g M)).card=M*(∑ a∈A.image (Exponent g), CoordinateWeight g a) := by
  rw [selected_proper_cells_card u g M A hg hA hgap,Finset.sum_image]
  · congr 1
    apply Finset.sum_congr rfl
    intro d hd
    exact totient_coordinate_weight g d hg (hA hd)
  · intro d hd e he heq
    exact exponent_injective g hg (hA hd) (hA he) heq

theorem exponent_anchor (g : ℕ) (hg : 0<g) : Exponent g g=0 := by
  funext p
  simp [Exponent,Nat.div_self hg]

theorem exponent_zero_iff (g d : ℕ) (hg : 0<g) (hd : d∈g.divisors) :
    Exponent g d=0 ↔ d=g := by
  constructor
  · intro he
    exact exponent_injective g hg hd (Nat.mem_divisors.mpr ⟨dvd_refl g,hg.ne'⟩)
      (he.trans (exponent_anchor g hg).symm)
  · intro he
    rw [he]
    exact exponent_anchor g hg

theorem quotient_involution (g d : ℕ) (hg : 0<g) (hd : d∈g.divisors) : g/(g/d)=d := by
  calc
    g/(g/d)=(d*(g/d))/(g/d) := by
      congr 1
      exact (Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)).symm
    _=d := Nat.mul_div_cancel d (quotient_pos g d hg hd)

theorem quotient_factorization_injective (g : ℕ) (hg : 0<g) :
    Set.InjOn (fun d => (g/d).factorization) (g.divisors : Set ℕ) := by
  intro d hd e he heq
  have hq : g/d=g/e := Nat.eq_of_factorization_eq' (quotient_pos g d hg hd).ne'
    (quotient_pos g e hg he).ne' heq
  calc
    d=g/(g/d) := (quotient_involution g d hg hd).symm
    _=g/(g/e) := by rw [hq]
    _=e := quotient_involution g e hg he

theorem quotient_factorization_surjective (g : ℕ) (hg : 0<g)
    (f : ℕ→₀ℕ) (hf : f≤g.factorization) :
    ∃ d∈g.divisors, (g/d).factorization=f := by
  let n := f.prod (fun p a => p^a)
  have hng : n∣g := Nat.prod_pow_dvd_of_le_factorization hf
  have hn : n∈g.divisors := Nat.mem_divisors.mpr ⟨hng,hg.ne'⟩
  have hd : g/n∈g.divisors := Nat.mem_divisors.mpr ⟨quotient_dvd g n hn,hg.ne'⟩
  refine ⟨g/n,hd,?_⟩
  rw [quotient_involution g n hg hn]
  exact Nat.factorization_prod_pow_eq_self_of_le_factorization hf

def DivisorFactorMap (g : ℕ) (hg : 0<g) : ↥g.divisors→↥(Finset.Iic g.factorization) :=
  fun d => ⟨(g/d.val).factorization,Finset.mem_Iic.mpr (quotient_factorization_le_base g d.val hg d.property)⟩

theorem divisorFactorMap_bijective (g : ℕ) (hg : 0<g) :
    Function.Bijective (DivisorFactorMap g hg) := by
  constructor
  · intro d e he
    apply Subtype.ext
    exact quotient_factorization_injective g hg d.property e.property (congrArg Subtype.val he)
  · intro f
    obtain ⟨d,hd,he⟩ := quotient_factorization_surjective g hg f.val (Finset.mem_Iic.mp f.property)
    exact ⟨⟨d,hd⟩,Subtype.ext he⟩

theorem exists_divisor_factor_box_equiv (g : ℕ) (hg : 0<g) :
    ∃ e : ↥g.divisors≃↥(Finset.Iic g.factorization),
      ∀ d : ↥g.divisors, (e d).val=(g/d.val).factorization := by
  exact ⟨Equiv.ofBijective (DivisorFactorMap g hg) (divisorFactorMap_bijective g hg),fun _ => rfl⟩

#print axioms quotient_pos
#print axioms quotient_dvd
#print axioms totient_eq_primeFactors_product
#print axioms actual_cell_prime_power_weight
#print axioms quotient_factorization_le_iff
#print axioms quotient_factorization_le_base
#print axioms factorization_zero_outside
#print axioms exponent_le_iff
#print axioms exponent_injective
#print axioms totient_coordinate_weight
#print axioms actual_cell_coordinate_weight
#print axioms selected_cells_coordinate_score
#print axioms exponent_anchor
#print axioms exponent_zero_iff
#print axioms quotient_involution
#print axioms quotient_factorization_injective
#print axioms quotient_factorization_surjective
#print axioms divisorFactorMap_bijective
#print axioms exists_divisor_factor_box_equiv
end
end JSP233.FactorCells34
