import Erdos272.Resources.FactorCells34
import Erdos272.Counting.TailSelection34

/-! Actual lcm collision labels become coordinate meets. This does not
construct the descending collision forest or assert its total cost. -/
namespace JSP233.CollisionLabels34
open StarCompletion APGeometry AnchorCapacity33 FactorCells34 TailSelection34
open scoped Classical
noncomputable section

theorem exponent_lcm_inf (g d e : ℕ) (_hg : 0<g)
    (hd : d∈g.divisors) (he : e∈g.divisors) :
    Exponent g (Nat.lcm d e)=Exponent g d⊓Exponent g e := by
  have hdg := Nat.dvd_of_mem_divisors hd
  have heg := Nat.dvd_of_mem_divisors he
  have hL : Nat.lcm d e∣g := Nat.lcm_dvd hdg heg
  have hd0 := (Nat.pos_of_mem_divisors hd).ne'
  have he0 := (Nat.pos_of_mem_divisors he).ne'
  funext p
  simp only [Exponent,Pi.inf_apply,Nat.factorization_div hdg,Nat.factorization_div heg,
    Nat.factorization_div hL,Nat.factorization_lcm hd0 he0,Finsupp.tsub_apply,Finsupp.sup_apply]
  omega

theorem divisor_image_card (g : ℕ) (A : Finset ℕ) (hg : 0<g) (hA : A⊆g.divisors) :
    (A.image (Exponent g)).card=A.card := by
  apply Finset.card_image_of_injOn
  intro d hd e he hh
  exact exponent_injective g hg (hA hd) (hA he) hh

theorem divisor_images_disjoint (g : ℕ) (A B : Finset ℕ) (hg : 0<g)
    (hA : A⊆g.divisors) (hB : B⊆g.divisors) (hdis : Disjoint A B) :
    Disjoint (A.image (Exponent g)) (B.image (Exponent g)) := by
  apply Finset.disjoint_left.mpr
  intro a ha hb
  obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨e,he,hh⟩ := Finset.mem_image.mp hb
  have hed := exponent_injective g hg (hB he) (hA hd) hh
  exact Finset.disjoint_left.mp hdis hd (hed ▸ he)

theorem divisor_clique_image (g L : ℕ) (B : Finset ℕ) (hg : 0<g)
    (hL : L∈g.divisors) (hB : B⊆g.divisors)
    (hstrict : ∀ d∈B, d∣L ∧ d≠L)
    (hpair : ∀ d∈B, ∀ e∈B, d≠e → Nat.lcm d e=L) :
    MeetClique (Exponent g L) (B.image (Exponent g)) := by
  constructor
  · intro a ha
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp ha
    refine ⟨(exponent_le_iff g L d hg hL (hB hd)).mpr (hstrict d hd).1,?_⟩
    intro hh
    exact (hstrict d hd).2 (exponent_injective g hg (hB hd) hL hh)
  · intro a ha b hb hne
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hb
    have hde : d≠e := by intro hh; subst e; exact hne rfl
    rw [←exponent_lcm_inf g d e hg (hB hd) (hB he),hpair d hd e he hde]

theorem integer_lcm_nat (d e : ℕ) : Int.lcm (d:ℤ) (e:ℤ)=Nat.lcm d e := by
  simp [Int.lcm]

theorem actual_pure_pair_label (u v : ℤ) (g d e : ℕ) (hg : 0<g)
    (hspan : u+(g:ℤ)≤v) (hvg : (g:ℤ)∣v-u)
    (S T : Finset ℤ) (hS : PureTrace u v (g:ℤ) (d:ℤ) S)
    (hT : PureTrace u v (g:ℤ) (e:ℤ) T) (hpair : IsAP (S∩T)) :
    APAt (Nat.lcm d e:ℤ) u (S∩T) ∧
      Exponent g (Nat.lcm d e)=Exponent g d⊓Exponent g e := by
  have hgZ : (0:ℤ)<g := by exact_mod_cast hg
  have hdg : d∣g := by exact_mod_cast hS.2.1
  have heg : e∣g := by exact_mod_cast hT.2.1
  refine ⟨?_,exponent_lcm_inf g d e hg (Nat.mem_divisors.mpr ⟨hdg,hg.ne'⟩)
    (Nat.mem_divisors.mpr ⟨heg,hg.ne'⟩)⟩
  simpa only [integer_lcm_nat] using pure_pair_APAt_lcm hgZ hspan hvg hS hT hpair

#print axioms exponent_lcm_inf
#print axioms divisor_image_card
#print axioms divisor_images_disjoint
#print axioms divisor_clique_image
#print axioms integer_lcm_nat
#print axioms actual_pure_pair_label
end
end JSP233.CollisionLabels34
