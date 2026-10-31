import Erdos272.Retention.LongTerminal35
import Erdos272.Arithmetic.PrimePrefix35

/-! Actual unordered witness-pair coding, retaining the variable anchor in
every coprime row. The geometric prefix-witness property is explicit. -/
namespace JSP233.TraceWitnessCodes36
open StarCompletion LongTerminal35 StarResources30 PrivatePairExistence
open scoped Classical BigOperators
noncomputable section

def StructuralPairs (c : ℤ) (S : Finset ℤ) : Finset (Finset ℤ) :=
  ((S.erase c).powersetCard 2).filter (IntrinsicPair c S)

theorem structural_pair_mem {c : ℤ} {S Q : Finset ℤ} :
    Q∈StructuralPairs c S ↔ IntrinsicPair c S Q := by
  constructor
  · intro h; exact (Finset.mem_filter.mp h).2
  · intro h
    exact Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨fun x hx =>
      Finset.mem_erase.mpr ⟨by intro he; exact h.2.1 (he ▸ hx),h.2.2.1 hx⟩,h.1⟩,h⟩

theorem divisor_from_primitive_index {P d e i j : ℕ} (hd : d∣P) (he : e∣P)
    (hi : Nat.Coprime i P) (hj : Nat.Coprime j P) (hcode : i*d=j*e) : d=e := by
  have hl : Nat.gcd (i*d) P=d := by rw [hi.gcd_mul_left_cancel,Nat.gcd_eq_left hd]
  have hr : Nat.gcd (j*e) P=e := by rw [hj.gcd_mul_left_cancel,Nat.gcd_eq_left he]
  exact hl.symm.trans ((congrArg (fun n => Nat.gcd n P) hcode).trans hr)

theorem actual_variable_anchor_codes {S H Z : Finset ℤ} {c : ℤ} {P : ℕ}
    (I : Finset ℕ) (k : ℕ→ℕ) (hP : 0<P) (hdiv : ∀ d∈I,d∣P)
    (hprefix : ∀ d : ℕ, d∈I → ∀ i : ℕ, 0 < i → i ≤ k d → c+(i:ℤ)*(d:ℤ)∈H)
    (hout : Disjoint Z H)
    (hW : ∀ z∈Z,∀ d∈I,∀ i : ℕ, 0 < i → i ≤ k d → Nat.Coprime i ((z-c).natAbs) →
      IntrinsicPair c S {c+(i:ℤ)*(d:ℤ),z}) :
    (∑ z∈Z,∑ d∈I,(PrimePrefix35.CoprimePrefix (P*(z-c).natAbs) (k d)).card)≤
      (StructuralPairs c S).card := by
  let V : Finset (Σ _ : ℤ, Σ _ : ℕ, ℕ) := Z.sigma (fun z => I.sigma (fun d =>
    PrimePrefix35.CoprimePrefix (P*(z-c).natAbs) (k d)))
  let f : (Σ _ : ℤ, Σ _ : ℕ, ℕ)→Finset ℤ :=
    fun q => {c+(q.2.2:ℤ)*(q.2.1:ℤ),q.1}
  have hs : ∀ q∈V,q.1∈Z ∧ q.2.1∈I ∧ c+(q.2.2:ℤ)*(q.2.1:ℤ)∈H ∧
      Nat.Coprime q.2.2 P ∧ IntrinsicPair c S (f q) := by
    intro q hq
    obtain ⟨hz,hd,hi⟩ := Finset.mem_sigma.mp hq |>.imp_right Finset.mem_sigma.mp
    obtain ⟨hiI,hcop⟩ := Finset.mem_filter.mp hi
    obtain ⟨hip,hik⟩ := Finset.mem_Icc.mp hiI
    obtain ⟨hic,hit⟩ := Nat.coprime_mul_iff_right.mp hcop
    exact ⟨hz,hd,hprefix q.2.1 hd q.2.2 hip hik,hic,hW q.1 hz q.2.1 hd q.2.2 hip hik hit⟩
  have hmaps : Set.MapsTo f (V:Set (Σ _ : ℤ, Σ _ : ℕ, ℕ)) (StructuralPairs c S) :=
    fun q hq => structural_pair_mem.mpr (hs q hq).2.2.2.2
  have hinj : Set.InjOn f (V:Set (Σ _ : ℤ, Σ _ : ℕ, ℕ)) := by
    rintro ⟨z,d,i⟩ ha ⟨w,e,j⟩ hb heq
    have hza := hs ⟨z,d,i⟩ ha
    have hwb := hs ⟨w,e,j⟩ hb
    change ({c+(i:ℤ)*d,z}:Finset ℤ)={c+(j:ℤ)*e,w} at heq
    have hznot : z∉H := fun hh => Finset.disjoint_left.mp hout hza.1 hh
    have hwnot : w∉H := fun hh => Finset.disjoint_left.mp hout hwb.1 hh
    have hzm : z∈({c+(j:ℤ)*e,w}:Finset ℤ) := by rw [←heq]; simp
    have hzw : z=w := by
      simp only [Finset.mem_insert,Finset.mem_singleton] at hzm
      exact hzm.resolve_left (fun he => hznot (he.symm ▸ hwb.2.2.1))
    have hym : c+(i:ℤ)*d∈({c+(j:ℤ)*e,w}:Finset ℤ) := by rw [←heq]; simp
    have hy : c+(i:ℤ)*d=c+(j:ℤ)*e := by
      simp only [Finset.mem_insert,Finset.mem_singleton] at hym
      exact hym.resolve_right (fun he => hwnot (he ▸ hza.2.2.1))
    have hcode : i*d=j*e := by exact_mod_cast (show (i:ℤ)*d=(j:ℤ)*e by omega)
    have hde := divisor_from_primitive_index (hdiv d hza.2.1) (hdiv e hwb.2.1)
      hza.2.2.2.1 hwb.2.2.2.1 hcode
    have hdpos := Nat.pos_of_dvd_of_pos (hdiv d hza.2.1) hP
    have hij : i=j := by rw [←hde] at hcode; nlinarith
    cases hzw; cases hde; cases hij
    rfl
  simpa only [V,Finset.card_sigma] using Finset.card_le_card_of_injOn f hmaps hinj

theorem actual_structural_private {Ω : Finset ℤ} {F : Finset (Finset ℤ)} {c : ℤ}
    (hlegal : Legal Ω F) (hroot : Rooted F c) {S Q : Finset ℤ}
    (hS : S∈F) (hQ : Q∈StructuralPairs c S) :
    Q∈AvailableBadPairsAt c Ω F ∧ ∀ T∈F,T≠S → ¬Q⊆T :=
  intrinsic_pair_private hlegal hroot hS (structural_pair_mem.mp hQ)

theorem actual_family_structural_budget {Ω : Finset ℤ} {F : Finset (Finset ℤ)} {c : ℤ}
    (hlegal : Legal Ω F) (hroot : Rooted F c) :
    (∑ S∈F,(StructuralPairs c S).card)≤(PairUniverse c Ω).card := by
  let V := F.sigma (StructuralPairs c)
  have hmaps : Set.MapsTo (fun q : Σ _ : Finset ℤ,Finset ℤ => q.2)
      (V:Set (Σ _ : Finset ℤ,Finset ℤ)) (PairUniverse c Ω) := by
    intro q hq
    obtain ⟨hS,hQ⟩ := Finset.mem_sigma.mp hq
    exact available_subset_pairUniverse c Ω F (actual_structural_private hlegal hroot hS hQ).1
  have hinj : Set.InjOn (fun q : Σ _ : Finset ℤ,Finset ℤ => q.2)
      (V:Set (Σ _ : Finset ℤ,Finset ℤ)) := by
    rintro ⟨S,Q⟩ ha ⟨T,R⟩ hb heq
    change Q=R at heq
    obtain ⟨hS,hQ⟩ := Finset.mem_sigma.mp ha
    obtain ⟨hT,hR⟩ := Finset.mem_sigma.mp hb
    have hST : S=T := by
      by_contra hne
      have hn := (actual_structural_private hlegal hroot hS hQ).2 T hT (fun he => hne he.symm)
      apply hn
      rw [heq]
      exact (structural_pair_mem.mp hR).2.2.1
    cases hST; cases heq
    rfl
  simpa only [V,Finset.card_sigma] using Finset.card_le_card_of_injOn _ hmaps hinj

#print axioms structural_pair_mem
#print axioms divisor_from_primitive_index
#print axioms actual_variable_anchor_codes
#print axioms actual_structural_private
#print axioms actual_family_structural_budget
end
end JSP233.TraceWitnessCodes36
