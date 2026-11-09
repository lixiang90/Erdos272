module

public import Erdos272.Foundation.StarCompletion
public import Erdos272.Foundation.PrivateUnion
public import Mathlib.Data.Int.GCD
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Finset.Max

@[expose] public section

/-! Arithmetic geometry of actual finite integer arithmetic progressions. -/

namespace JSP233.APGeometry

open StarCompletion

def APAt (d p : Int) (S : Finset Int) : Prop :=
  PrivateUnion.APAt d p (fun x => x ∈ S)

theorem isAP_iff_exists_APAt (S : Finset Int) :
    IsAP S ↔ ∃ d p, APAt d p S ∧ p ∈ S := by
  constructor
  · rintro ⟨d,p,hd,lo,hi,hr,hp⟩
    exact ⟨d,p,⟨hd,lo,hi,hr⟩,hp⟩
  · rintro ⟨d,p,⟨hd,lo,hi,hr⟩,hp⟩
    exact ⟨d,p,hd,lo,hi,hr,hp⟩

theorem apAt_rebase {d p u : Int} {S : Finset Int}
    (hS : APAt d p S) (hu : u ∈ S) : APAt d u S :=
  PrivateUnion.APAt_rebase d p u _ hS hu

theorem apAt_dvd_sub {d p x y : Int} {S : Finset Int}
    (hS : APAt d p S) (hx : x ∈ S) (hy : y ∈ S) : d ∣ y-x := by
  obtain ⟨_, lo, hi, hr⟩ := hS
  have h := Int.dvd_sub ((hr y).mp hy).2.2 ((hr x).mp hx).2.2
  convert h using 1
  ring

theorem apAt_fill {d p x y z : Int} {S : Finset Int}
    (hS : APAt d p S) (hx : x ∈ S) (hy : y ∈ S)
    (hxz : x ≤ z) (hzy : z ≤ y) (hdz : d ∣ z-x) : z ∈ S := by
  obtain ⟨_, lo, hi, hr⟩ := apAt_rebase hS hx
  exact (hr z).mpr ⟨le_trans ((hr x).mp hx).1 hxz,
    le_trans hzy ((hr y).mp hy).2.1, hdz⟩

theorem apAt_inter {d e p : Int} {S T : Finset Int}
    (hS : APAt d p S) (hT : APAt e p T) :
    APAt (Int.lcm d e : Int) p (S ∩ T) := by
  obtain ⟨hd, a, b, hSr⟩ := hS
  obtain ⟨he, c, f, hTr⟩ := hT
  refine ⟨?_, max a c, min b f, ?_⟩
  · exact_mod_cast Int.lcm_pos (by omega : d ≠ 0) (by omega : e ≠ 0)
  · intro x
    simp only [Finset.mem_inter, hSr, hTr, Int.coe_lcm_dvd_iff]
    omega

theorem isAP_inter_of_nonempty {S T : Finset Int}
    (hS : IsAP S) (hT : IsAP T) (hne : (S ∩ T).Nonempty) :
    IsAP (S ∩ T) := by
  obtain ⟨p, hp⟩ := hne
  obtain ⟨d, a, hS, _⟩ := (isAP_iff_exists_APAt S).mp hS
  obtain ⟨e, b, hT, _⟩ := (isAP_iff_exists_APAt T).mp hT
  exact (isAP_iff_exists_APAt _).mpr ⟨_, p,
    apAt_inter (apAt_rebase hS (Finset.mem_inter.mp hp).1)
      (apAt_rebase hT (Finset.mem_inter.mp hp).2), hp⟩

/-- Intersect a real finite family inside an explicitly specified first set. -/
def familyInter (S : Finset Int) (H : Finset (Finset Int)) : Finset Int :=
  S.filter (fun x => ∀ T ∈ H, x ∈ T)

theorem familyInter_insert (S T : Finset Int) (H : Finset (Finset Int)) :
    familyInter S (insert T H) = familyInter (S ∩ T) H := by
  ext x
  simp [familyInter, and_assoc]

theorem familyInter_isAP {S : Finset Int} {H : Finset (Finset Int)}
    (hS : IsAP S) (hH : ∀ T ∈ H, IsAP T)
    (hne : (familyInter S H).Nonempty) : IsAP (familyInter S H) := by
  induction H using Finset.induction_on generalizing S with
  | empty => simpa [familyInter] using hS
  | @insert T H hnot ih =>
    rw [familyInter_insert] at hne ⊢
    have hSTne : (S ∩ T).Nonempty := by
      obtain ⟨x,hx⟩ := hne
      exact ⟨x,(Finset.mem_filter.mp hx).1⟩
    exact ih (isAP_inter_of_nonempty hS (hH T (by simp)) hSTne)
      (by intro U hU; exact hH U (Finset.mem_insert_of_mem hU)) hne

/-- The actual common intersection of a legal family with at least two
members is an AP whenever nonempty, although its members may be crooked. -/
theorem actual_common_kernel_isAP
    (Ω : Finset Int) (H : Finset (Finset Int))
    (hground : ∀ S ∈ H, S ⊆ Ω)
    (hpair : ∀ S ∈ H, ∀ T ∈ H, S ≠ T → IsAP (S ∩ T))
    (htwo : 2 ≤ H.card)
    (hne : (Ω.filter (fun x => ∀ S ∈ H, x ∈ S)).Nonempty) :
    IsAP (Ω.filter (fun x => ∀ S ∈ H, x ∈ S)) := by
  obtain ⟨S,hS⟩ := Finset.card_pos.mp (by omega : 0 < H.card)
  have herase : (H.erase S).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem hS]
    omega
  obtain ⟨T,hT⟩ := herase
  have hTH : T ∈ H := (Finset.mem_erase.mp hT).2
  have hST : S ≠ T := Ne.symm (Finset.mem_erase.mp hT).1
  let J := (H.erase S).image (fun U => S ∩ U)
  have hJ : ∀ U ∈ J, IsAP U := by
    intro U hU
    obtain ⟨V,hV,rfl⟩ := Finset.mem_image.mp hU
    exact hpair S hS V (Finset.mem_erase.mp hV).2
      (Ne.symm (Finset.mem_erase.mp hV).1)
  have heq : familyInter (S ∩ T) J = Ω.filter (fun x => ∀ U ∈ H, x ∈ U) := by
    ext x
    simp only [familyInter, Finset.mem_filter, Finset.mem_inter]
    constructor
    · intro hx
      refine ⟨hground S hS hx.1.1, ?_⟩
      intro U hU
      by_cases he : U = S
      · simpa [he] using hx.1.1
      · have hUJ : S ∩ U ∈ J := Finset.mem_image.mpr
          ⟨U,Finset.mem_erase.mpr ⟨he,hU⟩,rfl⟩
        exact (Finset.mem_inter.mp (hx.2 _ hUJ)).2
    · intro hx
      refine ⟨⟨hx.2 S hS,hx.2 T hTH⟩,?_⟩
      intro U hU
      obtain ⟨V,hV,rfl⟩ := Finset.mem_image.mp hU
      exact Finset.mem_inter.mpr ⟨hx.2 S hS,hx.2 V (Finset.mem_erase.mp hV).2⟩
  rw [← heq] at hne ⊢
  exact familyInter_isAP (hpair S hS T hTH hST) hJ hne

theorem commonKernel_isAP (Ω : Finset Int) (F : Finset (Finset Int)) (c : Int)
    (hF : Legal Ω F) (htwo : 2 ≤ (Avoiders F c).card)
    (hne : (CommonKernel Ω F c).Nonempty) : IsAP (CommonKernel Ω F c) := by
  exact actual_common_kernel_isAP Ω (Avoiders F c)
    (by intro S hS; exact hF.1 S (Finset.mem_filter.mp hS).1)
    (by
      intro S hS T hT hne
      exact hF.2 S (Finset.mem_filter.mp hS).1 T (Finset.mem_filter.mp hT).1 hne)
    htwo hne

/-- An exact parametrization from actual endpoints, not a cardinality oracle. -/
theorem apAt_image_Icc {d p : Int} {S : Finset Int}
    (hS : APAt d p S) (hne : S.Nonempty) :
    let a := S.min' hne
    let b := S.max' hne
    S = (Finset.Icc (0 : Int) ((b-a)/d)).image (fun i => a+d*i) := by
  dsimp
  let a := S.min' hne
  let b := S.max' hne
  have ha : a ∈ S := Finset.min'_mem S hne
  have hb : b ∈ S := Finset.max'_mem S hne
  have hd : 0 < d := hS.1
  have hba : d ∣ b-a := apAt_dvd_sub hS ha hb
  have hq := Int.ediv_mul_cancel hba
  change S = (Finset.Icc 0 ((b-a)/d)).image (fun i => a+d*i)
  ext x
  constructor
  · intro hx
    have hax : a ≤ x := Finset.min'_le S x hx
    have hxb : x ≤ b := Finset.le_max' S x hx
    have hdx : d ∣ x-a := apAt_dvd_sub hS ha hx
    have hqx := Int.ediv_mul_cancel hdx
    apply Finset.mem_image.mpr
    refine ⟨(x-a)/d, Finset.mem_Icc.mpr ⟨?_,?_⟩,?_⟩
    · exact Int.ediv_nonneg (by omega) (by omega)
    · nlinarith
    · nlinarith
  · intro hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    have hi' := Finset.mem_Icc.mp hi
    apply apAt_fill hS ha hb
    · nlinarith
    · nlinarith
    · exact ⟨i,by ring⟩

theorem apAt_span_eq {d p : Int} {S : Finset Int}
    (hS : APAt d p S) (hne : S.Nonempty) :
    S.max' hne - S.min' hne = d * ((S.card : Int)-1) := by
  let a := S.min' hne
  let b := S.max' hne
  have ha : a ∈ S := Finset.min'_mem S hne
  have hb : b ∈ S := Finset.max'_mem S hne
  have hba : a ≤ b := Finset.min'_le S b hb
  have hd : 0 < d := hS.1
  have hdiv : d ∣ b-a := apAt_dvd_sub hS ha hb
  have hqnonneg : 0 ≤ (b-a)/d := Int.ediv_nonneg (by omega) (by omega)
  have himage := apAt_image_Icc hS hne
  have hinj : Function.Injective (fun i : Int => a+d*i) := by
    intro i j he
    nlinarith
  have hcard : S.card = (Finset.Icc (0 : Int) ((b-a)/d)).card := by
    rw [himage]
    exact Finset.card_image_of_injective _ hinj
  have hcardInt : (S.card : Int) = (b-a)/d+1 := by
    rw [hcard]
    simpa using (Int.card_Icc_of_le (a := (0 : Int)) (b := ((b-a)/d)) (by omega))
  have hq := Int.ediv_mul_cancel hdiv
  change b-a = d*((S.card : Int)-1)
  nlinarith

theorem apAt_adjacent_min {d p : Int} {S : Finset Int}
    (hS : APAt d p S) (htwo : 2 ≤ S.card) :
    ∃ a b, a ∈ S ∧ a+d ∈ S ∧ b ∈ S ∧
      (∀ x ∈ S, a ≤ x ∧ x ≤ b) ∧ b-a = d*((S.card : Int)-1) := by
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  let a := S.min' hne
  let b := S.max' hne
  have ha : a ∈ S := Finset.min'_mem S hne
  have hb : b ∈ S := Finset.max'_mem S hne
  have hspan : b-a = d*((S.card : Int)-1) := apAt_span_eq hS hne
  have hd : 0 < d := hS.1
  refine ⟨a,b,ha,?_,hb,?_,hspan⟩
  · apply apAt_fill hS ha hb
    · omega
    · have hk : (2 : Int) ≤ (S.card : Int) := by exact_mod_cast htwo
      nlinarith
    · have : a+d-a=d := by omega
      rw [this]
  · intro x hx
    exact ⟨Finset.min'_le S x hx,Finset.le_max' S x hx⟩

/-- The chosen true AP step obeys the actual ambient span constraint. -/
theorem apAt_card_span {d p N : Int} {S : Finset Int}
    (hS : APAt d p S) (hne : S.Nonempty)
    (hground : S ⊆ Finset.Icc 1 N) :
    d*((S.card : Int)-1) ≤ N-1 := by
  have ha := Finset.mem_Icc.mp (hground (Finset.min'_mem S hne))
  have hb := Finset.mem_Icc.mp (hground (Finset.max'_mem S hne))
  have hs := apAt_span_eq hS hne
  omega

theorem apAt_eq_range {d p : Int} {S : Finset Int}
    (hS : APAt d p S) (hne : S.Nonempty) :
    S = (Finset.range S.card).image (fun i : Nat => S.min' hne+d*(i : Int)) := by
  let a := S.min' hne
  let b := S.max' hne
  have ha : a ∈ S := Finset.min'_mem S hne
  have hb : b ∈ S := Finset.max'_mem S hne
  have hd : 0 < d := hS.1
  have hspan : b-a = d*((S.card : Int)-1) := apAt_span_eq hS hne
  ext x
  constructor
  · intro hx
    have hax : a ≤ x := Finset.min'_le S x hx
    have hxb : x ≤ b := Finset.le_max' S x hx
    have hdiv : d ∣ x-a := apAt_dvd_sub hS ha hx
    have hq := Int.ediv_mul_cancel hdiv
    have hqpos : 0 ≤ (x-a)/d := Int.ediv_nonneg (by omega) (by omega)
    have hcast : (((x-a)/d).toNat : Int) = (x-a)/d := Int.toNat_of_nonneg hqpos
    refine Finset.mem_image.mpr ⟨((x-a)/d).toNat, Finset.mem_range.mpr ?_, ?_⟩
    · have hi : (x-a)/d < (S.card : Int) := by nlinarith
      omega
    · change a+d*((((x-a)/d).toNat : Nat) : Int)=x
      rw [hcast]
      nlinarith
  · intro hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    have hi' : (i : Int) < (S.card : Int) := by exact_mod_cast Finset.mem_range.mp hi
    change a+d*(i : Int) ∈ S
    apply apAt_fill hS ha hb
    · nlinarith [Int.natCast_nonneg i]
    · nlinarith
    · exact ⟨(i : Int),by ring⟩

/-- More than floor(N/3) actual kernel points force a step at most three. -/
theorem isAP_large_card_step_le_three {N : Nat} {S : Finset Int}
    (hS : IsAP S) (hN : 6 ≤ N) (hcard : N/3 < S.card)
    (hground : S ⊆ Finset.Icc 1 (N : Int)) :
    ∃ d p, APAt d p S ∧ p ∈ S ∧ d ≤ 3 := by
  obtain ⟨d,p,hd,hp⟩ := (isAP_iff_exists_APAt S).mp hS
  refine ⟨d,p,hd,hp,?_⟩
  have hs := apAt_card_span hd ⟨p,hp⟩ hground
  have hdpos : 0 < d := hd.1
  have hquot : (N : Int) < 3*((S.card : Int)) := by omega
  have hk : (3 : Int) ≤ (S.card : Int) := by omega
  by_contra hneg
  have hd4 : 4 ≤ d := by omega
  have hmul : 4*((S.card : Int)-1) ≤ d*((S.card : Int)-1) := by nlinarith
  have hex : (N : Int) ≤ 4*((N/3 : Nat) : Int) := by omega
  have hkq : ((N/3 : Nat) : Int) ≤ (S.card : Int)-1 := by omega
  nlinarith

/-- Full geometry extracted from an actual large AP kernel. -/
theorem isAP_large_card_geometry {N : Nat} {S : Finset Int}
    (hS : IsAP S) (hN : 6 ≤ N) (hcard : N/3 < S.card)
    (hground : S ⊆ Finset.Icc 1 (N : Int)) :
    ∃ d a b, APAt d a S ∧ 0 < d ∧ d ≤ 3 ∧
      a ∈ S ∧ a+d ∈ S ∧ b ∈ S ∧
      (∀ x ∈ S, a ≤ x ∧ x ≤ b) ∧
      b-a = d*((S.card : Int)-1) ∧
      S = (Finset.range S.card).image (fun i : Nat => a+d*(i : Int)) := by
  obtain ⟨d,p,hd,hp,hd3⟩ := isAP_large_card_step_le_three hS hN hcard hground
  have hne : S.Nonempty := ⟨p,hp⟩
  let a := S.min' hne
  let b := S.max' hne
  have ha : a ∈ S := Finset.min'_mem S hne
  have hb : b ∈ S := Finset.max'_mem S hne
  have hspan : b-a = d*((S.card : Int)-1) := apAt_span_eq hd hne
  have hdpos : 0 < d := hd.1
  refine ⟨d,a,b,apAt_rebase hd ha,hdpos,hd3,ha,?_,hb,?_,hspan,apAt_eq_range hd hne⟩
  · apply apAt_fill hd ha hb
    · omega
    · have hk : (3 : Int) ≤ (S.card : Int) := by omega
      nlinarith
    · have : a+d-a=d := by omega
      rw [this]
  · intro x hx
    exact ⟨Finset.min'_le S x hx,Finset.le_max' S x hx⟩

#print axioms apAt_inter
#print axioms isAP_inter_of_nonempty
#print axioms familyInter_isAP
#print axioms actual_common_kernel_isAP
#print axioms commonKernel_isAP
#print axioms apAt_image_Icc
#print axioms apAt_span_eq
#print axioms apAt_adjacent_min
#print axioms apAt_card_span
#print axioms apAt_eq_range
#print axioms isAP_large_card_step_le_three
#print axioms isAP_large_card_geometry

end JSP233.APGeometry
