import Erdos272.Core.SinglePrivate32
import Mathlib.Data.Int.Interval

/-! The complete unit-normalized singleton intrinsic-pair classification. -/
namespace JSP233.UnitPrivate32
open StarCompletion PrivatePairExistence SinglePrivate32
open scoped Classical
noncomputable section

theorem icc_isAP (lo hi : ℤ) (hle : lo≤hi) : IsAP (Finset.Icc lo hi) := by
  refine ⟨1,lo,by omega,lo,hi,?_,Finset.mem_Icc.mpr ⟨le_rfl,hle⟩⟩
  intro x
  simp

theorem unit_pair_properties {S : Finset ℤ} {v : ℤ}
    (hu : IntrinsicPairs 0 S={{1,v}}) : v∈S ∧ v≠0 ∧ 1≠v := by
  have hm : ({1,v} : Finset ℤ)∈IntrinsicPairs 0 S := by rw [hu]; simp
  obtain ⟨hsub,hcard,hzero,hmiss⟩ := (mem_intrinsicPairs 0 S {1,v}).mp hm
  refine ⟨hsub (by simp),?_,?_⟩
  · intro he; subst v; simp at hzero
  · intro he; rw [←he] at hcard; simp at hcard

theorem full_pair_with_exception {S : Finset ℤ} {a v : ℤ}
    (hz : 0∈S) (hu : IntrinsicPairs 0 S={{1,v}})
    (ha : a∈S) (hv : v∈S) (ha1 : a≠1) (h1v : 1≠v) :
    ∀ x, Completion a v x → x∈S := by
  apply completion_full_away_pair hz hu ha hv
  intro he
  have hh : (1:ℤ)∈({a,v} : Finset ℤ) := he.symm ▸ (by simp : (1:ℤ)∈({1,v} : Finset ℤ))
  simp only [Finset.mem_insert,Finset.mem_singleton] at hh
  rcases hh with hh | hh
  · exact ha1 hh.symm
  · exact h1v hh

theorem unit_interval_shape {S : Finset ℤ} {v : ℤ}
    (hz : 0∈S) (h1 : 1∈S) (hbad : ¬IsAP S) (hcard : 4≤S.card)
    (hu : IntrinsicPairs 0 S={{1,v}}) :
    ∃ R : ℤ, 2≤R ∧ (v≤-2 ∨ R+2≤v) ∧ S=insert v (Finset.Icc 0 R) := by
  obtain ⟨hv,hv0,h1v⟩ := unit_pair_properties hu
  obtain ⟨lo,R,hlo,hR,hout,hgrid,hAP⟩ := minimum_exception_interval
    hz h1 hv (by norm_num : (1:ℤ)≠0) hv0 h1v hbad hu (fun w hw => one_dvd w)
  have hI : S.erase v=Finset.Icc lo R := by simpa using hgrid
  have h1e : (1:ℤ)∈Finset.Icc lo R := by
    rw [←hI]
    exact Finset.mem_erase.mpr ⟨h1v,h1⟩
  have hR1 : 1≤R := (Finset.mem_Icc.mp h1e).2
  have hshape : S=insert v (Finset.Icc lo R) := by rw [←hI,Finset.insert_erase hv]
  have hlo0 : lo=0 := by
    by_contra hn
    have hlot : lo<0 := by omega
    have hminus : (-1:ℤ)∈S := by
      rw [hshape]
      exact Finset.mem_insert_of_mem (Finset.mem_Icc.mpr ⟨by omega,by omega⟩)
    have hfull := full_pair_with_exception hz hu hminus hv (by norm_num : (-1:ℤ)≠1) h1v
    apply hbad
    refine ⟨1,0,by omega,min lo v,max R v,?_,hz⟩
    intro x
    constructor
    · intro hx
      rw [hshape] at hx
      simp only [Finset.mem_insert,Finset.mem_Icc] at hx
      rcases hx with rfl | hx <;> exact ⟨by omega,by omega,one_dvd _⟩
    · rintro ⟨hl,hr,hdiv⟩
      by_cases hi : lo≤x ∧ x≤R
      · rw [hshape]
        exact Finset.mem_insert_of_mem (Finset.mem_Icc.mpr hi)
      · apply hfull x
        exact ⟨by omega,by omega,by simp⟩
  have hshape0 : S=insert v (Finset.Icc 0 R) := by simpa only [hlo0] using hshape
  have hout0 : v<0 ∨ R<v := by simpa only [hlo0] using hout
  have hvnot : v∉Finset.Icc (0:ℤ) R := by simp only [Finset.mem_Icc]; omega
  have hcount := congrArg Finset.card hshape0
  rw [Finset.card_insert_of_notMem hvnot,Int.card_Icc] at hcount
  have hR2 : 2≤R := by omega
  have hnotminus : v≠-1 := by
    intro he
    have heq : S=Finset.Icc v R := by
      rw [hshape0]
      ext x
      simp only [Finset.mem_insert,Finset.mem_Icc]
      omega
    exact hbad (heq ▸ icc_isAP v R (by omega))
  have hnotnext : v≠R+1 := by
    intro he
    have heq : S=Finset.Icc 0 v := by
      rw [hshape0]
      ext x
      simp only [Finset.mem_insert,Finset.mem_Icc]
      omega
    exact hbad (heq ▸ icc_isAP 0 v (by omega))
  exact ⟨R,hR2,by omega,hshape0⟩

theorem gcd_odd_two (t : ℤ) : Int.gcd (2*t-1) 2=1 := by
  apply Int.gcd_eq_one_iff.mpr
  intro c hca hc2
  have hh := Int.dvd_sub (dvd_mul_of_dvd_left hc2 t) hca
  convert hh using 1; ring

theorem gcd_odd_four (t : ℤ) : Int.gcd (2*t-1) 4=1 := by
  simpa using Int.gcd_pow_right_of_gcd_eq_one (k:=2) (gcd_odd_two t)

theorem even_coprime_obstruction (v : ℤ) (hv : 4≤v) (heven : (2:ℤ)∣v)
    (hno : ∀ a : ℤ, 2≤a → a≤v-2 → Int.gcd a v≠1) : v=4 ∨ v=6 := by
  obtain ⟨q,hqeq⟩ := heven
  have hq : 2≤q := by omega
  by_contra hn
  have hq4 : 4≤q := by omega
  by_cases hmod : q%2=0
  · have hh := Int.gcd_sub_mul_right_right (q-1) v 2
    have he : v-2*(q-1)=2 := by omega
    rw [he] at hh
    have hodd : q-1=2*(q/2)-1 := by omega
    have hg : Int.gcd (q-1) 2=1 := by rw [hodd]; exact gcd_odd_two _
    exact hno (q-1) (by omega) (by omega) (hh.symm.trans hg)
  · have hmod1 : q%2=1 := by omega
    have hh := Int.gcd_sub_mul_right_right (q-2) v 2
    have he : v-2*(q-2)=4 := by omega
    rw [he] at hh
    have hodd : q-2=2*(q/2)-1 := by omega
    have hg : Int.gcd (q-2) 4=1 := by rw [hodd]; exact gcd_odd_four _
    exact hno (q-2) (by omega) (by omega) (hh.symm.trans hg)

theorem gcd_two_cases (v : ℤ) : Int.gcd (2:ℤ) v=1 ∨ Int.gcd (2:ℤ) v=2 := by
  have hp := Int.gcd_pos_of_ne_zero_left v (by norm_num : (2:ℤ)≠0)
  have hl := Int.gcd_le_natAbs_left v (by norm_num : (2:ℤ)≠0)
  norm_num at hl
  omega

theorem positive_unit_exception {S : Finset ℤ} {R v : ℤ}
    (hz : 0∈S) (hu : IntrinsicPairs 0 S={{1,v}})
    (hR : 2≤R) (hv : R+2≤v) (hshape : S=insert v (Finset.Icc 0 R)) :
    (v=4 ∧ R=2) ∨ (v=6 ∧ R=4) := by
  obtain ⟨hvS,hv0,h1v⟩ := unit_pair_properties hu
  have h2 : (2:ℤ)∈S := by rw [hshape]; simp only [Finset.mem_insert,Finset.mem_Icc]; omega
  have hfull := full_pair_with_exception hz hu h2 hvS (by norm_num : (2:ℤ)≠1) h1v
  have hg2 : Int.gcd (2:ℤ) v=2 := by
    rcases gcd_two_cases v with hg | hg
    · have hm : R+1∈S := hfull _ ⟨by omega,by omega,by simp [hg]⟩
      rw [hshape] at hm
      simp only [Finset.mem_insert,Finset.mem_Icc] at hm
      omega
    · exact hg
  have hdv : (2:ℤ)∣v := by simpa only [hg2,Nat.cast_ofNat] using Int.gcd_dvd_right (2:ℤ) v
  have hm : v-2∈S := hfull _ ⟨by omega,by omega,by
    simpa only [hg2,Nat.cast_ofNat] using Int.dvd_sub hdv (dvd_refl (2:ℤ))⟩
  rw [hshape] at hm
  simp only [Finset.mem_insert,Finset.mem_Icc] at hm
  have hRv : R=v-2 := by omega
  have hno : ∀ a : ℤ, 2≤a → a≤v-2 → Int.gcd a v≠1 := by
    intro a ha hav hg
    have haS : a∈S := by rw [hshape]; simp only [Finset.mem_insert,Finset.mem_Icc]; omega
    have hf := full_pair_with_exception hz hu haS hvS (by omega) h1v
    have hx : v-1∈S := hf _ ⟨by omega,by omega,by simp [hg]⟩
    rw [hshape] at hx
    simp only [Finset.mem_insert,Finset.mem_Icc] at hx
    omega
  rcases even_coprime_obstruction v (by omega) hdv hno with h4 | h6
  · exact Or.inl ⟨h4,by omega⟩
  · exact Or.inr ⟨h6,by omega⟩

theorem negative_unit_exception {S : Finset ℤ} {R v : ℤ}
    (hz : 0∈S) (hu : IntrinsicPairs 0 S={{1,v}})
    (hR : 2≤R) (hv : v≤-2) (hshape : S=insert v (Finset.Icc 0 R)) :
    v=-2 ∧ R=2 := by
  obtain ⟨hvS,hv0,h1v⟩ := unit_pair_properties hu
  have h2 : (2:ℤ)∈S := by rw [hshape]; simp only [Finset.mem_insert,Finset.mem_Icc]; omega
  have hfull := full_pair_with_exception hz hu h2 hvS (by norm_num : (2:ℤ)≠1) h1v
  have hp := Int.gcd_pos_of_ne_zero_left v (by norm_num : (2:ℤ)≠0)
  have hl := Int.gcd_le_natAbs_left v (by norm_num : (2:ℤ)≠0)
  norm_num at hl
  have hm : -(Int.gcd (2:ℤ) v:ℤ)∈S := hfull _
    ⟨by omega,by omega,dvd_neg.mpr (dvd_refl _)⟩
  rw [hshape] at hm
  simp only [Finset.mem_insert,Finset.mem_Icc] at hm
  have hv2 : v=-2 := by omega
  have hR2 : R=2 := by
    by_contra hn
    have h3 : (3:ℤ)∈S := by rw [hshape]; simp only [Finset.mem_insert,Finset.mem_Icc]; omega
    have hf := full_pair_with_exception hz hu h3 hvS (by norm_num : (3:ℤ)≠1) h1v
    have hx : (-1:ℤ)∈S := hf _ ⟨by omega,by omega,by norm_num [hv2]⟩
    rw [hshape] at hx
    simp only [Finset.mem_insert,Finset.mem_Icc] at hx
    omega
  exact ⟨hv2,hR2⟩

theorem unit_singleton_classification {S : Finset ℤ} {v : ℤ}
    (hz : 0∈S) (h1 : 1∈S) (hbad : ¬IsAP S) (hcard : 4≤S.card)
    (hu : IntrinsicPairs 0 S={{1,v}}) :
    S={0,1,2,4} ∨ S={0,1,2,3,4,6} ∨ S={-2,0,1,2} := by
  obtain ⟨R,hR,hv,hshape⟩ := unit_interval_shape hz h1 hbad hcard hu
  rcases hv with hv | hv
  · obtain ⟨rfl,rfl⟩ := negative_unit_exception hz hu hR hv hshape
    right; right
    rw [hshape]
    ext x
    simp only [Finset.mem_insert,Finset.mem_singleton,Finset.mem_Icc]
    omega
  · rcases positive_unit_exception hz hu hR hv hshape with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · left
      rw [hshape]
      ext x
      simp only [Finset.mem_insert,Finset.mem_singleton,Finset.mem_Icc]
      omega
    · right; left
      rw [hshape]
      ext x
      simp only [Finset.mem_insert,Finset.mem_singleton,Finset.mem_Icc]
      omega

#print axioms icc_isAP
#print axioms unit_pair_properties
#print axioms full_pair_with_exception
#print axioms unit_interval_shape
#print axioms gcd_odd_two
#print axioms gcd_odd_four
#print axioms even_coprime_obstruction
#print axioms gcd_two_cases
#print axioms positive_unit_exception
#print axioms negative_unit_exception
#print axioms unit_singleton_classification
end
end JSP233.UnitPrivate32
