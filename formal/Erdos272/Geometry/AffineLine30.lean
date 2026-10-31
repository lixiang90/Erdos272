import Erdos272.Staircase.StaircaseComplete29
import Erdos272.Foundation.APGeometry
import Mathlib.Data.Int.GCD
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace JSP233.AffineLine30
open StarCompletion StaircaseGeometry APGeometry
open scoped BigOperators
set_option maxHeartbeats 1000000

def affine (c d x : Int) : Int := c+d*x
def mapSet (c d : Int) (S : Finset Int) : Finset Int := S.image (affine c d)
def mapFamily (c d : Int) (F : Finset (Finset Int)) : Finset (Finset Int) :=
  F.image (mapSet c d)

def IsStepPrimitive (c d : Int) (Q : Finset Int) : Prop :=
  Q.card=2 ∧ c∉Q ∧ ¬IsAP (insert c Q) ∧
    ∀ u∈Q, ∀ v∈Q, u≠v → Int.gcd (u-c) (v-c)=d.natAbs

noncomputable def gcdStepPairs (c d : Int) (S : Finset Int) : Finset (Finset Int) := by
  classical
  exact S.powerset.filter (IsStepPrimitive c d)
noncomputable def gcdStepPool (c d : Int) (F : Finset (Finset Int)) : Finset (Finset Int) :=
  F.biUnion (gcdStepPairs c d)

theorem affine_injective (c d : Int) (hd : 0<d) : Function.Injective (affine c d) := by
  intro x y h
  dsimp [affine] at h
  nlinarith

theorem affine_strictMono (c d : Int) (hd : 0<d) : StrictMono (affine c d) := by
  intro x y hxy
  dsimp [affine]
  nlinarith

theorem mem_mapSet (c d : Int) (hd : 0<d) (S : Finset Int) (x : Int) :
    affine c d x ∈ mapSet c d S ↔ x∈S := by
  constructor
  · intro hx
    obtain ⟨y,hy,heq⟩ := Finset.mem_image.mp hx
    have he : y=x := affine_injective c d hd heq
    simpa only [he] using hy
  · intro hx
    exact Finset.mem_image.mpr ⟨x,hx,rfl⟩

theorem mapSet_injective (c d : Int) (hd : 0<d) : Function.Injective (mapSet c d) := by
  intro S T heq
  ext x
  rw [←mem_mapSet c d hd S x,←mem_mapSet c d hd T x,heq]

theorem mapSet_card (c d : Int) (hd : 0<d) (S : Finset Int) :
    (mapSet c d S).card=S.card := Finset.card_image_of_injective _ (affine_injective c d hd)

theorem mapFamily_card (c d : Int) (hd : 0<d) (F : Finset (Finset Int)) :
    (mapFamily c d F).card=F.card := Finset.card_image_of_injective _ (mapSet_injective c d hd)

theorem mapSet_insert (c d x : Int) (S : Finset Int) :
    mapSet c d (insert x S)=insert (affine c d x) (mapSet c d S) := by
  simp [mapSet]

theorem affine_zero (c d : Int) : affine c d 0=c := by simp [affine]

theorem affine_sub (c d x y : Int) : affine c d x-affine c d y=d*(x-y) := by
  dsimp [affine]
  ring

theorem mem_gcdStepPairs (c d : Int) (S Q : Finset Int) :
    Q∈gcdStepPairs c d S ↔ Q⊆S ∧ IsStepPrimitive c d Q := by
  classical
  simp [gcdStepPairs]

theorem mem_gcdStepPool (c d : Int) (F : Finset (Finset Int)) (Q : Finset Int) :
    Q∈gcdStepPool c d F ↔ ∃ S∈F, Q⊆S ∧ IsStepPrimitive c d Q := by
  classical
  simp [gcdStepPool,mem_gcdStepPairs]

theorem affine_APAt (c d : Int) (hd : 0<d) {e p : Int} {S : Finset Int}
    (hS : APAt e p S) : APAt (d*e) (affine c d p) (mapSet c d S) := by
  obtain ⟨he,lo,hi,hr⟩ := hS
  refine ⟨mul_pos hd he,affine c d lo,affine c d hi,?_⟩
  intro y
  constructor
  · intro hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hlo,hhi,hediv⟩ := (hr x).mp hx
    refine ⟨?_,?_,?_⟩
    · dsimp [affine]; nlinarith
    · dsimp [affine]; nlinarith
    · rw [affine_sub]
      exact mul_dvd_mul_left d hediv
  · rintro ⟨hlo,hhi,hediv⟩
    obtain ⟨q,hq⟩ := hediv
    let x := p+e*q
    have hy : y=affine c d x := by
      calc
        y = affine c d p+(d*e)*q := by omega
        _ = _ := by dsimp [affine,x]; ring
    rw [hy] at hlo hhi
    have hxlo : lo≤x := by dsimp [affine] at hlo; nlinarith
    have hxhi : x≤hi := by dsimp [affine] at hhi; nlinarith
    have hxdiv : e∣x-p := ⟨q,by dsimp [x]; ring⟩
    exact Finset.mem_image.mpr ⟨x,(hr x).mpr ⟨hxlo,hxhi,hxdiv⟩,hy.symm⟩

theorem affine_isAP (c d : Int) (hd : 0<d) {S : Finset Int} (hS : IsAP S) :
    IsAP (mapSet c d S) := by
  obtain ⟨e,p,hAP,hp⟩ := (isAP_iff_exists_APAt S).mp hS
  exact (isAP_iff_exists_APAt _).mpr
    ⟨d*e,affine c d p,affine_APAt c d hd hAP,(mem_mapSet c d hd S p).mpr hp⟩

theorem affine_isAP_iff (c d : Int) (hd : 0<d) (S : Finset Int) :
    IsAP (mapSet c d S) ↔ IsAP S := by
  refine ⟨?_,affine_isAP c d hd⟩
  intro h
  obtain ⟨e,p,hAP,hp⟩ := (isAP_iff_exists_APAt _).mp h
  obtain ⟨z,hz,hzp⟩ := Finset.mem_image.mp hp
  by_cases hsmall : S.card≤2
  · exact nonempty_card_le_two_isAP ⟨z,hz⟩ hsmall
  have htwo : 2≤(mapSet c d S).card := by rw [mapSet_card c d hd]; omega
  obtain ⟨a,b,ha,hae,hb,hbounds,hspan⟩ := apAt_adjacent_min hAP htwo
  obtain ⟨u,hu,hua⟩ := Finset.mem_image.mp ha
  obtain ⟨v,hv,hve⟩ := Finset.mem_image.mp hae
  obtain ⟨w,hw,hwb⟩ := Finset.mem_image.mp hb
  have he : e=d*(v-u) := by dsimp [affine] at hua hve; nlinarith
  have hepos : 0<e := hAP.1
  have ht : 0<v-u := by nlinarith
  apply (isAP_iff_exists_APAt S).mpr
  refine ⟨v-u,u,⟨ht,u,w,?_⟩,hu⟩
  intro x
  constructor
  · intro hx
    have hbds := hbounds (affine c d x) ((mem_mapSet c d hd S x).mpr hx)
    have hdvd := apAt_dvd_sub hAP ha ((mem_mapSet c d hd S x).mpr hx)
    rw [←hua,affine_sub,he] at hdvd
    refine ⟨?_,?_,(mul_dvd_mul_iff_left (ne_of_gt hd)).mp hdvd⟩
    · rw [←hua,←hwb] at hbds; dsimp [affine] at hbds; nlinarith
    · rw [←hua,←hwb] at hbds; dsimp [affine] at hbds; nlinarith
  · rintro ⟨hux,hxw,hdiv⟩
    apply (mem_mapSet c d hd S x).mp
    apply apAt_fill hAP ha hb
    · rw [←hua]; dsimp [affine]; nlinarith
    · rw [←hwb]; dsimp [affine]; nlinarith
    · rw [←hua,affine_sub,he]
      exact mul_dvd_mul_left d hdiv

theorem mapWindow_APAt (c d : Int) (hd : 0<d) (l r : Nat) :
    APAt d c (mapSet c d (Window l r)) := by
  have hw : APAt 1 0 (Window l r) := by
    refine ⟨by decide,-(l:Int),(r:Int),?_⟩
    intro x
    simp [Window]
  simpa only [mul_one,affine_zero] using affine_APAt c d hd hw

theorem actual_AP_representation {S : Finset Int} {c : Int}
    (hS : IsAP S) (hc : c∈S) :
    ∃ d : Int, 0<d ∧ ∃ l r : Nat, S=mapSet c d (Window l r) := by
  obtain ⟨d,p,hAP,hp⟩ := (isAP_iff_exists_APAt S).mp hS
  have hd : 0<d := hAP.1
  have hne : S.Nonempty := ⟨c,hc⟩
  let a := S.min' hne
  have hrep : S=(Finset.range S.card).image (fun i : Nat => a+d*(i:Int)) := apAt_eq_range hAP hne
  have hcmem := hc
  rw [hrep] at hcmem
  obtain ⟨j,hj,hjEq⟩ := Finset.mem_image.mp hcmem
  have hjlt : j<S.card := Finset.mem_range.mp hj
  have hr : ((S.card-1-j:Nat):Int)=(S.card:Int)-1-(j:Int) := by omega
  refine ⟨d,hd,j,S.card-1-j,?_⟩
  ext x
  constructor
  · intro hx
    rw [hrep] at hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    have hi' : (i:Int)<(S.card:Int) := by exact_mod_cast Finset.mem_range.mp hi
    apply Finset.mem_image.mpr
    refine ⟨(i:Int)-(j:Int),?_,?_⟩
    · rw [mem_window,hr]
      constructor <;> omega
    · dsimp [affine]
      rw [←hjEq]
      ring
  · intro hx
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
    rw [mem_window,hr] at hu
    have hnonneg : 0≤u+(j:Int) := by omega
    have hcast : (((u+(j:Int)).toNat:Nat):Int)=u+(j:Int) := Int.toNat_of_nonneg hnonneg
    rw [hrep]
    apply Finset.mem_image.mpr
    refine ⟨(u+(j:Int)).toNat,Finset.mem_range.mpr (by omega),?_⟩
    rw [hcast]
    dsimp [affine]
    rw [←hjEq]
    ring

theorem step_unique {S : Finset Int} {c d e : Int} {l r L R : Nat}
    (hd : 0<d) (he : 0<e) (hcard : 2≤S.card)
    (hS : S=mapSet c d (Window l r)) (hT : S=mapSet c e (Window L R)) : d=e := by
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  have hAPd : APAt d c S := by rw [hS]; exact mapWindow_APAt c d hd l r
  have hAPe : APAt e c S := by rw [hT]; exact mapWindow_APAt c e he L R
  have hspanD := apAt_span_eq hAPd hne
  have hspanE := apAt_span_eq hAPe hne
  have hk : (2:Int)≤(S.card:Int) := by exact_mod_cast hcard
  nlinarith

theorem mapSet_subset_iff (c d : Int) (hd : 0<d) (Q S : Finset Int) :
    mapSet c d Q ⊆ mapSet c d S ↔ Q⊆S := by
  constructor
  · intro h x hx
    exact (mem_mapSet c d hd S x).mp (h ((mem_mapSet c d hd Q x).mpr hx))
  · intro h y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    exact (mem_mapSet c d hd S x).mpr (h hx)

theorem exists_preimage_subset (c d : Int) (S P : Finset Int)
    (hP : P⊆mapSet c d S) : ∃ Q⊆S, mapSet c d Q=P := by
  refine ⟨S.filter (fun x => affine c d x∈P),Finset.filter_subset _ _,?_⟩
  ext y
  constructor
  · intro hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    exact (Finset.mem_filter.mp hx).2
  · intro hy
    obtain ⟨x,hx,heq⟩ := Finset.mem_image.mp (hP hy)
    exact Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr ⟨hx,by simpa only [heq] using hy⟩,heq⟩

theorem gcd_affine_offsets (c d u v : Int) :
    Int.gcd (affine c d u-c) (affine c d v-c)=d.natAbs*Int.gcd u v := by
  have hu : affine c d u-c=d*u := by dsimp [affine]; ring
  have hv : affine c d v-c=d*v := by dsimp [affine]; ring
  rw [hu,hv,Int.gcd_mul_left]

theorem isStepPrimitive_map_iff (c d : Int) (hd : 0<d) (Q : Finset Int) :
    IsStepPrimitive c d (mapSet c d Q) ↔ IsPrimitiveBadPair Q := by
  have hAP : IsAP (insert c (mapSet c d Q)) ↔ IsAP (insert 0 Q) := by
    simpa only [mapSet_insert,affine_zero] using affine_isAP_iff c d hd (insert 0 Q)
  have hdabs : 0<d.natAbs := Int.natAbs_pos.mpr (ne_of_gt hd)
  constructor
  · rintro ⟨hcard,hroot,hbad,hg⟩
    refine ⟨?_,?_,(not_congr hAP).mp hbad,?_⟩
    · simpa only [mapSet_card c d hd Q] using hcard
    · intro hz
      have hc := (mem_mapSet c d hd Q 0).mpr hz
      exact hroot (by simpa only [affine_zero] using hc)
    · intro u hu v hv huv
      have heq := hg (affine c d u) ((mem_mapSet c d hd Q u).mpr hu)
        (affine c d v) ((mem_mapSet c d hd Q v).mpr hv)
        (fun he => huv (affine_injective c d hd he))
      rw [gcd_affine_offsets] at heq
      apply Nat.eq_of_mul_eq_mul_left hdabs
      simpa only [Nat.mul_one] using heq
  · rintro ⟨hcard,hroot,hbad,hg⟩
    refine ⟨?_,?_,(not_congr hAP).mpr hbad,?_⟩
    · rw [mapSet_card c d hd]; exact hcard
    · intro hc
      exact hroot ((mem_mapSet c d hd Q 0).mp (by simpa only [affine_zero] using hc))
    · intro u hu v hv huv
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hv
      have hab : a≠b := by intro he; apply huv; rw [he]
      rw [gcd_affine_offsets,hg a ha b hb hab,Nat.mul_one]

theorem gcdStepPairs_map (c d : Int) (hd : 0<d) (S : Finset Int) :
    gcdStepPairs c d (mapSet c d S)=(PrimitiveBadPairs S).image (mapSet c d) := by
  classical
  ext P
  constructor
  · intro hP
    obtain ⟨hsub,hprim⟩ := (mem_gcdStepPairs c d (mapSet c d S) P).mp hP
    obtain ⟨Q,hQ,hmap⟩ := exists_preimage_subset c d S P hsub
    have hunit : IsPrimitiveBadPair Q := (isStepPrimitive_map_iff c d hd Q).mp (by rw [hmap]; exact hprim)
    exact Finset.mem_image.mpr ⟨Q,(mem_primitiveBadPairs S Q).mpr ⟨hQ,hunit⟩,hmap⟩
  · intro hP
    obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hP
    obtain ⟨hsub,hunit⟩ := (mem_primitiveBadPairs S Q).mp hQ
    exact (mem_gcdStepPairs c d (mapSet c d S) (mapSet c d Q)).mpr
      ⟨(mapSet_subset_iff c d hd Q S).mpr hsub,(isStepPrimitive_map_iff c d hd Q).mpr hunit⟩

theorem gcdStepPool_mapFamily (c d : Int) (hd : 0<d) (F : Finset (Finset Int)) :
    gcdStepPool c d (mapFamily c d F)=(PrimitivePool F).image (mapSet c d) := by
  classical
  ext P
  constructor
  · intro hP
    obtain ⟨S,hS,hPS⟩ := Finset.mem_biUnion.mp hP
    obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hS
    rw [gcdStepPairs_map c d hd T] at hPS
    obtain ⟨Q,hQ,hmap⟩ := Finset.mem_image.mp hPS
    exact Finset.mem_image.mpr ⟨Q,Finset.mem_biUnion.mpr ⟨T,hT,hQ⟩,hmap⟩
  · intro hP
    obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hP
    obtain ⟨T,hT,hQT⟩ := Finset.mem_biUnion.mp hQ
    apply Finset.mem_biUnion.mpr
    refine ⟨mapSet c d T,Finset.mem_image.mpr ⟨T,hT,rfl⟩,?_⟩
    rw [gcdStepPairs_map c d hd T]
    exact Finset.mem_image.mpr ⟨Q,hQT,rfl⟩

theorem gcdStepPool_mapFamily_card (c d : Int) (hd : 0<d) (F : Finset (Finset Int)) :
    (gcdStepPool c d (mapFamily c d F)).card=(PrimitivePool F).card := by
  rw [gcdStepPool_mapFamily c d hd F]
  exact Finset.card_image_of_injective _ (mapSet_injective c d hd)

theorem mapped_family_defect_eq (c d : Int) (hd : 0<d) (F : Finset (Finset Int)) :
    ((mapFamily c d F).card:Int)-(gcdStepPool c d (mapFamily c d F)).card=
      (F.card:Int)-(PrimitivePool F).card := by
  rw [mapFamily_card c d hd,gcdStepPool_mapFamily_card c d hd]

theorem exists_normalized_family (c d : Int) (hd : 0<d) (F : Finset (Finset Int))
    (P : Nat → Nat → Prop)
    (hF : ∀ S∈F, ∃ l r : Nat, S=mapSet c d (Window l r) ∧ 4≤S.card ∧ P l r) :
    ∃ U : Finset (Finset Int), mapFamily c d U=F ∧
      ∀ T∈U, ∃ l r : Nat, T=Window l r ∧ 4≤T.card ∧ P l r := by
  classical
  revert hF
  induction F using Finset.induction_on with
  | empty =>
    intro hF
    exact ⟨∅,by simp [mapFamily],by simp⟩
  | @insert S F hnot ih =>
    intro hF
    obtain ⟨l,r,hS,hlarge,hP⟩ := hF S (Finset.mem_insert_self _ _)
    obtain ⟨U,hU,hunit⟩ := ih (fun T hT => hF T (Finset.mem_insert_of_mem hT))
    refine ⟨insert (Window l r) U,?_,?_⟩
    · change (insert (Window l r) U).image (mapSet c d)=insert S F
      rw [Finset.image_insert]
      change insert (mapSet c d (Window l r)) (mapFamily c d U)=insert S F
      rw [←hS,hU]
    · intro T hT
      rcases Finset.mem_insert.mp hT with rfl | hT
      · refine ⟨l,r,rfl,?_,hP⟩
        rw [←mapSet_card c d hd,←hS]
        exact hlarge
      · exact hunit T hT

theorem fixed_step_defect_le_one (c d : Int) (hd : 0<d) (F : Finset (Finset Int))
    (hF : ∀ S∈F, ∃ l r : Nat, S=mapSet c d (Window l r) ∧ 4≤S.card) :
    (F.card:Int)-(gcdStepPool c d F).card≤1 := by
  obtain ⟨U,hU,hunit⟩ := exists_normalized_family c d hd F (fun _ _ => True) (by
    intro S hS
    obtain ⟨l,r,heq,hl⟩ := hF S hS
    exact ⟨l,r,heq,hl,trivial⟩)
  rw [←hU,mapped_family_defect_eq c d hd]
  apply StaircaseComplete29.actual_family_defect_le_one U
  intro T hT
  obtain ⟨l,r,heq,hl,htrue⟩ := hunit T hT
  exact ⟨l,r,heq,hl⟩

theorem fixed_step_left_thin_defect_nonpos (c d : Int) (hd : 0<d) (F : Finset (Finset Int))
    (hF : ∀ S∈F, ∃ l r : Nat, S=mapSet c d (Window l r) ∧ 4≤S.card ∧ l≤1) :
    (F.card:Int)-(gcdStepPool c d F).card≤0 := by
  obtain ⟨U,hU,hunit⟩ := exists_normalized_family c d hd F (fun l _ => l≤1) hF
  rw [←hU,mapped_family_defect_eq c d hd]
  exact StaircaseThin.actual_left_thin_defect_nonpos U hunit

theorem fixed_step_right_thin_defect_nonpos (c d : Int) (hd : 0<d) (F : Finset (Finset Int))
    (hF : ∀ S∈F, ∃ l r : Nat, S=mapSet c d (Window l r) ∧ 4≤S.card ∧ r≤1) :
    (F.card:Int)-(gcdStepPool c d F).card≤0 := by
  obtain ⟨U,hU,hunit⟩ := exists_normalized_family c d hd F (fun _ r => r≤1) hF
  rw [←hU,mapped_family_defect_eq c d hd]
  exact StaircaseThin.actual_right_thin_defect_nonpos U hunit

#print axioms affine_injective
#print axioms affine_strictMono
#print axioms mem_mapSet
#print axioms mapSet_injective
#print axioms mapSet_card
#print axioms mapFamily_card
#print axioms mapSet_insert
#print axioms affine_zero
#print axioms affine_sub
#print axioms mem_gcdStepPairs
#print axioms mem_gcdStepPool
#print axioms affine_APAt
#print axioms affine_isAP
#print axioms affine_isAP_iff
#print axioms mapWindow_APAt
#print axioms actual_AP_representation
#print axioms step_unique
#print axioms mapSet_subset_iff
#print axioms exists_preimage_subset
#print axioms gcd_affine_offsets
#print axioms isStepPrimitive_map_iff
#print axioms gcdStepPairs_map
#print axioms gcdStepPool_mapFamily
#print axioms gcdStepPool_mapFamily_card
#print axioms mapped_family_defect_eq
#print axioms exists_normalized_family
#print axioms fixed_step_defect_le_one
#print axioms fixed_step_left_thin_defect_nonpos
#print axioms fixed_step_right_thin_defect_nonpos
end JSP233.AffineLine30
