module

public import Erdos272.Capacity.AnchorCapacity33
public import Erdos272.Capacity.AnchorEuler33
public import Erdos272.Resources.FactorCells34
public import Erdos272.Traces.PureTailCollision35
public import Mathlib.Data.Finset.Sort

@[expose] public section

/-! Native nonprincipal-prefix charging and its actual gcd-cell resource payment.
The prefix and key choices below are constructed from the finite traces. -/
namespace JSP233.AnchorAssembly37
open AnchorCapacity33
open scoped Classical BigOperators
noncomputable section

abbrev Point (n : ℕ) := Fin (n+1) → ℕ

def Prefix (n k : ℕ) : Finset (Fin (n+1)) := Finset.univ.filter (fun i => i.val≤k)

def PrefixFace {n : ℕ} (k : ℕ) (Q : Finset (Point n)) : Finset (Point n) :=
  Face (Prefix n k) Q

def Principal {n : ℕ} (Q : Finset (Point n)) : Prop := ∃ a, Q=Finset.Iic a

theorem mem_prefix {n k : ℕ} {i : Fin (n+1)} : i∈Prefix n k ↔ i.val≤k := by
  classical
  simp [Prefix]

theorem mem_prefixFace {n k : ℕ} {a : Point n} {Q : Finset (Point n)} :
    a∈PrefixFace k Q ↔ a∈Q ∧ ∀ i, i∉Prefix n k → a i=0 := by
  simp only [PrefixFace,Face,Finset.mem_filter]

theorem prefixFace_subset {n k : ℕ} (Q : Finset (Point n)) : PrefixFace k Q⊆Q :=
  fun _ ha => (mem_prefixFace.mp ha).1

theorem prefixFace_full {n : ℕ} (Q : Finset (Point n)) : PrefixFace n Q=Q := by
  classical
  ext a
  simp only [PrefixFace,Face,Finset.mem_filter]
  constructor
  · exact And.left
  · intro ha
    refine ⟨ha,?_⟩
    intro i hi
    exact (hi (mem_prefix.mpr (by omega))).elim

theorem prefixFace_nonempty {n k : ℕ} {Q : Finset (Point n)}
    (hQ : Q.Nonempty) (hd : DownClosed Q) : (PrefixFace k Q).Nonempty := by
  classical
  obtain ⟨a,ha⟩ := hQ
  refine ⟨0,mem_prefixFace.mpr ⟨hd a ha _ (by intro i; exact Nat.zero_le _),?_⟩⟩
  simp

theorem prefixFace_zero_principal {n : ℕ} {Q : Finset (Point n)}
    (hQ : Q.Nonempty) (hd : DownClosed Q) : Principal (PrefixFace 0 Q) := by
  classical
  apply downclosed_joinClosed_principal (prefixFace_nonempty hQ hd)
    (face_downclosed _ hd)
  intro a ha b hb
  have has := (mem_prefixFace.mp ha).2
  have hbs := (mem_prefixFace.mp hb).2
  rcases le_total (a 0) (b 0) with hab | hba
  · have hle : a≤b := by
      intro i
      by_cases hi : i=0
      · subst i; exact hab
      · have hiv : ¬i.val≤0 := by intro hv; exact hi (Fin.ext (by simpa only [Fin.val_zero] using Nat.eq_zero_of_le_zero hv))
        rw [has i (by simpa only [mem_prefix] using hiv)]
        exact Nat.zero_le _
    simpa only [sup_eq_right.mpr hle] using hb
  · have hle : b≤a := by
      intro i
      by_cases hi : i=0
      · subst i; exact hba
      · have hiv : ¬i.val≤0 := by intro hv; exact hi (Fin.ext (by simpa only [Fin.val_zero] using Nat.eq_zero_of_le_zero hv))
        rw [hbs i (by simpa only [mem_prefix] using hiv)]
        exact Nat.zero_le _
    simpa only [sup_eq_left.mpr hle] using ha

theorem exists_first_nonprincipal {n : ℕ} {Q : Finset (Point n)}
    (hQ : Q.Nonempty) (hd : DownClosed Q) (hn : ¬Principal Q) :
    ∃ j : Fin (n+1), 0< j.val ∧ ¬Principal (PrefixFace j.val Q) ∧
      Principal (PrefixFace (j.val-1) Q) := by
  classical
  have hex : ∃ k : ℕ, ¬Principal (PrefixFace k Q) := ⟨n,by simpa [prefixFace_full] using hn⟩
  let k := Nat.find hex
  have hkn : k≤n := Nat.find_min' hex (by simpa [prefixFace_full] using hn)
  have hk0 : 0<k := by
    by_contra he
    have heq : k=0 := by omega
    have hbad := Nat.find_spec hex
    change ¬Principal (PrefixFace k Q) at hbad
    rw [heq] at hbad
    exact hbad (prefixFace_zero_principal hQ hd)
  refine ⟨⟨k,by omega⟩,hk0,Nat.find_spec hex,?_⟩
  exact of_not_not (Nat.find_min hex (by omega : k-1<k))

def First {n : ℕ} (Q : Finset (Point n)) : Fin (n+1) :=
  if h : Q.Nonempty ∧ DownClosed Q ∧ ¬Principal Q then
    Classical.choose (exists_first_nonprincipal h.1 h.2.1 h.2.2) else 0

theorem first_spec {n : ℕ} {Q : Finset (Point n)}
    (hQ : Q.Nonempty) (hd : DownClosed Q) (hn : ¬Principal Q) :
    0 < (First Q).val ∧ ¬Principal (PrefixFace (First Q).val Q) ∧
      Principal (PrefixFace ((First Q).val-1) Q) := by
  classical
  have hh : Q.Nonempty ∧ DownClosed Q ∧ ¬Principal Q := ⟨hQ,hd,hn⟩
  simp only [First,dif_pos hh]
  exact Classical.choose_spec (exists_first_nonprincipal hQ hd hn)

theorem prefixFace_flat {n : ℕ} {j : Fin (n+1)} (hj : 0< j.val)
    (Q : Finset (Point n)) :
    (PrefixFace j.val Q).filter (fun a => a j=0)=PrefixFace (j.val-1) Q := by
  classical
  ext a
  simp only [PrefixFace,Face,Finset.mem_filter]
  constructor
  · rintro ⟨⟨ha,hs⟩,hz⟩
    refine ⟨ha,?_⟩
    intro i hi
    have hil : j.val - 1 < i.val := by simpa only [mem_prefix,not_le] using hi
    by_cases hij : i=j
    · subst i; exact hz
    · apply hs i
      simp only [mem_prefix,not_le]
      have hne : i.val≠j.val := by intro he; exact hij (Fin.ext (by simpa only [Fin.val_zero,Fin.val_mk] using he))
      omega
  · rintro ⟨ha,hs⟩
    refine ⟨⟨ha,?_⟩,hs j ?_⟩
    · intro i hi
      apply hs i
      simp only [mem_prefix,not_le] at hi ⊢
      omega
    · simp only [mem_prefix,not_le]
      omega

theorem actual_later_prefix_key {n : ℕ} {Q : Finset (Point n)}
    (hQ : Q.Nonempty) (hd : DownClosed Q) (hn : ¬Principal Q) :
    ∃ top : Point n, ∃ i : Fin (n+1),
      top∈Q ∧ AnchorEuler33.Highest top=First Q ∧ i.val<(First Q).val ∧
      PrefixWitness (First Q) (PrefixFace (First Q).val Q) top i := by
  classical
  let j := First Q
  have hs := first_spec hQ hd hn
  obtain ⟨a,ha⟩ := hs.2.2
  have hface : (PrefixFace j.val Q).filter (fun x => x j=0)=Finset.Iic a := by
    rw [prefixFace_flat hs.1]
    exact ha
  obtain ⟨top,i,hpos,hw⟩ := prefix_witness_exists j (PrefixFace j.val Q) a
    (face_downclosed _ hd) hface hs.2.1
  have htop := (mem_prefixFace.mp hw.2.1)
  have hi : i.val< j.val := by
    by_contra hh
    have hij : i≠j := hw.1
    have hiv : j.val < i.val := by
      have hne : i.val≠j.val := by intro he; exact hij (Fin.ext (by simpa only [Fin.val_zero,Fin.val_mk] using he))
      omega
    have hin : i∉Prefix n j.val := by simp [mem_prefix]; omega
    have hzero := (mem_prefixFace.mp hw.2.2.1).2 i hin
    simp only [Function.update_of_ne hij,Function.update_self] at hzero
    omega
  have hne : top≠0 := by intro he; subst top; simp at hpos
  have hhigh := AnchorEuler33.highest_spec top hne
  have hle : (AnchorEuler33.Highest top).val≤j.val := by
    by_contra hh
    have hz := htop.2 (AnchorEuler33.Highest top) (by simpa [mem_prefix] using hh)
    omega
  have hge : j.val≤(AnchorEuler33.Highest top).val := by
    by_contra hh
    have hz := hhigh.2 j (by omega)
    omega
  exact ⟨top,i,htop.1,Fin.ext (by omega),hi,hw⟩

theorem two_prefix_hull_join {n : ℕ} {Q : Finset (Point n)}
    (hs : ∀ a∈Q, ∀ i : Fin (n+1), 1 < i.val → a i=0)
    (h1 : 1 < n+1) :
    AxisPoint (0:Fin (n+1)) (Hull Q 0) ⊔
      AxisPoint (⟨1,h1⟩:Fin (n+1)) (Hull Q ⟨1,h1⟩)=Hull Q := by
  classical
  funext i
  by_cases hi0 : i=0
  · subst i; simp [AxisPoint]
  by_cases hi1 : i=(⟨1,h1⟩:Fin (n+1))
  · subst i; simp [AxisPoint]
  · have hi0v : i.val≠0 := by intro he; exact hi0 (Fin.ext (by simpa only [Fin.val_zero,Fin.val_mk] using he))
    have hi1v : i.val≠1 := by intro he; exact hi1 (Fin.ext (by simpa only [Fin.val_zero,Fin.val_mk] using he))
    have hz : Hull Q i=0 := by
      apply Nat.eq_zero_of_le_zero
      exact Finset.sup_le (fun a ha => le_of_eq (hs a ha i (by omega)))
    simp [AxisPoint,hi0,hi1,hz]

theorem two_prefix_hull_comparable {n : ℕ} {Q R : Finset (Point n)}
    (hQ : Q.Nonempty) (hR : R.Nonempty) (hdQ : DownClosed Q) (hdR : DownClosed R)
    (hnQ : ¬Principal Q) (hjoin : JoinClosed (Q∩R))
    (hsQ : ∀ a∈Q, ∀ i : Fin (n+1), 1 < i.val → a i=0)
    (h1 : 1 < n+1) (hle : Hull Q≤Hull R) : False := by
  classical
  have haxis : ∀ i : Fin (n+1), AxisPoint i (Hull Q i)∈Q∩R := by
    intro i
    refine Finset.mem_inter.mpr ⟨axisPoint_mem hQ hdQ i,?_⟩
    apply hdR _ (axisPoint_mem hR hdR i)
    intro k
    by_cases hki : k=i
    · subst k; simpa only [AxisPoint,Function.update_self] using hle i
    · simp [AxisPoint,hki]
  have hh := hjoin _ (haxis 0) _ (haxis ⟨1,h1⟩)
  rw [two_prefix_hull_join hsQ h1] at hh
  exact hull_not_mem hdQ hnQ (Finset.mem_inter.mp hh).1

theorem two_prefix_first_hull_pos {n : ℕ} {Q : Finset (Point n)}
    (hQ : Q.Nonempty) (hd : DownClosed Q) (hn : ¬Principal Q)
    (hs : ∀ a∈Q, ∀ i : Fin (n+1), 1 < i.val → a i=0) (h1 : 1 < n+1) :
    0<Hull Q 0 := by
  classical
  by_contra hh
  have hz : Hull Q 0=0 := by omega
  have hj := two_prefix_hull_join hs h1
  have ha0 : AxisPoint (0:Fin (n+1)) (Hull Q 0)=0 := by simp [AxisPoint,hz]
  rw [ha0,sup_eq_right.mpr (show (0:Point n)≤AxisPoint ⟨1,h1⟩ (Hull Q ⟨1,h1⟩) from fun i => Nat.zero_le _)] at hj
  exact hull_not_mem hd hn (hj ▸ axisPoint_mem hQ hd ⟨1,h1⟩)

theorem first_two_prefix_key_injective {n : ℕ} (F : Finset (Finset (Point n)))
    (hne : ∀ Q∈F, Q.Nonempty) (hd : ∀ Q∈F, DownClosed Q)
    (hn : ∀ Q∈F, ¬Principal Q)
    (hj : ∀ Q∈F, (First Q).val=1)
    (hp : ∀ Q∈F, ∀ R∈F, Q≠R → JoinClosed (Q∩R)) :
    Set.InjOn (fun Q => Hull (PrefixFace 1 Q) (0:Fin (n+1))) (F : Set _) := by
  classical
  intro Q hQ R hR he
  by_contra hQR
  let A := PrefixFace 1 Q
  let B := PrefixFace 1 R
  have h1 : 1 < n+1 := by have hh := (First Q).isLt; rw [hj Q hQ] at hh; exact hh
  have hA := prefixFace_nonempty (k:=1) (hne Q hQ) (hd Q hQ)
  have hB := prefixFace_nonempty (k:=1) (hne R hR) (hd R hR)
  have hdA := face_downclosed (Prefix n 1) (hd Q hQ)
  have hdB := face_downclosed (Prefix n 1) (hd R hR)
  have hnA : ¬Principal A := by simpa [A,hj Q hQ] using (first_spec (hne Q hQ) (hd Q hQ) (hn Q hQ)).2.1
  have hnB : ¬Principal B := by simpa [B,hj R hR] using (first_spec (hne R hR) (hd R hR) (hn R hR)).2.1
  have hsA : ∀ a∈A, ∀ i : Fin (n+1), 1 < i.val → a i=0 := by
    intro a ha i hi; exact (mem_prefixFace.mp ha).2 i (by simp [mem_prefix]; omega)
  have hsB : ∀ a∈B, ∀ i : Fin (n+1), 1 < i.val → a i=0 := by
    intro a ha i hi; exact (mem_prefixFace.mp ha).2 i (by simp [mem_prefix]; omega)
  have hjoin : JoinClosed (A∩B) := by
    intro a ha b hb
    obtain ⟨haQ,haR⟩ := Finset.mem_inter.mp ha
    obtain ⟨hbQ,hbR⟩ := Finset.mem_inter.mp hb
    have hab := hp Q hQ R hR hQR a
      (Finset.mem_inter.mpr ⟨(mem_prefixFace.mp haQ).1,(mem_prefixFace.mp haR).1⟩)
      b (Finset.mem_inter.mpr ⟨(mem_prefixFace.mp hbQ).1,(mem_prefixFace.mp hbR).1⟩)
    have hs : ∀ i, i∉Prefix n 1 → (a⊔b) i=0 := by
      intro i hi
      simp only [Pi.sup_apply,(mem_prefixFace.mp haQ).2 i hi,(mem_prefixFace.mp hbQ).2 i hi,max_self]
    exact Finset.mem_inter.mpr ⟨mem_prefixFace.mpr ⟨(Finset.mem_inter.mp hab).1,hs⟩,
      mem_prefixFace.mpr ⟨(Finset.mem_inter.mp hab).2,hs⟩⟩
  rcases le_total (Hull A ⟨1,h1⟩) (Hull B ⟨1,h1⟩) with hle | hle
  · apply two_prefix_hull_comparable hA hB hdA hdB hnA hjoin hsA h1
    intro i
    by_cases hi0 : i=0
    · subst i; exact le_of_eq he
    by_cases hi1 : i=(⟨1,h1⟩:Fin (n+1))
    · subst i; exact hle
    · have hi0v : i.val≠0 := by intro hh; exact hi0 (Fin.ext (by simpa only [Fin.val_zero] using hh))
      have hi1v : i.val≠1 := by intro hh; exact hi1 (Fin.ext (by simpa only [Fin.val_mk] using hh))
      have hz : Hull A i=0 := Nat.eq_zero_of_le_zero (Finset.sup_le (fun a ha => le_of_eq (hsA a ha i (by omega))))
      rw [hz]; exact Nat.zero_le _
  · apply two_prefix_hull_comparable hB hA hdB hdA hnB (by simpa only [Finset.inter_comm] using hjoin) hsB h1
    intro i
    by_cases hi0 : i=0
    · subst i; exact le_of_eq he.symm
    by_cases hi1 : i=(⟨1,h1⟩:Fin (n+1))
    · subst i; exact hle
    · have hi0v : i.val≠0 := by intro hh; exact hi0 (Fin.ext (by simpa only [Fin.val_zero] using hh))
      have hi1v : i.val≠1 := by intro hh; exact hi1 (Fin.ext (by simpa only [Fin.val_mk] using hh))
      have hz : Hull B i=0 := Nat.eq_zero_of_le_zero (Finset.sup_le (fun a ha => le_of_eq (hsB a ha i (by omega))))
      rw [hz]; exact Nat.zero_le _

def NativeKey {n : ℕ} (Q : Finset (Point n)) : Point n × Fin (n+1) :=
  if (First Q).val=1 then (AxisPoint 0 (Hull (PrefixFace 1 Q) 0),0)
  else if h : Q.Nonempty ∧ DownClosed Q ∧ ¬Principal Q then
    let top := (actual_later_prefix_key h.1 h.2.1 h.2.2).choose
    (top,((actual_later_prefix_key h.1 h.2.1 h.2.2).choose_spec).choose)
  else (0,0)

theorem nativeKey_first {n : ℕ} {Q : Finset (Point n)} (h : (First Q).val=1) :
    NativeKey Q=(AxisPoint 0 (Hull (PrefixFace 1 Q) 0),0) := by
  simp only [NativeKey,if_pos h]

theorem nativeKey_later {n : ℕ} {Q : Finset (Point n)}
    (hQ : Q.Nonempty) (hd : DownClosed Q) (hn : ¬Principal Q)
    (h : (First Q).val≠1) :
    (NativeKey Q).1∈Q ∧ AnchorEuler33.Highest (NativeKey Q).1=First Q ∧
      (NativeKey Q).2.val<(First Q).val ∧
      PrefixWitness (First Q) (PrefixFace (First Q).val Q) (NativeKey Q).1 (NativeKey Q).2 := by
  have hv : Q.Nonempty ∧ DownClosed Q ∧ ¬Principal Q := ⟨hQ,hd,hn⟩
  simpa only [NativeKey,if_neg h,dif_pos hv] using
    ((actual_later_prefix_key hQ hd hn).choose_spec).choose_spec

theorem highest_axis_zero {n : ℕ} {m : ℕ} (hm : 0<m) :
    AnchorEuler33.Highest (AxisPoint (0:Fin (n+1)) m)=0 := by
  have hn : AxisPoint (0:Fin (n+1)) m≠0 := by
    intro he
    have hh := congrFun he 0
    simp [AxisPoint] at hh
    omega
  have hs := AnchorEuler33.highest_spec _ hn
  by_contra he
  have hz : AxisPoint (0:Fin (n+1)) m (AnchorEuler33.Highest (AxisPoint 0 m))=0 := by
    exact Function.update_of_ne he m (0:Point n)
  omega

theorem nativeKey_first_spec {n : ℕ} {Q : Finset (Point n)}
    (hQ : Q.Nonempty) (hd : DownClosed Q) (hn : ¬Principal Q)
    (h : (First Q).val=1) :
    (NativeKey Q).1∈Q ∧ (NativeKey Q).1≠0 ∧
      AnchorEuler33.Highest (NativeKey Q).1=0 ∧ (NativeKey Q).2=0 := by
  let A := PrefixFace 1 Q
  have hA := prefixFace_nonempty (k:=1) hQ hd
  have hdA := face_downclosed (Prefix n 1) hd
  have hnA : ¬Principal A := by simpa [A,h] using (first_spec hQ hd hn).2.1
  have h1 : 1<n+1 := by have hh := (First Q).isLt; rw [h] at hh; exact hh
  have hs : ∀ a∈A, ∀ i : Fin (n+1), 1 < i.val → a i=0 := by
    intro a ha i hi
    exact (mem_prefixFace.mp ha).2 i (by simp [mem_prefix]; omega)
  have hpos := two_prefix_first_hull_pos hA hdA hnA hs h1
  rw [nativeKey_first h]
  refine ⟨prefixFace_subset Q (axisPoint_mem hA hdA 0),?_,highest_axis_zero hpos,rfl⟩
  intro he
  have hh := congrFun he 0
  simp only [AxisPoint,Function.update_self,Pi.zero_apply] at hh
  omega

theorem prefixFace_pair_joinClosed {n k : ℕ} {Q R : Finset (Point n)}
    (hp : JoinClosed (Q∩R)) : JoinClosed (PrefixFace k Q∩PrefixFace k R) := by
  intro a ha b hb
  obtain ⟨haQ,haR⟩ := Finset.mem_inter.mp ha
  obtain ⟨hbQ,hbR⟩ := Finset.mem_inter.mp hb
  have hab := hp a (Finset.mem_inter.mpr ⟨(mem_prefixFace.mp haQ).1,(mem_prefixFace.mp haR).1⟩)
    b (Finset.mem_inter.mpr ⟨(mem_prefixFace.mp hbQ).1,(mem_prefixFace.mp hbR).1⟩)
  have hs : ∀ i, i∉Prefix n k → (a⊔b) i=0 := by
    intro i hi
    simp only [Pi.sup_apply,(mem_prefixFace.mp haQ).2 i hi,(mem_prefixFace.mp hbQ).2 i hi,max_self]
  exact Finset.mem_inter.mpr ⟨mem_prefixFace.mpr ⟨(Finset.mem_inter.mp hab).1,hs⟩,
    mem_prefixFace.mpr ⟨(Finset.mem_inter.mp hab).2,hs⟩⟩

theorem nativeKey_injective {n : ℕ} (F : Finset (Finset (Point n)))
    (hne : ∀ Q∈F, Q.Nonempty) (hd : ∀ Q∈F, DownClosed Q)
    (hn : ∀ Q∈F, ¬Principal Q)
    (hp : ∀ Q∈F, ∀ R∈F, Q≠R → JoinClosed (Q∩R)) :
    Set.InjOn NativeKey (F : Set (Finset (Point n))) := by
  classical
  intro Q hQ R hR he
  by_contra hQR
  have he1 := congrArg Prod.fst he
  have he2 := congrArg Prod.snd he
  by_cases hq : (First Q).val=1
  · have hsQ := nativeKey_first_spec (hne Q hQ) (hd Q hQ) (hn Q hQ) hq
    by_cases hr : (First R).val=1
    · let G := F.filter (fun A => (First A).val=1)
      have hinj := first_two_prefix_key_injective G
        (fun A ha => hne A (Finset.mem_filter.mp ha).1)
        (fun A ha => hd A (Finset.mem_filter.mp ha).1)
        (fun A ha => hn A (Finset.mem_filter.mp ha).1)
        (fun A ha => (Finset.mem_filter.mp ha).2)
        (fun A ha B hb hab => hp A (Finset.mem_filter.mp ha).1 B (Finset.mem_filter.mp hb).1 hab)
      apply hQR
      apply hinj (Finset.mem_filter.mpr ⟨hQ,hq⟩) (Finset.mem_filter.mpr ⟨hR,hr⟩)
      have hh := congrFun he1 0
      simpa only [nativeKey_first hq,nativeKey_first hr,Prod.fst,AxisPoint,Function.update_self] using hh
    · have hsR := nativeKey_later (hne R hR) (hd R hR) (hn R hR) hr
      have hj := (congrArg AnchorEuler33.Highest he1).trans hsR.2.1
      rw [hsQ.2.2.1] at hj
      have hzero := congrArg Fin.val hj
      have hpos := (first_spec (hne R hR) (hd R hR) (hn R hR)).1
      simp only [Fin.val_zero] at hzero
      omega
  · have hsQ := nativeKey_later (hne Q hQ) (hd Q hQ) (hn Q hQ) hq
    by_cases hr : (First R).val=1
    · have hsR := nativeKey_first_spec (hne R hR) (hd R hR) (hn R hR) hr
      have hj := (congrArg AnchorEuler33.Highest he1).symm.trans hsQ.2.1
      rw [hsR.2.2.1] at hj
      have hzero := congrArg Fin.val hj
      have hpos := (first_spec (hne Q hQ) (hd Q hQ) (hn Q hQ)).1
      simp only [Fin.val_zero] at hzero
      omega
    · have hsR := nativeKey_later (hne R hR) (hd R hR) (hn R hR) hr
      have hj : First Q=First R := hsQ.2.1.symm.trans ((congrArg AnchorEuler33.Highest he1).trans hsR.2.1)
      have hwR : PrefixWitness (First Q) (PrefixFace (First Q).val R) (NativeKey Q).1 (NativeKey Q).2 := by
        rw [hj,he1,he2]
        exact hsR.2.2.2
      exact prefix_same_key_impossible (prefixFace_pair_joinClosed (hp Q hQ R hR hQR)) hsQ.2.2.2 hwR

def Allowed {n : ℕ} (j : Fin (n+1)) : Finset (Fin (n+1)) :=
  if j.val=0 then {0} else if 2≤j.val then Finset.Iio j else ∅

def Resources {n : ℕ} (Q : Finset (Point n)) : Finset (Point n × Fin (n+1)) :=
  (Q.erase 0).biUnion (fun a => ({a}:Finset (Point n)).product (Allowed (AnchorEuler33.Highest a)))

theorem allowed_card {n : ℕ} (j : Fin (n+1)) :
    (Allowed j).card=AnchorEuler33.ShellCost j.val := by
  unfold Allowed AnchorEuler33.ShellCost
  by_cases h0 : j.val=0
  · simp [h0]
  by_cases h2 : 2≤j.val
  · have h1 : j.val≠1 := by omega
    simp [h0,h1,h2,Fin.card_Iio]
  · have h1 : j.val=1 := by omega
    simp [h1]

theorem resources_card {n : ℕ} (Q : Finset (Point n)) :
    (Resources Q).card=∑ j : Fin (n+1), (AnchorEuler33.ShellFiber Q j).card*AnchorEuler33.ShellCost j.val := by
  classical
  rw [Resources,Finset.card_biUnion (by
    intro a ha b hb hab
    apply Finset.disjoint_left.mpr
    intro x hxa hxb
    have h1 := Finset.mem_singleton.mp (Finset.mem_product.mp hxa).1
    have h2 := Finset.mem_singleton.mp (Finset.mem_product.mp hxb).1
    exact hab (h1.symm.trans h2))]
  calc
    _=∑ a∈Q.erase 0, AnchorEuler33.ShellCost (AnchorEuler33.Highest a).val := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.product_eq_sprod,Finset.card_product,Finset.card_singleton,one_mul,allowed_card]
    _=_ := AnchorEuler33.shell_fiber_score Q

theorem nativeKey_mem_resources {n : ℕ} {Q R : Finset (Point n)}
    (hR : R.Nonempty) (hd : DownClosed R) (hn : ¬Principal R) (hsub : R⊆Q) :
    NativeKey R∈Resources Q := by
  classical
  by_cases hfirst : (First R).val=1
  · have hs := nativeKey_first_spec hR hd hn hfirst
    apply Finset.mem_biUnion.mpr
    refine ⟨(NativeKey R).1,Finset.mem_erase.mpr ⟨hs.2.1,hsub hs.1⟩,?_⟩
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_singleton.mpr rfl,?_⟩
    simp [Allowed,hs.2.2.1,hs.2.2.2]
  · have hs := nativeKey_later hR hd hn hfirst
    have hj := (first_spec hR hd hn).1
    have h2 : 2≤(First R).val := by omega
    have hne : (NativeKey R).1≠0 := by
      intro he
      have hz : AnchorEuler33.Highest (0:Point n)=0 := by simp [AnchorEuler33.Highest]
      rw [he,hz] at hs
      have hh := congrArg Fin.val hs.2.1
      simp only [Fin.val_zero] at hh
      omega
    apply Finset.mem_biUnion.mpr
    refine ⟨(NativeKey R).1,Finset.mem_erase.mpr ⟨hne,hsub hs.1⟩,?_⟩
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_singleton.mpr rfl,?_⟩
    simp only [Allowed,hs.2.1,if_neg (by omega : (First R).val≠0),if_pos h2,Finset.mem_Iio]
    exact hs.2.2.1

theorem actual_nonprincipal_euler_payment {n : ℕ} (p : Fin (n+1)→ℕ)
    (Q : Finset (Point n)) (F : Finset (Finset (Point n)))
    (hprime : ∀ i, (p i).Prime) (hmono : StrictMono p)
    (hsub : ∀ R∈F, R⊆Q) (hne : ∀ R∈F, R.Nonempty)
    (hdown : ∀ R∈F, DownClosed R) (hnon : ∀ R∈F, ¬Principal R)
    (hpair : ∀ R∈F, ∀ S∈F, R≠S → JoinClosed (R∩S)) :
    2*AnchorEuler33.PotentialScore Q+F.card≤AnchorEuler33.EulerScore p Q := by
  have hmap : F.image NativeKey⊆Resources Q := by
    intro x hx
    obtain ⟨R,hR,rfl⟩ := Finset.mem_image.mp hx
    exact nativeKey_mem_resources (hne R hR) (hdown R hR) (hnon R hR) (hsub R hR)
  have hcard := Finset.card_le_card hmap
  rw [Finset.card_image_of_injOn (nativeKey_injective F hne hdown hnon hpair),resources_card] at hcard
  have hs := AnchorEuler33.actual_euler_shell_budget p Q hprime hmono
  omega

def OrderedPrime (g n : ℕ) (hc : g.primeFactors.card=n+1) : Fin (n+1)≃o↥g.primeFactors :=
  g.primeFactors.orderIsoOfFin hc

def ActualExponent (g n : ℕ) (hc : g.primeFactors.card=n+1) (d : ℕ) : Point n :=
  fun i => FactorCells34.Exponent g d (OrderedPrime g n hc i)

def ActualPrimes (g n : ℕ) (hc : g.primeFactors.card=n+1) : Fin (n+1)→ℕ :=
  fun i => (OrderedPrime g n hc i).val

theorem actualPrimes_prime (g n : ℕ) (hc : g.primeFactors.card=n+1) :
    ∀ i, (ActualPrimes g n hc i).Prime := by
  intro i
  exact Nat.prime_of_mem_primeFactors (OrderedPrime g n hc i).property

theorem actualPrimes_strictMono (g n : ℕ) (hc : g.primeFactors.card=n+1) :
    StrictMono (ActualPrimes g n hc) := by
  intro i j hij
  exact (OrderedPrime g n hc).strictMono hij

theorem actualExponent_injective (g n : ℕ) (hc : g.primeFactors.card=n+1) (hg : 0<g) :
    Set.InjOn (ActualExponent g n hc) (g.divisors : Set ℕ) := by
  intro d hd e he hh
  apply FactorCells34.exponent_injective g hg hd he
  funext p
  obtain ⟨i,rfl⟩ := (OrderedPrime g n hc).surjective p
  exact congrFun hh i

theorem actualExponent_zero_iff (g n d : ℕ) (hc : g.primeFactors.card=n+1)
    (hg : 0<g) (hd : d∈g.divisors) : ActualExponent g n hc d=0 ↔ d=g := by
  constructor
  · intro hh
    apply (FactorCells34.exponent_zero_iff g d hg hd).mp
    funext p
    obtain ⟨i,rfl⟩ := (OrderedPrime g n hc).surjective p
    exact congrFun hh i
  · intro he
    subst d
    unfold ActualExponent
    rw [FactorCells34.exponent_anchor g hg]
    rfl

theorem actualExponent_eulerWeight (g n d : ℕ) (hc : g.primeFactors.card=n+1)
    (hg : 0<g) (hd : d∈g.divisors) :
    AnchorEuler33.EulerWeight (ActualPrimes g n hc) (ActualExponent g n hc d)=Nat.totient (g/d) := by
  rw [FactorCells34.totient_coordinate_weight g d hg hd]
  unfold AnchorEuler33.EulerWeight FactorCells34.CoordinateWeight ActualPrimes ActualExponent
  exact (OrderedPrime g n hc).toEquiv.prod_comp
    (fun p : ↥g.primeFactors => Nat.totient (p.val^FactorCells34.Exponent g d p))

theorem actualExponent_erase (g n : ℕ) (hc : g.primeFactors.card=n+1) (hg : 0<g)
    (A : Finset ℕ) (hA : A⊆g.divisors) :
    (A.erase g).image (ActualExponent g n hc)=(A.image (ActualExponent g n hc)).erase 0 := by
  ext a
  constructor
  · intro ha
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hne,hdA⟩ := Finset.mem_erase.mp hd
    exact Finset.mem_erase.mpr ⟨by
      intro he
      exact hne ((actualExponent_zero_iff g n d hc hg (hA hdA)).mp he),
      Finset.mem_image.mpr ⟨d,hdA,rfl⟩⟩
  · intro ha
    obtain ⟨hne,ha⟩ := Finset.mem_erase.mp ha
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_image.mpr ⟨d,Finset.mem_erase.mpr ⟨by
      intro he
      exact hne ((actualExponent_zero_iff g n d hc hg (hA hd)).mpr he),hd⟩,rfl⟩

theorem actual_gcd_cell_eulerScore (u : ℤ) (g M n : ℕ)
    (hc : g.primeFactors.card=n+1) (hg : 0<g)
    (A : Finset ℕ) (hA : A⊆g.divisors) :
    ((A.erase g).biUnion (DivisorCells34.Cell u g M)).card=
      M*AnchorEuler33.EulerScore (ActualPrimes g n hc) (A.image (ActualExponent g n hc)) := by
  rw [DivisorCells34.selected_proper_cells_card u g M (A.erase g) hg
    ((Finset.erase_subset _ _).trans hA) (Finset.notMem_erase _ _)]
  unfold AnchorEuler33.EulerScore
  rw [←actualExponent_erase g n hc hg A hA,Finset.sum_image]
  · congr 1
    apply Finset.sum_congr rfl
    intro d hd
    exact (actualExponent_eulerWeight g n d hc hg (hA (Finset.mem_erase.mp hd).2)).symm
  · intro d hd e he hde
    exact actualExponent_injective g n hc hg (hA (Finset.mem_erase.mp hd).2)
      (hA (Finset.mem_erase.mp he).2) hde

theorem actual_nonprincipal_gcd_cell_payment (u : ℤ) (g M n : ℕ)
    (hc : g.primeFactors.card=n+1) (hg : 0<g) (hM : 0<M)
    (A : Finset ℕ) (hA : A⊆g.divisors) (F : Finset (Finset (Point n)))
    (hsub : ∀ R∈F, R⊆A.image (ActualExponent g n hc))
    (hne : ∀ R∈F, R.Nonempty) (hdown : ∀ R∈F, DownClosed R)
    (hnon : ∀ R∈F, ¬Principal R)
    (hpair : ∀ R∈F, ∀ S∈F, R≠S → JoinClosed (R∩S)) :
    2*AnchorEuler33.PotentialScore (A.image (ActualExponent g n hc))+F.card≤
      ((A.erase g).biUnion (DivisorCells34.Cell u g M)).card := by
  have hpay := actual_nonprincipal_euler_payment (ActualPrimes g n hc)
    (A.image (ActualExponent g n hc)) F (actualPrimes_prime g n hc)
    (actualPrimes_strictMono g n hc) hsub hne hdown hnon hpair
  rw [actual_gcd_cell_eulerScore u g M n hc hg A hA]
  have hm := Nat.mul_le_mul_right (AnchorEuler33.EulerScore (ActualPrimes g n hc)
    (A.image (ActualExponent g n hc))) (by omega : 1≤M)
  simp only [one_mul] at hm
  exact hpay.trans hm

theorem actual_nonprincipal_member_cell_payment {α : Type*} [DecidableEq α]
    (u : ℤ) (g M n : ℕ) (D : Finset α) (trace : α→Finset (Point n)) (hc : g.primeFactors.card=n+1) (hg : 0<g) (hM : 0<M)
    (A : Finset ℕ) (hA : A⊆g.divisors)
    (hsub : ∀ S∈D, trace S⊆A.image (ActualExponent g n hc))
    (hne : ∀ S∈D, (trace S).Nonempty) (hdown : ∀ S∈D, DownClosed (trace S))
    (hnon : ∀ S∈D, ¬Principal (trace S))
    (hpair : ∀ S∈D, ∀ T∈D, S≠T → JoinClosed (trace S∩trace T)) :
    2*AnchorEuler33.PotentialScore (A.image (ActualExponent g n hc))+D.card≤
      ((A.erase g).biUnion (DivisorCells34.Cell u g M)).card := by
  have hinj := nonprincipal_trace_image_injective D trace hne hdown hnon hpair
  have hf := actual_nonprincipal_gcd_cell_payment u g M n hc hg hM A hA (D.image trace)
    (by intro R hR; obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hR; exact hsub S hS)
    (by intro R hR; obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hR; exact hne S hS)
    (by intro R hR; obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hR; exact hdown S hS)
    (by intro R hR; obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hR; exact hnon S hS)
    (by
      intro R hR U hU hRU
      obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hR
      obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hU
      exact hpair S hS T hT (by intro he; subst T; exact hRU rfl))
  rwa [Finset.card_image_of_injOn hinj] at hf

theorem actualExponent_tailMultiplicity (g n d : ℕ) (hc : g.primeFactors.card=n+1) :
    AnchorEuler33.TailMultiplicity (ActualExponent g n hc d)=
      ∏ p∈(Finset.univ.erase (OrderedPrime g n hc 0)), (FactorCells34.Exponent g d p+1) := by
  classical
  have hi := Finset.mul_prod_erase Finset.univ
    (fun i : Fin (n+1) => ActualExponent g n hc d i+1) (Finset.mem_univ 0)
  have hp := Finset.mul_prod_erase Finset.univ
    (fun p : ↥g.primeFactors => FactorCells34.Exponent g d p+1)
    (Finset.mem_univ (OrderedPrime g n hc 0))
  have hall := (OrderedPrime g n hc).toEquiv.prod_comp
    (fun p : ↥g.primeFactors => FactorCells34.Exponent g d p+1)
  change (ActualExponent g n hc d 0+1)*AnchorEuler33.TailMultiplicity (ActualExponent g n hc d)=_ at hi
  change (ActualExponent g n hc d 0+1)*(∏ p∈Finset.univ.erase (OrderedPrime g n hc 0),
    (FactorCells34.Exponent g d p+1))=_ at hp
  change (∏ i : Fin (n+1), (ActualExponent g n hc d i+1))=_ at hall
  rw [hall] at hi
  exact Nat.eq_of_mul_eq_mul_left (by omega : 0<ActualExponent g n hc d 0+1) (hi.trans hp.symm)

theorem actual_potentialScore (g n : ℕ) (hc : g.primeFactors.card=n+1)
    (hg : 0<g) (A : Finset ℕ) (hA : A⊆g.divisors) :
    AnchorCapacity33.PotentialScore (OrderedPrime g n hc 0) (A.image (FactorCells34.Exponent g))=
      AnchorEuler33.PotentialScore (A.image (ActualExponent g n hc)) := by
  classical
  unfold AnchorCapacity33.PotentialScore AnchorEuler33.PotentialScore
  rw [Finset.sum_image,Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro d hd
    rw [actualExponent_tailMultiplicity]
  · intro d hd e he hde
    exact actualExponent_injective g n hc hg (hA hd) (hA he) hde
  · intro d hd e he hde
    exact FactorCells34.exponent_injective g hg (hA hd) (hA he) hde

theorem actual_mixed_tail_cell_payment (u v : ℤ) (g M n : ℕ)
    (hc : g.primeFactors.card=n+1) (hg : 0<g) (hM : 0<M)
    (hspan : u+(g:ℤ)≤v) (hvg : (g:ℤ)∣v-u)
    (P : Finset (Finset ℤ)) (step : Finset ℤ→ℕ)
    (hpure : ∀ S∈P, TailSelection34.PureTrace u v (g:ℤ) (step S:ℤ) S)
    (hbad : ∀ S∈P, ¬StarCompletion.IsAP S)
    (hpairs : ∀ S∈P, ∀ T∈P, S≠T → StarCompletion.IsAP (S∩T))
    (A : Finset ℕ) (hA : A⊆g.divisors) (hsteps : ∀ S∈P, step S∈A)
    (F : Finset (Finset (Point n)))
    (hsub : ∀ R∈F, R⊆A.image (ActualExponent g n hc))
    (hne : ∀ R∈F, R.Nonempty) (hdown : ∀ R∈F, DownClosed R)
    (hnon : ∀ R∈F, ¬Principal R)
    (hpair : ∀ R∈F, ∀ S∈F, R≠S → JoinClosed (R∩S)) :
    ∃ tail : Finset ℤ→ℤ, TailSelection34.TailChoice P (fun S => (step S:ℤ)) u v tail ∧
      P.card-(P.image tail).card+F.card≤((A.erase g).biUnion (DivisorCells34.Cell u g M)).card := by
  obtain ⟨tail,hchoice,hcost⟩ := PureTailCollision35.actual_pure_net_collision_bound P step u v g
    hg hspan hvg hpure hbad hpairs (OrderedPrime g n hc 0) (A.image (FactorCells34.Exponent g))
    (by intro S hS; exact Finset.mem_image.mpr ⟨step S,hsteps S hS,rfl⟩)
  rw [actual_potentialScore g n hc hg A hA] at hcost
  have hpay := actual_nonprincipal_gcd_cell_payment u g M n hc hg hM A hA F
    hsub hne hdown hnon hpair
  exact ⟨tail,hchoice,by omega⟩

theorem actual_mixed_union_capacity (u : ℤ) (g M n : ℕ)
    (hc : g.primeFactors.card=n+1) (hg : 0<g) (hM : 0<M)
    (P D : Finset (Finset ℤ)) (step : Finset ℤ→ℕ) (trace : Finset ℤ→Finset (Point n))
    (hpure : ∀ S∈P, TailSelection34.PureTrace u (u+((g*M:ℕ):ℤ)) (g:ℤ) (step S:ℤ) S)
    (hbad : ∀ S∈P, ¬StarCompletion.IsAP S)
    (hpairs : ∀ S∈P, ∀ T∈P, S≠T → StarCompletion.IsAP (S∩T))
    (A : Finset ℕ) (hA : A⊆g.divisors) (hsteps : ∀ S∈P, step S∈A)
    (hsub : ∀ S∈D, trace S⊆A.image (ActualExponent g n hc))
    (hne : ∀ S∈D, (trace S).Nonempty) (hdown : ∀ S∈D, DownClosed (trace S))
    (hnon : ∀ S∈D, ¬Principal (trace S))
    (hpair : ∀ S∈D, ∀ T∈D, S≠T → JoinClosed (trace S∩trace T))
    (hcell : (A.erase g).biUnion (DivisorCells34.Cell u g M)⊆(P∪D).biUnion id)
    (hanchor : AnchorTrace u (u+((g*M:ℕ):ℤ)) (g:ℤ)⊆(P∪D).biUnion id) :
    P.card+D.card+(M+1)≤((P∪D).biUnion id).card := by
  classical
  let v := u+((g*M:ℕ):ℤ)
  let U := (P∪D).biUnion id
  let I := (A.erase g).biUnion (DivisorCells34.Cell u g M)
  let K := AnchorTrace u v (g:ℤ)
  have hspan : u+(g:ℤ)≤v := by
    dsimp [v]
    have hh : g≤g*M := by simpa only [mul_one] using Nat.mul_le_mul_left g (by omega : 1≤M)
    have hhZ : (g:ℤ)≤(g:ℤ)*(M:ℤ) := by exact_mod_cast hh
    omega
  have hvg : (g:ℤ)∣v-u := by
    dsimp [v]
    refine ⟨(M:ℤ),?_⟩
    simp
  obtain ⟨tail,ht,hcost⟩ := PureTailCollision35.actual_pure_net_collision_bound P step u v g
    hg hspan hvg hpure hbad hpairs (OrderedPrime g n hc 0) (A.image (FactorCells34.Exponent g))
    (by intro S hS; exact Finset.mem_image.mpr ⟨step S,hsteps S hS,rfl⟩)
  rw [actual_potentialScore g n hc hg A hA] at hcost
  have hpay := actual_nonprincipal_member_cell_payment u g M n D trace hc hg hM A hA
    hsub hne hdown hnon hpair
  have hIK : Disjoint I K := by
    apply Finset.disjoint_left.mpr
    intro x hxI hxK
    obtain ⟨d,hd,hxd⟩ := Finset.mem_biUnion.mp hxI
    have hxg : x∈DivisorCells34.Cell u g M g := by
      rw [DivisorCells34.cell_anchor_eq_trace]
      exact hxK
    exact Finset.disjoint_left.mp (DivisorCells34.cells_disjoint u g M d g
      (Finset.mem_erase.mp hd).1) hxd hxg
  have hinterval : K∪I⊆Finset.Icc u v := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxK | hxI
    · exact (Finset.mem_filter.mp hxK).1
    · obtain ⟨d,hd,hxd⟩ := Finset.mem_biUnion.mp hxI
      exact (Finset.mem_filter.mp hxd).1
  have hdis : Disjoint (K∪I) (P.image tail) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hy
    exact (ht S hS).2.1 (hinterval hx)
  have htail : P.image tail⊆U := by
    intro x hx
    obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_biUnion.mpr ⟨S,Finset.mem_union.mpr (Or.inl hS),(ht S hS).1⟩
  have hresource : (K∪I)∪P.image tail⊆U :=
    Finset.union_subset (Finset.union_subset hanchor hcell) htail
  have hcard := Finset.card_le_card hresource
  rw [Finset.card_union_of_disjoint hdis,Finset.card_union_of_disjoint hIK.symm] at hcard
  have hK : K.card=M+1 := DivisorCells34.anchor_trace_card u g M hg
  have himage := Finset.card_image_le (s:=P) (f:=tail)
  change P.card-(P.image tail).card≤2*AnchorEuler33.PotentialScore (A.image (ActualExponent g n hc)) at hcost
  change 2*AnchorEuler33.PotentialScore (A.image (ActualExponent g n hc))+D.card≤I.card at hpay
  change P.card+D.card+(M+1)≤U.card
  omega

#print axioms mem_prefix
#print axioms mem_prefixFace
#print axioms prefixFace_subset
#print axioms prefixFace_full
#print axioms prefixFace_nonempty
#print axioms prefixFace_zero_principal
#print axioms exists_first_nonprincipal
#print axioms first_spec
#print axioms prefixFace_flat
#print axioms actual_later_prefix_key
#print axioms two_prefix_hull_join
#print axioms two_prefix_hull_comparable
#print axioms two_prefix_first_hull_pos
#print axioms first_two_prefix_key_injective
#print axioms nativeKey_first
#print axioms nativeKey_later
#print axioms highest_axis_zero
#print axioms nativeKey_first_spec
#print axioms prefixFace_pair_joinClosed
#print axioms nativeKey_injective
#print axioms allowed_card
#print axioms resources_card
#print axioms nativeKey_mem_resources
#print axioms actual_nonprincipal_euler_payment
#print axioms actualPrimes_prime
#print axioms actualPrimes_strictMono
#print axioms actualExponent_injective
#print axioms actualExponent_zero_iff
#print axioms actualExponent_eulerWeight
#print axioms actualExponent_erase
#print axioms actual_gcd_cell_eulerScore
#print axioms actual_nonprincipal_gcd_cell_payment
#print axioms actual_nonprincipal_member_cell_payment
#print axioms actualExponent_tailMultiplicity
#print axioms actual_potentialScore
#print axioms actual_mixed_tail_cell_payment
#print axioms actual_mixed_union_capacity
end
end JSP233.AnchorAssembly37





