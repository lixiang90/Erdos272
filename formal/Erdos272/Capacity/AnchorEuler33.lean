module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-! Actual Euler-factor shell payment for arbitrary finite dimension.
The arithmetic weights are Mathlib's Nat.totient, not an assumed weight bound. -/
namespace JSP233.AnchorEuler33
open scoped BigOperators Classical
noncomputable section

theorem totient_prime_power_pos (p a : ℕ) (hp : p.Prime) :
    1≤Nat.totient (p^a) := by
  exact Nat.succ_le_of_lt (Nat.totient_pos.mpr (pow_pos hp.pos a))

theorem totient_prime_power_step (p a : ℕ) (hp : p.Prime) :
    Nat.totient (p^(a+2))=p*Nat.totient (p^(a+1)) := by
  rw [show a+2=(a+1)+1 by omega,Nat.totient_prime_pow_succ hp,
    Nat.totient_prime_pow_succ hp,pow_succ]
  ring

theorem totient_odd_prime_power_twice (p a : ℕ) (hp : p.Prime) (hp3 : 3≤p) :
    2*(a+1)≤Nat.totient (p^(a+1)) := by
  induction a with
  | zero => simpa only [zero_add,pow_one,Nat.totient_prime hp] using (show 2≤p-1 by omega)
  | succ a ih =>
    rw [show a+1+1=a+2 by omega,totient_prime_power_step p a hp]
    have hm := Nat.mul_le_mul_right (Nat.totient (p^(a+1))) hp3
    nlinarith

theorem totient_odd_prime_power_linear (p a : ℕ) (hp : p.Prime) (hp3 : 3≤p) :
    a+1≤Nat.totient (p^a) := by
  cases a with
  | zero => simp
  | succ a =>
    have hh := totient_odd_prime_power_twice p a hp hp3
    omega

theorem totient_later_prime_power_gap (p a : ℕ) (hp : p.Prime) (hp5 : 5≤p) :
    2*(a+2)+(p-5)≤Nat.totient (p^(a+1)) := by
  induction a with
  | zero =>
    simp only [zero_add,pow_one,Nat.totient_prime hp]
    omega
  | succ a ih =>
    rw [show a+1+1=a+2 by omega,totient_prime_power_step p a hp]
    have hm := Nat.mul_le_mul_right (Nat.totient (p^(a+1))) hp5
    nlinarith

theorem sorted_prime_coordinate_lower (n : ℕ) (p : Fin (n+1)→ℕ)
    (hp : ∀ i, (p i).Prime) (hmono : StrictMono p)
    (j : Fin (n+1)) (hj : 0<j.val) : 2*j.val+1≤p j := by
  have hrec : ∀ m, ∀ hm : m<n+1,
      m=0 ∨ 2*m+1≤p ⟨m,hm⟩ := by
    intro m
    induction m with
    | zero => intro hm; exact Or.inl rfl
    | succ m ih =>
      intro hm
      have hm0 : m<n+1 := by omega
      have hlt : p ⟨m,hm0⟩<p ⟨m+1,hm⟩ :=
        hmono (show (⟨m,hm0⟩:Fin (n+1))<⟨m+1,hm⟩ by exact Nat.lt_succ_self m)
      apply Or.inr
      by_cases hz : m=0
      · have hh := (hp ⟨m,hm0⟩).two_le
        omega
      · have hprev : 2*m+1≤p ⟨m,hm0⟩ := (ih hm0).resolve_left hz
        have h3 : 3≤p ⟨m,hm0⟩ := by omega
        have h3' : 3≤p ⟨m+1,hm⟩ := by omega
        have hodd : p ⟨m,hm0⟩%2=1 := by
          rcases (hp ⟨m,hm0⟩).eq_two_or_odd with he | he
          · omega
          · exact he
        have hodd' : p ⟨m+1,hm⟩%2=1 := by
          rcases (hp ⟨m+1,hm⟩).eq_two_or_odd with he | he
          · omega
          · exact he
        omega
  exact (hrec j.val j.isLt).resolve_left (by omega)

def EulerWeight {n : ℕ} (p a : Fin (n+1)→ℕ) : ℕ :=
  ∏ i, Nat.totient (p i^a i)

def TailMultiplicity {n : ℕ} (a : Fin (n+1)→ℕ) : ℕ :=
  ∏ i∈(Finset.univ.erase (0:Fin (n+1))), (a i+1)

def ShellCost (j : ℕ) : ℕ := if j=0 then 1 else if j=1 then 0 else j

theorem tailMultiplicity_pos {n : ℕ} (a : Fin (n+1)→ℕ) :
    1≤TailMultiplicity a := by
  change 1≤∏ i∈(Finset.univ.erase (0:Fin (n+1))), (a i+1)
  apply Finset.one_le_prod
  intro i hi
  omega

theorem eulerWeight_pos {n : ℕ} (p a : Fin (n+1)→ℕ)
    (hp : ∀ i, (p i).Prime) : 1≤EulerWeight p a := by
  apply Finset.one_le_prod
  intro i hi
  exact totient_prime_power_pos (p i) (a i) (hp i)

theorem eulerWeight_factor_lower {n : ℕ} (p a : Fin (n+1)→ℕ)
    (hp : ∀ i, (p i).Prime)
    (hodd : ∀ i, 0 < i.val → 3≤p i)
    (j : Fin (n+1)) (hj : j≠0) :
    (∏ i∈((Finset.univ.erase (0:Fin (n+1))).erase j), (a i+1))
      *Nat.totient (p j^a j)≤EulerWeight p a := by
  let C := Finset.univ.erase (0:Fin (n+1))
  have hjC : j∈C := Finset.mem_erase.mpr ⟨hj,Finset.mem_univ j⟩
  have hprod : (∏ i∈C.erase j,(a i+1))≤
      ∏ i∈C.erase j,Nat.totient (p i^a i) := by
    apply Finset.prod_le_prod
    intro i hi
    have hi0 : i≠0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
    have hiv : 0 < i.val := by
      have hnv : i.val≠0 := by intro he; exact hi0 (Fin.ext he)
      omega
    exact totient_odd_prime_power_linear (p i) (a i) (hp i) (hodd i hiv)
  have hm := Nat.mul_le_mul_right (Nat.totient (p j^a j)) hprod
  rw [Finset.prod_erase_mul C (fun i => Nat.totient (p i^a i)) hjC] at hm
  have hf := totient_prime_power_pos (p (0:Fin (n+1))) (a 0) (hp 0)
  have hsplit := Finset.mul_prod_erase Finset.univ
    (fun i => Nat.totient (p i^a i)) (Finset.mem_univ (0:Fin (n+1)))
  change Nat.totient (p 0^a 0)*(∏ i∈C,Nat.totient (p i^a i))=EulerWeight p a at hsplit
  change (∏ i∈C.erase j,(a i+1))*Nat.totient (p j^a j)≤EulerWeight p a
  nlinarith

theorem eulerWeight_later_shell {n : ℕ} (p a : Fin (n+1)→ℕ)
    (hp : ∀ i, (p i).Prime) (hmono : StrictMono p)
    (j : Fin (n+1)) (hj : 2≤j.val) (haj : 0<a j) :
    2*(TailMultiplicity a-1)+j.val≤EulerWeight p a := by
  have hodd : ∀ i : Fin (n+1), 0 < i.val → 3≤p i := by
    intro i hi
    have hh := sorted_prime_coordinate_lower n p hp hmono i hi
    omega
  have hj0 : j≠0 := by intro he; subst j; simp at hj
  let U := ∏ i∈((Finset.univ.erase (0:Fin (n+1))).erase j), (a i+1)
  have hU : 1≤U := by
    dsimp [U]
    apply Finset.one_le_prod
    intro i hi
    omega
  have hw := eulerWeight_factor_lower p a hp hodd j hj0
  change U*Nat.totient (p j^a j)≤EulerWeight p a at hw
  have hT : TailMultiplicity a=U*(a j+1) := by
    dsimp [TailMultiplicity,U]
    exact (Finset.prod_erase_mul (Finset.univ.erase (0:Fin (n+1)))
      (fun i => a i+1) (Finset.mem_erase.mpr ⟨hj0,Finset.mem_univ j⟩)).symm
  have hplow := sorted_prime_coordinate_lower n p hp hmono j (by omega)
  have hp5 : 5≤p j := by omega
  obtain ⟨z,hz⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a j≠0)
  change a j=z+1 at hz
  have hgap := totient_later_prime_power_gap (p j) z (hp j) hp5
  rw [hz] at hw hT
  have hm := Nat.mul_le_mul_left U hgap
  have hsub : TailMultiplicity a-1+1=TailMultiplicity a := by
    have := tailMultiplicity_pos a
    omega
  have hcost : j.val≤p j-5+2 := by omega
  have hu := Nat.mul_le_mul_right (p j-5) hU
  nlinarith

theorem eulerWeight_shell_point {n : ℕ} (p a : Fin (n+1)→ℕ)
    (hp : ∀ i, (p i).Prime) (hmono : StrictMono p)
    (j : Fin (n+1)) (haj : 0<a j)
    (htop : ∀ i, j.val < i.val → a i=0) :
    2*(TailMultiplicity a-1)+ShellCost j.val≤EulerWeight p a := by
  by_cases hj0 : j.val=0
  · have hT : TailMultiplicity a=1 := by
      unfold TailMultiplicity
      apply Finset.prod_eq_one
      intro i hi
      have hi0 : i≠0 := (Finset.mem_erase.mp hi).1
      have hiv : 0 < i.val := by
        have hnv : i.val≠0 := by intro he; exact hi0 (Fin.ext he)
        omega
      simp [htop i (by omega)]
    simp only [hT,Nat.sub_self,mul_zero,zero_add,ShellCost,hj0,ite_true]
    exact eulerWeight_pos p a hp
  by_cases hj1 : j.val=1
  · have hjne : j≠0 := by intro he; subst j; simp at hj1
    have hjC : j∈Finset.univ.erase (0:Fin (n+1)) :=
      Finset.mem_erase.mpr ⟨hjne,Finset.mem_univ j⟩
    have hT : TailMultiplicity a=a j+1 := by
      unfold TailMultiplicity
      apply Finset.prod_eq_single j
      · intro i hi hne
        have hi0 : i≠0 := (Finset.mem_erase.mp hi).1
        have hiv : j.val < i.val := by
          have hij : i.val≠j.val := by intro he; exact hne (Fin.ext he)
          have hi0v : i.val≠0 := by intro he; exact hi0 (Fin.ext he)
          omega
        simp [htop i hiv]
      · intro hnot
        exact (hnot hjC).elim
    have hodd : ∀ i : Fin (n+1), 0 < i.val → 3≤p i := by
      intro i hi
      have hh := sorted_prime_coordinate_lower n p hp hmono i hi
      omega
    have hw := eulerWeight_factor_lower p a hp hodd j hjne
    have hU : 1≤∏ i∈((Finset.univ.erase (0:Fin (n+1))).erase j), (a i+1) := by
      apply Finset.one_le_prod
      intro i hi
      omega
    have hm := Nat.mul_le_mul_right (Nat.totient (p j^a j)) hU
    obtain ⟨z,hz⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a j≠0)
    change a j=z+1 at hz
    have hh := totient_odd_prime_power_twice (p j) z (hp j) (hodd j (by omega))
    rw [←hz] at hh
    have hphiU : Nat.totient (p j^a j)≤
        (∏ i∈((Finset.univ.erase (0:Fin (n+1))).erase j), (a i+1))
          *Nat.totient (p j^a j) := by simpa only [one_mul] using hm
    have hphi : Nat.totient (p j^a j)≤EulerWeight p a := hphiU.trans hw
    simpa [hT,ShellCost,hj1] using hh.trans hphi
  · have hh := eulerWeight_later_shell p a hp hmono j (by omega) haj
    simpa only [ShellCost,hj0,ite_false,hj1] using hh

theorem exists_highest_coordinate {n : ℕ} (a : Fin (n+1)→ℕ) (hne : a≠0) :
    ∃ j, 0<a j ∧ ∀ i, j.val < i.val → a i=0 := by
  let I := Finset.univ.filter (fun i => 0<a i)
  have hI : I.Nonempty := by
    by_contra hnone
    apply hne
    funext i
    change a i=0
    have hnot : ¬0<a i := by
      intro hi
      exact hnone ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩⟩
    omega
  refine ⟨I.max' hI,(Finset.mem_filter.mp (Finset.max'_mem I hI)).2,?_⟩
  intro i hi
  by_contra hz
  have hipos : 0<a i := by omega
  have himem : i∈I := Finset.mem_filter.mpr ⟨Finset.mem_univ i,hipos⟩
  have hle : i≤I.max' hI := Finset.le_max' I i himem
  have hlev : i.val≤(I.max' hI).val := hle
  omega

def Highest {n : ℕ} (a : Fin (n+1)→ℕ) : Fin (n+1) :=
  if h : a≠0 then Classical.choose (exists_highest_coordinate a h) else 0

theorem highest_spec {n : ℕ} (a : Fin (n+1)→ℕ) (hne : a≠0) :
    0<a (Highest a) ∧ ∀ i, (Highest a).val < i.val → a i=0 := by
  simp only [Highest,dif_pos hne]
  exact Classical.choose_spec (exists_highest_coordinate a hne)

def PotentialScore {n : ℕ} (Q : Finset (Fin (n+1)→ℕ)) : ℕ :=
  ∑ a∈Q, (TailMultiplicity a-1)

def EulerScore {n : ℕ} (p : Fin (n+1)→ℕ) (Q : Finset (Fin (n+1)→ℕ)) : ℕ :=
  ∑ a∈Q.erase 0, EulerWeight p a

def ShellFiber {n : ℕ} (Q : Finset (Fin (n+1)→ℕ)) (j : Fin (n+1)) :
    Finset (Fin (n+1)→ℕ) := (Q.erase 0).filter (fun a => Highest a=j)

theorem tailMultiplicity_zero (n : ℕ) :
    TailMultiplicity (0:Fin (n+1)→ℕ)=1 := by
  simp [TailMultiplicity]

theorem potentialScore_erase_zero {n : ℕ} (Q : Finset (Fin (n+1)→ℕ)) :
    (∑ a∈Q.erase 0, (TailMultiplicity a-1))=PotentialScore Q := by
  by_cases hz : (0:Fin (n+1)→ℕ)∈Q
  · have hh := Finset.sum_erase_add Q (fun a => TailMultiplicity a-1) hz
    simpa only [tailMultiplicity_zero,Nat.sub_self,add_zero,PotentialScore] using hh
  · rw [Finset.erase_eq_of_notMem hz]
    rfl

theorem shell_fiber_score {n : ℕ} (Q : Finset (Fin (n+1)→ℕ)) :
    (∑ a∈Q.erase 0, ShellCost (Highest a).val)=
      ∑ j : Fin (n+1), (ShellFiber Q j).card*ShellCost j.val := by
  have hh := Finset.sum_fiberwise' (Q.erase 0) Highest
    (fun j : Fin (n+1) => ShellCost j.val)
  simpa only [ShellFiber,Finset.sum_const,nsmul_eq_mul,Nat.cast_id] using hh.symm

theorem actual_euler_shell_budget {n : ℕ} (p : Fin (n+1)→ℕ)
    (Q : Finset (Fin (n+1)→ℕ)) (hp : ∀ i, (p i).Prime) (hmono : StrictMono p) :
    2*PotentialScore Q+
      (∑ j : Fin (n+1), (ShellFiber Q j).card*ShellCost j.val)≤EulerScore p Q := by
  have hh := Finset.sum_le_sum (s:=Q.erase 0) (fun a ha => by
    have hne : a≠0 := (Finset.mem_erase.mp ha).1
    have hs := highest_spec a hne
    exact eulerWeight_shell_point p a hp hmono (Highest a) hs.1 hs.2)
  rw [Finset.sum_add_distrib,←Finset.mul_sum,potentialScore_erase_zero,
    shell_fiber_score] at hh
  exact hh

theorem shell_demand_bound {n : ℕ} (Q : Finset (Fin (n+1)→ℕ))
    (f₂ : ℕ) (f : Fin (n+1)→ℕ)
    (hfirst : f₂≤(ShellFiber Q 0).card)
    (hlater : ∀ j, 2≤j.val → f j≤j.val*(ShellFiber Q j).card) :
    f₂+(∑ j∈Finset.univ.filter (fun j : Fin (n+1) => 2≤j.val), f j)≤
      ∑ j : Fin (n+1), (ShellFiber Q j).card*ShellCost j.val := by
  let demand := fun j : Fin (n+1) => if j=0 then f₂ else if 2≤j.val then f j else 0
  have hpoint : ∀ j : Fin (n+1), demand j≤(ShellFiber Q j).card*ShellCost j.val := by
    intro j
    by_cases hj0 : j=0
    · subst j
      simpa [demand,ShellCost] using hfirst
    by_cases hj2 : 2≤j.val
    · have hjv0 : j.val≠0 := by intro he; exact hj0 (Fin.ext he)
      have hjv1 : j.val≠1 := by omega
      simpa [demand,hj0,hj2,ShellCost,hjv0,hjv1,Nat.mul_comm] using hlater j hj2
    · simp [demand,hj0,hj2]
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun j hj => hpoint j)
  have hsplit : ∀ j : Fin (n+1), demand j=
      (if j=0 then f₂ else 0)+(if 2≤j.val then f j else 0) := by
    intro j
    by_cases hj0 : j=0
    · subst j; simp [demand]
    · simp [demand,hj0]
  simp_rw [hsplit] at hh
  rw [Finset.sum_add_distrib] at hh
  simpa only [Finset.sum_ite_eq',Finset.mem_univ,ite_true,←Finset.sum_filter] using hh

theorem actual_euler_mixed_payment {n : ℕ} (p : Fin (n+1)→ℕ)
    (Q : Finset (Fin (n+1)→ℕ)) (hp : ∀ i, (p i).Prime) (hmono : StrictMono p)
    (f₂ : ℕ) (f : Fin (n+1)→ℕ)
    (hfirst : f₂≤(ShellFiber Q 0).card)
    (hlater : ∀ j, 2≤j.val → f j≤j.val*(ShellFiber Q j).card) :
    2*PotentialScore Q+f₂+
      (∑ j∈Finset.univ.filter (fun j : Fin (n+1) => 2≤j.val), f j)≤EulerScore p Q := by
  have hs := actual_euler_shell_budget p Q hp hmono
  have hd := shell_demand_bound Q f₂ f hfirst hlater
  omega

#print axioms totient_prime_power_pos
#print axioms totient_prime_power_step
#print axioms totient_odd_prime_power_twice
#print axioms totient_odd_prime_power_linear
#print axioms totient_later_prime_power_gap
#print axioms sorted_prime_coordinate_lower
#print axioms tailMultiplicity_pos
#print axioms eulerWeight_pos
#print axioms eulerWeight_factor_lower
#print axioms eulerWeight_later_shell
#print axioms eulerWeight_shell_point
#print axioms exists_highest_coordinate
#print axioms highest_spec
#print axioms tailMultiplicity_zero
#print axioms potentialScore_erase_zero
#print axioms shell_fiber_score
#print axioms actual_euler_shell_budget
#print axioms shell_demand_bound
#print axioms actual_euler_mixed_payment
end
end JSP233.AnchorEuler33
