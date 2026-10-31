import Erdos272.Arithmetic.LightPrice208

namespace JSP233.LightActualPrice208
open StarCompletion APGeometry NearAP36 LightPhases208
set_option maxHeartbeats 0

theorem actual_closed_credit {N d T E B V : ℕ} {F : Finset (Finset ℤ)}
    (a m e : Finset ℤ → ℕ) (hd : 0<d) (hB : 0<B)
    (hsize : ∀ S ∈ F,T≤S.card) (hTE : E<T) (hTV : T≤V)
    (hoff : ∀ S ∈ F,e S<E) (hcard : ∀ S ∈ F,S.card=m S+e S)
    (hsub : ∀ S ∈ F,Grid (a S) d (m S) ⊆ S)
    (hground : ∀ S ∈ F,S ⊆ Ground N) (hupper : ∀ S ∈ F,S.card≤V) :
    F.card+T*(Heavy N d T E B V F a).card ≤ LightPrice208.Closed N d T E B V+
      (F.filter (fun S=>Label a d B S∈Heavy N d T E B V F a)).card := by
  have hh := LightPhases208.actual_light_credit a m e hd hB hsize hTE hoff hcard hsub hground hupper
  rw [LightPrice208.price_closed hd hB hTE.le hTV] at hh
  exact hh

#print axioms actual_closed_credit
end JSP233.LightActualPrice208
