module

public import Erdos272.Arithmetic.N20258.IndividualFloors20258
public import Erdos272.Global.N20258.PopulationBands20258

@[expose] public section
namespace JSP233.PopulationSources20258
open PopulationBands20258 PopulationFloors20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

def source029 : Source :=
  ⟨⟨50,152,27,7000,1,[
    (.marks 50 1 152 false,550),
    (.marks 50 1 50 false,5),
    (.marks 50 1 58 false,55),
    (.marks 50 1 66 false,37),
    (.marks 50 1 74 false,19),
    (.marks 50 1 82 false,82),
    (.marks 50 1 90 false,28),
    (.marks 50 1 98 false,51),
    (.marks 50 1 106 false,106),
    (.marks 50 1 114 false,30),
    (.marks 50 1 122 false,507),
    (.marks 50 1 130 false,640),
    (.marks 50 1 138 false,660),
    (.marks 50 1 146 false,638),
    (.marks 50 2 50 false,9),
    (.marks 50 2 58 false,15),
    (.marks 50 2 66 false,15),
    (.marks 50 2 74 false,26),
    (.marks 50 2 82 false,16),
    (.marks 50 2 90 false,28),
    (.marks 50 2 98 false,45),
    (.marks 50 2 106 false,414),
    (.marks 50 2 114 false,502),
    (.marks 50 2 122 false,49),
    (.marks 50 3 58 false,6),
    (.marks 50 3 66 false,9),
    (.marks 50 3 74 false,12),
    (.marks 50 3 82 false,7),
    (.marks 50 3 90 false,162),
    (.marks 50 3 98 false,348),
    (.marks 50 4 50 false,1),
    (.marks 50 4 58 false,8),
    (.marks 50 4 66 false,8),
    (.marks 50 4 74 false,8),
    (.marks 50 4 82 false,111),
    (.marks 50 4 90 false,184),
    (.marks 50 5 58 false,3),
    (.marks 50 5 66 false,4),
    (.marks 50 5 74 false,16),
    (.marks 50 5 82 false,182),
    (.marks 50 6 50 false,16),
    (.marks 50 6 58 false,3),
    (.marks 50 6 74 false,136),
    (.marks 50 7 58 false,1),
    (.marks 50 7 66 false,4),
    (.marks 50 7 74 false,94),
    (.marks 50 8 58 false,28),
    (.marks 50 8 66 false,49),
    (.marks 50 8 74 false,24),
    (.marks 50 9 58 false,16),
    (.marks 50 9 66 false,52),
    (.marks 50 10 58 false,3),
    (.marks 50 10 66 false,40),
    (.marks 50 11 58 false,4),
    (.marks 50 11 66 false,29),
    (.marks 50 12 58 false,23),
    (.marks 50 12 66 false,22),
    (.marks 50 13 58 false,23),
    (.marks 50 13 66 false,16),
    (.marks 50 14 58 false,5),
    (.marks 50 14 66 false,11),
    (.marks 50 15 58 false,22),
    (.marks 50 15 66 false,8),
    (.marks 50 16 58 false,14),
    (.marks 50 16 66 false,4),
    (.marks 50 17 58 false,10),
    (.marks 50 18 58 false,31),
    (.marks 50 19 58 false,8),
    (.overlap 50 25 7 43,208),
    (.overlap 50 27 7 43,76),
    (.overlap 52 24 12 42,198),
    (.overlap 52 26 12 42,370),
    (.overlap 52 28 12 42,42),
    (.overlap 54 28 18 40,318),
    (.overlap 54 30 18 40,288),
    (.overlap 56 32 26 36,142),
    (.overlap 56 34 26 36,34),
    (.overlap 56 36 26 36,88)]⟩,
   []⟩

private theorem source029From50 : Window source029.plan source029.extras 50 57 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source029From58 : Window source029.plan source029.extras 58 65 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source029From66 : Window source029.plan source029.extras 66 73 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source029From74 : Window source029.plan source029.extras 74 81 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source029From82 : Window source029.plan source029.extras 82 89 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source029From90 : Window source029.plan source029.extras 90 97 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source029From98 : Window source029.plan source029.extras 98 105 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source029From106 : Window source029.plan source029.extras 106 113 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source029From114 : Window source029.plan source029.extras 114 121 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source029From122 : Window source029.plan source029.extras 122 129 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source029From130 : Window source029.plan source029.extras 130 137 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source029From138 : Window source029.plan source029.extras 138 145 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)
private theorem source029From146 : Window source029.plan source029.extras 146 152 :=
  window (g:=IndividualFloors20258.prices) (by decide +kernel)

theorem source029_valid : source029.Valid := by
  change source029.plan.Valid
  apply ordinary
  exact certify (by decide +kernel) (by decide +kernel) (join (join (join source029From50 (join source029From58 source029From66)) (join source029From74 (join source029From82 source029From90))) (join (join source029From98 (join source029From106 source029From114)) (join (join source029From122 source029From130) (join source029From138 source029From146))))

end JSP233.PopulationSources20258
