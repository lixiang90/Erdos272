import Erdos272.Arithmetic.SigmaWBase209
import Erdos272.Arithmetic.SigmaWBlock209_000
import Erdos272.Arithmetic.SigmaWBlock209_001
import Erdos272.Arithmetic.SigmaWBlock209_002
import Erdos272.Arithmetic.SigmaWBlock209_003
import Erdos272.Arithmetic.SigmaWBlock209_004
import Erdos272.Arithmetic.SigmaWBlock209_005
import Erdos272.Arithmetic.SigmaWBlock209_006
import Erdos272.Arithmetic.SigmaWBlock209_007
import Erdos272.Arithmetic.SigmaWBlock209_008
import Erdos272.Arithmetic.SigmaWBlock209_009
import Erdos272.Arithmetic.SigmaWBlock209_010
import Erdos272.Arithmetic.SigmaWBlock209_011
import Erdos272.Arithmetic.SigmaWBlock209_012
namespace JSP233.SigmaWChecked209
set_option maxHeartbeats 0
theorem state_32768 :
    (883134861=SigmaPrefix209.mass SigmaValue209.value 32768 ∧
     9645726899957=SigmaPrefix209.weighted SigmaValue209.value 32768) ∧
    ∀ t,0<t → t≤32768 → 31≤t → SigmaPrefix209.Good t
      (SigmaPrefix209.weighted SigmaValue209.value t) := by
  exact SigmaPrefix209.checkFrom_sound SigmaValue209.value 32768 0 0 0 883134861 9645726899957 (by decide +kernel) rfl SigmaWBase209.checked

theorem state_65536 :
    (3532518195=SigmaPrefix209.mass SigmaValue209.value 65536 ∧
     77166889199270=SigmaPrefix209.weighted SigmaValue209.value 65536) ∧
    ∀ t,32768<t → t≤65536 → 31≤t → SigmaPrefix209.Good t
      (SigmaPrefix209.weighted SigmaValue209.value t) := by
  exact SigmaPrefix209.checkFrom_sound SigmaValue209.value 32768 32768 883134861 9645726899957 3532518195 77166889199270 state_32768.1.1 state_32768.1.2 SigmaWBlock209_000.checked_32768

theorem state_98304 :
    (7948131532=SigmaPrefix209.mass SigmaValue209.value 98304 ∧
     260439459210299=SigmaPrefix209.weighted SigmaValue209.value 98304) ∧
    ∀ t,65536<t → t≤98304 → 31≤t → SigmaPrefix209.Good t
      (SigmaPrefix209.weighted SigmaValue209.value t) := by
  exact SigmaPrefix209.checkFrom_sound SigmaValue209.value 32768 65536 3532518195 77166889199270 7948131532 260439459210299 state_65536.1.1 state_65536.1.2 SigmaWBlock209_000.checked_65536

theorem state_131072 :
    (14129951284=SigmaPrefix209.mass SigmaValue209.value 131072 ∧
     617339409214351=SigmaPrefix209.weighted SigmaValue209.value 131072) ∧
    ∀ t,98304<t → t≤131072 → 31≤t → SigmaPrefix209.Good t
      (SigmaPrefix209.weighted SigmaValue209.value t) := by
  exact SigmaPrefix209.checkFrom_sound SigmaValue209.value 32768 98304 7948131532 260439459210299 14129951284 617339409214351 state_98304.1.1 state_98304.1.2 SigmaWBlock209_000.checked_98304

theorem state_163840 :
    (22078048848=SigmaPrefix209.mass SigmaValue209.value 163840 ∧
     1205742711120720=SigmaPrefix209.weighted SigmaValue209.value 163840) ∧
    ∀ t,131072<t → t≤163840 → 31≤t → SigmaPrefix209.Good t
      (SigmaPrefix209.weighted SigmaValue209.value t) := by
  exact SigmaPrefix209.checkFrom_sound SigmaValue209.value 32768 131072 14129951284 617339409214351 22078048848 1205742711120720 state_131072.1.1 state_131072.1.2 SigmaWBlock209_000.checked_131072

theorem state_196608 :
    (31792387858=SigmaPrefix209.mass SigmaValue209.value 196608 ∧
     2083525337909510=SigmaPrefix209.weighted SigmaValue209.value 196608) ∧
    ∀ t,163840<t → t≤196608 → 31≤t → SigmaPrefix209.Good t
      (SigmaPrefix209.weighted SigmaValue209.value t) := by
  exact SigmaPrefix209.checkFrom_sound SigmaValue209.value 32768 163840 22078048848 1205742711120720 31792387858 2083525337909510 state_163840.1.1 state_163840.1.2 SigmaWBlock209_001.checked_163840

theorem state_229376 :
    (43272914232=SigmaPrefix209.mass SigmaValue209.value 229376 ∧
     3308563261205529=SigmaPrefix209.weighted SigmaValue209.value 229376) ∧
    ∀ t,196608<t → t≤229376 → 31≤t → SigmaPrefix209.Good t
      (SigmaPrefix209.weighted SigmaValue209.value t) := by
  exact SigmaPrefix209.checkFrom_sound SigmaValue209.value 32768 196608 31792387858 2083525337909510 43272914232 3308563261205529 state_196608.1.1 state_196608.1.2 SigmaWBlock209_001.checked_196608

theorem state_262144 :
    (56519699688=SigmaPrefix209.mass SigmaValue209.value 262144 ∧
     4938732453590792=SigmaPrefix209.weighted SigmaValue209.value 262144) ∧
    ∀ t,229376<t → t≤262144 → 31≤t → SigmaPrefix209.Good t
      (SigmaPrefix209.weighted SigmaValue209.value t) := by
  exact SigmaPrefix209.checkFrom_sound SigmaValue209.value 32768 229376 43272914232 3308563261205529 56519699688 4938732453590792 state_229376.1.1 state_229376.1.2 SigmaWBlock209_001.checked_229376

theorem state_294912 :
    (71532820517=SigmaPrefix209.mass SigmaValue209.value 294912 ∧
     7031908887384602=SigmaPrefix209.weighted SigmaValue209.value 294912) ∧
    ∀ t,262144<t → t≤294912 → 31≤t → SigmaPrefix209.Good t
      (SigmaPrefix209.weighted SigmaValue209.value t) := by
  exact SigmaPrefix209.checkFrom_sound SigmaValue209.value 32768 262144 56519699688 4938732453590792 71532820517 7031908887384602 state_262144.1.1 state_262144.1.2 SigmaWBlock209_001.checked_262144

theorem state_327680 :
    (88311968888=SigmaPrefix209.mass SigmaValue209.value 327680 ∧
     9645968533835136=SigmaPrefix209.weighted SigmaValue209.value 327680) ∧
    ∀ t,294912<t → t≤327680 → 31≤t → SigmaPrefix209.Good t
      (SigmaPrefix209.weighted SigmaValue209.value t) := by
  exact SigmaPrefix209.checkFrom_sound SigmaValue209.value 32768 294912 71532820517 7031908887384602 88311968888 9645968533835136 state_294912.1.1 state_294912.1.2 SigmaWBlock209_002.checked_294912

theorem state_360448 :
    (106857296986=SigmaPrefix209.mass SigmaValue209.value 360448 ∧
     12838787367170674=SigmaPrefix209.weighted SigmaValue209.value 360448) ∧
    ∀ t,327680<t → t≤360448 → 31≤t → SigmaPrefix209.Good t
      (SigmaPrefix209.weighted SigmaValue209.value t) := by
  exact SigmaPrefix209.checkFrom_sound SigmaValue209.value 32768 327680 88311968888 9645968533835136 106857296986 12838787367170674 state_327680.1.1 state_327680.1.2 SigmaWBlock209_002.checked_327680

theorem state_393216 :
    (127169217062=SigmaPrefix209.mass SigmaValue209.value 393216 ∧
     16668241359257036=SigmaPrefix209.weighted SigmaValue209.value 393216) ∧
    ∀ t,360448<t → t≤393216 → 31≤t → SigmaPrefix209.Good t
      (SigmaPrefix209.weighted SigmaValue209.value t) := by
  exact SigmaPrefix209.checkFrom_sound SigmaValue209.value 32768 360448 106857296986 12838787367170674 127169217062 16668241359257036 state_360448.1.1 state_360448.1.2 SigmaWBlock209_002.checked_360448

theorem state_425984 :
    (149246955745=SigmaPrefix209.mass SigmaValue209.value 425984 ∧
     21192206480068162=SigmaPrefix209.weighted SigmaValue209.value 425984) ∧
    ∀ t,393216<t → t≤425984 → 31≤t → SigmaPrefix209.Good t
      (SigmaPrefix209.weighted SigmaValue209.value t) := by
  exact SigmaPrefix209.checkFrom_sound SigmaValue209.value 32768 393216 127169217062 16668241359257036 149246955745 21192206480068162 state_393216.1.1 state_393216.1.2 SigmaWBlock209_002.checked_393216

theorem state_458752 :
    (173091327877=SigmaPrefix209.mass SigmaValue209.value 458752 ∧
     26468558704645583=SigmaPrefix209.weighted SigmaValue209.value 458752) ∧
    ∀ t,425984<t → t≤458752 → 31≤t → SigmaPrefix209.Good t
      (SigmaPrefix209.weighted SigmaValue209.value t) := by
  exact SigmaPrefix209.checkFrom_sound SigmaValue209.value 32768 425984 149246955745 21192206480068162 173091327877 26468558704645583 state_425984.1.1 state_425984.1.2 SigmaWBlock209_003.checked_425984

theorem state_491520 :
    (198701926132=SigmaPrefix209.mass SigmaValue209.value 491520 ∧
     32555174002780811=SigmaPrefix209.weighted SigmaValue209.value 491520) ∧
    ∀ t,458752<t → t≤491520 → 31≤t → SigmaPrefix209.Good t
      (SigmaPrefix209.weighted SigmaValue209.value t) := by
  exact SigmaPrefix209.checkFrom_sound SigmaValue209.value 32768 458752 173091327877 26468558704645583 198701926132 32555174002780811 state_458752.1.1 state_458752.1.2 SigmaWBlock209_003.checked_458752

theorem state_524288 :
    (226078355122=SigmaPrefix209.mass SigmaValue209.value 524288 ∧
     39509928349949158=SigmaPrefix209.weighted SigmaValue209.value 524288) ∧
    ∀ t,491520<t → t≤524288 → 31≤t → SigmaPrefix209.Good t
      (SigmaPrefix209.weighted SigmaValue209.value t) := by
  exact SigmaPrefix209.checkFrom_sound SigmaValue209.value 32768 491520 198701926132 32555174002780811 226078355122 39509928349949158 state_491520.1.1 state_491520.1.2 SigmaWBlock209_003.checked_491520

theorem state_557056 :
    (255221259495=SigmaPrefix209.mass SigmaValue209.value 557056 ∧
     47390697715389575=SigmaPrefix209.weighted SigmaValue209.value 557056) ∧
    ∀ t,524288<t → t≤557056 → 31≤t → SigmaPrefix209.Good t
      (SigmaPrefix209.weighted SigmaValue209.value t) := by
  exact SigmaPrefix209.checkFrom_sound SigmaValue209.value 32768 524288 226078355122 39509928349949158 255221259495 47390697715389575 state_524288.1.1 state_524288.1.2 SigmaWBlock209_003.checked_524288

theorem state_589824 :
    (286130601301=SigmaPrefix209.mass SigmaValue209.value 589824 ∧
     56255358072574848=SigmaPrefix209.weighted SigmaValue209.value 589824) ∧
    ∀ t,557056<t → t≤589824 → 31≤t → SigmaPrefix209.Good t
      (SigmaPrefix209.weighted SigmaValue209.value t) := by
  exact SigmaPrefix209.checkFrom_sound SigmaValue209.value 32768 557056 255221259495 47390697715389575 286130601301 56255358072574848 state_557056.1.1 state_557056.1.2 SigmaWBlock209_004.checked_557056

theorem state_622592 :
    (318805575924=SigmaPrefix209.mass SigmaValue209.value 622592 ∧
     66161785394834323=SigmaPrefix209.weighted SigmaValue209.value 622592) ∧
    ∀ t,589824<t → t≤622592 → 31≤t → SigmaPrefix209.Good t
      (SigmaPrefix209.weighted SigmaValue209.value t) := by
  exact SigmaPrefix209.checkFrom_sound SigmaValue209.value 32768 589824 286130601301 56255358072574848 318805575924 66161785394834323 state_589824.1.1 state_589824.1.2 SigmaWBlock209_004.checked_589824

theorem state_655360 :
    (353247314241=SigmaPrefix209.mass SigmaValue209.value 655360 ∧
     77167855651521567=SigmaPrefix209.weighted SigmaValue209.value 655360) ∧
    ∀ t,622592<t → t≤655360 → 31≤t → SigmaPrefix209.Good t
      (SigmaPrefix209.weighted SigmaValue209.value t) := by
  exact SigmaPrefix209.checkFrom_sound SigmaValue209.value 32768 622592 318805575924 66161785394834323 353247314241 77167855651521567 state_622592.1.1 state_622592.1.2 SigmaWBlock209_004.checked_622592

theorem state_688128 :
    (389455435091=SigmaPrefix209.mass SigmaValue209.value 688128 ∧
     89331444817939897=SigmaPrefix209.weighted SigmaValue209.value 688128) ∧
    ∀ t,655360<t → t≤688128 → 31≤t → SigmaPrefix209.Good t
      (SigmaPrefix209.weighted SigmaValue209.value t) := by
  exact SigmaPrefix209.checkFrom_sound SigmaValue209.value 32768 655360 353247314241 77167855651521567 389455435091 89331444817939897 state_655360.1.1 state_655360.1.2 SigmaWBlock209_004.checked_655360

theorem state_720896 :
    (427429064375=SigmaPrefix209.mass SigmaValue209.value 720896 ∧
     102710428864543979=SigmaPrefix209.weighted SigmaValue209.value 720896) ∧
    ∀ t,688128<t → t≤720896 → 31≤t → SigmaPrefix209.Good t
      (SigmaPrefix209.weighted SigmaValue209.value t) := by
  exact SigmaPrefix209.checkFrom_sound SigmaValue209.value 32768 688128 389455435091 89331444817939897 427429064375 102710428864543979 state_688128.1.1 state_688128.1.2 SigmaWBlock209_005.checked_688128

theorem state_753664 :
    (467169576809=SigmaPrefix209.mass SigmaValue209.value 753664 ∧
     117362683765698588=SigmaPrefix209.weighted SigmaValue209.value 753664) ∧
    ∀ t,720896<t → t≤753664 → 31≤t → SigmaPrefix209.Good t
      (SigmaPrefix209.weighted SigmaValue209.value t) := by
  exact SigmaPrefix209.checkFrom_sound SigmaValue209.value 32768 720896 427429064375 102710428864543979 467169576809 117362683765698588 state_720896.1.1 state_720896.1.2 SigmaWBlock209_005.checked_720896

theorem state_786432 :
    (508676234635=SigmaPrefix209.mass SigmaValue209.value 786432 ∧
     133346085490306931=SigmaPrefix209.weighted SigmaValue209.value 786432) ∧
    ∀ t,753664<t → t≤786432 → 31≤t → SigmaPrefix209.Good t
      (SigmaPrefix209.weighted SigmaValue209.value t) := by
  exact SigmaPrefix209.checkFrom_sound SigmaValue209.value 32768 753664 467169576809 117362683765698588 508676234635 133346085490306931 state_753664.1.1 state_753664.1.2 SigmaWBlock209_005.checked_753664

theorem state_819200 :
    (551948952109=SigmaPrefix209.mass SigmaValue209.value 819200 ∧
     150718510013007001=SigmaPrefix209.weighted SigmaValue209.value 819200) ∧
    ∀ t,786432<t → t≤819200 → 31≤t → SigmaPrefix209.Good t
      (SigmaPrefix209.weighted SigmaValue209.value t) := by
  exact SigmaPrefix209.checkFrom_sound SigmaValue209.value 32768 786432 508676234635 133346085490306931 551948952109 150718510013007001 state_786432.1.1 state_786432.1.2 SigmaWBlock209_005.checked_786432

theorem state_851968 :
    (596987656585=SigmaPrefix209.mass SigmaValue209.value 851968 ∧
     169537833305375632=SigmaPrefix209.weighted SigmaValue209.value 851968) ∧
    ∀ t,819200<t → t≤851968 → 31≤t → SigmaPrefix209.Good t
      (SigmaPrefix209.weighted SigmaValue209.value t) := by
  exact SigmaPrefix209.checkFrom_sound SigmaValue209.value 32768 819200 551948952109 150718510013007001 596987656585 169537833305375632 state_819200.1.1 state_819200.1.2 SigmaWBlock209_006.checked_819200

theorem state_884736 :
    (643793362829=SigmaPrefix209.mass SigmaValue209.value 884736 ∧
     189861931339928742=SigmaPrefix209.weighted SigmaValue209.value 884736) ∧
    ∀ t,851968<t → t≤884736 → 31≤t → SigmaPrefix209.Good t
      (SigmaPrefix209.weighted SigmaValue209.value t) := by
  exact SigmaPrefix209.checkFrom_sound SigmaValue209.value 32768 851968 596987656585 169537833305375632 643793362829 189861931339928742 state_851968.1.1 state_851968.1.2 SigmaWBlock209_006.checked_851968

theorem state_917504 :
    (692364419336=SigmaPrefix209.mass SigmaValue209.value 917504 ∧
     211748680091400001=SigmaPrefix209.weighted SigmaValue209.value 917504) ∧
    ∀ t,884736<t → t≤917504 → 31≤t → SigmaPrefix209.Good t
      (SigmaPrefix209.weighted SigmaValue209.value t) := by
  exact SigmaPrefix209.checkFrom_sound SigmaValue209.value 32768 884736 643793362829 189861931339928742 692364419336 211748680091400001 state_884736.1.1 state_884736.1.2 SigmaWBlock209_006.checked_884736

theorem state_950272 :
    (742702242939=SigmaPrefix209.mass SigmaValue209.value 950272 ∧
     235255955526925439=SigmaPrefix209.weighted SigmaValue209.value 950272) ∧
    ∀ t,917504<t → t≤950272 → 31≤t → SigmaPrefix209.Good t
      (SigmaPrefix209.weighted SigmaValue209.value t) := by
  exact SigmaPrefix209.checkFrom_sound SigmaValue209.value 32768 917504 692364419336 211748680091400001 742702242939 235255955526925439 state_917504.1.1 state_917504.1.2 SigmaWBlock209_006.checked_917504

theorem state_983040 :
    (794806589490=SigmaPrefix209.mass SigmaValue209.value 983040 ∧
     260441633618669750=SigmaPrefix209.weighted SigmaValue209.value 983040) ∧
    ∀ t,950272<t → t≤983040 → 31≤t → SigmaPrefix209.Good t
      (SigmaPrefix209.weighted SigmaValue209.value t) := by
  exact SigmaPrefix209.checkFrom_sound SigmaValue209.value 32768 950272 742702242939 235255955526925439 794806589490 260441633618669750 state_950272.1.1 state_950272.1.2 SigmaWBlock209_007.checked_950272

theorem state_1015808 :
    (848676129169=SigmaPrefix209.mass SigmaValue209.value 1015808 ∧
     287363590349003096=SigmaPrefix209.weighted SigmaValue209.value 1015808) ∧
    ∀ t,983040<t → t≤1015808 → 31≤t → SigmaPrefix209.Good t
      (SigmaPrefix209.weighted SigmaValue209.value t) := by
  exact SigmaPrefix209.checkFrom_sound SigmaValue209.value 32768 983040 794806589490 260441633618669750 848676129169 287363590349003096 state_983040.1.1 state_983040.1.2 SigmaWBlock209_007.checked_983040

theorem state_1048576 :
    (904312961284=SigmaPrefix209.mass SigmaValue209.value 1048576 ∧
     316079701674661190=SigmaPrefix209.weighted SigmaValue209.value 1048576) ∧
    ∀ t,1015808<t → t≤1048576 → 31≤t → SigmaPrefix209.Good t
      (SigmaPrefix209.weighted SigmaValue209.value t) := by
  exact SigmaPrefix209.checkFrom_sound SigmaValue209.value 32768 1015808 848676129169 287363590349003096 904312961284 316079701674661190 state_1015808.1.1 state_1015808.1.2 SigmaWBlock209_007.checked_1015808

theorem state_1081344 :
    (961715476158=SigmaPrefix209.mass SigmaValue209.value 1081344 ∧
     346647843581531278=SigmaPrefix209.weighted SigmaValue209.value 1081344) ∧
    ∀ t,1048576<t → t≤1081344 → 31≤t → SigmaPrefix209.Good t
      (SigmaPrefix209.weighted SigmaValue209.value t) := by
  exact SigmaPrefix209.checkFrom_sound SigmaValue209.value 32768 1048576 904312961284 316079701674661190 961715476158 346647843581531278 state_1048576.1.1 state_1048576.1.2 SigmaWBlock209_007.checked_1048576

theorem state_1114112 :
    (1020884044627=SigmaPrefix209.mass SigmaValue209.value 1114112 ∧
     379125892034555784=SigmaPrefix209.weighted SigmaValue209.value 1114112) ∧
    ∀ t,1081344<t → t≤1114112 → 31≤t → SigmaPrefix209.Good t
      (SigmaPrefix209.weighted SigmaValue209.value t) := by
  exact SigmaPrefix209.checkFrom_sound SigmaValue209.value 32768 1081344 961715476158 346647843581531278 1020884044627 379125892034555784 state_1081344.1.1 state_1081344.1.2 SigmaWBlock209_008.checked_1081344

theorem state_1146880 :
    (1081819722725=SigmaPrefix209.mass SigmaValue209.value 1146880 ∧
     413571723007393013=SigmaPrefix209.weighted SigmaValue209.value 1146880) ∧
    ∀ t,1114112<t → t≤1146880 → 31≤t → SigmaPrefix209.Good t
      (SigmaPrefix209.weighted SigmaValue209.value t) := by
  exact SigmaPrefix209.checkFrom_sound SigmaValue209.value 32768 1114112 1020884044627 379125892034555784 1081819722725 413571723007393013 state_1114112.1.1 state_1114112.1.2 SigmaWBlock209_008.checked_1114112

theorem state_1179648 :
    (1144521227282=SigmaPrefix209.mass SigmaValue209.value 1179648 ∧
     450043212476086539=SigmaPrefix209.weighted SigmaValue209.value 1179648) ∧
    ∀ t,1146880<t → t≤1179648 → 31≤t → SigmaPrefix209.Good t
      (SigmaPrefix209.weighted SigmaValue209.value t) := by
  exact SigmaPrefix209.checkFrom_sound SigmaValue209.value 32768 1146880 1081819722725 413571723007393013 1144521227282 450043212476086539 state_1146880.1.1 state_1146880.1.2 SigmaWBlock209_008.checked_1146880

theorem state_1212416 :
    (1208988099319=SigmaPrefix209.mass SigmaValue209.value 1212416 ∧
     488598236408629381=SigmaPrefix209.weighted SigmaValue209.value 1212416) ∧
    ∀ t,1179648<t → t≤1212416 → 31≤t → SigmaPrefix209.Good t
      (SigmaPrefix209.weighted SigmaValue209.value t) := by
  exact SigmaPrefix209.checkFrom_sound SigmaValue209.value 32768 1179648 1144521227282 450043212476086539 1208988099319 488598236408629381 state_1179648.1.1 state_1179648.1.2 SigmaWBlock209_008.checked_1179648

theorem state_1245184 :
    (1275221843368=SigmaPrefix209.mass SigmaValue209.value 1245184 ∧
     529294670777401336=SigmaPrefix209.weighted SigmaValue209.value 1245184) ∧
    ∀ t,1212416<t → t≤1245184 → 31≤t → SigmaPrefix209.Good t
      (SigmaPrefix209.weighted SigmaValue209.value t) := by
  exact SigmaPrefix209.checkFrom_sound SigmaValue209.value 32768 1212416 1208988099319 488598236408629381 1275221843368 529294670777401336 state_1212416.1.1 state_1212416.1.2 SigmaWBlock209_009.checked_1212416

theorem state_1277952 :
    (1343222559417=SigmaPrefix209.mass SigmaValue209.value 1277952 ∧
     572190391549258093=SigmaPrefix209.weighted SigmaValue209.value 1277952) ∧
    ∀ t,1245184<t → t≤1277952 → 31≤t → SigmaPrefix209.Good t
      (SigmaPrefix209.weighted SigmaValue209.value t) := by
  exact SigmaPrefix209.checkFrom_sound SigmaValue209.value 32768 1245184 1275221843368 529294670777401336 1343222559417 572190391549258093 state_1245184.1.1 state_1245184.1.2 SigmaWBlock209_009.checked_1245184

theorem state_1310720 :
    (1412988441977=SigmaPrefix209.mass SigmaValue209.value 1310720 ∧
     617343274710874100=SigmaPrefix209.weighted SigmaValue209.value 1310720) ∧
    ∀ t,1277952<t → t≤1310720 → 31≤t → SigmaPrefix209.Good t
      (SigmaPrefix209.weighted SigmaValue209.value t) := by
  exact SigmaPrefix209.checkFrom_sound SigmaValue209.value 32768 1277952 1343222559417 572190391549258093 1412988441977 617343274710874100 state_1277952.1.1 state_1277952.1.2 SigmaWBlock209_009.checked_1277952

theorem state_1343488 :
    (1484520615210=SigmaPrefix209.mass SigmaValue209.value 1343488 ∧
     664811196230396280=SigmaPrefix209.weighted SigmaValue209.value 1343488) ∧
    ∀ t,1310720<t → t≤1343488 → 31≤t → SigmaPrefix209.Good t
      (SigmaPrefix209.weighted SigmaValue209.value t) := by
  exact SigmaPrefix209.checkFrom_sound SigmaValue209.value 32768 1310720 1412988441977 617343274710874100 1484520615210 664811196230396280 state_1310720.1.1 state_1310720.1.2 SigmaWBlock209_009.checked_1310720

theorem state_1376256 :
    (1557820517200=SigmaPrefix209.mass SigmaValue209.value 1376256 ∧
     714652032064866399=SigmaPrefix209.weighted SigmaValue209.value 1376256) ∧
    ∀ t,1343488<t → t≤1376256 → 31≤t → SigmaPrefix209.Good t
      (SigmaPrefix209.weighted SigmaValue209.value t) := by
  exact SigmaPrefix209.checkFrom_sound SigmaValue209.value 32768 1343488 1484520615210 664811196230396280 1557820517200 714652032064866399 state_1343488.1.1 state_1343488.1.2 SigmaWBlock209_010.checked_1343488

theorem state_1409024 :
    (1632884485780=SigmaPrefix209.mass SigmaValue209.value 1409024 ∧
     766923658203041330=SigmaPrefix209.weighted SigmaValue209.value 1409024) ∧
    ∀ t,1376256<t → t≤1409024 → 31≤t → SigmaPrefix209.Good t
      (SigmaPrefix209.weighted SigmaValue209.value t) := by
  exact SigmaPrefix209.checkFrom_sound SigmaValue209.value 32768 1376256 1557820517200 714652032064866399 1632884485780 766923658203041330 state_1376256.1.1 state_1376256.1.2 SigmaWBlock209_010.checked_1376256

theorem state_1441792 :
    (1709715966837=SigmaPrefix209.mass SigmaValue209.value 1441792 ∧
     821683950610673542=SigmaPrefix209.weighted SigmaValue209.value 1441792) ∧
    ∀ t,1409024<t → t≤1441792 → 31≤t → SigmaPrefix209.Good t
      (SigmaPrefix209.weighted SigmaValue209.value t) := by
  exact SigmaPrefix209.checkFrom_sound SigmaValue209.value 32768 1409024 1632884485780 766923658203041330 1709715966837 821683950610673542 state_1409024.1.1 state_1409024.1.2 SigmaWBlock209_010.checked_1409024

theorem state_1474560 :
    (1788314208782=SigmaPrefix209.mass SigmaValue209.value 1474560 ∧
     878990785259547359=SigmaPrefix209.weighted SigmaValue209.value 1474560) ∧
    ∀ t,1441792<t → t≤1474560 → 31≤t → SigmaPrefix209.Good t
      (SigmaPrefix209.weighted SigmaValue209.value t) := by
  exact SigmaPrefix209.checkFrom_sound SigmaValue209.value 32768 1441792 1709715966837 821683950610673542 1788314208782 878990785259547359 state_1441792.1.1 state_1441792.1.2 SigmaWBlock209_010.checked_1441792

theorem state_1507328 :
    (1868676897079=SigmaPrefix209.mass SigmaValue209.value 1507328 ∧
     938902038128466394=SigmaPrefix209.weighted SigmaValue209.value 1507328) ∧
    ∀ t,1474560<t → t≤1507328 → 31≤t → SigmaPrefix209.Good t
      (SigmaPrefix209.weighted SigmaValue209.value t) := by
  exact SigmaPrefix209.checkFrom_sound SigmaValue209.value 32768 1474560 1788314208782 878990785259547359 1868676897079 938902038128466394 state_1474560.1.1 state_1474560.1.2 SigmaWBlock209_011.checked_1474560

theorem state_1540096 :
    (1950806729308=SigmaPrefix209.mass SigmaValue209.value 1540096 ∧
     1001475585175743233=SigmaPrefix209.weighted SigmaValue209.value 1540096) ∧
    ∀ t,1507328<t → t≤1540096 → 31≤t → SigmaPrefix209.Good t
      (SigmaPrefix209.weighted SigmaValue209.value t) := by
  exact SigmaPrefix209.checkFrom_sound SigmaValue209.value 32768 1507328 1868676897079 938902038128466394 1950806729308 1001475585175743233 state_1507328.1.1 state_1507328.1.2 SigmaWBlock209_011.checked_1507328

theorem state_1572864 :
    (2034703314496=SigmaPrefix209.mass SigmaValue209.value 1572864 ∧
     1066769302399477479=SigmaPrefix209.weighted SigmaValue209.value 1572864) ∧
    ∀ t,1540096<t → t≤1572864 → 31≤t → SigmaPrefix209.Good t
      (SigmaPrefix209.weighted SigmaValue209.value t) := by
  exact SigmaPrefix209.checkFrom_sound SigmaValue209.value 32768 1540096 1950806729308 1001475585175743233 2034703314496 1066769302399477479 state_1540096.1.1 state_1540096.1.2 SigmaWBlock209_011.checked_1540096

theorem state_1605632 :
    (2120365692169=SigmaPrefix209.mass SigmaValue209.value 1605632 ∧
     1134841065742355028=SigmaPrefix209.weighted SigmaValue209.value 1605632) ∧
    ∀ t,1572864<t → t≤1605632 → 31≤t → SigmaPrefix209.Good t
      (SigmaPrefix209.weighted SigmaValue209.value t) := by
  exact SigmaPrefix209.checkFrom_sound SigmaValue209.value 32768 1572864 2034703314496 1066769302399477479 2120365692169 1134841065742355028 state_1572864.1.1 state_1572864.1.2 SigmaWBlock209_011.checked_1572864

theorem state_1638400 :
    (2207794612777=SigmaPrefix209.mass SigmaValue209.value 1638400 ∧
     1205748751192216168=SigmaPrefix209.weighted SigmaValue209.value 1638400) ∧
    ∀ t,1605632<t → t≤1638400 → 31≤t → SigmaPrefix209.Good t
      (SigmaPrefix209.weighted SigmaValue209.value t) := by
  exact SigmaPrefix209.checkFrom_sound SigmaValue209.value 32768 1605632 2120365692169 1134841065742355028 2207794612777 1205748751192216168 state_1605632.1.1 state_1605632.1.2 SigmaWBlock209_012.checked_1605632

theorem state_1670000 :
    (2293779434299=SigmaPrefix209.mass SigmaValue209.value 1670000 ∧
     1276869228407426598=SigmaPrefix209.weighted SigmaValue209.value 1670000) ∧
    ∀ t,1638400<t → t≤1670000 → 31≤t → SigmaPrefix209.Good t
      (SigmaPrefix209.weighted SigmaValue209.value t) := by
  exact SigmaPrefix209.checkFrom_sound SigmaValue209.value 31600 1638400 2207794612777 1205748751192216168 2293779434299 1276869228407426598 state_1638400.1.1 state_1638400.1.2 SigmaWBlock209_012.checked_1638400

theorem good (s : Nat) (hs : 31≤s) (hsN : s≤1670000) :
    SigmaPrefix209.Good s (SigmaPrefix209.weighted SigmaValue209.value s) := by
  by_cases h_32768 : s≤32768
  · exact state_32768.2 s (by omega) h_32768 hs
  by_cases h_65536 : s≤65536
  · exact state_65536.2 s (by omega) h_65536 hs
  by_cases h_98304 : s≤98304
  · exact state_98304.2 s (by omega) h_98304 hs
  by_cases h_131072 : s≤131072
  · exact state_131072.2 s (by omega) h_131072 hs
  by_cases h_163840 : s≤163840
  · exact state_163840.2 s (by omega) h_163840 hs
  by_cases h_196608 : s≤196608
  · exact state_196608.2 s (by omega) h_196608 hs
  by_cases h_229376 : s≤229376
  · exact state_229376.2 s (by omega) h_229376 hs
  by_cases h_262144 : s≤262144
  · exact state_262144.2 s (by omega) h_262144 hs
  by_cases h_294912 : s≤294912
  · exact state_294912.2 s (by omega) h_294912 hs
  by_cases h_327680 : s≤327680
  · exact state_327680.2 s (by omega) h_327680 hs
  by_cases h_360448 : s≤360448
  · exact state_360448.2 s (by omega) h_360448 hs
  by_cases h_393216 : s≤393216
  · exact state_393216.2 s (by omega) h_393216 hs
  by_cases h_425984 : s≤425984
  · exact state_425984.2 s (by omega) h_425984 hs
  by_cases h_458752 : s≤458752
  · exact state_458752.2 s (by omega) h_458752 hs
  by_cases h_491520 : s≤491520
  · exact state_491520.2 s (by omega) h_491520 hs
  by_cases h_524288 : s≤524288
  · exact state_524288.2 s (by omega) h_524288 hs
  by_cases h_557056 : s≤557056
  · exact state_557056.2 s (by omega) h_557056 hs
  by_cases h_589824 : s≤589824
  · exact state_589824.2 s (by omega) h_589824 hs
  by_cases h_622592 : s≤622592
  · exact state_622592.2 s (by omega) h_622592 hs
  by_cases h_655360 : s≤655360
  · exact state_655360.2 s (by omega) h_655360 hs
  by_cases h_688128 : s≤688128
  · exact state_688128.2 s (by omega) h_688128 hs
  by_cases h_720896 : s≤720896
  · exact state_720896.2 s (by omega) h_720896 hs
  by_cases h_753664 : s≤753664
  · exact state_753664.2 s (by omega) h_753664 hs
  by_cases h_786432 : s≤786432
  · exact state_786432.2 s (by omega) h_786432 hs
  by_cases h_819200 : s≤819200
  · exact state_819200.2 s (by omega) h_819200 hs
  by_cases h_851968 : s≤851968
  · exact state_851968.2 s (by omega) h_851968 hs
  by_cases h_884736 : s≤884736
  · exact state_884736.2 s (by omega) h_884736 hs
  by_cases h_917504 : s≤917504
  · exact state_917504.2 s (by omega) h_917504 hs
  by_cases h_950272 : s≤950272
  · exact state_950272.2 s (by omega) h_950272 hs
  by_cases h_983040 : s≤983040
  · exact state_983040.2 s (by omega) h_983040 hs
  by_cases h_1015808 : s≤1015808
  · exact state_1015808.2 s (by omega) h_1015808 hs
  by_cases h_1048576 : s≤1048576
  · exact state_1048576.2 s (by omega) h_1048576 hs
  by_cases h_1081344 : s≤1081344
  · exact state_1081344.2 s (by omega) h_1081344 hs
  by_cases h_1114112 : s≤1114112
  · exact state_1114112.2 s (by omega) h_1114112 hs
  by_cases h_1146880 : s≤1146880
  · exact state_1146880.2 s (by omega) h_1146880 hs
  by_cases h_1179648 : s≤1179648
  · exact state_1179648.2 s (by omega) h_1179648 hs
  by_cases h_1212416 : s≤1212416
  · exact state_1212416.2 s (by omega) h_1212416 hs
  by_cases h_1245184 : s≤1245184
  · exact state_1245184.2 s (by omega) h_1245184 hs
  by_cases h_1277952 : s≤1277952
  · exact state_1277952.2 s (by omega) h_1277952 hs
  by_cases h_1310720 : s≤1310720
  · exact state_1310720.2 s (by omega) h_1310720 hs
  by_cases h_1343488 : s≤1343488
  · exact state_1343488.2 s (by omega) h_1343488 hs
  by_cases h_1376256 : s≤1376256
  · exact state_1376256.2 s (by omega) h_1376256 hs
  by_cases h_1409024 : s≤1409024
  · exact state_1409024.2 s (by omega) h_1409024 hs
  by_cases h_1441792 : s≤1441792
  · exact state_1441792.2 s (by omega) h_1441792 hs
  by_cases h_1474560 : s≤1474560
  · exact state_1474560.2 s (by omega) h_1474560 hs
  by_cases h_1507328 : s≤1507328
  · exact state_1507328.2 s (by omega) h_1507328 hs
  by_cases h_1540096 : s≤1540096
  · exact state_1540096.2 s (by omega) h_1540096 hs
  by_cases h_1572864 : s≤1572864
  · exact state_1572864.2 s (by omega) h_1572864 hs
  by_cases h_1605632 : s≤1605632
  · exact state_1605632.2 s (by omega) h_1605632 hs
  by_cases h_1638400 : s≤1638400
  · exact state_1638400.2 s (by omega) h_1638400 hs
  by_cases h_1670000 : s≤1670000
  · exact state_1670000.2 s (by omega) h_1670000 hs
  omega
#print axioms good
end JSP233.SigmaWChecked209
